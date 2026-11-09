//! A file on a RedoxFS image, shared by clients through one cache.
//!
//! A pwrite updates that cache, so a map already held sees the bytes with no
//! invalidate. The map size is a sparse truncate: unwritten pages read as
//! zeroes and the image stores only the blocks RedoxFS allocated.
//!
//! The lock file is a second shared map. A one-byte record lock belongs to
//! the client that took it: closing another handle does not release it, and
//! dropping the client does.
//!
//! A data pwrite is visible at once and unstable until `fdatasync`. The meta
//! suffix goes out through `sync_pwrite`, which does not return until those
//! bytes are stable together. A crash drops what is still unstable, or lands
//! a named subset of it first.

use std::collections::{BTreeMap, BTreeSet};
use std::fs;
use std::io::{self, ErrorKind};
use std::os::unix::fs::MetadataExt;
use std::path::{Path, PathBuf};
use std::sync::{Arc, Mutex};
use std::time::SystemTime;

use redoxfs::{DiskSparse, FileSystem, Node, TreePtr, BLOCK_SIZE};

mod ffi;

pub use ffi::{
    shim_create, shim_fdatasync, shim_get, shim_pread, shim_put, shim_pwrite, shim_size,
};

/// One page. LMDB's meta pages and RedoxFS blocks are this size.
pub const PAGE: u64 = BLOCK_SIZE;

/// Room past the map size for the filesystem itself.
const DISK_SLACK: u64 = 16 * 1024 * 1024;

#[derive(Clone, Copy)]
enum Which {
    Data,
    Lock,
}

struct File {
    node: TreePtr<Node>,
    size: u64,
    pages: BTreeMap<u64, Vec<u8>>,
}

/// One byte of the lock file. Exclusive and shared exclude each other.
#[derive(Default)]
struct ByteLock {
    exclusive: Option<u64>,
    shared: BTreeSet<u64>,
}

struct Inner {
    fs: FileSystem<DiskSparse>,
    image: PathBuf,
    data: File,
    lock: File,
    locks: BTreeMap<u64, ByteLock>,
    next_client: u64,
    /// Data pages whose cache is ahead of the image.
    data_dirty: BTreeSet<u64>,
    /// Logical size that a crash keeps.
    data_stable_size: u64,
}

/// The file service. Clients taken from it share one cache and one image.
pub struct Service {
    inner: Arc<Mutex<Inner>>,
}

/// One client of the service. Dropping it releases the record locks it holds.
pub struct Client {
    inner: Arc<Mutex<Inner>>,
    id: u64,
}

/// A shared view of the data file. It reads the service cache; nothing invalidates it.
pub struct SharedMap {
    inner: Arc<Mutex<Inner>>,
}

/// A writable shared view of the lock file. Dropping it does not release record locks.
pub struct LockMap {
    inner: Arc<Mutex<Inner>>,
}

/// A second open of the lock file. Closing it does not release record locks.
pub struct LockHandle {
    _inner: Arc<Mutex<Inner>>,
}

impl Service {
    /// Create `image`, a data file, and a lock file on a RedoxFS filesystem large enough for `map_size`.
    pub fn create(image: impl AsRef<Path>, map_size: u64) -> io::Result<Self> {
        let image = image.as_ref().to_path_buf();
        let disk_size = map_size
            .checked_add(DISK_SLACK)
            .ok_or_else(|| io::Error::new(ErrorKind::InvalidInput, "map size overflows"))?;
        let disk = DiskSparse::create(&image, disk_size).map_err(fs_err)?;
        let (sec, nsec) = now();
        let mut fs = FileSystem::create(disk, None, sec, nsec).map_err(fs_err)?;
        let data = fs
            .tx(|tx| {
                tx.create_node(
                    TreePtr::root(),
                    "data.mdb",
                    Node::MODE_FILE | 0o644,
                    sec,
                    nsec,
                )
            })
            .map_err(fs_err)?;
        let lock = fs
            .tx(|tx| {
                tx.create_node(
                    TreePtr::root(),
                    "data.mdb-lock",
                    Node::MODE_FILE | 0o644,
                    sec,
                    nsec,
                )
            })
            .map_err(fs_err)?;
        let inner = Inner {
            fs,
            image,
            data: File {
                node: data.ptr(),
                size: 0,
                pages: BTreeMap::new(),
            },
            lock: File {
                node: lock.ptr(),
                size: 0,
                pages: BTreeMap::new(),
            },
            locks: BTreeMap::new(),
            next_client: 1,
            data_dirty: BTreeSet::new(),
            data_stable_size: 0,
        };
        Ok(Self {
            inner: Arc::new(Mutex::new(inner)),
        })
    }

    pub fn client(&self) -> Client {
        let mut inner = self.inner.lock().expect("file service lock");
        let id = inner.next_client;
        inner.next_client += 1;
        Client {
            inner: Arc::clone(&self.inner),
            id,
        }
    }
}

impl Drop for Client {
    fn drop(&mut self) {
        self.inner
            .lock()
            .expect("file service lock")
            .release_client(self.id);
    }
}

impl Client {
    pub fn pread(&self, offset: u64, buf: &mut [u8]) -> io::Result<usize> {
        self.inner
            .lock()
            .expect("file service lock")
            .pread_file(Which::Data, offset, buf)
    }

    pub fn pwrite(&self, offset: u64, data: &[u8]) -> io::Result<()> {
        self.inner
            .lock()
            .expect("file service lock")
            .pwrite_file(Which::Data, offset, data)
    }

    /// Make every dirty data page stable. Does not write the meta page.
    pub fn fdatasync(&self) -> io::Result<()> {
        self.inner.lock().expect("file service lock").fdatasync()
    }

    /// Write `data` and return only once those bytes are stable, as one suffix.
    pub fn sync_pwrite(&self, offset: u64, data: &[u8]) -> io::Result<()> {
        self.inner
            .lock()
            .expect("file service lock")
            .sync_pwrite(offset, data)
    }

    /// Drop unstable data. Pages in `reorder` land first, in that order; the rest go.
    pub fn crash(&self, reorder: &[u64]) -> io::Result<()> {
        self.inner.lock().expect("file service lock").crash(reorder)
    }

    /// A crash during a synchronous pwrite. Only `prefix` bytes become stable.
    pub fn crash_during_sync_pwrite(
        &self,
        offset: u64,
        data: &[u8],
        prefix: usize,
    ) -> io::Result<()> {
        self.inner
            .lock()
            .expect("file service lock")
            .crash_during_sync_pwrite(offset, data, prefix)
    }

    /// The data file's logical size becomes `size`. A grow does not allocate the hole.
    pub fn set_map_size(&self, size: u64) -> io::Result<()> {
        self.inner
            .lock()
            .expect("file service lock")
            .set_map_size(size)
    }

    /// Blocks the image file occupies, in bytes.
    pub fn allocated_bytes(&self) -> io::Result<u64> {
        self.inner
            .lock()
            .expect("file service lock")
            .allocated_bytes()
    }

    pub fn map(&self) -> SharedMap {
        SharedMap {
            inner: Arc::clone(&self.inner),
        }
    }

    /// Exclusive lock of the one byte at `offset`. `WouldBlock` when another client holds it.
    pub fn lock_exclusive(&self, offset: u64) -> io::Result<()> {
        self.inner
            .lock()
            .expect("file service lock")
            .lock_exclusive(self.id, offset)
    }

    /// Shared lock of the one byte at `offset`. Replaces this client's exclusive lock there.
    pub fn lock_shared(&self, offset: u64) -> io::Result<()> {
        self.inner
            .lock()
            .expect("file service lock")
            .lock_shared(self.id, offset)
    }

    /// True when a different client holds the byte at `offset`.
    pub fn lock_blocks(&self, offset: u64) -> bool {
        self.inner
            .lock()
            .expect("file service lock")
            .lock_blocks(self.id, offset)
    }

    /// Logical size of the data file, including bytes not yet stable.
    pub fn size(&self) -> u64 {
        self.inner.lock().expect("file service lock").data.size
    }

    pub fn lock_map(&self) -> LockMap {
        LockMap {
            inner: Arc::clone(&self.inner),
        }
    }

    pub fn open_lock_handle(&self) -> LockHandle {
        LockHandle {
            _inner: Arc::clone(&self.inner),
        }
    }
}

impl SharedMap {
    /// The page at `index`. A hole reads as zeroes.
    pub fn page(&self, index: u64) -> io::Result<[u8; PAGE as usize]> {
        let mut buf = [0u8; PAGE as usize];
        let n = self.inner.lock().expect("file service lock").pread_file(
            Which::Data,
            index * PAGE,
            &mut buf,
        )?;
        if n < buf.len() {
            buf[n..].fill(0);
        }
        Ok(buf)
    }
}

impl LockMap {
    pub fn write_at(&self, offset: u64, data: &[u8]) -> io::Result<()> {
        self.inner
            .lock()
            .expect("file service lock")
            .pwrite_file(Which::Lock, offset, data)
    }

    pub fn read_at(&self, offset: u64, buf: &mut [u8]) -> io::Result<usize> {
        self.inner
            .lock()
            .expect("file service lock")
            .pread_file(Which::Lock, offset, buf)
    }
}

impl Inner {
    fn slot(&mut self, which: Which) -> &mut File {
        match which {
            Which::Data => &mut self.data,
            Which::Lock => &mut self.lock,
        }
    }

    fn pread_file(&mut self, which: Which, offset: u64, buf: &mut [u8]) -> io::Result<usize> {
        if offset >= self.slot(which).size || buf.is_empty() {
            return Ok(0);
        }
        let want = buf.len().min((self.slot(which).size - offset) as usize);
        let mut done = 0;
        while done < want {
            let abs = offset + done as u64;
            let page = abs / PAGE;
            let page_off = (abs % PAGE) as usize;
            let take = (PAGE as usize - page_off).min(want - done);
            let cached = self.slot(which).pages.get(&page).cloned();
            if let Some(cached) = cached {
                buf[done..done + take].copy_from_slice(&cached[page_off..page_off + take]);
            } else {
                let n = self.read_disk(which, abs, &mut buf[done..done + take])?;
                if n < take {
                    buf[done + n..done + take].fill(0);
                }
            }
            done += take;
        }
        Ok(want)
    }

    fn pwrite_file(&mut self, which: Which, offset: u64, data: &[u8]) -> io::Result<()> {
        if data.is_empty() {
            return Ok(());
        }
        let end = offset
            .checked_add(data.len() as u64)
            .ok_or_else(|| io::Error::new(ErrorKind::InvalidInput, "write overflows"))?;
        let mut done = 0;
        while done < data.len() {
            let abs = offset + done as u64;
            let page = abs / PAGE;
            let page_off = (abs % PAGE) as usize;
            let take = (PAGE as usize - page_off).min(data.len() - done);
            let mut bytes = if page_off == 0 && take == PAGE as usize {
                vec![0u8; PAGE as usize]
            } else {
                self.load_page(which, page)?
            };
            bytes[page_off..page_off + take].copy_from_slice(&data[done..done + take]);
            if let Which::Data = which {
                self.data_dirty.insert(page);
            } else {
                self.write_disk(which, page * PAGE, &bytes)?;
            }
            self.slot(which).pages.insert(page, bytes);
            done += take;
        }
        if end > self.slot(which).size {
            self.slot(which).size = end;
        }
        Ok(())
    }

    fn set_map_size(&mut self, size: u64) -> io::Result<()> {
        if size < self.data.size {
            return Err(io::Error::new(
                ErrorKind::InvalidInput,
                "map size shrinks the file",
            ));
        }
        let (sec, nsec) = now();
        let node = self.data.node;
        self.fs
            .tx(|tx| tx.truncate_node(node, size, sec, nsec))
            .map_err(fs_err)?;
        self.data.size = size;
        self.data_stable_size = size;
        Ok(())
    }

    fn fdatasync(&mut self) -> io::Result<()> {
        let dirty: Vec<u64> = self.data_dirty.iter().copied().collect();
        for page in dirty {
            let bytes = self.cached_page(page)?;
            self.write_disk(Which::Data, page * PAGE, &bytes)?;
            self.data_dirty.remove(&page);
        }
        self.data_stable_size = self.data.size;
        Ok(())
    }

    fn sync_pwrite(&mut self, offset: u64, data: &[u8]) -> io::Result<()> {
        self.pwrite_file(Which::Data, offset, data)?;
        self.stabilize_range(offset, data.len())
    }

    fn crash_during_sync_pwrite(
        &mut self,
        offset: u64,
        data: &[u8],
        prefix: usize,
    ) -> io::Result<()> {
        let prefix = prefix.min(data.len());
        if prefix > 0 {
            self.sync_pwrite(offset, &data[..prefix])?;
        }
        self.crash(&[])
    }

    fn crash(&mut self, reorder: &[u64]) -> io::Result<()> {
        for page in reorder {
            if !self.data_dirty.contains(page) {
                continue;
            }
            let bytes = self.cached_page(*page)?;
            self.write_disk(Which::Data, page * PAGE, &bytes)?;
            self.data_dirty.remove(page);
            let end = page.saturating_add(1).saturating_mul(PAGE);
            if end > self.data_stable_size && end <= self.data.size {
                self.data_stable_size = end;
            }
        }
        for page in self.data_dirty.iter().copied().collect::<Vec<_>>() {
            self.data.pages.remove(&page);
        }
        self.data_dirty.clear();
        self.data.size = self.data_stable_size;
        Ok(())
    }

    fn stabilize_range(&mut self, offset: u64, len: usize) -> io::Result<()> {
        if len == 0 {
            return Ok(());
        }
        let end = offset + len as u64;
        let mut page = offset / PAGE;
        let last = (end - 1) / PAGE;
        while page <= last {
            let bytes = self.cached_page(page)?;
            self.write_disk(Which::Data, page * PAGE, &bytes)?;
            self.data_dirty.remove(&page);
            page += 1;
        }
        self.data_stable_size = self.data.size;
        Ok(())
    }

    fn cached_page(&self, page: u64) -> io::Result<Vec<u8>> {
        self.data
            .pages
            .get(&page)
            .cloned()
            .ok_or_else(|| io::Error::other(format!("data page {page} is not in the cache")))
    }

    fn allocated_bytes(&self) -> io::Result<u64> {
        Ok(fs::metadata(&self.image)?.blocks() * 512)
    }

    fn load_page(&mut self, which: Which, page: u64) -> io::Result<Vec<u8>> {
        if let Some(cached) = self.slot(which).pages.get(&page) {
            return Ok(cached.clone());
        }
        let mut buf = vec![0u8; PAGE as usize];
        let offset = page * PAGE;
        if offset < self.slot(which).size {
            let n = self.read_disk(which, offset, &mut buf)?;
            buf[n..].fill(0);
        }
        Ok(buf)
    }

    fn read_disk(&mut self, which: Which, offset: u64, buf: &mut [u8]) -> io::Result<usize> {
        let node = self.slot(which).node;
        let (sec, nsec) = now();
        self.fs
            .tx(|tx| tx.read_node(node, offset, buf, sec, nsec))
            .map_err(fs_err)
    }

    fn write_disk(&mut self, which: Which, offset: u64, data: &[u8]) -> io::Result<()> {
        let node = self.slot(which).node;
        let (sec, nsec) = now();
        let n = self
            .fs
            .tx(|tx| tx.write_node(node, offset, data, sec, nsec))
            .map_err(fs_err)?;
        if n != data.len() {
            return Err(io::Error::new(
                ErrorKind::WriteZero,
                format!("redoxfs wrote {n} of {} bytes", data.len()),
            ));
        }
        Ok(())
    }

    fn lock_exclusive(&mut self, client: u64, offset: u64) -> io::Result<()> {
        let slot = self.locks.entry(offset).or_default();
        if slot.exclusive == Some(client) {
            return Ok(());
        }
        if slot.exclusive.is_some() || slot.shared.iter().any(|id| *id != client) {
            return Err(io::Error::new(ErrorKind::WouldBlock, "byte lock is held"));
        }
        slot.shared.remove(&client);
        slot.exclusive = Some(client);
        Ok(())
    }

    fn lock_shared(&mut self, client: u64, offset: u64) -> io::Result<()> {
        let slot = self.locks.entry(offset).or_default();
        if slot.exclusive.is_some() && slot.exclusive != Some(client) {
            return Err(io::Error::new(ErrorKind::WouldBlock, "byte lock is held"));
        }
        slot.exclusive = None;
        slot.shared.insert(client);
        Ok(())
    }

    fn lock_blocks(&self, client: u64, offset: u64) -> bool {
        let Some(slot) = self.locks.get(&offset) else {
            return false;
        };
        slot.exclusive.is_some_and(|id| id != client) || slot.shared.iter().any(|id| *id != client)
    }

    fn release_client(&mut self, client: u64) {
        self.locks.retain(|_, slot| {
            if slot.exclusive == Some(client) {
                slot.exclusive = None;
            }
            slot.shared.remove(&client);
            slot.exclusive.is_some() || !slot.shared.is_empty()
        });
    }
}

fn now() -> (u64, u32) {
    let time = SystemTime::now()
        .duration_since(SystemTime::UNIX_EPOCH)
        .expect("clock");
    (time.as_secs(), time.subsec_nanos())
}

fn fs_err(err: impl core::fmt::Debug) -> io::Error {
    io::Error::other(format!("redoxfs {err:?}"))
}
