//! A file on a RedoxFS image, shared by clients through one cache.
//!
//! A pwrite updates that cache, so a map already held sees the bytes with no
//! invalidate. The map size is a sparse truncate: unwritten pages read as
//! zeroes and the image stores only the blocks RedoxFS allocated.

use std::collections::BTreeMap;
use std::fs;
use std::io::{self, ErrorKind};
use std::os::unix::fs::MetadataExt;
use std::path::{Path, PathBuf};
use std::sync::{Arc, Mutex};
use std::time::SystemTime;

use redoxfs::{DiskSparse, FileSystem, Node, TreePtr, BLOCK_SIZE};

/// One page. LMDB's meta pages and RedoxFS blocks are this size.
pub const PAGE: u64 = BLOCK_SIZE;

/// Room past the map size for the filesystem itself.
const DISK_SLACK: u64 = 16 * 1024 * 1024;

struct Inner {
    fs: FileSystem<DiskSparse>,
    image: PathBuf,
    node: TreePtr<Node>,
    size: u64,
    pages: BTreeMap<u64, Vec<u8>>,
}

/// The file service. Clients taken from it share one cache and one image.
pub struct Service {
    inner: Arc<Mutex<Inner>>,
}

/// One client of the service.
pub struct Client {
    inner: Arc<Mutex<Inner>>,
}

/// A shared view of the file. It reads the service cache; nothing invalidates it.
pub struct SharedMap {
    inner: Arc<Mutex<Inner>>,
}

impl Service {
    /// Create `image` and a data file on a RedoxFS filesystem large enough for `map_size`.
    pub fn create(image: impl AsRef<Path>, map_size: u64) -> io::Result<Self> {
        let image = image.as_ref().to_path_buf();
        let disk_size = map_size
            .checked_add(DISK_SLACK)
            .ok_or_else(|| io::Error::new(ErrorKind::InvalidInput, "map size overflows"))?;
        let disk = DiskSparse::create(&image, disk_size).map_err(fs_err)?;
        let (sec, nsec) = now();
        let mut fs = FileSystem::create(disk, None, sec, nsec).map_err(fs_err)?;
        let node = fs
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
        let inner = Inner {
            fs,
            image,
            node: node.ptr(),
            size: 0,
            pages: BTreeMap::new(),
        };
        Ok(Self {
            inner: Arc::new(Mutex::new(inner)),
        })
    }

    pub fn client(&self) -> Client {
        Client {
            inner: Arc::clone(&self.inner),
        }
    }
}

impl Client {
    pub fn pread(&self, offset: u64, buf: &mut [u8]) -> io::Result<usize> {
        self.inner
            .lock()
            .expect("file service lock")
            .pread(offset, buf)
    }

    pub fn pwrite(&self, offset: u64, data: &[u8]) -> io::Result<()> {
        self.inner
            .lock()
            .expect("file service lock")
            .pwrite(offset, data)
    }

    /// The file's logical size becomes `size`. A grow does not allocate the hole.
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
}

impl SharedMap {
    /// The page at `index`. A hole reads as zeroes.
    pub fn page(&self, index: u64) -> io::Result<[u8; PAGE as usize]> {
        let mut buf = [0u8; PAGE as usize];
        let n = self
            .inner
            .lock()
            .expect("file service lock")
            .pread(index * PAGE, &mut buf)?;
        if n < buf.len() {
            buf[n..].fill(0);
        }
        Ok(buf)
    }
}

impl Inner {
    fn pread(&mut self, offset: u64, buf: &mut [u8]) -> io::Result<usize> {
        if offset >= self.size || buf.is_empty() {
            return Ok(0);
        }
        let want = buf.len().min((self.size - offset) as usize);
        let mut done = 0;
        while done < want {
            let abs = offset + done as u64;
            let page = abs / PAGE;
            let page_off = (abs % PAGE) as usize;
            let take = (PAGE as usize - page_off).min(want - done);
            if let Some(cached) = self.pages.get(&page) {
                buf[done..done + take].copy_from_slice(&cached[page_off..page_off + take]);
            } else {
                let n = self.read_disk(abs, &mut buf[done..done + take])?;
                if n < take {
                    buf[done + n..done + take].fill(0);
                }
            }
            done += take;
        }
        Ok(want)
    }

    fn pwrite(&mut self, offset: u64, data: &[u8]) -> io::Result<()> {
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
                self.load_page(page)?
            };
            bytes[page_off..page_off + take].copy_from_slice(&data[done..done + take]);
            self.write_disk(page * PAGE, &bytes)?;
            self.pages.insert(page, bytes);
            done += take;
        }
        if end > self.size {
            self.size = end;
        }
        Ok(())
    }

    fn set_map_size(&mut self, size: u64) -> io::Result<()> {
        if size < self.size {
            return Err(io::Error::new(
                ErrorKind::InvalidInput,
                "map size shrinks the file",
            ));
        }
        let (sec, nsec) = now();
        let node = self.node;
        self.fs
            .tx(|tx| tx.truncate_node(node, size, sec, nsec))
            .map_err(fs_err)?;
        self.size = size;
        Ok(())
    }

    fn allocated_bytes(&self) -> io::Result<u64> {
        Ok(fs::metadata(&self.image)?.blocks() * 512)
    }

    fn load_page(&mut self, page: u64) -> io::Result<Vec<u8>> {
        if let Some(cached) = self.pages.get(&page) {
            return Ok(cached.clone());
        }
        let mut buf = vec![0u8; PAGE as usize];
        let offset = page * PAGE;
        if offset < self.size {
            let n = self.read_disk(offset, &mut buf)?;
            buf[n..].fill(0);
        }
        Ok(buf)
    }

    fn read_disk(&mut self, offset: u64, buf: &mut [u8]) -> io::Result<usize> {
        let node = self.node;
        let (sec, nsec) = now();
        self.fs
            .tx(|tx| tx.read_node(node, offset, buf, sec, nsec))
            .map_err(fs_err)
    }

    fn write_disk(&mut self, offset: u64, data: &[u8]) -> io::Result<()> {
        let node = self.node;
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
