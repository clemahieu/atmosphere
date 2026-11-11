// SPDX-License-Identifier: MIT

//! Process-wide file service the LMDB shim calls.
//!
//! `mdb.c` is linked with `--wrap` and calls these symbols through function
//! pointers, so the static library does not name Rust symbols.

use std::io::{self, ErrorKind};
use std::path::Path;
use std::sync::{Mutex, Once};

use super::{Client, Service};

// `client` is dropped first, so its record locks release while `service` is alive.
struct Live {
    client: Client,
    #[allow(dead_code)]
    service: Service,
}

static LIVE: Mutex<Option<Live>> = Mutex::new(None);

#[repr(C)]
struct AtmoOps {
    pread: extern "C" fn(u64, *mut u8, usize) -> i64,
    pwrite: extern "C" fn(u64, *const u8, usize) -> i64,
    sync_pwrite: extern "C" fn(u64, *const u8, usize) -> i64,
    fdatasync: extern "C" fn() -> i32,
    set_map_size: extern "C" fn(u64) -> i32,
    lock_exclusive: extern "C" fn(u64) -> i32,
    lock_shared: extern "C" fn(u64) -> i32,
    lock_blocks: extern "C" fn(u64) -> i32,
    size: extern "C" fn() -> u64,
}

extern "C" {
    fn atmo_fs_bind(ops: *const AtmoOps);
    fn atmo_lmdb_put(
        map_size: u64,
        key: *const u8,
        key_len: usize,
        val: *const u8,
        val_len: usize,
    ) -> i32;
    fn atmo_lmdb_get(
        map_size: u64,
        key: *const u8,
        key_len: usize,
        val: *mut u8,
        val_cap: usize,
        val_len: *mut usize,
    ) -> i32;
}

fn ensure_bound() {
    static ONCE: Once = Once::new();
    ONCE.call_once(|| {
        let ops = AtmoOps {
            pread: atmo_fs_pread,
            pwrite: atmo_fs_pwrite,
            sync_pwrite: atmo_fs_sync_pwrite,
            fdatasync: atmo_fs_fdatasync,
            set_map_size: atmo_fs_set_map_size,
            lock_exclusive: atmo_fs_lock_exclusive,
            lock_shared: atmo_fs_lock_shared,
            lock_blocks: atmo_fs_lock_blocks,
            size: atmo_fs_size,
        };
        unsafe { atmo_fs_bind(&ops) }
    });
}

fn with_client<T>(f: impl FnOnce(&Client) -> io::Result<T>) -> io::Result<T> {
    let live = LIVE.lock().expect("live");
    let live = live
        .as_ref()
        .ok_or_else(|| io::Error::other("no file service"))?;
    f(&live.client)
}

pub fn shim_create(image: &Path, map_size: u64) -> io::Result<()> {
    ensure_bound();
    let service = Service::create(image, map_size)?;
    let client = service.client();
    *LIVE.lock().expect("live") = Some(Live { client, service });
    Ok(())
}

pub fn shim_pread(offset: u64, buf: &mut [u8]) -> io::Result<usize> {
    let n = atmo_fs_pread(offset, buf.as_mut_ptr(), buf.len());
    if n < 0 {
        Err(io::Error::other("pread failed"))
    } else {
        Ok(n as usize)
    }
}

pub fn shim_pwrite(offset: u64, data: &[u8]) -> io::Result<()> {
    let n = atmo_fs_pwrite(offset, data.as_ptr(), data.len());
    if n < 0 {
        Err(io::Error::other("pwrite failed"))
    } else {
        Ok(())
    }
}

pub fn shim_fdatasync() -> io::Result<()> {
    if atmo_fs_fdatasync() < 0 {
        Err(io::Error::other("fdatasync failed"))
    } else {
        Ok(())
    }
}

pub fn shim_size() -> io::Result<u64> {
    with_client(|client| Ok(client.size()))
}

pub fn shim_put(map_size: u64, key: &[u8], val: &[u8]) -> io::Result<()> {
    ensure_bound();
    let rc = unsafe { atmo_lmdb_put(map_size, key.as_ptr(), key.len(), val.as_ptr(), val.len()) };
    if rc == 0 {
        Ok(())
    } else {
        Err(io::Error::other(format!("lmdb put returned {rc}")))
    }
}

pub fn shim_get(map_size: u64, key: &[u8], val: &mut [u8]) -> io::Result<usize> {
    ensure_bound();
    let mut len = 0usize;
    let rc = unsafe {
        atmo_lmdb_get(
            map_size,
            key.as_ptr(),
            key.len(),
            val.as_mut_ptr(),
            val.len(),
            &mut len,
        )
    };
    if rc == 0 {
        Ok(len)
    } else {
        Err(io::Error::other(format!("lmdb get returned {rc}")))
    }
}

fn io_count(result: io::Result<()>, len: usize) -> i64 {
    match result {
        Ok(()) => len as i64,
        Err(_) => -1,
    }
}

fn lock_code(result: io::Result<()>) -> i32 {
    match result {
        Ok(()) => 0,
        Err(err) if err.kind() == ErrorKind::WouldBlock => -2,
        Err(_) => -1,
    }
}

#[no_mangle]
pub extern "C" fn atmo_fs_pread(offset: u64, buf: *mut u8, len: usize) -> i64 {
    if len == 0 {
        return 0;
    }
    if buf.is_null() {
        return -1;
    }
    let slice = unsafe { std::slice::from_raw_parts_mut(buf, len) };
    match with_client(|client| client.pread(offset, slice)) {
        Ok(n) => n as i64,
        Err(_) => -1,
    }
}

#[no_mangle]
pub extern "C" fn atmo_fs_pwrite(offset: u64, buf: *const u8, len: usize) -> i64 {
    if len == 0 {
        return 0;
    }
    if buf.is_null() {
        return -1;
    }
    let slice = unsafe { std::slice::from_raw_parts(buf, len) };
    io_count(with_client(|client| client.pwrite(offset, slice)), len)
}

#[no_mangle]
pub extern "C" fn atmo_fs_sync_pwrite(offset: u64, buf: *const u8, len: usize) -> i64 {
    if len == 0 {
        return 0;
    }
    if buf.is_null() {
        return -1;
    }
    let slice = unsafe { std::slice::from_raw_parts(buf, len) };
    io_count(with_client(|client| client.sync_pwrite(offset, slice)), len)
}

#[no_mangle]
pub extern "C" fn atmo_fs_fdatasync() -> i32 {
    match with_client(|client| client.fdatasync()) {
        Ok(()) => 0,
        Err(_) => -1,
    }
}

#[no_mangle]
pub extern "C" fn atmo_fs_set_map_size(size: u64) -> i32 {
    match with_client(|client| client.set_map_size(size)) {
        Ok(()) => 0,
        Err(_) => -1,
    }
}

#[no_mangle]
pub extern "C" fn atmo_fs_lock_exclusive(offset: u64) -> i32 {
    lock_code(with_client(|client| client.lock_exclusive(offset)))
}

#[no_mangle]
pub extern "C" fn atmo_fs_lock_shared(offset: u64) -> i32 {
    lock_code(with_client(|client| client.lock_shared(offset)))
}

#[no_mangle]
pub extern "C" fn atmo_fs_lock_blocks(offset: u64) -> i32 {
    match with_client(|client| Ok(client.lock_blocks(offset))) {
        Ok(true) => 1,
        Ok(false) => 0,
        Err(_) => -1,
    }
}

#[no_mangle]
pub extern "C" fn atmo_fs_size() -> u64 {
    with_client(|client| Ok(client.size())).unwrap_or(0)
}
