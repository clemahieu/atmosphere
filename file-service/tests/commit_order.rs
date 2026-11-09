use std::fs;
use std::time::{SystemTime, UNIX_EPOCH};

use file_service::{Service, PAGE};

const MAP: u64 = 32 * 1024 * 1024;
const DATA: u64 = PAGE * 2;
const SUFFIX: usize = 24;
const TXNID_OFF: usize = 16;

fn suffix(mapsize: u64, marker: u64, txnid: u64) -> [u8; SUFFIX] {
    let mut bytes = [0u8; SUFFIX];
    bytes[0..8].copy_from_slice(&mapsize.to_le_bytes());
    bytes[8..16].copy_from_slice(&marker.to_le_bytes());
    bytes[16..24].copy_from_slice(&txnid.to_le_bytes());
    bytes
}

fn meta_off(txnid: u64) -> u64 {
    (txnid & 1) * PAGE
}

fn selected(client: &file_service::Client) -> (u64, u64) {
    let mut pages = vec![0u8; (PAGE * 2) as usize];
    let n = client.pread(0, &mut pages).unwrap();
    assert_eq!(n, pages.len(), "pread of the two meta pages");
    let mut best_at = 0usize;
    let mut best = 0u64;
    for i in 0..2 {
        let at = i * PAGE as usize;
        let txnid = u64::from_le_bytes(pages[at + TXNID_OFF..at + SUFFIX].try_into().unwrap());
        if i == 0 || txnid > best {
            best = txnid;
            best_at = at;
        }
    }
    let marker = u64::from_le_bytes(pages[best_at + 8..best_at + 16].try_into().unwrap());
    (best, marker)
}

fn image_path(label: &str) -> std::path::PathBuf {
    std::env::temp_dir().join(format!(
        "atmo-file-svc-{label}-{}-{}.img",
        std::process::id(),
        SystemTime::now()
            .duration_since(UNIX_EPOCH)
            .unwrap()
            .as_nanos()
    ))
}

fn open(label: &str) -> (std::path::PathBuf, file_service::Client, Service) {
    let path = image_path(label);
    let service = Service::create(&path, MAP).unwrap();
    let client = service.client();
    client.sync_pwrite(meta_off(1), &suffix(MAP, 1, 1)).unwrap();
    client.sync_pwrite(meta_off(0), &suffix(MAP, 0, 0)).unwrap();
    client.set_map_size(MAP).unwrap();
    (path, client, service)
}

#[test]
fn commit_order_survives_only_with_fdatasync() {
    let (path, client, service) = open("before-meta");
    client.pwrite(DATA, &[0xAB]).unwrap();
    client.fdatasync().unwrap();
    client.crash(&[]).unwrap();
    let (txnid, _) = selected(&client);
    assert_eq!(
        txnid, 1,
        "crash before the meta pwrite published a new txnid"
    );
    println!("crash before the meta pwrite keeps the old txnid {txnid}");
    drop(client);
    drop(service);
    fs::remove_file(&path).unwrap();

    let (path, client, service) = open("torn");
    client.pwrite(DATA, &[0xAB]).unwrap();
    client.fdatasync().unwrap();
    let torn = suffix(MAP, 0x4D, 2);
    client
        .crash_during_sync_pwrite(meta_off(2), &torn, TXNID_OFF)
        .unwrap();
    let (txnid, marker) = selected(&client);
    assert_eq!(txnid, 1, "torn meta selected txnid {txnid} marker {marker}");
    let mut page0 = vec![0u8; SUFFIX];
    client.pread(meta_off(2), &mut page0).unwrap();
    let page0_txn = u64::from_le_bytes(page0[TXNID_OFF..SUFFIX].try_into().unwrap());
    assert_ne!(page0_txn, 2, "torn meta page carries the newer txnid");
    println!("a torn meta pwrite is not selected as a newer transaction");
    drop(client);
    drop(service);
    fs::remove_file(&path).unwrap();

    let (path, client, service) = open("synced");
    client.pwrite(DATA, &[0xAB]).unwrap();
    client.fdatasync().unwrap();
    client.sync_pwrite(meta_off(2), &suffix(MAP, 2, 2)).unwrap();
    client.crash(&[]).unwrap();
    let (txnid, _) = selected(&client);
    let mut data = [0u8; 1];
    client.pread(DATA, &mut data).unwrap();
    assert_eq!(txnid, 2);
    assert_eq!(data[0], 0xAB);
    println!(
        "fdatasync then the synchronous meta pwrite keeps data {data:02x?} with txnid {txnid}"
    );
    drop(client);
    drop(service);
    fs::remove_file(&path).unwrap();

    let (path, client, service) = open("nosync");
    client.pwrite(DATA, &[0xAB]).unwrap();
    client.sync_pwrite(meta_off(2), &suffix(MAP, 2, 2)).unwrap();
    client.crash(&[]).unwrap();
    let (txnid, _) = selected(&client);
    let mut data = [0u8; 1];
    let n = client.pread(DATA, &mut data).unwrap();
    let durable = txnid == 2 && n == 1 && data[0] == 0xAB;
    assert!(!durable, "durability held without the data fdatasync");
    println!(
        "the same test fails when the data fdatasync is removed: txnid {txnid}, data {data:02x?}"
    );
    drop(client);
    drop(service);
    fs::remove_file(&path).unwrap();

    let (path, client, service) = open("reorder");
    client.pwrite(DATA, &[0x11]).unwrap();
    client.pwrite(DATA + PAGE, &[0x22]).unwrap();
    client.crash(&[DATA / PAGE]).unwrap();
    let mut kept = [0u8; 1];
    let mut dropped = [0u8; 1];
    assert_eq!(client.pread(DATA, &mut kept).unwrap(), 1);
    assert_eq!(kept[0], 0x11, "reordered unstable page did not land");
    assert_eq!(client.pread(DATA + PAGE, &mut dropped).unwrap(), 1);
    assert_eq!(dropped[0], 0, "dropped unstable page landed");
    drop(client);
    drop(service);
    fs::remove_file(&path).unwrap();
}
