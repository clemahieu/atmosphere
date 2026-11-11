// SPDX-License-Identifier: MIT

use std::fs;
use std::time::{SystemTime, UNIX_EPOCH};

use file_service::{Service, PAGE};

const MAP: u64 = 32 * 1024 * 1024;

#[test]
fn shared_map_sees_pwrite_and_stays_sparse() {
    let path = std::env::temp_dir().join(format!(
        "atmo-file-svc-{}-{}.img",
        std::process::id(),
        SystemTime::now()
            .duration_since(UNIX_EPOCH)
            .unwrap()
            .as_nanos()
    ));
    let service = Service::create(&path, MAP).unwrap();
    let writer = service.client();
    let reader = service.client();

    let mut meta0 = [0u8; PAGE as usize];
    let mut meta1 = [0u8; PAGE as usize];
    meta0[0] = 0x11;
    meta1[0] = 0x22;
    writer.pwrite(0, &meta0).unwrap();
    writer.pwrite(PAGE, &meta1).unwrap();

    let mut got = [0u8; (PAGE * 2) as usize];
    let n = reader.pread(0, &mut got).unwrap();
    assert_eq!(n, got.len(), "pread of the two meta pages before any map");
    assert_eq!(&got[..PAGE as usize], &meta0);
    assert_eq!(&got[PAGE as usize..], &meta1);
    println!("pread before map: {n} bytes, both meta pages");

    let existing = reader.map();
    let mut updated = meta0;
    updated[0] = 0x33;
    writer.pwrite(0, &updated).unwrap();
    let seen = existing.page(0).unwrap();
    assert_eq!(seen, updated, "existing shared map sees the pwrite");
    println!("existing map sees pwrite: {:02x}", seen[0]);

    let later = writer.map();
    assert_eq!(later.page(0).unwrap(), updated, "map taken afterwards");
    assert_eq!(later.page(1).unwrap(), meta1);
    println!("later map sees pwrite: {:02x}", later.page(0).unwrap()[0]);

    let before = writer.allocated_bytes().unwrap();
    writer.set_map_size(MAP).unwrap();
    let far = existing.page(MAP / PAGE - 1).unwrap();
    assert!(
        far.iter().all(|byte| *byte == 0),
        "unwritten page reads as zeroes"
    );
    let mut far_pread = [1u8; PAGE as usize];
    let far_n = reader.pread(MAP - PAGE, &mut far_pread).unwrap();
    assert_eq!(far_n, far_pread.len());
    assert!(far_pread.iter().all(|byte| *byte == 0));
    let after = writer.allocated_bytes().unwrap();
    println!("unwritten page is zero; allocated {before} before grow, {after} after, map {MAP}");
    assert!(
        after < MAP / 16,
        "allocated {after} is not near the written pages"
    );
    assert!(
        after - before < 1024 * 1024,
        "grow allocated {after} from {before}"
    );

    drop(existing);
    drop(later);
    drop(writer);
    drop(reader);
    drop(service);
    fs::remove_file(&path).unwrap();
}
