use std::env;
use std::io::{Read, Write};
use std::os::unix::net::{UnixListener, UnixStream};
use std::process::{Command, Stdio};
use std::thread;
use std::time::{Duration, SystemTime, UNIX_EPOCH};

use file_service::Service;

const MAP: u64 = 32 * 1024 * 1024;

#[test]
fn lock_file_is_shared_and_dies_with_the_holder() {
    let path = std::env::temp_dir().join(format!(
        "atmo-file-svc-lock-{}-{}.img",
        std::process::id(),
        SystemTime::now()
            .duration_since(UNIX_EPOCH)
            .unwrap()
            .as_nanos()
    ));
    let service = Service::create(&path, MAP).unwrap();
    let first = service.client();
    let second = service.client();

    first.lock_exclusive(0).unwrap();
    let writer = first.lock_map();
    writer.write_at(0, b"INIT").unwrap();
    let reader = second.lock_map();
    let mut got = [0u8; 4];
    let n = reader.read_at(0, &mut got).unwrap();
    assert_eq!(n, 4);
    assert_eq!(&got, b"INIT");
    println!("two clients share the lock-file map; the first exclusive holder initialized it");

    assert!(
        second.lock_exclusive(0).is_err(),
        "the region is still held exclusively"
    );
    first.lock_shared(0).unwrap();
    second.lock_shared(0).unwrap();
    println!("the next opener took the shared lock");

    let holder_byte = 64u64;
    first.lock_exclusive(holder_byte).unwrap();
    let unrelated = first.open_lock_handle();
    drop(unrelated);
    drop(writer);
    assert!(
        second.lock_exclusive(holder_byte).is_err(),
        "closing an unrelated handle dropped the lock"
    );
    println!("closing an unrelated handle did not drop the lock");

    let sock_path = std::env::temp_dir().join(format!(
        "atmo-lock-{}-{}.sock",
        std::process::id(),
        SystemTime::now()
            .duration_since(UNIX_EPOCH)
            .unwrap()
            .as_nanos()
    ));
    let _ = std::fs::remove_file(&sock_path);
    let listener = UnixListener::bind(&sock_path).unwrap();
    listener.set_nonblocking(true).unwrap();
    let mut child = Command::new(env::current_exe().unwrap())
        .arg("lock_file_holder_child")
        .arg("--exact")
        .env("ATMO_LOCK_SOCK", &sock_path)
        .stdin(Stdio::null())
        .stdout(Stdio::null())
        .stderr(Stdio::null())
        .spawn()
        .unwrap();
    let mut stream = None;
    for _ in 0..50 {
        match listener.accept() {
            Ok((stream_in, _)) => {
                stream = Some(stream_in);
                break;
            }
            Err(err) if err.kind() == std::io::ErrorKind::WouldBlock => {
                thread::sleep(Duration::from_millis(100));
            }
            Err(err) => panic!("accept: {err}"),
        }
    }
    let mut stream = stream.expect("the holder did not connect");
    stream.set_nonblocking(false).unwrap();
    let holder_id = child.id() as u64;
    let holder = service.client();
    holder.lock_exclusive(holder_id).unwrap();
    assert!(second.lock_exclusive(holder_id).is_err());
    child.kill().unwrap();
    let mut byte = [0u8; 1];
    let n = stream.read(&mut byte).unwrap();
    assert_eq!(n, 0, "killing the holder drops its connection");
    drop(holder);
    let status = child.wait().unwrap();
    assert!(!status.success());
    second.lock_exclusive(holder_id).unwrap();
    println!(
        "a one-byte holder lock disappeared when that holder was killed, and the next opener took it"
    );

    drop(reader);
    drop(first);
    drop(second);
    drop(service);
    let _ = std::fs::remove_file(&sock_path);
    std::fs::remove_file(&path).unwrap();
}

/// The process a parent kills. It holds a connection open and does nothing else.
#[test]
fn lock_file_holder_child() {
    let Ok(path) = env::var("ATMO_LOCK_SOCK") else {
        return;
    };
    let mut stream = UnixStream::connect(path).unwrap();
    let mut byte = [0u8; 1];
    let _ = stream.read(&mut byte);
    let _ = stream.write(&byte);
}
