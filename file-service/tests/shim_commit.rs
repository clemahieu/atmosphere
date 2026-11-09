//! A commit through the LMDB shim is a data file the upstream tools can read,
//! and a data file those tools wrote opens back through the shim.

use std::path::{Path, PathBuf};
use std::process::Command;

use file_service::{
    shim_create, shim_fdatasync, shim_get, shim_pread, shim_put, shim_pwrite, shim_size,
};

const MAP: u64 = 10 * 1024 * 1024;

fn lmdb_dir() -> PathBuf {
    PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("../../reference/lmdb/libraries/liblmdb")
}

fn set_db_path(path: &Path) {
    unsafe { std::env::set_var("ATMO_LMDB_PATH", path) }
}

fn output(cmd: &mut Command) -> std::process::Output {
    let out = cmd
        .output()
        .unwrap_or_else(|err| panic!("spawn {cmd:?}: {err}"));
    if !out.status.success() {
        panic!(
            "{cmd:?} failed ({})\n{}",
            out.status,
            String::from_utf8_lossy(&out.stderr)
        );
    }
    out
}

fn compile_upstream(dir: &Path, lmdb: &Path) {
    let mdb_o = dir.join("mdb.o");
    let midl_o = dir.join("midl.o");
    let mod_o = dir.join("mod_stub.o");
    let stub = PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("src/mod_stub.c");
    output(
        Command::new("gcc")
            .args(["-c", "-O2", "-pthread"])
            .arg("-I")
            .arg(lmdb)
            .arg(&stub)
            .arg("-o")
            .arg(&mod_o),
    );
    output(
        Command::new("gcc")
            .args(["-c", "-O2", "-pthread"])
            .arg("-I")
            .arg(lmdb)
            .arg(lmdb.join("mdb.c"))
            .arg("-o")
            .arg(&mdb_o),
    );
    output(
        Command::new("gcc")
            .args(["-c", "-O2", "-pthread"])
            .arg("-I")
            .arg(lmdb)
            .arg(lmdb.join("midl.c"))
            .arg("-o")
            .arg(&midl_o),
    );
    for (src, bin) in [("mdb_stat.c", "mdb_stat"), ("mdb_dump.c", "mdb_dump")] {
        output(
            Command::new("gcc")
                .args(["-O2", "-pthread"])
                .arg("-I")
                .arg(lmdb)
                .arg(lmdb.join(src))
                .arg(&mdb_o)
                .arg(&midl_o)
                .arg(&mod_o)
                .arg("-o")
                .arg(dir.join(bin)),
        );
    }
    let harness = PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("src/upstream_write.c");
    output(
        Command::new("gcc")
            .args(["-O2", "-pthread"])
            .arg("-I")
            .arg(lmdb)
            .arg(&harness)
            .arg(&mdb_o)
            .arg(&midl_o)
            .arg("-o")
            .arg(dir.join("upstream_write")),
    );
}

#[test]
fn shim_commit_matches_upstream_tools() {
    let lmdb = lmdb_dir();
    assert!(lmdb.join("mdb.c").is_file(), "reference lmdb checkout");
    let dir = std::env::temp_dir().join(format!("atmo-lmdb-shim-{}", std::process::id()));
    let _ = std::fs::remove_dir_all(&dir);
    std::fs::create_dir_all(&dir).unwrap();

    let image = dir.join("image");
    shim_create(&image, MAP).unwrap();
    set_db_path(&dir.join("db"));
    shim_put(MAP, b"alpha", b"bravo").unwrap();

    let size = shim_size().unwrap();
    assert!(size >= 8192, "export covers the meta pages, size {size}");
    let mut bytes = vec![0u8; size as usize];
    let n = shim_pread(0, &mut bytes).unwrap();
    assert_eq!(n, bytes.len());
    let export = dir.join("export.mdb");
    std::fs::write(&export, &bytes).unwrap();

    compile_upstream(&dir, &lmdb);
    let stat = output(
        Command::new(dir.join("mdb_stat"))
            .args(["-n", "-e"])
            .arg(&export),
    );
    let dump = output(
        Command::new(dir.join("mdb_dump"))
            .args(["-n", "-p"])
            .arg(&export),
    );
    let stat_out = String::from_utf8_lossy(&stat.stdout);
    let dump_out = String::from_utf8_lossy(&dump.stdout);
    println!("mdb_stat:\n{stat_out}");
    println!("mdb_dump:\n{dump_out}");
    assert!(stat_out.contains("Entries: 1"), "{stat_out}");
    assert!(dump_out.contains("alpha"), "{dump_out}");
    assert!(dump_out.contains("bravo"), "{dump_out}");

    let upstream = dir.join("upstream.mdb");
    let wrote = output(
        Command::new(dir.join("upstream_write"))
            .arg(&upstream)
            .arg(MAP.to_string()),
    );
    println!(
        "upstream_write:\n{}",
        String::from_utf8_lossy(&wrote.stdout)
    );
    let written = std::fs::read(&upstream).unwrap();
    assert!(!written.is_empty());

    shim_create(&dir.join("image2"), MAP).unwrap();
    set_db_path(&dir.join("import"));
    shim_pwrite(0, &written).unwrap();
    shim_fdatasync().unwrap();
    let mut val = [0u8; 16];
    let n = shim_get(MAP, b"kite", &mut val).unwrap();
    println!("shim get: kite={}", String::from_utf8_lossy(&val[..n]));
    assert_eq!(&val[..n], b"hawk");
}
