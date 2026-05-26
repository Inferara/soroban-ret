use assert_cmd::Command;
use predicates::prelude::*;
use std::path::PathBuf;

fn fixture(name: &str) -> PathBuf {
    PathBuf::from(env!("CARGO_MANIFEST_DIR"))
        .join("../../tests/fixtures")
        .join(name)
}

fn bin() -> Command {
    Command::cargo_bin("soroban-ret").expect("binary should be built")
}

#[test]
fn decompiles_to_stdout() {
    bin()
        .arg(fixture("test_add_u64.wasm"))
        .assert()
        .success()
        .stdout(predicate::str::contains("pub fn add"))
        .stdout(predicate::str::contains("#[contract]"));
}

#[test]
fn writes_to_output_file() {
    let tmp = tempfile::NamedTempFile::new().expect("tempfile");
    let path = tmp.path().to_owned();
    bin()
        .arg(fixture("test_add_u64.wasm"))
        .arg("-o")
        .arg(&path)
        .assert()
        .success()
        .stderr(predicate::str::contains("Decompiled to"));
    let written = std::fs::read_to_string(&path).expect("read output");
    assert!(
        written.contains("#[contract]"),
        "missing contract in output"
    );
}

#[test]
fn info_subcommand_prints_metadata_to_stderr() {
    bin()
        .arg("--info")
        .arg(fixture("test_udt.wasm"))
        .assert()
        .success()
        .stderr(predicate::str::contains("Contract Info:"))
        .stderr(predicate::str::contains("Functions:"))
        .stderr(predicate::str::contains("Types:"));
}

#[test]
fn spec_only_omits_function_bodies() {
    bin()
        .arg("--spec-only")
        .arg(fixture("test_add_u64.wasm"))
        .assert()
        .success()
        .stdout(predicate::str::contains("pub fn add"))
        .stdout(predicate::str::contains("a + b").not());
}

#[test]
fn generic_mode_succeeds_on_soroban_contract() {
    bin()
        .arg("--generic")
        .arg(fixture("test_empty.wasm"))
        .assert()
        .success();
}

#[test]
fn verbose_flag_initializes_debug_logger() {
    bin()
        .arg("-v")
        .arg(fixture("test_empty.wasm"))
        .assert()
        .success();
}

#[test]
fn missing_input_file_exits_nonzero() {
    bin()
        .arg("/nonexistent/path/to/contract.wasm")
        .assert()
        .failure()
        .code(1)
        .stderr(predicate::str::contains("Error reading"));
}

#[test]
fn invalid_wasm_exits_nonzero() {
    let tmp = tempfile::NamedTempFile::new().expect("tempfile");
    std::fs::write(tmp.path(), b"not a real wasm").expect("write garbage");
    bin()
        .arg(tmp.path())
        .assert()
        .failure()
        .code(1)
        .stderr(predicate::str::contains("Decompilation error"));
}

#[test]
fn invalid_wasm_with_info_exits_nonzero() {
    let tmp = tempfile::NamedTempFile::new().expect("tempfile");
    std::fs::write(tmp.path(), b"not a real wasm").expect("write garbage");
    bin()
        .arg("--info")
        .arg(tmp.path())
        .assert()
        .failure()
        .code(1)
        .stderr(predicate::str::contains("Error:"));
}

#[test]
fn output_to_unwritable_path_exits_nonzero() {
    // Writing to a directory path fails.
    let dir = tempfile::tempdir().expect("tempdir");
    bin()
        .arg(fixture("test_add_u64.wasm"))
        .arg("-o")
        .arg(dir.path())
        .assert()
        .failure()
        .code(1)
        .stderr(predicate::str::contains("Error writing"));
}

#[test]
fn info_includes_constructor_marker_for_contract_with_ctor() {
    bin()
        .arg("--info")
        .arg(fixture("test_constructor.wasm"))
        .assert()
        .success()
        .stderr(predicate::str::contains("Constructor:"));
}
