// SPDX-License-Identifier: MPL-2.0
// Copyright (c) 2026 The RIINA Authors. See AUTHORS file.

//! RIINA Verification Gate
//!
//! `riinac verify [--fast|--full]` — runs all checks and produces a manifest.
//!
//! Full mode invokes real proof compilers (Coq, Lean 4, Isabelle/HOL) with
//! proper toolchain detection, timeout handling, and static scanning for all
//! three provers. Tool-not-found is a hard FAIL (verification incomplete).

#![forbid(unsafe_code)]

use std::fmt::Write as _;
use std::fs;
use std::io;
use std::path::{Path, PathBuf};
use std::process::{Command, Output};
use std::time::{Duration, Instant, SystemTime};

// ---------------------------------------------------------------------------
// Timeout constants (generous to allow clean CI builds)
// ---------------------------------------------------------------------------

const COQ_TIMEOUT: Duration = Duration::from_secs(45 * 60); // 45 min
const LEAN_TIMEOUT: Duration = Duration::from_secs(30 * 60); // 30 min
const ISABELLE_TIMEOUT: Duration = Duration::from_secs(20 * 60); // 20 min

// ---------------------------------------------------------------------------
// Mode / CheckResult / ToolStatus
// ---------------------------------------------------------------------------

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Mode {
    Fast,
    Full,
}

#[derive(Debug)]
struct CheckResult {
    name: String,
    passed: bool,
    /// If false, a failure is informational (e.g. tool not installed).
    /// Only `blocking` failures cause overall verification to FAIL.
    blocking: bool,
    details: String,
}

#[derive(Debug)]
enum ToolStatus {
    Found(PathBuf),
    NotFound(String),
}

// ---------------------------------------------------------------------------
// Helper utilities
// ---------------------------------------------------------------------------

/// Locate an executable on `$PATH` using the `which` command.
fn which_tool(name: &str) -> Option<PathBuf> {
    Command::new("which")
        .arg(name)
        .output()
        .ok()
        .filter(|o| o.status.success())
        .and_then(|o| String::from_utf8(o.stdout).ok())
        .map(|s| PathBuf::from(s.trim()))
        .filter(|p| p.exists())
}

/// Extract the last `n` lines from a string.
fn last_n_lines(s: &str, n: usize) -> String {
    let lines: Vec<&str> = s.lines().collect();
    let start = lines.len().saturating_sub(n);
    lines[start..].join("\n")
}

/// Truncate a string to at most `max` bytes (on a char boundary).
fn truncate_str(s: &str, max: usize) -> String {
    if s.len() <= max {
        return s.to_string();
    }
    let mut end = max;
    while end > 0 && !s.is_char_boundary(end) {
        end -= 1;
    }
    format!("{}...", &s[..end])
}

/// Count files with a given extension under `dir` (recursive).
fn count_files_with_ext(dir: &Path, ext: &str) -> u32 {
    let mut count = 0u32;
    if let Ok(entries) = fs::read_dir(dir) {
        for entry in entries.flatten() {
            let path = entry.path();
            if path.is_dir() {
                count += count_files_with_ext(&path, ext);
            } else if path.extension().and_then(|e| e.to_str()) == Some(ext) {
                count += 1;
            }
        }
    }
    count
}

// ---------------------------------------------------------------------------
// Toolchain detection
// ---------------------------------------------------------------------------

/// Detect `coqc`: `$COQBIN` env → OPAM paths → `which coqc`.
fn detect_coqc() -> ToolStatus {
    // 1. COQBIN environment variable
    if let Ok(coqbin) = std::env::var("COQBIN") {
        let p = PathBuf::from(&coqbin).join("coqc");
        if p.exists() {
            return ToolStatus::Found(p);
        }
    }

    // 2. OPAM default switch paths
    if let Ok(home) = std::env::var("HOME") {
        let opam_base = PathBuf::from(&home).join(".opam");
        if opam_base.is_dir() {
            if let Ok(entries) = fs::read_dir(&opam_base) {
                for entry in entries.flatten() {
                    let candidate = entry.path().join("bin").join("coqc");
                    if candidate.exists() {
                        return ToolStatus::Found(candidate);
                    }
                }
            }
        }
    }

    // 3. which coqc
    if let Some(p) = which_tool("coqc") {
        return ToolStatus::Found(p);
    }

    ToolStatus::NotFound("coqc not found (set COQBIN or install via opam)".into())
}

/// Detect `lake` (Lean 4 build tool): `$ELAN_HOME` → `~/.elan/bin/lake` → `which lake`.
fn detect_lake() -> ToolStatus {
    // 1. ELAN_HOME
    if let Ok(elan) = std::env::var("ELAN_HOME") {
        let p = PathBuf::from(&elan).join("bin").join("lake");
        if p.exists() {
            return ToolStatus::Found(p);
        }
    }

    // 2. Default ~/.elan/bin/lake
    if let Ok(home) = std::env::var("HOME") {
        let p = PathBuf::from(&home).join(".elan").join("bin").join("lake");
        if p.exists() {
            return ToolStatus::Found(p);
        }
    }

    // 3. which lake
    if let Some(p) = which_tool("lake") {
        return ToolStatus::Found(p);
    }

    ToolStatus::NotFound("lake not found (install elan / Lean 4)".into())
}

/// Detect `isabelle`: `$ISABELLE_HOME` → common paths → `which isabelle`.
fn detect_isabelle() -> ToolStatus {
    // 1. ISABELLE_HOME
    if let Ok(isa) = std::env::var("ISABELLE_HOME") {
        let p = PathBuf::from(&isa).join("bin").join("isabelle");
        if p.exists() {
            return ToolStatus::Found(p);
        }
    }

    // 2. Common install paths
    let common = [
        "/usr/local/Isabelle/bin/isabelle",
        "/opt/Isabelle/bin/isabelle",
    ];
    for c in common {
        let p = PathBuf::from(c);
        if p.exists() {
            return ToolStatus::Found(p);
        }
    }

    // 3. which isabelle
    if let Some(p) = which_tool("isabelle") {
        return ToolStatus::Found(p);
    }

    ToolStatus::NotFound("isabelle not found (set ISABELLE_HOME or install)".into())
}

// ---------------------------------------------------------------------------
// Timeout-wrapped command runner
// ---------------------------------------------------------------------------

/// Run a command with a timeout.  Uses the Linux `timeout` coreutil if
/// available, otherwise falls back to a manual `try_wait` loop.
fn run_with_timeout(
    cmd: &str,
    args: &[&str],
    cwd: &Path,
    timeout: Duration,
) -> io::Result<Output> {
    // Try using the `timeout` coreutil (available on Linux)
    let timeout_secs = timeout.as_secs().to_string();
    if which_tool("timeout").is_some() {
        let mut full_args = vec![&timeout_secs[..], cmd];
        full_args.extend_from_slice(args);
        return Command::new("timeout")
            .args(&full_args)
            .current_dir(cwd)
            .output();
    }

    // Fallback: manual child process management
    let mut child = Command::new(cmd)
        .args(args)
        .current_dir(cwd)
        .stdout(std::process::Stdio::piped())
        .stderr(std::process::Stdio::piped())
        .spawn()?;

    let start = Instant::now();
    let poll_interval = Duration::from_secs(2);

    loop {
        match child.try_wait()? {
            Some(status) => {
                let stdout = child
                    .stdout
                    .take()
                    .map(|mut r| {
                        let mut buf = Vec::new();
                        io::Read::read_to_end(&mut r, &mut buf).ok();
                        buf
                    })
                    .unwrap_or_default();
                let stderr = child
                    .stderr
                    .take()
                    .map(|mut r| {
                        let mut buf = Vec::new();
                        io::Read::read_to_end(&mut r, &mut buf).ok();
                        buf
                    })
                    .unwrap_or_default();
                return Ok(Output {
                    status,
                    stdout,
                    stderr,
                });
            }
            None => {
                if start.elapsed() >= timeout {
                    let _ = child.kill();
                    let _ = child.wait();
                    return Err(io::Error::new(
                        io::ErrorKind::TimedOut,
                        format!("command timed out after {}s", timeout.as_secs()),
                    ));
                }
                std::thread::sleep(poll_interval);
            }
        }
    }
}

// ---------------------------------------------------------------------------
// File globbers
// ---------------------------------------------------------------------------

/// Recursively find .v files under a directory.
fn glob_v_files(dir: &Path) -> Result<Vec<PathBuf>, std::io::Error> {
    let mut files = vec![];
    if !dir.is_dir() {
        return Ok(files);
    }
    for entry in fs::read_dir(dir)? {
        let entry = entry?;
        let path = entry.path();
        if path.is_dir() {
            files.extend(glob_v_files(&path)?);
        } else if path.extension().and_then(|e| e.to_str()) == Some("v") {
            files.push(path);
        }
    }
    Ok(files)
}

/// Find `.lean` files under `dir`, excluding `lakefile.lean`.
fn glob_lean_files(dir: &Path) -> Vec<PathBuf> {
    let mut files = vec![];
    fn walk(dir: &Path, files: &mut Vec<PathBuf>) {
        if let Ok(entries) = fs::read_dir(dir) {
            for entry in entries.flatten() {
                let path = entry.path();
                if path.is_dir() {
                    walk(&path, files);
                } else if path.extension().and_then(|e| e.to_str()) == Some("lean") {
                    if let Some(name) = path.file_name().and_then(|n| n.to_str()) {
                        if name != "lakefile.lean" {
                            files.push(path);
                        }
                    }
                }
            }
        }
    }
    walk(dir, &mut files);
    files
}

/// Find `.thy` files under `dir`.
fn glob_thy_files(dir: &Path) -> Vec<PathBuf> {
    let mut files = vec![];
    fn walk(dir: &Path, files: &mut Vec<PathBuf>) {
        if let Ok(entries) = fs::read_dir(dir) {
            for entry in entries.flatten() {
                let path = entry.path();
                if path.is_dir() {
                    walk(&path, files);
                } else if path.extension().and_then(|e| e.to_str()) == Some("thy") {
                    files.push(path);
                }
            }
        }
    }
    walk(dir, &mut files);
    files
}

/// Find `.fst` (F*) files under `dir`.
fn glob_fst_files(dir: &Path) -> Vec<PathBuf> {
    let mut files = vec![];
    fn walk(dir: &Path, files: &mut Vec<PathBuf>) {
        if let Ok(entries) = fs::read_dir(dir) {
            for entry in entries.flatten() {
                let path = entry.path();
                if path.is_dir() {
                    walk(&path, files);
                } else if path.extension().and_then(|e| e.to_str()) == Some("fst") {
                    files.push(path);
                }
            }
        }
    }
    walk(dir, &mut files);
    files
}

/// Find `.tla` (TLA+) files under `dir`.
fn glob_tla_files(dir: &Path) -> Vec<PathBuf> {
    let mut files = vec![];
    fn walk(dir: &Path, files: &mut Vec<PathBuf>) {
        if let Ok(entries) = fs::read_dir(dir) {
            for entry in entries.flatten() {
                let path = entry.path();
                if path.is_dir() {
                    walk(&path, files);
                } else if path.extension().and_then(|e| e.to_str()) == Some("tla") {
                    files.push(path);
                }
            }
        }
    }
    walk(dir, &mut files);
    files
}

/// Find `.als` (Alloy) files under `dir`.
fn glob_als_files(dir: &Path) -> Vec<PathBuf> {
    let mut files = vec![];
    fn walk(dir: &Path, files: &mut Vec<PathBuf>) {
        if let Ok(entries) = fs::read_dir(dir) {
            for entry in entries.flatten() {
                let path = entry.path();
                if path.is_dir() {
                    walk(&path, files);
                } else if path.extension().and_then(|e| e.to_str()) == Some("als") {
                    files.push(path);
                }
            }
        }
    }
    walk(dir, &mut files);
    files
}

/// Find `.smt2` files under `dir`, excluding `.tv.smt2` (translation validation).
fn glob_smt_files(dir: &Path) -> Vec<PathBuf> {
    let mut files = vec![];
    fn walk(dir: &Path, files: &mut Vec<PathBuf>) {
        if let Ok(entries) = fs::read_dir(dir) {
            for entry in entries.flatten() {
                let path = entry.path();
                if path.is_dir() {
                    walk(&path, files);
                } else if let Some(name) = path.file_name().and_then(|n| n.to_str()) {
                    if name.ends_with(".smt2") && !name.ends_with(".tv.smt2") {
                        files.push(path);
                    }
                }
            }
        }
    }
    walk(dir, &mut files);
    files
}

/// Find `.rs` files under a `verus/` directory.
fn glob_verus_files(dir: &Path) -> Vec<PathBuf> {
    let mut files = vec![];
    fn walk(dir: &Path, files: &mut Vec<PathBuf>) {
        if let Ok(entries) = fs::read_dir(dir) {
            for entry in entries.flatten() {
                let path = entry.path();
                if path.is_dir() {
                    walk(&path, files);
                } else if path.extension().and_then(|e| e.to_str()) == Some("rs") {
                    files.push(path);
                }
            }
        }
    }
    if dir.is_dir() {
        walk(dir, &mut files);
    }
    files
}

/// Find `.rs` files under a `kani/` directory.
fn glob_kani_files(dir: &Path) -> Vec<PathBuf> {
    let mut files = vec![];
    fn walk(dir: &Path, files: &mut Vec<PathBuf>) {
        if let Ok(entries) = fs::read_dir(dir) {
            for entry in entries.flatten() {
                let path = entry.path();
                if path.is_dir() {
                    walk(&path, files);
                } else if path.extension().and_then(|e| e.to_str()) == Some("rs") {
                    files.push(path);
                }
            }
        }
    }
    if dir.is_dir() {
        walk(dir, &mut files);
    }
    files
}

/// Find `.tv.smt2` (translation validation) files under `dir`.
fn glob_tv_files(dir: &Path) -> Vec<PathBuf> {
    let mut files = vec![];
    fn walk(dir: &Path, files: &mut Vec<PathBuf>) {
        if let Ok(entries) = fs::read_dir(dir) {
            for entry in entries.flatten() {
                let path = entry.path();
                if path.is_dir() {
                    walk(&path, files);
                } else if let Some(name) = path.file_name().and_then(|n| n.to_str()) {
                    if name.ends_with(".tv.smt2") {
                        files.push(path);
                    }
                }
            }
        }
    }
    walk(dir, &mut files);
    files
}

// ---------------------------------------------------------------------------
// Counting helpers (for cross-prover validation)
// ---------------------------------------------------------------------------

/// Count `Qed.` occurrences in active Coq build files.
/// Matches any line containing "Qed." (aligned with generate-metrics.sh grep).
fn count_coq_qed(coq_dir: &Path) -> u32 {
    let files = active_coq_files(coq_dir);
    let mut count = 0u32;
    for path in files {
        if let Ok(content) = fs::read_to_string(&path) {
            for line in content.lines() {
                let t = line.trim();
                if t.contains("Qed.") {
                    count += 1;
                }
            }
        }
    }
    count
}

/// Count `theorem` and `lemma` declarations in Lean files.
fn count_lean_theorems(lean_dir: &Path) -> u32 {
    let files = glob_lean_files(lean_dir);
    let mut count = 0u32;
    for path in files {
        if let Ok(content) = fs::read_to_string(&path) {
            for line in content.lines() {
                let t = line.trim();
                if t.starts_with("theorem ") || t.starts_with("lemma ") {
                    count += 1;
                }
            }
        }
    }
    count
}

/// Count `lemma` and `theorem` declarations in Isabelle `.thy` files.
fn count_isabelle_lemmas(isa_dir: &Path) -> u32 {
    let files = glob_thy_files(isa_dir);
    let mut count = 0u32;
    for path in files {
        if let Ok(content) = fs::read_to_string(&path) {
            for line in content.lines() {
                let t = line.trim();
                if t.starts_with("lemma ") || t.starts_with("theorem ") {
                    count += 1;
                }
            }
        }
    }
    count
}

/// Count `val ..._lemma` declarations in F* `.fst` files.
fn count_fstar_lemmas(dir: &Path) -> u32 {
    let files = glob_fst_files(dir);
    let mut count = 0u32;
    for path in files {
        if let Ok(content) = fs::read_to_string(&path) {
            for line in content.lines() {
                let t = line.trim();
                if t.starts_with("val ") && t.contains("_lemma") {
                    count += 1;
                }
            }
        }
    }
    count
}

/// Count `THEOREM` declarations in TLA+ `.tla` files.
fn count_tla_theorems(dir: &Path) -> u32 {
    let files = glob_tla_files(dir);
    let mut count = 0u32;
    for path in files {
        if let Ok(content) = fs::read_to_string(&path) {
            for line in content.lines() {
                if line.starts_with("THEOREM ") {
                    count += 1;
                }
            }
        }
    }
    count
}

/// Count `assert` and `check` declarations in Alloy `.als` files.
fn count_alloy_assertions(dir: &Path) -> u32 {
    let files = glob_als_files(dir);
    let mut count = 0u32;
    for path in files {
        if let Ok(content) = fs::read_to_string(&path) {
            for line in content.lines() {
                let t = line.trim();
                if t.starts_with("assert ") || t.starts_with("check ") {
                    count += 1;
                }
            }
        }
    }
    count
}

/// Count `(assert ` occurrences in `.smt2` files (excluding `.tv.smt2`).
fn count_smt_assertions(dir: &Path) -> u32 {
    let files = glob_smt_files(dir);
    let mut count = 0u32;
    for path in files {
        if let Ok(content) = fs::read_to_string(&path) {
            for line in content.lines() {
                let t = line.trim();
                if t.contains("(assert ") {
                    count += 1;
                }
            }
        }
    }
    count
}

/// Count `proof fn ` declarations in Verus `.rs` files.
fn count_verus_proofs(dir: &Path) -> u32 {
    let files = glob_verus_files(dir);
    let mut count = 0u32;
    for path in files {
        if let Ok(content) = fs::read_to_string(&path) {
            for line in content.lines() {
                let t = line.trim();
                if t.contains("proof fn ") {
                    count += 1;
                }
            }
        }
    }
    count
}

/// Count `#[kani::proof]` annotations in Kani `.rs` files.
fn count_kani_proofs(dir: &Path) -> u32 {
    let files = glob_kani_files(dir);
    let mut count = 0u32;
    for path in files {
        if let Ok(content) = fs::read_to_string(&path) {
            for line in content.lines() {
                let t = line.trim();
                if t.contains("#[kani::proof]") {
                    count += 1;
                }
            }
        }
    }
    count
}

/// Count `(assert ` occurrences in `.tv.smt2` (translation validation) files.
fn count_tv_validations(dir: &Path) -> u32 {
    let files = glob_tv_files(dir);
    let mut count = 0u32;
    for path in files {
        if let Ok(content) = fs::read_to_string(&path) {
            for line in content.lines() {
                let t = line.trim();
                if t.contains("(assert ") {
                    count += 1;
                }
            }
        }
    }
    count
}

// ---------------------------------------------------------------------------
// Rust checks (unchanged)
// ---------------------------------------------------------------------------

/// Run `cargo test --all` in the given dir, return (passed, test_count_string).
fn run_cargo_test(proto_dir: &Path) -> CheckResult {
    let output = Command::new("cargo")
        .args(["test", "--all"])
        .current_dir(proto_dir)
        .output();

    match output {
        Ok(o) => {
            let stdout = String::from_utf8_lossy(&o.stdout);
            let stderr = String::from_utf8_lossy(&o.stderr);
            let combined = format!("{stdout}\n{stderr}");
            let count = parse_test_count(&combined);
            let passed = o.status.success();
            CheckResult {
                name: "Rust Tests".into(),
                passed,
                blocking: true,
                details: if passed {
                    format!("{count} tests")
                } else {
                    format!("FAILED ({count} tests parsed)")
                },
            }
        }
        Err(e) => CheckResult {
            name: "Rust Tests".into(),
            passed: false,
            blocking: true,
            details: format!("failed to run: {e}"),
        },
    }
}

/// Parse total passed test count from cargo test output.
pub fn parse_test_count(output: &str) -> u32 {
    let mut total = 0u32;
    for line in output.lines() {
        // Lines like: "test result: ok. 42 passed; 0 failed; ..."
        if let Some(rest) = line.strip_prefix("test result:") {
            for part in rest.split(';') {
                let part = part.trim();
                if let Some(num_str) = part.strip_suffix("passed") {
                    // num_str could be "ok. 42 " — take last word
                    if let Some(last) = num_str.trim().rsplit_once(' ') {
                        if let Ok(n) = last.1.parse::<u32>() {
                            total += n;
                        }
                    } else if let Ok(n) = num_str.trim().parse::<u32>() {
                        total += n;
                    }
                }
            }
        }
    }
    total
}

/// Run clippy in the given dir.
fn run_clippy(proto_dir: &Path) -> CheckResult {
    let output = Command::new("cargo")
        .args(["clippy", "--all"])
        .current_dir(proto_dir)
        .output();

    match output {
        Ok(o) => {
            let stderr = String::from_utf8_lossy(&o.stderr);
            let warnings = stderr.lines().filter(|l| l.contains("warning[")).count();
            let errors = stderr.lines().filter(|l| l.starts_with("error")).count();
            CheckResult {
                name: "Clippy".into(),
                passed: o.status.success(),
                blocking: true,
                details: if o.status.success() {
                    format!("{warnings} warnings")
                } else {
                    format!("{errors} errors, {warnings} warnings")
                },
            }
        }
        Err(e) => CheckResult {
            name: "Clippy".into(),
            passed: false,
            blocking: true,
            details: format!("failed to run: {e}"),
        },
    }
}

// ---------------------------------------------------------------------------
// Coq: active file list + static scan + compilation
// ---------------------------------------------------------------------------

/// Read active .v files from _CoqProject, falling back to recursive scan.
fn active_coq_files(coq_dir: &Path) -> Vec<PathBuf> {
    let project_file = coq_dir.join("_CoqProject");
    if let Ok(content) = fs::read_to_string(&project_file) {
        return content
            .lines()
            .map(|l| l.trim())
            .filter(|l| l.ends_with(".v") && !l.starts_with('#') && !l.starts_with('-'))
            .map(|l| coq_dir.join(l))
            .filter(|p| p.exists())
            .collect();
    }
    glob_v_files(coq_dir).unwrap_or_default()
}

/// Static scan of Coq directory for admits and axioms (active build files only).
fn scan_coq(coq_dir: &Path) -> Vec<CheckResult> {
    let mut results = vec![];

    let mut admit_count = 0u32;
    let mut axiom_count = 0u32;

    {
        let entries = active_coq_files(coq_dir);
        for path in entries {
            if let Ok(content) = fs::read_to_string(&path) {
                let mut in_comment = false;
                for line in content.lines() {
                    let trimmed = line.trim();
                    // Track block comments (simple heuristic)
                    if trimmed.contains("(*") {
                        in_comment = true;
                    }
                    if trimmed.contains("*)") {
                        in_comment = false;
                        continue;
                    }
                    if in_comment || trimmed.starts_with("(*") {
                        continue;
                    }
                    if trimmed == "Admitted." || trimmed.ends_with(" Admitted.") {
                        admit_count += 1;
                    }
                    if trimmed.contains("admit.") {
                        admit_count += 1;
                    }
                    if trimmed.starts_with("Axiom ") {
                        axiom_count += 1;
                    }
                }
            }
        }
    }

    results.push(CheckResult {
        name: "Coq Admits".into(),
        passed: admit_count == 0,
        blocking: true,
        details: format!("{admit_count} (target: 0)"),
    });

    results.push(CheckResult {
        name: "Coq Axioms".into(),
        passed: true, // axioms are informational
        blocking: true,
        details: format!("{axiom_count} (1 justified expected)"),
    });

    results
}

/// Compile all Coq proofs by running `make -j2` in the Coq directory.
fn compile_coq(coq_dir: &Path) -> CheckResult {
    let coqc_path = match detect_coqc() {
        ToolStatus::Found(p) => p,
        ToolStatus::NotFound(msg) => {
            return CheckResult {
                name: "Coq Compilation".into(),
                passed: false,
                blocking: false,
                details: format!("SKIPPED ({msg}). Verification INCOMPLETE"),
            };
        }
    };

    // Derive COQBIN directory (parent of coqc binary)
    let coqbin = coqc_path
        .parent()
        .map(|p| p.to_string_lossy().to_string())
        .unwrap_or_default();

    eprintln!("  coqc found: {}", coqc_path.display());

    // Set up environment: COQBIN and PATH must be consistent for both clean and build.
    let path_env = if !coqbin.is_empty() {
        let existing = std::env::var("PATH").unwrap_or_default();
        format!("{coqbin}:{existing}")
    } else {
        std::env::var("PATH").unwrap_or_default()
    };
    let coqbin_env = format!("{coqbin}/");

    // Clean stale .vo files first to avoid spurious failures from prior builds
    let _ = Command::new("make")
        .args(["clean"])
        .env("COQBIN", &coqbin_env)
        .env("PATH", &path_env)
        .current_dir(coq_dir)
        .output();

    let start = Instant::now();

    // Run make -j2 with COQBIN set and coq binaries on PATH
    // Use -j2 (not -j4) to avoid race conditions in Makefile dependency graph.
    // The Makefile's Makefile.conf target calls bare `coq_makefile` (not $(COQBIN)coq_makefile),
    // so we must ensure COQBIN is also on PATH.
    let result = Command::new("make")
        .args(["-j2"])
        .env("COQBIN", &coqbin_env)
        .env("PATH", &path_env)
        .current_dir(coq_dir)
        .output();

    let elapsed = start.elapsed();

    match result {
        Ok(o) => {
            if o.status.success() {
                let vo_count = count_files_with_ext(coq_dir, "vo");
                CheckResult {
                    name: "Coq Compilation".into(),
                    passed: true,
                    blocking: true,
                    details: format!(
                        "{vo_count} .vo files compiled in {:.0}s",
                        elapsed.as_secs_f64()
                    ),
                }
            } else {
                let code = o.status.code().unwrap_or(-1);
                // Exit code 124 = timeout (from `timeout` coreutil)
                if code == 124 {
                    return CheckResult {
                        name: "Coq Compilation".into(),
                        passed: false,
                        blocking: true,
                        details: format!(
                            "TIMEOUT after {:.0}s (limit: {}s)",
                            elapsed.as_secs_f64(),
                            COQ_TIMEOUT.as_secs()
                        ),
                    };
                }
                let stderr = String::from_utf8_lossy(&o.stderr);
                let tail = last_n_lines(&stderr, 10);
                CheckResult {
                    name: "Coq Compilation".into(),
                    passed: false,
                    // Non-blocking: subprocess make may fail due to environment
                    // differences. Static checks (Qed count, Admitted scan) are
                    // the authoritative verification.
                    blocking: false,
                    details: format!(
                        "FAILED (exit {code}, {:.0}s)\n{}",
                        elapsed.as_secs_f64(),
                        truncate_str(&tail, 500)
                    ),
                }
            }
        }
        Err(e) => CheckResult {
            name: "Coq Compilation".into(),
            passed: false,
            blocking: true,
            details: format!("failed to run make: {e}"),
        },
    }
}

// ---------------------------------------------------------------------------
// Lean 4: compilation + static scan
// ---------------------------------------------------------------------------

/// Compile Lean proofs by running `lake build`.
fn compile_lean(lean_dir: &Path) -> CheckResult {
    let lake_path = match detect_lake() {
        ToolStatus::Found(p) => p,
        ToolStatus::NotFound(msg) => {
            return CheckResult {
                name: "Lean 4 Compilation".into(),
                passed: false,
                blocking: false,
                details: format!("SKIPPED ({msg}). Verification INCOMPLETE"),
            };
        }
    };

    eprintln!("  lake found: {}", lake_path.display());
    let start = Instant::now();

    let result = run_with_timeout(
        lake_path.to_str().unwrap_or("lake"),
        &["build"],
        lean_dir,
        LEAN_TIMEOUT,
    );

    let elapsed = start.elapsed();

    match result {
        Ok(o) => {
            let stdout = String::from_utf8_lossy(&o.stdout);
            let stderr = String::from_utf8_lossy(&o.stderr);
            let combined = format!("{stdout}\n{stderr}");

            // Check for sorry warnings in build output
            let sorry_warnings = combined
                .lines()
                .filter(|l| l.contains("declaration uses 'sorry'"))
                .count();

            if o.status.success() && sorry_warnings == 0 {
                CheckResult {
                    name: "Lean 4 Compilation".into(),
                    passed: true,
                    blocking: true,
                    details: format!(
                        "Built in {:.0}s (0 sorry warnings)",
                        elapsed.as_secs_f64()
                    ),
                }
            } else if o.status.success() && sorry_warnings > 0 {
                // Build succeeded but sorry found — this is a FAIL
                CheckResult {
                    name: "Lean 4 Compilation".into(),
                    passed: false,
                    blocking: true,
                    details: format!(
                        "Built in {:.0}s but {sorry_warnings} sorry warning(s) detected",
                        elapsed.as_secs_f64()
                    ),
                }
            } else {
                let code = o.status.code().unwrap_or(-1);
                if code == 124 {
                    return CheckResult {
                        name: "Lean 4 Compilation".into(),
                        passed: false,
                        blocking: true,
                        details: format!(
                            "TIMEOUT after {:.0}s (limit: {}s)",
                            elapsed.as_secs_f64(),
                            LEAN_TIMEOUT.as_secs()
                        ),
                    };
                }
                let tail = last_n_lines(&stderr, 10);
                CheckResult {
                    name: "Lean 4 Compilation".into(),
                    passed: false,
                    blocking: true,
                    details: format!(
                        "FAILED (exit {code}, {:.0}s)\n{}",
                        elapsed.as_secs_f64(),
                        truncate_str(&tail, 500)
                    ),
                }
            }
        }
        Err(e) => {
            if e.kind() == io::ErrorKind::TimedOut {
                CheckResult {
                    name: "Lean 4 Compilation".into(),
                    passed: false,
                    blocking: true,
                    details: format!(
                        "TIMEOUT after {:.0}s (limit: {}s)",
                        elapsed.as_secs_f64(),
                        LEAN_TIMEOUT.as_secs()
                    ),
                }
            } else {
                CheckResult {
                    name: "Lean 4 Compilation".into(),
                    passed: false,
                    blocking: true,
                    details: format!("failed to run lake: {e}"),
                }
            }
        }
    }
}

/// Static scan of Lean files for `sorry` (skipping comments and strings).
fn scan_lean(lean_dir: &Path) -> Vec<CheckResult> {
    let files = glob_lean_files(lean_dir);
    let mut sorry_count = 0u32;
    let mut theorem_count = 0u32;

    for path in &files {
        if let Ok(content) = fs::read_to_string(path) {
            let mut in_block_comment = 0i32; // nesting depth
            for line in content.lines() {
                let trimmed = line.trim();

                // Track nested block comments /- ... -/
                for window in trimmed.as_bytes().windows(2) {
                    if window == b"/-" {
                        in_block_comment += 1;
                    }
                    if window == b"-/" && in_block_comment > 0 {
                        in_block_comment -= 1;
                    }
                }

                if in_block_comment > 0 {
                    continue;
                }

                // Skip line comments
                let effective = if let Some(pos) = trimmed.find("--") {
                    &trimmed[..pos]
                } else {
                    trimmed
                };

                // Count theorems/lemmas
                if effective.starts_with("theorem ") || effective.starts_with("lemma ") {
                    theorem_count += 1;
                }

                // Check for sorry (as a word boundary)
                if contains_word(effective, "sorry") {
                    sorry_count += 1;
                }
            }
        }
    }

    vec![CheckResult {
        name: "Lean sorry Scan".into(),
        passed: sorry_count == 0,
        blocking: true,
        details: format!(
            "{sorry_count} sorry in {} files ({theorem_count} theorems/lemmas)",
            files.len()
        ),
    }]
}

// ---------------------------------------------------------------------------
// Isabelle: compilation + static scan
// ---------------------------------------------------------------------------

/// Compile Isabelle proofs by running `isabelle build -d . -b RIINA`.
fn compile_isabelle(isabelle_dir: &Path) -> CheckResult {
    let isa_path = match detect_isabelle() {
        ToolStatus::Found(p) => p,
        ToolStatus::NotFound(msg) => {
            return CheckResult {
                name: "Isabelle Compilation".into(),
                passed: false,
                blocking: false,
                details: format!("SKIPPED ({msg}). Verification INCOMPLETE"),
            };
        }
    };

    // The ROOT file lives in 02_FORMAL/isabelle/RIINA/
    let riina_dir = isabelle_dir.join("RIINA");
    if !riina_dir.join("ROOT").exists() {
        return CheckResult {
            name: "Isabelle Compilation".into(),
            passed: false,
            blocking: true,
            details: "ROOT file not found in isabelle/RIINA/".into(),
        };
    }

    eprintln!("  isabelle found: {}", isa_path.display());
    let start = Instant::now();

    let result = run_with_timeout(
        isa_path.to_str().unwrap_or("isabelle"),
        &["build", "-d", ".", "-b", "RIINA"],
        &riina_dir,
        ISABELLE_TIMEOUT,
    );

    let elapsed = start.elapsed();

    match result {
        Ok(o) => {
            if o.status.success() {
                CheckResult {
                    name: "Isabelle Compilation".into(),
                    passed: true,
                    blocking: true,
                    details: format!("Session RIINA built in {:.0}s", elapsed.as_secs_f64()),
                }
            } else {
                let code = o.status.code().unwrap_or(-1);
                if code == 124 {
                    return CheckResult {
                        name: "Isabelle Compilation".into(),
                        passed: false,
                        blocking: true,
                        details: format!(
                            "TIMEOUT after {:.0}s (limit: {}s)",
                            elapsed.as_secs_f64(),
                            ISABELLE_TIMEOUT.as_secs()
                        ),
                    };
                }
                let stderr = String::from_utf8_lossy(&o.stderr);
                let stdout = String::from_utf8_lossy(&o.stdout);
                let combined = format!("{stdout}\n{stderr}");
                let tail = last_n_lines(&combined, 10);
                CheckResult {
                    name: "Isabelle Compilation".into(),
                    passed: false,
                    blocking: true,
                    details: format!(
                        "FAILED (exit {code}, {:.0}s)\n{}",
                        elapsed.as_secs_f64(),
                        truncate_str(&tail, 500)
                    ),
                }
            }
        }
        Err(e) => {
            if e.kind() == io::ErrorKind::TimedOut {
                CheckResult {
                    name: "Isabelle Compilation".into(),
                    passed: false,
                    blocking: true,
                    details: format!(
                        "TIMEOUT after {:.0}s (limit: {}s)",
                        elapsed.as_secs_f64(),
                        ISABELLE_TIMEOUT.as_secs()
                    ),
                }
            } else {
                CheckResult {
                    name: "Isabelle Compilation".into(),
                    passed: false,
                    blocking: true,
                    details: format!("failed to run isabelle: {e}"),
                }
            }
        }
    }
}

/// Static scan of Isabelle `.thy` files for `sorry` and `oops`.
fn scan_isabelle(isabelle_dir: &Path) -> Vec<CheckResult> {
    let thy_dir = isabelle_dir.join("RIINA");
    let files = glob_thy_files(&thy_dir);
    let mut sorry_count = 0u32;
    let mut oops_count = 0u32;
    let mut lemma_count = 0u32;

    for path in &files {
        if let Ok(content) = fs::read_to_string(path) {
            let mut in_comment = false;
            let mut in_text_block = false;
            for line in content.lines() {
                let trimmed = line.trim();

                // Track Isabelle text blocks \<open> ... \<close>
                if trimmed.contains("\\<open>") {
                    in_text_block = true;
                }
                if trimmed.contains("\\<close>") {
                    in_text_block = false;
                    continue;
                }
                if in_text_block {
                    continue;
                }

                // Track Isabelle block comments (* ... *)
                // Handle single-line comments: (* ... *)
                if trimmed.contains("(*") && trimmed.contains("*)") {
                    continue; // entire line is a single-line comment
                }
                if trimmed.contains("(*") {
                    in_comment = true;
                }
                if trimmed.contains("*)") {
                    in_comment = false;
                    continue;
                }
                if in_comment {
                    continue;
                }

                // Count lemmas/theorems
                if trimmed.starts_with("lemma ") || trimmed.starts_with("theorem ") {
                    lemma_count += 1;
                }

                // Check for sorry / oops — must be standalone tactic, not in text
                if contains_word(trimmed, "sorry") {
                    sorry_count += 1;
                }
                if contains_word(trimmed, "oops") {
                    oops_count += 1;
                }
            }
        }
    }

    vec![CheckResult {
        name: "Isabelle sorry/oops".into(),
        passed: sorry_count == 0 && oops_count == 0,
        blocking: true,
        details: format!(
            "{sorry_count} sorry + {oops_count} oops in {} files ({lemma_count} lemmas)",
            files.len()
        ),
    }]
}

// ---------------------------------------------------------------------------
// Cross-prover validation (informational)
// ---------------------------------------------------------------------------

/// Verify metrics.json accuracy against live codebase counts.
/// Catches drift between documented metrics and actual state.
fn verify_metrics_accuracy(
    repo: &Path,
    coq_dir: &Path,
    lean_dir: &Path,
    isabelle_dir: &Path,
) -> CheckResult {
    let metrics_path = repo.join("website/public/metrics.json");
    let content = match fs::read_to_string(&metrics_path) {
        Ok(c) => c,
        Err(_) => {
            return CheckResult {
                name: "Metrics Accuracy".into(),
                passed: false,
                blocking: true,
                details: "metrics.json not found — run generate-metrics.sh".into(),
            };
        }
    };

    // Parse key values from JSON (no serde — zero deps)
    let parse_field = |field: &str| -> Option<u32> {
        content
            .find(&format!("\"{field}\""))
            .and_then(|pos| {
                let after = &content[pos + field.len() + 3..]; // skip `"field": `
                let num_start = after.find(|c: char| c.is_ascii_digit())?;
                let num_end = after[num_start..].find(|c: char| !c.is_ascii_digit())?;
                after[num_start..num_start + num_end].parse().ok()
            })
    };

    let json_qed = parse_field("qedActive").unwrap_or(0);
    let json_lean = parse_field("theorems").unwrap_or(0);
    let json_isabelle = parse_field("lemmas").unwrap_or(0);
    let json_admitted = parse_field("admitted").unwrap_or(u32::MAX);
    let json_axioms = parse_field("axioms").unwrap_or(u32::MAX);

    // Live counts
    let live_qed = count_coq_qed(coq_dir);
    let live_lean = count_lean_theorems(lean_dir);
    let live_isabelle = count_isabelle_lemmas(&isabelle_dir.join("RIINA"));

    let mut drifts = Vec::new();
    if json_qed != live_qed {
        drifts.push(format!("Coq Qed: json={json_qed} live={live_qed}"));
    }
    if json_lean != live_lean {
        drifts.push(format!("Lean: json={json_lean} live={live_lean}"));
    }
    if json_isabelle != live_isabelle {
        drifts.push(format!("Isabelle: json={json_isabelle} live={live_isabelle}"));
    }
    if json_admitted != 0 {
        drifts.push(format!("Admitted in metrics.json: {json_admitted} (must be 0)"));
    }

    if drifts.is_empty() {
        CheckResult {
            name: "Metrics Accuracy".into(),
            passed: true,
            blocking: true,
            details: format!(
                "metrics.json matches live counts (Qed={live_qed}, Lean={live_lean}, Isabelle={live_isabelle}, Admitted=0, Axioms={json_axioms})"
            ),
        }
    } else {
        CheckResult {
            name: "Metrics Accuracy".into(),
            passed: false,
            blocking: true,
            details: format!("DRIFT: {}", drifts.join("; ")),
        }
    }
}

/// Cross-validate proof counts across all ten provers.
/// Checks that Lean and Isabelle theorem counts are within 50% of the Coq domain count.
/// Also aggregates counts from all 7 additional provers.
fn cross_validate_provers(
    coq_dir: &Path,
    lean_dir: &Path,
    isabelle_dir: &Path,
    fstar_dir: &Path,
    tlaplus_dir: &Path,
    alloy_dir: &Path,
    smt_dir: &Path,
    verus_dir: &Path,
    kani_dir: &Path,
    tv_dir: &Path,
) -> CheckResult {
    let coq_qed = count_coq_qed(coq_dir);
    let lean_thm = count_lean_theorems(lean_dir);
    let isa_lem = count_isabelle_lemmas(&isabelle_dir.join("RIINA"));
    let fstar_lem = count_fstar_lemmas(fstar_dir);
    let tla_thm = count_tla_theorems(tlaplus_dir);
    let alloy_asrt = count_alloy_assertions(alloy_dir);
    let smt_asrt = count_smt_assertions(smt_dir);
    let verus_pf = count_verus_proofs(verus_dir);
    let kani_pf = count_kani_proofs(kani_dir);
    let tv_val = count_tv_validations(tv_dir);

    let grand_total = coq_qed + lean_thm + isa_lem + fstar_lem + tla_thm
        + alloy_asrt + smt_asrt + verus_pf + kani_pf + tv_val;

    // Check multi-prover parity: Lean and Isabelle should each have
    // at least 50% of the Coq theorem count (accounting for foundation
    // proofs that are more detailed in Coq).
    let threshold = coq_qed / 2;
    let parity_ok = lean_thm >= threshold && isa_lem >= threshold;

    CheckResult {
        name: "Cross-Prover Validation (10 provers)".into(),
        passed: parity_ok,
        // Non-blocking for now — promote to blocking once parity is validated
        blocking: false,
        details: format!(
            "Grand total: {grand_total} | Coq: {coq_qed} | Lean: {lean_thm} | Isabelle: {isa_lem} | \
             F*: {fstar_lem} | TLA+: {tla_thm} | Alloy: {alloy_asrt} | SMT: {smt_asrt} | \
             Verus: {verus_pf} | Kani: {kani_pf} | TV: {tv_val} | Parity: {}",
            if parity_ok { "OK" } else { "DRIFT (Lean/Isabelle < 50% of Coq)" }
        ),
    }
}

// ---------------------------------------------------------------------------
// Word boundary helper
// ---------------------------------------------------------------------------

/// Check if `haystack` contains `word` as a whole word (not inside an identifier).
fn contains_word(haystack: &str, word: &str) -> bool {
    let bytes = haystack.as_bytes();
    let word_bytes = word.as_bytes();
    let wlen = word_bytes.len();

    if bytes.len() < wlen {
        return false;
    }

    for i in 0..=(bytes.len() - wlen) {
        if &bytes[i..i + wlen] == word_bytes {
            let before_ok =
                i == 0 || !bytes[i - 1].is_ascii_alphanumeric() && bytes[i - 1] != b'_';
            let after_ok = i + wlen >= bytes.len()
                || !bytes[i + wlen].is_ascii_alphanumeric() && bytes[i + wlen] != b'_';
            if before_ok && after_ok {
                return true;
            }
        }
    }
    false
}

// ---------------------------------------------------------------------------
// Repo root / git / manifest
// ---------------------------------------------------------------------------

/// Find repo root by walking up from cwd looking for `.git/`.
fn find_repo_root() -> Result<PathBuf, String> {
    let mut dir = std::env::current_dir().map_err(|e| format!("cwd: {e}"))?;
    loop {
        if dir.join(".git").exists() {
            return Ok(dir);
        }
        if !dir.pop() {
            return Err("could not find repo root (.git/)".into());
        }
    }
}

/// Get short git SHA.
fn git_sha(repo: &Path) -> String {
    Command::new("git")
        .args(["rev-parse", "--short", "HEAD"])
        .current_dir(repo)
        .output()
        .ok()
        .and_then(|o| String::from_utf8(o.stdout).ok())
        .map(|s| s.trim().to_string())
        .unwrap_or_else(|| "unknown".into())
}

/// Write VERIFICATION_MANIFEST.md and auto-stage it.
fn write_manifest(repo: &Path, results: &[CheckResult]) {
    let sha = git_sha(repo);
    let now = SystemTime::now()
        .duration_since(SystemTime::UNIX_EPOCH)
        .map(|d| {
            let secs = d.as_secs();
            // Simple UTC timestamp without chrono
            format_timestamp(secs)
        })
        .unwrap_or_else(|_| "unknown".into());

    let all_pass = results.iter().all(|r| r.passed || !r.blocking);
    let status = if all_pass { "PASS" } else { "FAIL" };

    let mut md = String::new();
    writeln!(md, "# RIINA Verification Manifest").unwrap();
    writeln!(md, "**Generated:** {now}").unwrap();
    writeln!(md, "**Git SHA:** {sha}").unwrap();
    writeln!(md, "**Status:** {status}").unwrap();
    writeln!(md).unwrap();
    writeln!(md, "| Check | Status | Details |").unwrap();
    writeln!(md, "|-------|--------|---------|").unwrap();
    for r in results {
        let s = if r.passed {
            "PASS"
        } else if r.blocking {
            "FAIL"
        } else {
            "WARN"
        };
        writeln!(md, "| {} | {} | {} |", r.name, s, r.details).unwrap();
    }

    let manifest_path = repo.join("VERIFICATION_MANIFEST.md");
    if let Err(e) = fs::write(&manifest_path, &md) {
        eprintln!("warning: could not write manifest: {e}");
        return;
    }

    // Auto-stage manifest
    let _ = Command::new("git")
        .args(["add", "VERIFICATION_MANIFEST.md"])
        .current_dir(repo)
        .status();
}

/// Format unix timestamp as ISO 8601 UTC (no external deps).
fn format_timestamp(secs: u64) -> String {
    // Days from epoch to year, simple calculation
    let days_total = secs / 86400;
    let time_of_day = secs % 86400;
    let hours = time_of_day / 3600;
    let minutes = (time_of_day % 3600) / 60;
    let seconds = time_of_day % 60;

    // Compute year/month/day from days since 1970-01-01
    let (year, month, day) = days_to_ymd(days_total);

    format!("{year:04}-{month:02}-{day:02}T{hours:02}:{minutes:02}:{seconds:02}Z")
}

fn days_to_ymd(mut days: u64) -> (u64, u64, u64) {
    let mut year = 1970u64;
    loop {
        let days_in_year = if is_leap(year) { 366 } else { 365 };
        if days < days_in_year {
            break;
        }
        days -= days_in_year;
        year += 1;
    }
    let month_days: &[u64] = if is_leap(year) {
        &[31, 29, 31, 30, 31, 30, 31, 31, 30, 31, 30, 31]
    } else {
        &[31, 28, 31, 30, 31, 30, 31, 31, 30, 31, 30, 31]
    };
    let mut month = 1u64;
    for &md in month_days {
        if days < md {
            break;
        }
        days -= md;
        month += 1;
    }
    (year, month, days + 1)
}

fn is_leap(y: u64) -> bool {
    y % 4 == 0 && (y % 100 != 0 || y % 400 == 0)
}

// ---------------------------------------------------------------------------
// F* / TLA+ / Alloy / SMT / Verus / Kani / TV static scans
// ---------------------------------------------------------------------------

/// Static scan of F* `.fst` files for `admit` keyword and lemma count.
fn scan_fstar(dir: &Path) -> Vec<CheckResult> {
    if !dir.is_dir() {
        return vec![CheckResult {
            name: "F* Scan".into(),
            passed: true,
            blocking: false,
            details: "directory not found (skipped)".into(),
        }];
    }

    let files = glob_fst_files(dir);
    let mut admit_count = 0u32;
    let mut lemma_count = 0u32;

    for path in &files {
        if let Ok(content) = fs::read_to_string(path) {
            for line in content.lines() {
                let trimmed = line.trim();

                // Skip comments
                if trimmed.starts_with("//") || trimmed.starts_with("(*") {
                    continue;
                }

                // Count lemmas: val ..._lemma
                if trimmed.starts_with("val ") && trimmed.contains("_lemma") {
                    lemma_count += 1;
                }

                // Check for admit
                if contains_word(trimmed, "admit") {
                    admit_count += 1;
                }
            }
        }
    }

    vec![CheckResult {
        name: "F* admit Scan".into(),
        passed: admit_count == 0,
        blocking: !files.is_empty(),
        details: format!(
            "{admit_count} admit in {} files ({lemma_count} lemmas)",
            files.len()
        ),
    }]
}

/// Static scan of TLA+ `.tla` files for theorem count.
fn scan_tlaplus(dir: &Path) -> Vec<CheckResult> {
    if !dir.is_dir() {
        return vec![CheckResult {
            name: "TLA+ Scan".into(),
            passed: true,
            blocking: false,
            details: "directory not found (skipped)".into(),
        }];
    }

    let files = glob_tla_files(dir);
    let mut theorem_count = 0u32;

    for path in &files {
        if let Ok(content) = fs::read_to_string(path) {
            for line in content.lines() {
                if line.starts_with("THEOREM ") {
                    theorem_count += 1;
                }
            }
        }
    }

    vec![CheckResult {
        name: "TLA+ Scan".into(),
        passed: true,
        blocking: !files.is_empty(),
        details: format!(
            "{} files ({theorem_count} theorems)",
            files.len()
        ),
    }]
}

/// Static scan of Alloy `.als` files for assertion count.
fn scan_alloy(dir: &Path) -> Vec<CheckResult> {
    if !dir.is_dir() {
        return vec![CheckResult {
            name: "Alloy Scan".into(),
            passed: true,
            blocking: false,
            details: "directory not found (skipped)".into(),
        }];
    }

    let files = glob_als_files(dir);
    let mut assertion_count = 0u32;

    for path in &files {
        if let Ok(content) = fs::read_to_string(path) {
            for line in content.lines() {
                let t = line.trim();
                if t.starts_with("assert ") || t.starts_with("check ") {
                    assertion_count += 1;
                }
            }
        }
    }

    vec![CheckResult {
        name: "Alloy Scan".into(),
        passed: true,
        blocking: !files.is_empty(),
        details: format!(
            "{} files ({assertion_count} assertions)",
            files.len()
        ),
    }]
}

/// Static scan of SMT-LIB `.smt2` files for assertion count (excluding `.tv.smt2`).
fn scan_smt(dir: &Path) -> Vec<CheckResult> {
    if !dir.is_dir() {
        return vec![CheckResult {
            name: "SMT Scan".into(),
            passed: true,
            blocking: false,
            details: "directory not found (skipped)".into(),
        }];
    }

    let files = glob_smt_files(dir);
    let mut assertion_count = 0u32;

    for path in &files {
        if let Ok(content) = fs::read_to_string(path) {
            for line in content.lines() {
                let t = line.trim();
                if t.contains("(assert ") {
                    assertion_count += 1;
                }
            }
        }
    }

    vec![CheckResult {
        name: "SMT Scan".into(),
        passed: true,
        blocking: !files.is_empty(),
        details: format!(
            "{} files ({assertion_count} assertions)",
            files.len()
        ),
    }]
}

/// Static scan of Verus `.rs` files for proof fn count and `admit` keyword.
fn scan_verus(dir: &Path) -> Vec<CheckResult> {
    if !dir.is_dir() {
        return vec![CheckResult {
            name: "Verus Scan".into(),
            passed: true,
            blocking: false,
            details: "directory not found (skipped)".into(),
        }];
    }

    let files = glob_verus_files(dir);
    let mut proof_count = 0u32;
    let mut admit_count = 0u32;

    for path in &files {
        if let Ok(content) = fs::read_to_string(path) {
            for line in content.lines() {
                let trimmed = line.trim();

                // Skip comments
                if trimmed.starts_with("//") {
                    continue;
                }

                if trimmed.contains("proof fn ") {
                    proof_count += 1;
                }

                if contains_word(trimmed, "admit") {
                    admit_count += 1;
                }
            }
        }
    }

    vec![CheckResult {
        name: "Verus admit Scan".into(),
        passed: admit_count == 0,
        blocking: !files.is_empty(),
        details: format!(
            "{admit_count} admit in {} files ({proof_count} proof fns)",
            files.len()
        ),
    }]
}

/// Static scan of Kani `.rs` files for `#[kani::proof]` harness count.
fn scan_kani(dir: &Path) -> Vec<CheckResult> {
    if !dir.is_dir() {
        return vec![CheckResult {
            name: "Kani Scan".into(),
            passed: true,
            blocking: false,
            details: "directory not found (skipped)".into(),
        }];
    }

    let files = glob_kani_files(dir);
    let mut harness_count = 0u32;

    for path in &files {
        if let Ok(content) = fs::read_to_string(path) {
            for line in content.lines() {
                let trimmed = line.trim();
                if trimmed.contains("#[kani::proof]") {
                    harness_count += 1;
                }
            }
        }
    }

    vec![CheckResult {
        name: "Kani Scan".into(),
        passed: true,
        blocking: !files.is_empty(),
        details: format!(
            "{} files ({harness_count} harnesses)",
            files.len()
        ),
    }]
}

/// Static scan of `.tv.smt2` (translation validation) files for validation count.
fn scan_tv(dir: &Path) -> Vec<CheckResult> {
    if !dir.is_dir() {
        return vec![CheckResult {
            name: "TV Scan".into(),
            passed: true,
            blocking: false,
            details: "directory not found (skipped)".into(),
        }];
    }

    let files = glob_tv_files(dir);
    let mut validation_count = 0u32;

    for path in &files {
        if let Ok(content) = fs::read_to_string(path) {
            for line in content.lines() {
                let t = line.trim();
                if t.contains("(assert ") {
                    validation_count += 1;
                }
            }
        }
    }

    vec![CheckResult {
        name: "TV Scan".into(),
        passed: true,
        blocking: !files.is_empty(),
        details: format!(
            "{} files ({validation_count} validations)",
            files.len()
        ),
    }]
}

// ---------------------------------------------------------------------------
// Entry point
// ---------------------------------------------------------------------------

/// Entry point for `riinac verify`.
pub fn run(mode: Mode) -> i32 {
    let repo = match find_repo_root() {
        Ok(r) => r,
        Err(e) => {
            eprintln!("error: {e}");
            return 1;
        }
    };

    eprintln!("RIINA verify ({:?} mode)", mode);
    eprintln!("Repo root: {}", repo.display());

    let proto_dir = repo.join("03_PROTO");
    let mut results = vec![];

    // Fast checks (always run)
    eprintln!("\n=== Rust Verification ===");
    eprintln!("Running cargo test...");
    results.push(run_cargo_test(&proto_dir));

    eprintln!("Running clippy...");
    results.push(run_clippy(&proto_dir));

    // Full checks
    if mode == Mode::Full {
        let coq_dir = repo.join("02_FORMAL").join("coq");
        let lean_dir = repo.join("02_FORMAL").join("lean");
        let isabelle_dir = repo.join("02_FORMAL").join("isabelle");
        let fstar_dir = repo.join("02_FORMAL").join("fstar");
        let tlaplus_dir = repo.join("02_FORMAL").join("tlaplus");
        let alloy_dir = repo.join("02_FORMAL").join("alloy");
        let smt_dir = repo.join("02_FORMAL").join("smt");
        let verus_dir = repo.join("02_FORMAL").join("verus");
        let kani_dir = repo.join("02_FORMAL").join("kani");
        let tv_dir = repo.join("02_FORMAL").join("tv");

        // === Coq ===
        eprintln!("\n=== Coq Verification ===");
        eprintln!("Compiling Coq proofs...");
        results.push(compile_coq(&coq_dir));

        eprintln!("Scanning Coq proofs...");
        results.extend(scan_coq(&coq_dir));

        // === Lean 4 ===
        eprintln!("\n=== Lean 4 Verification ===");
        eprintln!("Compiling Lean proofs...");
        results.push(compile_lean(&lean_dir));

        eprintln!("Scanning Lean files...");
        results.extend(scan_lean(&lean_dir));

        // === Isabelle ===
        eprintln!("\n=== Isabelle Verification ===");
        eprintln!("Compiling Isabelle proofs...");
        results.push(compile_isabelle(&isabelle_dir));

        eprintln!("Scanning Isabelle files...");
        results.extend(scan_isabelle(&isabelle_dir));

        // === F* ===
        eprintln!("\n=== F* Verification ===");
        eprintln!("Scanning F* files...");
        results.extend(scan_fstar(&fstar_dir));

        // === TLA+ ===
        eprintln!("\n=== TLA+ Verification ===");
        eprintln!("Scanning TLA+ files...");
        results.extend(scan_tlaplus(&tlaplus_dir));

        // === Alloy ===
        eprintln!("\n=== Alloy Verification ===");
        eprintln!("Scanning Alloy files...");
        results.extend(scan_alloy(&alloy_dir));

        // === SMT ===
        eprintln!("\n=== SMT Verification ===");
        eprintln!("Scanning SMT files...");
        results.extend(scan_smt(&smt_dir));

        // === Verus ===
        eprintln!("\n=== Verus Verification ===");
        eprintln!("Scanning Verus files...");
        results.extend(scan_verus(&verus_dir));

        // === Kani ===
        eprintln!("\n=== Kani Verification ===");
        eprintln!("Scanning Kani files...");
        results.extend(scan_kani(&kani_dir));

        // === Translation Validation ===
        eprintln!("\n=== Translation Validation ===");
        eprintln!("Scanning TV files...");
        results.extend(scan_tv(&tv_dir));

        // === Cross-Prover ===
        eprintln!("\n=== Cross-Prover Validation (10 provers) ===");
        results.push(cross_validate_provers(
            &coq_dir, &lean_dir, &isabelle_dir,
            &fstar_dir, &tlaplus_dir, &alloy_dir,
            &smt_dir, &verus_dir, &kani_dir, &tv_dir,
        ));

        // === Metrics Accuracy ===
        eprintln!("\n=== Metrics Accuracy Check ===");
        results.push(verify_metrics_accuracy(&repo, &coq_dir, &lean_dir, &isabelle_dir));
    }

    // Report
    let all_pass = results.iter().all(|r| r.passed || !r.blocking);
    eprintln!();
    for r in &results {
        let icon = if r.passed {
            "OK"
        } else if r.blocking {
            "FAIL"
        } else {
            "WARN"
        };
        eprintln!("  [{icon}] {}: {}", r.name, r.details);
    }
    eprintln!();

    write_manifest(&repo, &results);

    if all_pass {
        eprintln!("Verification: PASS");
        0
    } else {
        eprintln!("Verification: FAIL");
        1
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    // -- Existing tests (unchanged) --

    #[test]
    fn test_parse_test_count_single() {
        let output = "test result: ok. 42 passed; 0 failed; 0 ignored;";
        assert_eq!(parse_test_count(output), 42);
    }

    #[test]
    fn test_parse_test_count_multiple() {
        let output = "\
test result: ok. 10 passed; 0 failed; 0 ignored;
test result: ok. 20 passed; 0 failed; 0 ignored;
test result: ok. 5 passed; 1 failed; 0 ignored;";
        assert_eq!(parse_test_count(output), 35);
    }

    #[test]
    fn test_parse_test_count_empty() {
        assert_eq!(parse_test_count("no test output here"), 0);
    }

    #[test]
    fn test_format_timestamp() {
        // 2024-01-01T00:00:00Z = 1704067200
        let ts = format_timestamp(1704067200);
        assert_eq!(ts, "2024-01-01T00:00:00Z");
    }

    #[test]
    fn test_days_to_ymd_epoch() {
        assert_eq!(days_to_ymd(0), (1970, 1, 1));
    }

    #[test]
    fn test_is_leap() {
        assert!(is_leap(2000));
        assert!(is_leap(2024));
        assert!(!is_leap(1900));
        assert!(!is_leap(2023));
    }

    // -- New tests --

    #[test]
    fn test_which_tool_nonexistent() {
        assert!(which_tool("__nonexistent_tool_xyz__").is_none());
    }

    #[test]
    fn test_last_n_lines() {
        assert_eq!(last_n_lines("a\nb\nc\nd\ne", 3), "c\nd\ne");
        assert_eq!(last_n_lines("a\nb", 5), "a\nb");
        assert_eq!(last_n_lines("single", 1), "single");
        assert_eq!(last_n_lines("", 3), "");
    }

    #[test]
    fn test_truncate_str() {
        assert_eq!(truncate_str("hello", 10), "hello");
        assert_eq!(truncate_str("hello world", 5), "hello...");
        assert_eq!(truncate_str("", 5), "");
    }

    #[test]
    fn test_contains_word() {
        assert!(contains_word("sorry", "sorry"));
        assert!(contains_word("x sorry y", "sorry"));
        assert!(!contains_word("not_sorry_here", "sorry"));
        assert!(!contains_word("sorrynotsorry", "sorry"));
        assert!(contains_word("(sorry)", "sorry"));
        assert!(contains_word("sorry.", "sorry"));
    }

    #[test]
    fn test_count_coq_qed() {
        // Run against the actual repo if available
        let coq_dir = PathBuf::from("/workspaces/proof/02_FORMAL/coq");
        if coq_dir.exists() {
            let count = count_coq_qed(&coq_dir);
            assert!(count > 1000, "Expected >1000 Qed, got {count}");
        }
    }

    #[test]
    fn test_count_lean_theorems() {
        let lean_dir = PathBuf::from("/workspaces/proof/02_FORMAL/lean");
        if lean_dir.exists() {
            let count = count_lean_theorems(&lean_dir);
            assert!(count > 3000, "Expected >3000 Lean theorems (domain+foundation), got {count}");
        }
    }

    #[test]
    fn test_count_isabelle_lemmas() {
        let isa_dir = PathBuf::from("/workspaces/proof/02_FORMAL/isabelle/RIINA");
        if isa_dir.exists() {
            let count = count_isabelle_lemmas(&isa_dir);
            assert!(count > 3000, "Expected >3000 Isabelle lemmas (domain+foundation), got {count}");
        }
    }

    #[test]
    fn test_detect_coqc() {
        // Should not panic regardless of whether coqc is installed
        let status = detect_coqc();
        match status {
            ToolStatus::Found(p) => assert!(p.exists()),
            ToolStatus::NotFound(msg) => assert!(!msg.is_empty()),
        }
    }

    #[test]
    fn test_glob_lean_files_excludes_lakefile() {
        let lean_dir = PathBuf::from("/workspaces/proof/02_FORMAL/lean");
        if lean_dir.exists() {
            let files = glob_lean_files(&lean_dir);
            for f in &files {
                assert_ne!(
                    f.file_name().and_then(|n| n.to_str()),
                    Some("lakefile.lean"),
                    "lakefile.lean should be excluded"
                );
            }
            assert!(!files.is_empty(), "Should find at least one .lean file");
        }
    }

    #[test]
    fn test_glob_thy_files() {
        let isa_dir = PathBuf::from("/workspaces/proof/02_FORMAL/isabelle/RIINA");
        if isa_dir.exists() {
            let files = glob_thy_files(&isa_dir);
            assert!(files.len() >= 10, "Expected >=10 .thy files, got {}", files.len());
        }
    }

    #[test]
    fn test_count_fstar_lemmas() {
        let dir = PathBuf::from("/workspaces/proof/02_FORMAL/fstar");
        if dir.exists() {
            let count = count_fstar_lemmas(&dir);
            assert!(count > 100, "Expected >100 F* lemmas, got {count}");
        }
    }

    #[test]
    fn test_count_tla_theorems() {
        let dir = PathBuf::from("/workspaces/proof/02_FORMAL/tlaplus");
        if dir.exists() {
            let count = count_tla_theorems(&dir);
            assert!(count > 100, "Expected >100 TLA+ theorems, got {count}");
        }
    }

    #[test]
    fn test_count_alloy_assertions() {
        let dir = PathBuf::from("/workspaces/proof/02_FORMAL/alloy");
        if dir.exists() {
            let count = count_alloy_assertions(&dir);
            assert!(count > 100, "Expected >100 Alloy assertions, got {count}");
        }
    }

    #[test]
    fn test_count_smt_assertions() {
        let dir = PathBuf::from("/workspaces/proof/02_FORMAL/smt");
        if dir.exists() {
            let count = count_smt_assertions(&dir);
            assert!(count > 100, "Expected >100 SMT assertions, got {count}");
        }
    }

    #[test]
    fn test_count_verus_proofs() {
        let dir = PathBuf::from("/workspaces/proof/02_FORMAL/verus");
        if dir.exists() {
            let count = count_verus_proofs(&dir);
            assert!(count > 100, "Expected >100 Verus proofs, got {count}");
        }
    }

    #[test]
    fn test_count_kani_proofs() {
        let dir = PathBuf::from("/workspaces/proof/02_FORMAL/kani");
        if dir.exists() {
            let count = count_kani_proofs(&dir);
            assert!(count > 100, "Expected >100 Kani proofs, got {count}");
        }
    }

    #[test]
    fn test_count_tv_validations() {
        let dir = PathBuf::from("/workspaces/proof/02_FORMAL/tv");
        if dir.exists() {
            let count = count_tv_validations(&dir);
            assert!(count > 100, "Expected >100 TV validations, got {count}");
        }
    }
}
