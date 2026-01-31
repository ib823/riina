//! RIINA Verification Gate
//!
//! `riinac verify [--fast|--full]` — runs all checks and produces a manifest.

#![forbid(unsafe_code)]

use std::fmt::Write as _;
use std::fs;
use std::path::{Path, PathBuf};
use std::process::Command;
use std::time::SystemTime;

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Mode {
    Fast,
    Full,
}

#[derive(Debug)]
struct CheckResult {
    name: String,
    passed: bool,
    details: String,
}

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
        .args(["clippy", "--all", "--", "-D", "warnings"])
        .current_dir(proto_dir)
        .output();

    match output {
        Ok(o) => CheckResult {
            name: "Clippy".into(),
            passed: o.status.success(),
            details: if o.status.success() {
                "0 warnings".into()
            } else {
                let stderr = String::from_utf8_lossy(&o.stderr);
                let warning_count = stderr.lines().filter(|l| l.contains("warning[")).count();
                format!("{warning_count} warnings/errors")
            },
        },
        Err(e) => CheckResult {
            name: "Clippy".into(),
            passed: false,
            details: format!("failed to run: {e}"),
        },
    }
}

/// Scan Coq directory for admits and axioms.
fn scan_coq(coq_dir: &Path) -> Vec<CheckResult> {
    let mut results = vec![];

    let mut admit_count = 0u32;
    let mut axiom_count = 0u32;

    if let Ok(entries) = glob_v_files(coq_dir) {
        for path in entries {
            if let Ok(content) = fs::read_to_string(&path) {
                for line in content.lines() {
                    let trimmed = line.trim();
                    if trimmed == "Admitted." || trimmed.ends_with(" Admitted.") {
                        admit_count += 1;
                    }
                    if trimmed.contains("admit.") && !trimmed.starts_with("(*") {
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
        details: format!("{admit_count} (target: 0)"),
    });

    results.push(CheckResult {
        name: "Coq Axioms".into(),
        passed: true, // axioms are informational
        details: format!("{axiom_count} (5 justified expected)"),
    });

    results
}

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

    let all_pass = results.iter().all(|r| r.passed);
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
        let s = if r.passed { "PASS" } else { "FAIL" };
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

    // Fast checks
    eprintln!("Running cargo test...");
    results.push(run_cargo_test(&proto_dir));

    eprintln!("Running clippy...");
    results.push(run_clippy(&proto_dir));

    // Full checks
    if mode == Mode::Full {
        let coq_dir = repo.join("02_FORMAL").join("coq");
        eprintln!("Scanning Coq proofs...");
        results.extend(scan_coq(&coq_dir));
    }

    // Report
    let all_pass = results.iter().all(|r| r.passed);
    eprintln!();
    for r in &results {
        let icon = if r.passed { "OK" } else { "FAIL" };
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
}
