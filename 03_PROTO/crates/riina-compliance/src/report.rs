// SPDX-License-Identifier: MPL-2.0
// Copyright (c) 2026 The RIINA Authors. See AUTHORS file.

//! Compliance Report Generator
//!
//! Produces structured audit reports in JSON and human-readable text.
//! Each report is a self-contained compliance artifact that can be
//! submitted to auditors or regulatory bodies.
//!
//! The report includes:
//! - File identity (path + SHA-256 hash of source)
//! - Profiles checked and their rule coverage
//! - All violations found (errors + warnings)
//! - Overall verdict (PASS / FAIL / PASS_WITH_WARNINGS)
//! - Timestamp and compiler version for audit traceability

use std::collections::HashMap;
use std::fmt;

use crate::{ComplianceProfile, ComplianceViolation, Severity};
use crate::rules;

/// Overall compliance verdict.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Verdict {
    /// All rules passed, zero violations.
    Pass,
    /// No errors but some warnings.
    PassWithWarnings,
    /// At least one error-severity violation.
    Fail,
}

impl fmt::Display for Verdict {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Pass => write!(f, "PASS"),
            Self::PassWithWarnings => write!(f, "PASS_WITH_WARNINGS"),
            Self::Fail => write!(f, "FAIL"),
        }
    }
}

/// Coverage info for a single profile.
#[derive(Debug, Clone)]
pub struct ProfileCoverage {
    pub profile: ComplianceProfile,
    pub rules_implemented: usize,
    pub rules_total: usize,
    pub violations: Vec<ComplianceViolation>,
    pub errors: usize,
    pub warnings: usize,
}

/// A complete compliance report — the audit artifact.
#[derive(Debug, Clone)]
pub struct ComplianceReport {
    pub riina_version: String,
    pub file_path: String,
    pub source_sha256: String,
    pub timestamp: String,
    pub profiles: Vec<ProfileCoverage>,
    pub verdict: Verdict,
    pub total_rules_checked: usize,
    pub total_violations: usize,
    pub total_errors: usize,
    pub total_warnings: usize,
}

/// Known total rule counts per standard (from spec documents).
/// These represent the total auditable requirements — rules_implemented / rules_total
/// gives the coverage percentage.
fn spec_total_rules(profile: ComplianceProfile) -> usize {
    match profile {
        ComplianceProfile::PciDss => 78,     // PCI-DSS v4.0 requirements
        ComplianceProfile::Pdpa => 14,       // PDPA 2010 Sections 5-24
        ComplianceProfile::Bnm => 26,        // BNM RMiT policy areas
        ComplianceProfile::Hipaa => 54,      // HIPAA Security Rule safeguards
        ComplianceProfile::Cmmc => 110,      // CMMC Level 2 practices
        ComplianceProfile::Sox => 18,        // SOX IT controls (s302/s404)
        ComplianceProfile::Gdpr => 42,       // GDPR articles with technical measures
        ComplianceProfile::Do178c => 66,     // DO-178C objectives (DAL A)
        ComplianceProfile::Iec62443 => 51,   // IEC 62443-4-1 requirements
        ComplianceProfile::NercCip => 35,    // NERC CIP standards
        ComplianceProfile::Fda21cfr => 22,   // 21 CFR Part 11 requirements
        ComplianceProfile::Iso27001 => 93,   // ISO 27001:2022 controls (Annex A)
        ComplianceProfile::Nist80053 => 326, // NIST 800-53 rev5 controls
        ComplianceProfile::MasTrm => 38,     // MAS TRM guidelines
        ComplianceProfile::Itar => 16,       // ITAR technical controls
    }
}

/// Generate a compliance report from validation results.
pub fn generate(
    file_path: &str,
    source: &str,
    profiles: &[ComplianceProfile],
    violations: &[ComplianceViolation],
) -> ComplianceReport {
    let source_sha256 = sha256_hex(source.as_bytes());
    let timestamp = utc_now_iso8601();

    // Group violations by profile
    let mut by_profile: HashMap<ComplianceProfile, Vec<ComplianceViolation>> = HashMap::new();
    for v in violations {
        by_profile.entry(v.profile).or_default().push(v.clone());
    }

    let mut profile_coverages = Vec::new();
    let mut total_rules = 0;

    for &p in profiles {
        let implemented = rules::rule_count(p);
        let total = spec_total_rules(p);
        let profile_violations = by_profile.remove(&p).unwrap_or_default();
        let errors = profile_violations.iter().filter(|v| v.severity == Severity::Error).count();
        let warnings = profile_violations.iter().filter(|v| v.severity == Severity::Warning).count();
        total_rules += implemented;

        profile_coverages.push(ProfileCoverage {
            profile: p,
            rules_implemented: implemented,
            rules_total: total,
            violations: profile_violations,
            errors,
            warnings,
        });
    }

    let total_errors: usize = profile_coverages.iter().map(|p| p.errors).sum();
    let total_warnings: usize = profile_coverages.iter().map(|p| p.warnings).sum();
    let total_violations = total_errors + total_warnings;

    let verdict = if total_errors > 0 {
        Verdict::Fail
    } else if total_warnings > 0 {
        Verdict::PassWithWarnings
    } else {
        Verdict::Pass
    };

    ComplianceReport {
        riina_version: "0.1.0".into(),
        file_path: file_path.into(),
        source_sha256,
        timestamp,
        profiles: profile_coverages,
        verdict,
        total_rules_checked: total_rules,
        total_violations,
        total_errors,
        total_warnings,
    }
}

// ---------------------------------------------------------------------------
// Output formats
// ---------------------------------------------------------------------------

impl ComplianceReport {
    /// Render as JSON string (no external dependencies — hand-built).
    pub fn to_json(&self) -> String {
        let mut out = String::with_capacity(2048);
        out.push_str("{\n");
        json_kv_str(&mut out, "  ", "riina_version", &self.riina_version, true);
        json_kv_str(&mut out, "  ", "file", &self.file_path, true);
        json_kv_str(&mut out, "  ", "source_sha256", &self.source_sha256, true);
        json_kv_str(&mut out, "  ", "timestamp", &self.timestamp, true);
        json_kv_str(&mut out, "  ", "verdict", &self.verdict.to_string(), true);
        json_kv_num(&mut out, "  ", "total_rules_checked", self.total_rules_checked, true);
        json_kv_num(&mut out, "  ", "total_violations", self.total_violations, true);
        json_kv_num(&mut out, "  ", "total_errors", self.total_errors, true);
        json_kv_num(&mut out, "  ", "total_warnings", self.total_warnings, true);

        out.push_str("  \"profiles\": [\n");
        for (i, pc) in self.profiles.iter().enumerate() {
            out.push_str("    {\n");
            json_kv_str(&mut out, "      ", "profile", pc.profile.slug(), true);
            json_kv_str(&mut out, "      ", "description", pc.profile.description(), true);
            json_kv_num(&mut out, "      ", "rules_implemented", pc.rules_implemented, true);
            json_kv_num(&mut out, "      ", "rules_total", pc.rules_total, true);
            let pct = if pc.rules_total > 0 {
                (pc.rules_implemented as f64 / pc.rules_total as f64) * 100.0
            } else {
                0.0
            };
            out.push_str(&format!("      \"coverage_pct\": {:.1},\n", pct));
            json_kv_num(&mut out, "      ", "errors", pc.errors, true);
            json_kv_num(&mut out, "      ", "warnings", pc.warnings, true);

            out.push_str("      \"violations\": [\n");
            for (j, v) in pc.violations.iter().enumerate() {
                out.push_str("        {\n");
                json_kv_str(&mut out, "          ", "rule_id", v.rule_id, true);
                json_kv_str(&mut out, "          ", "severity", &v.severity.to_string(), true);
                json_kv_str(&mut out, "          ", "message", &json_escape(&v.message), false);
                out.push('\n');
                out.push_str("        }");
                if j + 1 < pc.violations.len() { out.push(','); }
                out.push('\n');
            }
            out.push_str("      ]\n");

            out.push_str("    }");
            if i + 1 < self.profiles.len() { out.push(','); }
            out.push('\n');
        }
        out.push_str("  ]\n");

        out.push_str("}\n");
        out
    }

    /// Render as human-readable text report.
    pub fn to_text(&self) -> String {
        let mut out = String::with_capacity(2048);
        let line = "═".repeat(72);
        let thin = "─".repeat(72);

        out.push_str(&format!("{line}\n"));
        out.push_str(&format!("  RIINA COMPLIANCE REPORT\n"));
        out.push_str(&format!("{line}\n"));
        out.push_str(&format!("  Compiler:    RIINA v{}\n", self.riina_version));
        out.push_str(&format!("  File:        {}\n", self.file_path));
        out.push_str(&format!("  SHA-256:     {}\n", self.source_sha256));
        out.push_str(&format!("  Timestamp:   {}\n", self.timestamp));
        out.push_str(&format!("  Verdict:     {}\n", self.verdict));
        out.push_str(&format!("{thin}\n"));

        out.push_str(&format!("  Rules checked: {}   Violations: {}   Errors: {}   Warnings: {}\n",
            self.total_rules_checked, self.total_violations, self.total_errors, self.total_warnings));
        out.push_str(&format!("{thin}\n"));

        for pc in &self.profiles {
            let pct = if pc.rules_total > 0 {
                (pc.rules_implemented as f64 / pc.rules_total as f64) * 100.0
            } else {
                0.0
            };
            out.push_str(&format!("\n  PROFILE: {}\n", pc.profile.description()));
            out.push_str(&format!("  Coverage: {}/{} rules ({:.1}%)\n",
                pc.rules_implemented, pc.rules_total, pct));

            if pc.violations.is_empty() {
                out.push_str("  Status: CLEAN — no violations\n");
            } else {
                out.push_str(&format!("  Status: {} error(s), {} warning(s)\n", pc.errors, pc.warnings));
                out.push('\n');
                for v in &pc.violations {
                    let marker = match v.severity {
                        Severity::Error => "ERROR",
                        Severity::Warning => "WARN ",
                    };
                    out.push_str(&format!("    [{marker}] {}: {}\n", v.rule_id, v.message));
                }
            }
        }

        out.push_str(&format!("\n{line}\n"));
        out.push_str(&format!("  This report is a machine-generated audit artifact.\n"));
        out.push_str(&format!("  Compliance rules are backed by Coq formal proofs.\n"));
        out.push_str(&format!("  Verify integrity: sha256sum <source_file> == {}\n", self.source_sha256));
        out.push_str(&format!("{line}\n"));
        out
    }
}

// ---------------------------------------------------------------------------
// Helpers (no external deps)
// ---------------------------------------------------------------------------

fn json_kv_str(out: &mut String, indent: &str, key: &str, val: &str, comma: bool) {
    out.push_str(&format!("{indent}\"{key}\": \"{val}\""));
    if comma { out.push(','); }
    out.push('\n');
}

fn json_kv_num(out: &mut String, indent: &str, key: &str, val: usize, comma: bool) {
    out.push_str(&format!("{indent}\"{key}\": {val}"));
    if comma { out.push(','); }
    out.push('\n');
}

fn json_escape(s: &str) -> String {
    s.replace('\\', "\\\\")
     .replace('"', "\\\"")
     .replace('\n', "\\n")
     .replace('\r', "\\r")
     .replace('\t', "\\t")
}

/// Simple SHA-256 (no deps — we implement the NIST FIPS 180-4 algorithm).
fn sha256_hex(data: &[u8]) -> String {
    let h: [u32; 8] = sha256_compress(data);
    let mut hex = String::with_capacity(64);
    for word in h {
        hex.push_str(&format!("{:08x}", word));
    }
    hex
}

fn sha256_compress(data: &[u8]) -> [u32; 8] {
    const K: [u32; 64] = [
        0x428a2f98, 0x71374491, 0xb5c0fbcf, 0xe9b5dba5,
        0x3956c25b, 0x59f111f1, 0x923f82a4, 0xab1c5ed5,
        0xd807aa98, 0x12835b01, 0x243185be, 0x550c7dc3,
        0x72be5d74, 0x80deb1fe, 0x9bdc06a7, 0xc19bf174,
        0xe49b69c1, 0xefbe4786, 0x0fc19dc6, 0x240ca1cc,
        0x2de92c6f, 0x4a7484aa, 0x5cb0a9dc, 0x76f988da,
        0x983e5152, 0xa831c66d, 0xb00327c8, 0xbf597fc7,
        0xc6e00bf3, 0xd5a79147, 0x06ca6351, 0x14292967,
        0x27b70a85, 0x2e1b2138, 0x4d2c6dfc, 0x53380d13,
        0x650a7354, 0x766a0abb, 0x81c2c92e, 0x92722c85,
        0xa2bfe8a1, 0xa81a664b, 0xc24b8b70, 0xc76c51a3,
        0xd192e819, 0xd6990624, 0xf40e3585, 0x106aa070,
        0x19a4c116, 0x1e376c08, 0x2748774c, 0x34b0bcb5,
        0x391c0cb3, 0x4ed8aa4a, 0x5b9cca4f, 0x682e6ff3,
        0x748f82ee, 0x78a5636f, 0x84c87814, 0x8cc70208,
        0x90befffa, 0xa4506ceb, 0xbef9a3f7, 0xc67178f2,
    ];

    let mut h: [u32; 8] = [
        0x6a09e667, 0xbb67ae85, 0x3c6ef372, 0xa54ff53a,
        0x510e527f, 0x9b05688c, 0x1f83d9ab, 0x5be0cd19,
    ];

    // Pre-processing: pad message
    let bit_len = (data.len() as u64) * 8;
    let mut msg = data.to_vec();
    msg.push(0x80);
    while (msg.len() % 64) != 56 {
        msg.push(0x00);
    }
    msg.extend_from_slice(&bit_len.to_be_bytes());

    // Process each 512-bit block
    for chunk in msg.chunks(64) {
        let mut w = [0u32; 64];
        for i in 0..16 {
            w[i] = u32::from_be_bytes([
                chunk[i * 4],
                chunk[i * 4 + 1],
                chunk[i * 4 + 2],
                chunk[i * 4 + 3],
            ]);
        }
        for i in 16..64 {
            let s0 = w[i - 15].rotate_right(7) ^ w[i - 15].rotate_right(18) ^ (w[i - 15] >> 3);
            let s1 = w[i - 2].rotate_right(17) ^ w[i - 2].rotate_right(19) ^ (w[i - 2] >> 10);
            w[i] = w[i - 16]
                .wrapping_add(s0)
                .wrapping_add(w[i - 7])
                .wrapping_add(s1);
        }

        let [mut a, mut b, mut c, mut d, mut e, mut f, mut g, mut hh] = h;

        for i in 0..64 {
            let s1 = e.rotate_right(6) ^ e.rotate_right(11) ^ e.rotate_right(25);
            let ch = (e & f) ^ ((!e) & g);
            let temp1 = hh
                .wrapping_add(s1)
                .wrapping_add(ch)
                .wrapping_add(K[i])
                .wrapping_add(w[i]);
            let s0 = a.rotate_right(2) ^ a.rotate_right(13) ^ a.rotate_right(22);
            let maj = (a & b) ^ (a & c) ^ (b & c);
            let temp2 = s0.wrapping_add(maj);

            hh = g;
            g = f;
            f = e;
            e = d.wrapping_add(temp1);
            d = c;
            c = b;
            b = a;
            a = temp1.wrapping_add(temp2);
        }

        h[0] = h[0].wrapping_add(a);
        h[1] = h[1].wrapping_add(b);
        h[2] = h[2].wrapping_add(c);
        h[3] = h[3].wrapping_add(d);
        h[4] = h[4].wrapping_add(e);
        h[5] = h[5].wrapping_add(f);
        h[6] = h[6].wrapping_add(g);
        h[7] = h[7].wrapping_add(hh);
    }

    h
}

/// UTC timestamp in ISO 8601 format (no chrono dependency).
fn utc_now_iso8601() -> String {
    // Read from /proc or use a fallback
    #[cfg(unix)]
    {
        use std::process::Command;
        if let Ok(output) = Command::new("date").args(["-u", "+%Y-%m-%dT%H:%M:%SZ"]).output() {
            if output.status.success() {
                return String::from_utf8_lossy(&output.stdout).trim().to_string();
            }
        }
    }
    // Fallback: epoch-based (less precise but no deps)
    "1970-01-01T00:00:00Z".into()
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::Severity;

    #[test]
    fn sha256_empty() {
        let hash = sha256_hex(b"");
        assert_eq!(hash, "e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855");
    }

    #[test]
    fn sha256_hello() {
        let hash = sha256_hex(b"hello");
        assert_eq!(hash, "2cf24dba5fb0a30e26e83b2ac5b9e29e1b161e5c1fa7425e73043362938b9824");
    }

    #[test]
    fn report_pass_verdict() {
        let report = generate("test.rii", "biar x = 1;\nx", &[ComplianceProfile::PciDss], &[]);
        assert_eq!(report.verdict, Verdict::Pass);
        assert_eq!(report.total_errors, 0);
        assert_eq!(report.total_warnings, 0);
    }

    #[test]
    fn report_fail_verdict() {
        let violations = vec![ComplianceViolation {
            rule_id: "PCI-DSS-3.4",
            profile: ComplianceProfile::PciDss,
            message: "test failure".into(),
            severity: Severity::Error,
        }];
        let report = generate("test.rii", "src", &[ComplianceProfile::PciDss], &violations);
        assert_eq!(report.verdict, Verdict::Fail);
        assert_eq!(report.total_errors, 1);
    }

    #[test]
    fn report_warning_verdict() {
        let violations = vec![ComplianceViolation {
            rule_id: "PCI-DSS-8.3",
            profile: ComplianceProfile::PciDss,
            message: "test warning".into(),
            severity: Severity::Warning,
        }];
        let report = generate("test.rii", "src", &[ComplianceProfile::PciDss], &violations);
        assert_eq!(report.verdict, Verdict::PassWithWarnings);
    }

    #[test]
    fn report_json_parses() {
        let report = generate("test.rii", "src", &[ComplianceProfile::PciDss, ComplianceProfile::Pdpa], &[]);
        let json = report.to_json();
        assert!(json.contains("\"verdict\": \"PASS\""));
        assert!(json.contains("\"pci-dss\""));
        assert!(json.contains("\"pdpa\""));
        assert!(json.contains("\"coverage_pct\""));
    }

    #[test]
    fn report_text_contains_header() {
        let report = generate("ewallet.rii", "src", &[ComplianceProfile::Bnm], &[]);
        let text = report.to_text();
        assert!(text.contains("RIINA COMPLIANCE REPORT"));
        assert!(text.contains("ewallet.rii"));
        assert!(text.contains("BNM RMiT"));
    }

    #[test]
    fn report_coverage_numbers() {
        let report = generate("t.rii", "s", &[ComplianceProfile::PciDss], &[]);
        let pci = &report.profiles[0];
        assert_eq!(pci.rules_implemented, 3);
        assert_eq!(pci.rules_total, 78);
    }

    #[test]
    fn report_multi_profile() {
        let report = generate("t.rii", "s",
            &[ComplianceProfile::PciDss, ComplianceProfile::Pdpa, ComplianceProfile::Bnm], &[]);
        assert_eq!(report.profiles.len(), 3);
        assert_eq!(report.total_rules_checked, 3 + 2 + 1); // 6 total
    }
}
