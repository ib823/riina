// SPDX-License-Identifier: MPL-2.0
// Copyright (c) 2026 The RIINA Authors. See AUTHORS file.

//! RIINA Compliance Profile Validation
//!
//! Industry-specific compliance checks that run after core type-checking.
//! Core theorems (type safety, noninterference) always apply; compliance is opt-in.
//!
//! Spec: 04_SPECS/industries/

#![forbid(unsafe_code)]

mod rules;
pub mod report;
mod validator;

#[cfg(test)]
mod tests;

use std::fmt;
use std::str::FromStr;

use riina_types::Expr;

/// The 15 compliance profiles corresponding to 04_SPECS/industries/.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum ComplianceProfile {
    /// PCI-DSS (Payment Card Industry)
    PciDss,
    /// PDPA (Malaysia Personal Data Protection Act)
    Pdpa,
    /// BNM RMiT (Bank Negara Malaysia)
    Bnm,
    /// HIPAA (US Healthcare)
    Hipaa,
    /// CMMC (US Defense)
    Cmmc,
    /// SOX (US Financial Reporting)
    Sox,
    /// GDPR (EU Data Protection)
    Gdpr,
    /// DO-178C (Aviation Software)
    Do178c,
    /// IEC 62443 (Industrial Control Systems)
    Iec62443,
    /// NERC CIP (Energy Grid)
    NercCip,
    /// FDA 21 CFR Part 11 (Pharma)
    Fda21cfr,
    /// ISO 27001 (Information Security)
    Iso27001,
    /// NIST 800-53 (US Federal)
    Nist80053,
    /// MAS TRM (Singapore Financial)
    MasTrm,
    /// ITAR (US Arms Export)
    Itar,
}

impl ComplianceProfile {
    /// All profiles in order.
    pub const ALL: &'static [ComplianceProfile] = &[
        Self::PciDss, Self::Pdpa, Self::Bnm, Self::Hipaa, Self::Cmmc,
        Self::Sox, Self::Gdpr, Self::Do178c, Self::Iec62443, Self::NercCip,
        Self::Fda21cfr, Self::Iso27001, Self::Nist80053, Self::MasTrm, Self::Itar,
    ];

    /// CLI slug (lowercase, hyphenated).
    pub fn slug(self) -> &'static str {
        match self {
            Self::PciDss => "pci-dss",
            Self::Pdpa => "pdpa",
            Self::Bnm => "bnm",
            Self::Hipaa => "hipaa",
            Self::Cmmc => "cmmc",
            Self::Sox => "sox",
            Self::Gdpr => "gdpr",
            Self::Do178c => "do-178c",
            Self::Iec62443 => "iec-62443",
            Self::NercCip => "nerc-cip",
            Self::Fda21cfr => "fda-21cfr",
            Self::Iso27001 => "iso-27001",
            Self::Nist80053 => "nist-800-53",
            Self::MasTrm => "mas-trm",
            Self::Itar => "itar",
        }
    }

    /// Human-readable description.
    pub fn description(self) -> &'static str {
        match self {
            Self::PciDss => "PCI-DSS: Payment Card Industry Data Security Standard",
            Self::Pdpa => "PDPA: Malaysia Personal Data Protection Act 2010",
            Self::Bnm => "BNM RMiT: Bank Negara Malaysia Risk Management in Technology",
            Self::Hipaa => "HIPAA: US Health Insurance Portability and Accountability Act",
            Self::Cmmc => "CMMC: US Cybersecurity Maturity Model Certification",
            Self::Sox => "SOX: Sarbanes-Oxley Act",
            Self::Gdpr => "GDPR: EU General Data Protection Regulation",
            Self::Do178c => "DO-178C: Airborne Systems Software",
            Self::Iec62443 => "IEC 62443: Industrial Automation and Control Systems Security",
            Self::NercCip => "NERC CIP: North American Electric Reliability Critical Infrastructure",
            Self::Fda21cfr => "FDA 21 CFR Part 11: Electronic Records and Signatures",
            Self::Iso27001 => "ISO 27001: Information Security Management Systems",
            Self::Nist80053 => "NIST 800-53: Security and Privacy Controls for Federal Systems",
            Self::MasTrm => "MAS TRM: Monetary Authority of Singapore Technology Risk Management",
            Self::Itar => "ITAR: International Traffic in Arms Regulations",
        }
    }
}

impl FromStr for ComplianceProfile {
    type Err = String;

    fn from_str(s: &str) -> Result<Self, Self::Err> {
        match s {
            "pci-dss" => Ok(Self::PciDss),
            "pdpa" => Ok(Self::Pdpa),
            "bnm" => Ok(Self::Bnm),
            "hipaa" => Ok(Self::Hipaa),
            "cmmc" => Ok(Self::Cmmc),
            "sox" => Ok(Self::Sox),
            "gdpr" => Ok(Self::Gdpr),
            "do-178c" => Ok(Self::Do178c),
            "iec-62443" => Ok(Self::Iec62443),
            "nerc-cip" => Ok(Self::NercCip),
            "fda-21cfr" => Ok(Self::Fda21cfr),
            "iso-27001" => Ok(Self::Iso27001),
            "nist-800-53" => Ok(Self::Nist80053),
            "mas-trm" => Ok(Self::MasTrm),
            "itar" => Ok(Self::Itar),
            _ => Err(format!("Unknown compliance profile: '{s}'")),
        }
    }
}

impl fmt::Display for ComplianceProfile {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}", self.slug())
    }
}

/// Severity of a compliance violation.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Severity {
    Error,
    Warning,
}

impl fmt::Display for Severity {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Error => write!(f, "error"),
            Self::Warning => write!(f, "warning"),
        }
    }
}

/// A single compliance violation.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ComplianceViolation {
    pub rule_id: &'static str,
    pub profile: ComplianceProfile,
    pub message: String,
    pub severity: Severity,
}

impl fmt::Display for ComplianceViolation {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "[{}] {}: {} — {}",
            self.severity, self.profile.slug(), self.rule_id, self.message)
    }
}

/// Parse a comma-separated list of profile slugs.
pub fn parse_profiles(input: &str) -> Result<Vec<ComplianceProfile>, String> {
    input
        .split(',')
        .map(|s| s.trim().parse::<ComplianceProfile>())
        .collect()
}

/// Validate an expression against a set of compliance profiles.
/// Returns a list of violations (empty = compliant).
pub fn validate(expr: &Expr, profiles: &[ComplianceProfile]) -> Vec<ComplianceViolation> {
    let rules = rules::rules_for_profiles(profiles);
    validator::walk(expr, &rules)
}

/// Returns true if any violation is an Error (not just Warning).
pub fn has_errors(violations: &[ComplianceViolation]) -> bool {
    violations.iter().any(|v| v.severity == Severity::Error)
}
