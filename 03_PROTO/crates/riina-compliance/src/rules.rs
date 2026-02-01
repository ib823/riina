// SPDX-License-Identifier: MPL-2.0
// Copyright (c) 2026 The RIINA Authors. See AUTHORS file.

//! Compliance rule definitions per profile.
//! Spec: 04_SPECS/industries/

use riina_types::{Expr, Effect};

use crate::{ComplianceProfile, ComplianceViolation, Severity};

/// A compliance rule: a check function that inspects a single AST node
/// and returns violations if the node violates the rule.
#[allow(dead_code)]
pub struct ComplianceRule {
    pub id: &'static str,
    pub profile: ComplianceProfile,
    pub description: &'static str,
    pub check: fn(&Expr) -> Option<ComplianceViolation>,
}

/// Number of implemented rules for a profile.
pub fn rule_count(profile: ComplianceProfile) -> usize {
    match profile {
        ComplianceProfile::PciDss => 3,
        ComplianceProfile::Pdpa => 2,
        ComplianceProfile::Bnm => 1,
        _ => 0,
    }
}

/// Collect all rules for the given profiles.
pub fn rules_for_profiles(profiles: &[ComplianceProfile]) -> Vec<ComplianceRule> {
    let mut rules = Vec::new();
    for &p in profiles {
        match p {
            ComplianceProfile::PciDss => rules.extend(pci_dss_rules()),
            ComplianceProfile::Pdpa => rules.extend(pdpa_rules()),
            ComplianceProfile::Bnm => rules.extend(bnm_rules()),
            _ => {} // Stub profiles — no rules yet
        }
    }
    rules
}

// ---------------------------------------------------------------------------
// PCI-DSS rules (Spec: 04_SPECS/industries/IND_C_FINANCIAL.md)
// ---------------------------------------------------------------------------

fn pci_dss_rules() -> Vec<ComplianceRule> {
    vec![
        ComplianceRule {
            id: "PCI-DSS-3.4",
            profile: ComplianceProfile::PciDss,
            description: "Secret data must not be declassified without a Prove guard",
            check: |expr| {
                // Declassify(value, proof) — proof must be a Prove(_)
                if let Expr::Declassify(_, proof) = expr {
                    if !matches!(proof.as_ref(), Expr::Prove(_)) {
                        return Some(ComplianceViolation {
                            rule_id: "PCI-DSS-3.4",
                            profile: ComplianceProfile::PciDss,
                            message: "Declassification of secret data requires a Prove guard".into(),
                            severity: Severity::Error,
                        });
                    }
                }
                None
            },
        },
        ComplianceRule {
            id: "PCI-DSS-6.5",
            profile: ComplianceProfile::PciDss,
            description: "Card data variables must use Secret<_> type",
            check: |expr| {
                // Let binding with name containing "card" but type is not Secret
                if let Expr::Let(name, value, _) = expr {
                    let lower = name.to_lowercase();
                    if (lower.contains("card") || lower.contains("pan") || lower.contains("cvv"))
                        && !matches!(value.as_ref(), Expr::Classify(_))
                    {
                        return Some(ComplianceViolation {
                            rule_id: "PCI-DSS-6.5",
                            profile: ComplianceProfile::PciDss,
                            message: format!(
                                "Variable '{name}' appears to hold card data but is not wrapped in classify (Secret<_>)"
                            ),
                            severity: Severity::Error,
                        });
                    }
                }
                None
            },
        },
        ComplianceRule {
            id: "PCI-DSS-8.3",
            profile: ComplianceProfile::PciDss,
            description: "Authentication functions must require Crypto effect",
            check: |expr| {
                // LetRec binding with auth-related name but body has no Perform(Crypto, _)
                if let Expr::LetRec(name, _ty, body, _) = expr {
                    let lower = name.to_lowercase();
                    if (lower.contains("auth") || lower.contains("login") || lower.contains("verify_password"))
                        && !contains_effect(body, Effect::Crypto)
                    {
                        return Some(ComplianceViolation {
                            rule_id: "PCI-DSS-8.3",
                            profile: ComplianceProfile::PciDss,
                            message: format!(
                                "Authentication function '{name}' does not use Crypto effect"
                            ),
                            severity: Severity::Warning,
                        });
                    }
                }
                None
            },
        },
    ]
}

// ---------------------------------------------------------------------------
// PDPA rules (Spec: 04_SPECS/industries/IND_C_FINANCIAL.md / PDPA)
// ---------------------------------------------------------------------------

fn pdpa_rules() -> Vec<ComplianceRule> {
    vec![
        ComplianceRule {
            id: "PDPA-S7",
            profile: ComplianceProfile::Pdpa,
            description: "User input must be Tainted<_, UserInput>",
            check: |expr| {
                // A Let binding named "*_input" or "*_user*" that is not a Perform
                // (heuristic: raw string/int from user should be tainted)
                if let Expr::Let(name, value, _) = expr {
                    let lower = name.to_lowercase();
                    if (lower.contains("user_input") || lower.contains("personal_data"))
                        && !is_tainted_expr(value)
                    {
                        return Some(ComplianceViolation {
                            rule_id: "PDPA-S7",
                            profile: ComplianceProfile::Pdpa,
                            message: format!(
                                "Variable '{name}' holds user data but is not marked as Tainted<_, UserInput>"
                            ),
                            severity: Severity::Error,
                        });
                    }
                }
                None
            },
        },
        ComplianceRule {
            id: "PDPA-S24",
            profile: ComplianceProfile::Pdpa,
            description: "No Network effect on personal data without sanitization",
            check: |expr| {
                // Perform(Network, arg) where arg contains a var with "personal" or "user"
                if let Expr::Perform(Effect::Network | Effect::NetworkSecure, arg) = expr {
                    if contains_personal_data_var(arg) {
                        return Some(ComplianceViolation {
                            rule_id: "PDPA-S24",
                            profile: ComplianceProfile::Pdpa,
                            message: "Sending personal data over network without sanitization".into(),
                            severity: Severity::Error,
                        });
                    }
                }
                None
            },
        },
    ]
}

// ---------------------------------------------------------------------------
// BNM RMiT rules (Spec: 04_SPECS/industries/IND_C_FINANCIAL.md / BNM)
// ---------------------------------------------------------------------------

fn bnm_rules() -> Vec<ComplianceRule> {
    vec![
        ComplianceRule {
            id: "BNM-RMiT-10",
            profile: ComplianceProfile::Bnm,
            description: "Financial crypto must use ConstantTime<_>",
            check: |expr| {
                // Perform(Crypto, _) inside a function with "financial" or "payment" in name
                // We check at the Perform level: if crypto is performed, the enclosing
                // expression should be ConstantTime-wrapped.
                // Simplified heuristic: flag Perform(Crypto, _) on non-ConstantTime arg
                if let Expr::Perform(Effect::Crypto, arg) = expr {
                    if !is_constant_time_wrapped(arg) {
                        return Some(ComplianceViolation {
                            rule_id: "BNM-RMiT-10",
                            profile: ComplianceProfile::Bnm,
                            message: "Crypto operation argument should use ConstantTime<_> type for financial data".into(),
                            severity: Severity::Warning,
                        });
                    }
                }
                None
            },
        },
    ]
}

// ---------------------------------------------------------------------------
// Helpers
// ---------------------------------------------------------------------------

/// Check if an expression tree contains a Perform with the given effect.
fn contains_effect(expr: &Expr, target: Effect) -> bool {
    match expr {
        Expr::Perform(eff, _) if *eff == target => true,
        Expr::Lam(_, _, body) => contains_effect(body, target),
        Expr::App(f, a) => contains_effect(f, target) || contains_effect(a, target),
        Expr::Let(_, v, b) | Expr::LetRec(_, _, v, b) => {
            contains_effect(v, target) || contains_effect(b, target)
        }
        Expr::If(c, t, e) => {
            contains_effect(c, target) || contains_effect(t, target) || contains_effect(e, target)
        }
        Expr::Perform(_, inner) => contains_effect(inner, target),
        Expr::BinOp(_, l, r) | Expr::Pair(l, r) | Expr::Assign(l, r) => {
            contains_effect(l, target) || contains_effect(r, target)
        }
        _ => false,
    }
}

/// Check if an expression is "tainted" (wrapped in a taint-producing construct).
fn is_tainted_expr(expr: &Expr) -> bool {
    // In RIINA, tainted data comes from Perform with specific effects
    // or from explicitly typed tainted bindings. For the compliance check,
    // we look for Perform(Read/Network, _) or Classify wrapping.
    matches!(expr, Expr::Perform(_, _) | Expr::Classify(_))
}

/// Check if an expression references a variable with personal-data naming.
fn contains_personal_data_var(expr: &Expr) -> bool {
    match expr {
        Expr::Var(name) => {
            let lower = name.to_lowercase();
            lower.contains("personal") || lower.contains("user_data")
                || lower.contains("nama") || lower.contains("ic_number")
        }
        Expr::App(f, a) => contains_personal_data_var(f) || contains_personal_data_var(a),
        Expr::Pair(l, r) => contains_personal_data_var(l) || contains_personal_data_var(r),
        Expr::Fst(e) | Expr::Snd(e) | Expr::Classify(e) => contains_personal_data_var(e),
        _ => false,
    }
}

/// Check if a crypto argument is wrapped in ConstantTime (heuristic).
fn is_constant_time_wrapped(_expr: &Expr) -> bool {
    // In practice, we'd check if the expression's type is ConstantTime<_>.
    // Since the compliance validator runs on the untyped AST, we use a
    // naming heuristic: variables named "*_ct" or "*_constant_time".
    // For now, always return false to flag for manual review.
    false
}
