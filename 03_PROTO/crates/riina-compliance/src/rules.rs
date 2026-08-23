// Copyright (c) 2026 The RIINA Authors. All rights reserved.

//! Compliance rule definitions per profile.
//! Spec: 04_SPECS/industries/
//!
//! 562 rules across 16 compliance profiles, each with AST-level detection.

use riina_types::{Effect, Expr};

use crate::{ComplianceProfile, ComplianceViolation, Severity};

/// A compliance rule: a check function that inspects a single AST node
/// and returns violations if the node violates the rule.
/// Type alias for compliance check function.
type CheckFn = Box<dyn Fn(&Expr) -> Option<ComplianceViolation> + Send + Sync>;

#[allow(dead_code)]
pub struct ComplianceRule {
    pub id: &'static str,
    pub profile: ComplianceProfile,
    pub description: &'static str,
    pub check: CheckFn,
}

/// Number of implemented rules for a profile.
pub fn rule_count(profile: ComplianceProfile) -> usize {
    match profile {
        ComplianceProfile::PciDss => 56,
        ComplianceProfile::Pdpa => 20,
        ComplianceProfile::Bnm => 20,
        ComplianceProfile::Hipaa => 33,
        ComplianceProfile::Cmmc => 63,
        ComplianceProfile::Sox => 18,
        ComplianceProfile::Gdpr => 34,
        ComplianceProfile::Do178c => 48,
        ComplianceProfile::Iec62443 => 32,
        ComplianceProfile::NercCip => 20,
        ComplianceProfile::Fda21cfr => 18,
        ComplianceProfile::Iso27001 => 59,
        ComplianceProfile::Nist80053 => 81,
        ComplianceProfile::MasTrm => 20,
        ComplianceProfile::Itar => 12,
        ComplianceProfile::EsgSdg => 30,
        ComplianceProfile::Cra => 15,
        ComplianceProfile::Dora => 14,
        ComplianceProfile::Nis2 => 13,
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
            ComplianceProfile::Hipaa => rules.extend(hipaa_rules()),
            ComplianceProfile::Cmmc => rules.extend(cmmc_rules()),
            ComplianceProfile::Sox => rules.extend(sox_rules()),
            ComplianceProfile::Gdpr => rules.extend(gdpr_rules()),
            ComplianceProfile::Do178c => rules.extend(do178c_rules()),
            ComplianceProfile::Iec62443 => rules.extend(iec62443_rules()),
            ComplianceProfile::NercCip => rules.extend(nerc_cip_rules()),
            ComplianceProfile::Fda21cfr => rules.extend(fda_rules()),
            ComplianceProfile::Iso27001 => rules.extend(iso27001_rules()),
            ComplianceProfile::Nist80053 => rules.extend(nist_rules()),
            ComplianceProfile::MasTrm => rules.extend(mas_trm_rules()),
            ComplianceProfile::Itar => rules.extend(itar_rules()),
            ComplianceProfile::EsgSdg => rules.extend(esg_sdg_rules()),
            ComplianceProfile::Cra => rules.extend(cra_rules()),
            ComplianceProfile::Dora => rules.extend(dora_rules()),
            ComplianceProfile::Nis2 => rules.extend(nis2_rules()),
        }
    }
    rules
}

// ===========================================================================
// Helper functions
// ===========================================================================

/// Check if a name (lowercased) contains any of the given keywords.
fn name_matches(name: &str, keywords: &[String]) -> bool {
    let lower = name.to_lowercase();
    keywords.iter().any(|k| lower.contains(k.as_str()))
}

/// Apply `f` to each DIRECT sub-expression of `expr`, short-circuiting on the
/// first `true`.
///
/// This is the single structural walk behind every `contains_*` / `has_*`
/// predicate below, and it is deliberately **EXHAUSTIVE — no wildcard arm**.
/// That is the whole point: every predicate in this file used to carry its own
/// hand-written match ending in `_ => false`, so a variant nobody remembered to
/// list did not fail the build, it silently truncated the walk and the rule
/// stopped seeing the code it was written to police. `Expr::Return` was exactly
/// that — `pulang e` is the ordinary way to write a RIINA function body, and
/// none of the five walks descended through it, so an effectful function
/// scanned as effect-free (see the `pulang_wrapped_body_scans_like_a_bare_body`
/// and `every_expr_variant_is_walked_*` regressions).
///
/// With the enumeration centralised here, adding an `Expr` variant fails to
/// compile in ONE place instead of silently degrading every predicate. Do not
/// add a `_ =>` arm to this match.
fn any_child(expr: &Expr, f: &mut dyn FnMut(&Expr) -> bool) -> bool {
    match expr {
        // Leaves — no sub-expressions.
        Expr::Unit
        | Expr::Bool(_)
        | Expr::Int(_)
        | Expr::IntN { .. }
        | Expr::String(_)
        | Expr::Var(_)
        | Expr::SlotGet(_)
        | Expr::Break
        | Expr::Continue
        | Expr::Loc(_)
        | Expr::ChoreographyBlock { .. }
        | Expr::UIColor(_, _, _)
        | Expr::UIStyleDecl { .. } => false,

        // One sub-expression.
        Expr::Lam(_, _, e)
        | Expr::Fst(e)
        | Expr::Snd(e)
        | Expr::Inl(e, _)
        | Expr::Inr(e, _)
        | Expr::Return(e)
        | Expr::Perform(_, e)
        | Expr::Ref(e, _)
        | Expr::Deref(e)
        | Expr::Classify(e)
        | Expr::Prove(e)
        | Expr::Require(_, e)
        | Expr::Grant(_, e)
        | Expr::FieldAccess(e, _)
        | Expr::ActorRecv(e)
        | Expr::ContentHash(e)
        | Expr::ContractDeploy(e)
        | Expr::SlotSet(_, e)
        | Expr::ZakatCalculate(e) => f(e),

        // Two sub-expressions.
        Expr::App(a, b)
        | Expr::Pair(a, b)
        | Expr::Let(_, _, a, b)
        | Expr::LetMut(_, a, b)
        | Expr::While(a, b)
        | Expr::LetRec(_, _, a, b)
        | Expr::Handle(a, _, b)
        | Expr::Assign(a, b)
        | Expr::Declassify(a, b)
        | Expr::BinOp(_, a, b)
        | Expr::Spawn(a, b)
        | Expr::ActorSend(a, b)
        | Expr::CRDTMerge(a, b)
        | Expr::ContentVerify(a, b)
        | Expr::UIText(a, b)
        | Expr::UIButton(a, b)
        | Expr::UIContrastCheck(a, b) => f(a) || f(b),

        // Three sub-expressions.
        Expr::If(a, b, c) | Expr::Case(a, _, b, _, c) => f(a) || f(b) || f(c),
        Expr::TokenTransfer { from, to, amount } => f(from) || f(to) || f(amount),
        Expr::ActorDecl {
            init_state,
            handler,
            ..
        } => f(init_state) || f(handler),

        // REQ-44: top-level functions form a mutually-recursive GROUP. Every
        // group member is a function body — miss this arm and compliance stops
        // inspecting every top-level function in the program.
        Expr::LetRecGroup(bindings, cont) => {
            bindings.iter().any(|(_, _, e)| f(e)) || f(cont)
        }

        // Sequences of sub-expressions.
        Expr::ListLit(items)
        | Expr::UIDisplay(items)
        | Expr::UIRow(items)
        | Expr::UIColumn(items) => items.iter().any(f),
        Expr::RecordLit(_, fields) => fields.iter().any(|(_, e)| f(e)),
        Expr::FFICall { args, .. } => args.iter().any(f),
    }
}

/// Check if an expression tree contains a Perform with the given effect.
fn contains_effect(expr: &Expr, target: Effect) -> bool {
    match expr {
        Expr::Perform(eff, _) if *eff == target => true,
        _ => any_child(expr, &mut |c| contains_effect(c, target)),
    }
}

/// Check if an expression contains a security operation (Classify, Declassify, Grant).
fn contains_security_op(expr: &Expr) -> bool {
    match expr {
        Expr::Classify(_) | Expr::Declassify(_, _) | Expr::Grant(_, _) => true,
        _ => any_child(expr, &mut contains_security_op),
    }
}

/// Check if an expression tree contains an If or Case (base case for recursion).
fn has_if_or_case(expr: &Expr) -> bool {
    match expr {
        Expr::If(_, _, _) | Expr::Case(_, _, _, _, _) => true,
        _ => any_child(expr, &mut has_if_or_case),
    }
}

/// Check if a Var in the expression matches any of the given keywords.
fn contains_var_matching(expr: &Expr, keywords: &[String]) -> bool {
    match expr {
        Expr::Var(name) => name_matches(name, keywords),
        _ => any_child(expr, &mut |c| contains_var_matching(c, keywords)),
    }
}

/// Check if an expression is "tainted" (wrapped in a taint-producing construct).
fn is_tainted_expr(expr: &Expr) -> bool {
    matches!(expr, Expr::Perform(_, _) | Expr::Classify(_))
}

/// Check if a crypto argument is wrapped in ConstantTime (heuristic).
fn is_constant_time_wrapped(_expr: &Expr) -> bool {
    false
}

fn to_owned_keywords(keywords: &[&str]) -> Vec<String> {
    keywords.iter().map(|k| (*k).to_string()).collect()
}

// ===========================================================================
// Template rule builders
// ===========================================================================

/// Template A: Let binding with sensitive name must use Classify.
fn sensitive_let_rule(
    id: &'static str,
    profile: ComplianceProfile,
    description: &'static str,
    keywords: &[&str],
    severity: Severity,
) -> ComplianceRule {
    let kw = to_owned_keywords(keywords);
    ComplianceRule {
        id,
        profile,
        description,
        check: Box::new(move |expr| {
            if let Expr::Let(name, _, value, _) = expr {
                if name_matches(name, &kw) && !matches!(value.as_ref(), Expr::Classify(_)) {
                    return Some(ComplianceViolation {
                        rule_id: id,
                        profile,
                        message: format!("Variable '{}' must be classified as Secret", name),
                        severity,
                    });
                }
            }
            None
        }),
    }
}

/// Template B: Let binding with credential-like name must not be a string literal.
fn hardcoded_credential_rule(
    id: &'static str,
    profile: ComplianceProfile,
    description: &'static str,
    keywords: &[&str],
    severity: Severity,
) -> ComplianceRule {
    let kw = to_owned_keywords(keywords);
    ComplianceRule {
        id,
        profile,
        description,
        check: Box::new(move |expr| {
            if let Expr::Let(name, _, value, _) = expr {
                if name_matches(name, &kw) && matches!(value.as_ref(), Expr::String(_)) {
                    return Some(ComplianceViolation {
                        rule_id: id,
                        profile,
                        message: format!("Variable '{}' contains a hardcoded credential", name),
                        severity,
                    });
                }
            }
            None
        }),
    }
}

/// Template C: Perform(Network, _) should use NetworkSecure instead.
fn insecure_network_rule(
    id: &'static str,
    profile: ComplianceProfile,
    description: &'static str,
    severity: Severity,
) -> ComplianceRule {
    ComplianceRule {
        id,
        profile,
        description,
        check: Box::new(move |expr| {
            if let Expr::Perform(Effect::Network, _) = expr {
                return Some(ComplianceViolation {
                    rule_id: id,
                    profile,
                    message: "Network communication must use secure channel (NetworkSecure effect)"
                        .into(),
                    severity,
                });
            }
            None
        }),
    }
}

/// Template D: String literal containing weak crypto algorithm names.
fn weak_crypto_rule(
    id: &'static str,
    profile: ComplianceProfile,
    description: &'static str,
    severity: Severity,
) -> ComplianceRule {
    ComplianceRule {
        id,
        profile,
        description,
        check: Box::new(move |expr| {
            if let Expr::String(s) = expr {
                let lower = s.to_lowercase();
                if lower.contains("md5")
                    || lower.contains("sha1")
                    || lower.contains("des")
                    || lower.contains("rc4")
                    || lower.contains("rot13")
                {
                    return Some(ComplianceViolation {
                        rule_id: id,
                        profile,
                        message: format!("Weak cryptographic algorithm detected: '{}'", s),
                        severity,
                    });
                }
            }
            None
        }),
    }
}

/// Template E: String literal containing insecure HTTP URL.
fn insecure_url_rule(
    id: &'static str,
    profile: ComplianceProfile,
    description: &'static str,
    severity: Severity,
) -> ComplianceRule {
    ComplianceRule {
        id,
        profile,
        description,
        check: Box::new(move |expr| {
            if let Expr::String(s) = expr {
                if s.contains("http://") {
                    return Some(ComplianceViolation {
                        rule_id: id,
                        profile,
                        message: format!("Insecure HTTP URL detected: '{}'. Use HTTPS instead", s),
                        severity,
                    });
                }
            }
            None
        }),
    }
}

/// Template F: LetRec with auth-related name must use Crypto effect.
fn auth_crypto_rule(
    id: &'static str,
    profile: ComplianceProfile,
    description: &'static str,
    keywords: &[&str],
    severity: Severity,
) -> ComplianceRule {
    let kw = to_owned_keywords(keywords);
    ComplianceRule {
        id,
        profile,
        description,
        check: Box::new(move |expr| {
            if let Expr::LetRec(name, _ty, body, _) = expr {
                if name_matches(name, &kw) && !contains_effect(body, Effect::Crypto) {
                    return Some(ComplianceViolation {
                        rule_id: id,
                        profile,
                        message: format!(
                            "Authentication function '{}' must use Crypto effect",
                            name
                        ),
                        severity,
                    });
                }
            }
            None
        }),
    }
}

/// Template G: Declassify without Prove guard.
fn declassify_prove_rule(
    id: &'static str,
    profile: ComplianceProfile,
    description: &'static str,
    severity: Severity,
) -> ComplianceRule {
    ComplianceRule {
        id,
        profile,
        description,
        check: Box::new(move |expr| {
            if let Expr::Declassify(_, proof) = expr {
                if !matches!(proof.as_ref(), Expr::Prove(_)) {
                    return Some(ComplianceViolation {
                        rule_id: id,
                        profile,
                        message: "Declassification requires a Prove guard for audit compliance"
                            .into(),
                        severity,
                    });
                }
            }
            None
        }),
    }
}

/// Template H: Let binding with security op value but body lacks Write (audit trail).
fn audit_trail_rule(
    id: &'static str,
    profile: ComplianceProfile,
    description: &'static str,
    severity: Severity,
) -> ComplianceRule {
    ComplianceRule {
        id,
        profile,
        description,
        check: Box::new(move |expr| {
            if let Expr::Let(_, _, value, body) = expr {
                if contains_security_op(value) && !contains_effect(body, Effect::Write) {
                    return Some(ComplianceViolation {
                        rule_id: id,
                        profile,
                        message: "Security operation without audit trail (missing Write effect in continuation)".into(),
                        severity,
                    });
                }
            }
            None
        }),
    }
}

/// Template I: FFICall detected — needs security review.
fn ffi_review_rule(
    id: &'static str,
    profile: ComplianceProfile,
    description: &'static str,
    severity: Severity,
) -> ComplianceRule {
    ComplianceRule {
        id,
        profile,
        description,
        check: Box::new(move |expr| {
            if let Expr::FFICall { name, .. } = expr {
                return Some(ComplianceViolation {
                    rule_id: id,
                    profile,
                    message: format!("FFI call to '{}' requires security review", name),
                    severity,
                });
            }
            None
        }),
    }
}

/// Template J: Handle with Unit body (error swallowed).
fn trivial_handle_rule(
    id: &'static str,
    profile: ComplianceProfile,
    description: &'static str,
    severity: Severity,
) -> ComplianceRule {
    ComplianceRule {
        id,
        profile,
        description,
        check: Box::new(move |expr| {
            if let Expr::Handle(_, _, body) = expr {
                if matches!(body.as_ref(), Expr::Unit) {
                    return Some(ComplianceViolation {
                        rule_id: id,
                        profile,
                        message: "Error handler discards error (body is Unit)".into(),
                        severity,
                    });
                }
            }
            None
        }),
    }
}

/// Template K: Grant with overly broad effect (System, Process).
fn broad_grant_rule(
    id: &'static str,
    profile: ComplianceProfile,
    description: &'static str,
    severity: Severity,
) -> ComplianceRule {
    ComplianceRule {
        id,
        profile,
        description,
        check: Box::new(move |expr| {
            if let Expr::Grant(effect, _) = expr {
                if matches!(effect, Effect::System | Effect::Process) {
                    return Some(ComplianceViolation {
                        rule_id: id,
                        profile,
                        message: format!("Overly broad capability grant: {:?} effect", effect),
                        severity,
                    });
                }
            }
            None
        }),
    }
}

/// Template L: Perform(Network/NetworkSecure, arg) where arg references sensitive var.
fn sensitive_network_send_rule(
    id: &'static str,
    profile: ComplianceProfile,
    description: &'static str,
    keywords: &[&str],
    severity: Severity,
) -> ComplianceRule {
    let kw = to_owned_keywords(keywords);
    ComplianceRule {
        id,
        profile,
        description,
        check: Box::new(move |expr| {
            if let Expr::Perform(Effect::Network | Effect::NetworkSecure, arg) = expr {
                if contains_var_matching(arg, &kw) {
                    return Some(ComplianceViolation {
                        rule_id: id,
                        profile,
                        message: "Sending sensitive data over network without sanitization".into(),
                        severity,
                    });
                }
            }
            None
        }),
    }
}

/// Template M: LetRec without If/Case in body (no base case → potential infinite recursion).
fn unbounded_recursion_rule(
    id: &'static str,
    profile: ComplianceProfile,
    description: &'static str,
    severity: Severity,
) -> ComplianceRule {
    ComplianceRule {
        id,
        profile,
        description,
        check: Box::new(move |expr| {
            if let Expr::LetRec(name, _, body, _) = expr {
                if !has_if_or_case(body) {
                    return Some(ComplianceViolation {
                        rule_id: id,
                        profile,
                        message: format!(
                            "Recursive function '{}' has no visible base case (missing If/Case)",
                            name
                        ),
                        severity,
                    });
                }
            }
            None
        }),
    }
}

/// Template N: Let binding with input-like name must be tainted (Perform/Classify).
fn tainted_input_rule(
    id: &'static str,
    profile: ComplianceProfile,
    description: &'static str,
    keywords: &[&str],
    severity: Severity,
) -> ComplianceRule {
    let kw = to_owned_keywords(keywords);
    ComplianceRule {
        id,
        profile,
        description,
        check: Box::new(move |expr| {
            if let Expr::Let(name, _, value, _) = expr {
                if name_matches(name, &kw) && !is_tainted_expr(value) {
                    return Some(ComplianceViolation {
                        rule_id: id,
                        profile,
                        message: format!(
                            "Variable '{}' holds user input but is not taint-tracked",
                            name
                        ),
                        severity,
                    });
                }
            }
            None
        }),
    }
}

/// Template O: String literal containing a hardcoded IP address pattern.
fn hardcoded_ip_rule(
    id: &'static str,
    profile: ComplianceProfile,
    description: &'static str,
    severity: Severity,
) -> ComplianceRule {
    ComplianceRule {
        id,
        profile,
        description,
        check: Box::new(move |expr| {
            if let Expr::String(s) = expr {
                // Simple heuristic: contains digit.digit.digit.digit pattern
                let bytes = s.as_bytes();
                let mut i = 0;
                while i < bytes.len() {
                    if bytes[i].is_ascii_digit() {
                        // Try to match N.N.N.N
                        let mut parts = 0;
                        let mut j = i;
                        while j < bytes.len() && parts < 4 {
                            if !bytes[j].is_ascii_digit() {
                                break;
                            }
                            while j < bytes.len() && bytes[j].is_ascii_digit() {
                                j += 1;
                            }
                            parts += 1;
                            if parts < 4 {
                                if j < bytes.len() && bytes[j] == b'.' {
                                    j += 1;
                                } else {
                                    break;
                                }
                            }
                        }
                        if parts == 4 {
                            return Some(ComplianceViolation {
                                rule_id: id,
                                profile,
                                message: format!(
                                    "Hardcoded IP address detected in string: '{}'",
                                    s
                                ),
                                severity,
                            });
                        }
                    }
                    i += 1;
                }
            }
            None
        }),
    }
}

/// Template P: Integer literal matching a well-known network port.
fn hardcoded_port_rule(
    id: &'static str,
    profile: ComplianceProfile,
    description: &'static str,
    severity: Severity,
) -> ComplianceRule {
    ComplianceRule {
        id,
        profile,
        description,
        check: Box::new(move |expr| {
            if let Expr::Int(n) = expr {
                let well_known: &[u64] = &[
                    20, 21, 22, 23, 25, 53, 80, 110, 143, 443, 445, 993, 995, 1433, 1521, 3306,
                    3389, 5432, 5900, 6379, 8080, 8443, 9090, 27017,
                ];
                if well_known.contains(n) {
                    return Some(ComplianceViolation {
                        rule_id: id,
                        profile,
                        message: format!("Hardcoded network port detected: {}", n),
                        severity,
                    });
                }
            }
            None
        }),
    }
}

/// Template Q: String literal containing debug/diagnostic patterns.
fn debug_code_rule(
    id: &'static str,
    profile: ComplianceProfile,
    description: &'static str,
    severity: Severity,
) -> ComplianceRule {
    ComplianceRule {
        id,
        profile,
        description,
        check: Box::new(move |expr| {
            if let Expr::String(s) = expr {
                let lower = s.to_lowercase();
                if lower.contains("debug")
                    || lower.contains("println")
                    || lower.contains("console.log")
                    || lower.contains("print_debug")
                    || lower.contains("todo!")
                    || lower.contains("fixme")
                    || lower.contains("hack:")
                {
                    return Some(ComplianceViolation {
                        rule_id: id,
                        profile,
                        message: format!("Debug/diagnostic code detected: '{}'", s),
                        severity,
                    });
                }
            }
            None
        }),
    }
}

/// Template R: Let binding with security-flag name bound to Bool(false).
fn insecure_default_rule(
    id: &'static str,
    profile: ComplianceProfile,
    description: &'static str,
    keywords: &[&str],
    severity: Severity,
) -> ComplianceRule {
    let kw = to_owned_keywords(keywords);
    ComplianceRule {
        id,
        profile,
        description,
        check: Box::new(move |expr| {
            if let Expr::Let(name, _, value, _) = expr {
                if name_matches(name, &kw) && matches!(value.as_ref(), Expr::Bool(false)) {
                    return Some(ComplianceViolation {
                        rule_id: id,
                        profile,
                        message: format!(
                            "Security setting '{}' defaults to false (insecure default)",
                            name
                        ),
                        severity,
                    });
                }
            }
            None
        }),
    }
}

/// Template S: Let binding with temporal name but body lacks Time effect.
fn temporal_no_expiry_rule(
    id: &'static str,
    profile: ComplianceProfile,
    description: &'static str,
    keywords: &[&str],
    severity: Severity,
) -> ComplianceRule {
    let kw = to_owned_keywords(keywords);
    ComplianceRule {
        id,
        profile,
        description,
        check: Box::new(move |expr| {
            if let Expr::Let(name, _, _value, body) = expr {
                if name_matches(name, &kw) && !contains_effect(body, Effect::Time) {
                    return Some(ComplianceViolation {
                        rule_id: id,
                        profile,
                        message: format!("Variable '{}' holds temporal data but body lacks Time effect for expiry handling", name),
                        severity,
                    });
                }
            }
            None
        }),
    }
}

/// Template T: Grant with non-standard effects (FileSystem, Random, Time) beyond System/Process.
fn excessive_grant_rule(
    id: &'static str,
    profile: ComplianceProfile,
    description: &'static str,
    severity: Severity,
) -> ComplianceRule {
    ComplianceRule {
        id,
        profile,
        description,
        check: Box::new(move |expr| {
            if let Expr::Grant(effect, _) = expr {
                if matches!(effect, Effect::FileSystem | Effect::Random | Effect::Time) {
                    return Some(ComplianceViolation {
                        rule_id: id,
                        profile,
                        message: format!(
                            "Excessive capability grant: {:?} effect should be minimized",
                            effect
                        ),
                        severity,
                    });
                }
            }
            None
        }),
    }
}

/// Template U: Classify operation in Let value but body lacks Write (audit) effect.
fn classify_without_audit_rule(
    id: &'static str,
    profile: ComplianceProfile,
    description: &'static str,
    severity: Severity,
) -> ComplianceRule {
    ComplianceRule {
        id,
        profile,
        description,
        check: Box::new(move |expr| {
            if let Expr::Let(_, _, value, body) = expr {
                if matches!(value.as_ref(), Expr::Classify(_))
                    && !contains_effect(body, Effect::Write)
                {
                    return Some(ComplianceViolation {
                        rule_id: id,
                        profile,
                        message: "Classification operation without audit trail (missing Write effect in continuation)".into(),
                        severity,
                    });
                }
            }
            None
        }),
    }
}

/// Template V: FFICall with sensitive-looking function name.
fn sensitive_ffi_rule(
    id: &'static str,
    profile: ComplianceProfile,
    description: &'static str,
    keywords: &[&str],
    severity: Severity,
) -> ComplianceRule {
    let kw = to_owned_keywords(keywords);
    ComplianceRule {
        id,
        profile,
        description,
        check: Box::new(move |expr| {
            if let Expr::FFICall { name, .. } = expr {
                if name_matches(name, &kw) {
                    return Some(ComplianceViolation {
                        rule_id: id,
                        profile,
                        message: format!(
                            "FFI call to sensitive function '{}' requires enhanced security review",
                            name
                        ),
                        severity,
                    });
                }
            }
            None
        }),
    }
}

// ===========================================================================
// PCI-DSS rules (25)
// ===========================================================================

fn pci_dss_rules() -> Vec<ComplianceRule> {
    vec![
        // --- Existing 3 rules (preserved) ---
        ComplianceRule {
            id: "PCI-DSS-3.4",
            profile: ComplianceProfile::PciDss,
            description: "Secret data must not be declassified without a Prove guard",
            check: Box::new(|expr| {
                if let Expr::Declassify(_, proof) = expr {
                    if !matches!(proof.as_ref(), Expr::Prove(_)) {
                        return Some(ComplianceViolation {
                            rule_id: "PCI-DSS-3.4",
                            profile: ComplianceProfile::PciDss,
                            message: "Declassification of secret data requires a Prove guard"
                                .into(),
                            severity: Severity::Error,
                        });
                    }
                }
                None
            }),
        },
        ComplianceRule {
            id: "PCI-DSS-6.5",
            profile: ComplianceProfile::PciDss,
            description: "Card data variables must use Secret<_> type",
            check: Box::new(|expr| {
                if let Expr::Let(name, _, value, _) = expr {
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
            }),
        },
        ComplianceRule {
            id: "PCI-DSS-8.3",
            profile: ComplianceProfile::PciDss,
            description: "Authentication functions must require Crypto effect",
            check: Box::new(|expr| {
                if let Expr::LetRec(name, _ty, body, _) = expr {
                    let lower = name.to_lowercase();
                    if (lower.contains("auth")
                        || lower.contains("login")
                        || lower.contains("verify_password"))
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
            }),
        },
        // --- New 12 rules ---
        sensitive_let_rule(
            "PCI-DSS-3.5.1",
            ComplianceProfile::PciDss,
            "Encryption keys must be Secret-typed",
            &[
                "encryption_key",
                "aes_key",
                "private_key",
                "secret_key",
                "crypto_key",
            ],
            Severity::Error,
        ),
        insecure_network_rule(
            "PCI-DSS-4.1",
            ComplianceProfile::PciDss,
            "Transmission encryption required",
            Severity::Error,
        ),
        insecure_url_rule(
            "PCI-DSS-6.5.2",
            ComplianceProfile::PciDss,
            "Insecure HTTP communication detected",
            Severity::Error,
        ),
        weak_crypto_rule(
            "PCI-DSS-6.5.3",
            ComplianceProfile::PciDss,
            "Weak cryptographic algorithm detected",
            Severity::Error,
        ),
        trivial_handle_rule(
            "PCI-DSS-6.5.4",
            ComplianceProfile::PciDss,
            "Error handling must not swallow errors",
            Severity::Warning,
        ),
        hardcoded_credential_rule(
            "PCI-DSS-6.5.5",
            ComplianceProfile::PciDss,
            "Hardcoded credentials detected",
            &[
                "password",
                "passwd",
                "api_key",
                "secret_token",
                "access_key",
            ],
            Severity::Error,
        ),
        sensitive_let_rule(
            "PCI-DSS-6.5.6",
            ComplianceProfile::PciDss,
            "Authentication data must be Secret-typed",
            &["password", "credential", "auth_token", "session_key"],
            Severity::Error,
        ),
        ffi_review_rule(
            "PCI-DSS-6.2.1",
            ComplianceProfile::PciDss,
            "FFI calls require security review",
            Severity::Warning,
        ),
        sensitive_let_rule(
            "PCI-DSS-8.3.1",
            ComplianceProfile::PciDss,
            "MFA/authentication data must be Secret-typed",
            &["pin_code", "otp", "mfa_code", "two_factor"],
            Severity::Error,
        ),
        audit_trail_rule(
            "PCI-DSS-10.2",
            ComplianceProfile::PciDss,
            "Security operations must produce audit events",
            Severity::Warning,
        ),
        broad_grant_rule(
            "PCI-DSS-11.3",
            ComplianceProfile::PciDss,
            "Overly broad capability grants require review",
            Severity::Warning,
        ),
        unbounded_recursion_rule(
            "PCI-DSS-6.3.1",
            ComplianceProfile::PciDss,
            "Recursive functions must have a visible base case",
            Severity::Warning,
        ),
        // --- 10 new rules (templates O-V + L, N) ---
        hardcoded_ip_rule(
            "PCI-DSS-1.3.1",
            ComplianceProfile::PciDss,
            "No hardcoded IP addresses in payment systems",
            Severity::Warning,
        ),
        hardcoded_port_rule(
            "PCI-DSS-1.3.2",
            ComplianceProfile::PciDss,
            "No hardcoded network ports in payment systems",
            Severity::Warning,
        ),
        insecure_default_rule(
            "PCI-DSS-2.2.1",
            ComplianceProfile::PciDss,
            "Security settings must not default to false",
            &[
                "encryption_enabled",
                "tls_required",
                "auth_required",
                "secure_mode",
                "verify_ssl",
            ],
            Severity::Error,
        ),
        temporal_no_expiry_rule(
            "PCI-DSS-3.6.1",
            ComplianceProfile::PciDss,
            "Cryptographic keys must have expiry handling",
            &[
                "key_created",
                "cert_date",
                "token_issued",
                "key_timestamp",
                "session_start",
            ],
            Severity::Warning,
        ),
        debug_code_rule(
            "PCI-DSS-4.2.1",
            ComplianceProfile::PciDss,
            "No debug code in production payment systems",
            Severity::Warning,
        ),
        sensitive_network_send_rule(
            "PCI-DSS-6.5.7",
            ComplianceProfile::PciDss,
            "Card data must not be sent over network without sanitization",
            &["card", "pan", "cvv", "card_number", "expiry"],
            Severity::Error,
        ),
        tainted_input_rule(
            "PCI-DSS-6.5.8",
            ComplianceProfile::PciDss,
            "User input in payment flow must be taint-tracked",
            &["user_input", "form_data", "payment_input", "card_input"],
            Severity::Error,
        ),
        excessive_grant_rule(
            "PCI-DSS-7.1.1",
            ComplianceProfile::PciDss,
            "Excessive capability grants in payment context",
            Severity::Warning,
        ),
        sensitive_ffi_rule(
            "PCI-DSS-8.5.1",
            ComplianceProfile::PciDss,
            "FFI calls to auth-related functions need enhanced review",
            &["auth", "login", "password", "credential", "token"],
            Severity::Warning,
        ),
        classify_without_audit_rule(
            "PCI-DSS-10.3.1",
            ComplianceProfile::PciDss,
            "Classification operations must have audit trail",
            Severity::Warning,
        ),
        // --- 30 new PCI-DSS rules ---
        // Requirement 1: Network Security
        sensitive_let_rule(
            "PCI-DSS-1.1.1",
            ComplianceProfile::PciDss,
            "Firewall configuration data must be classified",
            &["firewall_config", "network_rule", "acl_data", "filter_rule"],
            Severity::Error,
        ),
        insecure_default_rule(
            "PCI-DSS-1.2.1",
            ComplianceProfile::PciDss,
            "Network segmentation must be enabled",
            &[
                "segmentation_enabled",
                "vlan_active",
                "zone_isolation",
                "network_partition",
            ],
            Severity::Error,
        ),
        sensitive_network_send_rule(
            "PCI-DSS-1.3.3",
            ComplianceProfile::PciDss,
            "DMZ traffic must not leak cardholder data",
            &["cardholder", "pan_data", "card_number", "payment_data"],
            Severity::Error,
        ),
        insecure_network_rule(
            "PCI-DSS-1.4.1",
            ComplianceProfile::PciDss,
            "Personal firewall must use secure channel",
            Severity::Error,
        ),
        sensitive_let_rule(
            "PCI-DSS-1.5.1",
            ComplianceProfile::PciDss,
            "Network topology data must be classified",
            &[
                "network_diagram",
                "topology_data",
                "network_map",
                "infrastructure_data",
            ],
            Severity::Warning,
        ),
        // Requirement 2: Secure Configurations
        hardcoded_credential_rule(
            "PCI-DSS-2.1.1",
            ComplianceProfile::PciDss,
            "No vendor-supplied default credentials",
            &[
                "default_password",
                "factory_key",
                "vendor_credential",
                "default_token",
            ],
            Severity::Error,
        ),
        insecure_default_rule(
            "PCI-DSS-2.3.1",
            ComplianceProfile::PciDss,
            "Non-console admin access encryption enabled",
            &[
                "admin_encryption",
                "mgmt_tls",
                "console_secure",
                "admin_ssl",
            ],
            Severity::Error,
        ),
        // Requirement 3: Protect Stored Data
        sensitive_let_rule(
            "PCI-DSS-3.1.1",
            ComplianceProfile::PciDss,
            "Data retention policy data must be classified",
            &[
                "retention_data",
                "purge_data",
                "data_lifecycle",
                "storage_policy",
            ],
            Severity::Warning,
        ),
        sensitive_let_rule(
            "PCI-DSS-3.2.1",
            ComplianceProfile::PciDss,
            "Authentication data storage must be classified",
            &[
                "auth_store",
                "credential_cache",
                "token_store",
                "session_store",
            ],
            Severity::Error,
        ),
        declassify_prove_rule(
            "PCI-DSS-3.3.1",
            ComplianceProfile::PciDss,
            "PAN masking declassification requires Prove guard",
            Severity::Error,
        ),
        sensitive_let_rule(
            "PCI-DSS-3.7.1",
            ComplianceProfile::PciDss,
            "Key management procedures data must be classified",
            &[
                "key_procedure",
                "key_custodian",
                "key_ceremony",
                "key_split",
            ],
            Severity::Error,
        ),
        // Requirement 4: Encrypt Transmission
        weak_crypto_rule(
            "PCI-DSS-4.1.1",
            ComplianceProfile::PciDss,
            "Weak crypto in cardholder data transmission",
            Severity::Error,
        ),
        sensitive_let_rule(
            "PCI-DSS-4.2.2",
            ComplianceProfile::PciDss,
            "End-user messaging data must be classified",
            &[
                "message_data",
                "email_content",
                "chat_data",
                "notification_data",
            ],
            Severity::Warning,
        ),
        // Requirement 5: Anti-Malware
        tainted_input_rule(
            "PCI-DSS-5.1.1",
            ComplianceProfile::PciDss,
            "Malware scan input must be taint-tracked",
            &["scan_input", "malware_data", "virus_scan", "threat_input"],
            Severity::Error,
        ),
        insecure_default_rule(
            "PCI-DSS-5.2.1",
            ComplianceProfile::PciDss,
            "Anti-malware must be enabled",
            &[
                "antimalware_enabled",
                "virus_scan_active",
                "malware_protection",
                "realtime_scan",
            ],
            Severity::Error,
        ),
        // Requirement 6: Secure Development
        ffi_review_rule(
            "PCI-DSS-6.3.2",
            ComplianceProfile::PciDss,
            "Custom application FFI calls require review",
            Severity::Warning,
        ),
        unbounded_recursion_rule(
            "PCI-DSS-6.5.9",
            ComplianceProfile::PciDss,
            "Application code must have bounded recursion",
            Severity::Warning,
        ),
        // Requirement 7: Restrict Access
        sensitive_let_rule(
            "PCI-DSS-7.1.2",
            ComplianceProfile::PciDss,
            "Access control system data must be classified",
            &["access_system", "rbac_data", "privilege_data", "role_data"],
            Severity::Error,
        ),
        broad_grant_rule(
            "PCI-DSS-7.2.1",
            ComplianceProfile::PciDss,
            "Access control: overly broad grants flagged",
            Severity::Warning,
        ),
        sensitive_let_rule(
            "PCI-DSS-7.3.1",
            ComplianceProfile::PciDss,
            "Access policy data must be classified",
            &[
                "access_policy",
                "authorization_rule",
                "entitlement_data",
                "permission_set",
            ],
            Severity::Warning,
        ),
        // Requirement 8: Authentication
        auth_crypto_rule(
            "PCI-DSS-8.1.1",
            ComplianceProfile::PciDss,
            "User identification must use Crypto",
            &[
                "user_identify",
                "account_auth",
                "login_verify",
                "identity_check",
            ],
            Severity::Error,
        ),
        hardcoded_credential_rule(
            "PCI-DSS-8.2.1",
            ComplianceProfile::PciDss,
            "No hardcoded authentication credentials",
            &[
                "user_password",
                "login_credential",
                "auth_secret",
                "account_key",
            ],
            Severity::Error,
        ),
        temporal_no_expiry_rule(
            "PCI-DSS-8.3.1",
            ComplianceProfile::PciDss,
            "MFA tokens must have temporal handling",
            &[
                "mfa_token_time",
                "otp_expiry",
                "auth_timestamp",
                "session_timeout",
            ],
            Severity::Warning,
        ),
        // Requirement 9: Physical Access (logical checks)
        sensitive_let_rule(
            "PCI-DSS-9.1.1",
            ComplianceProfile::PciDss,
            "Physical access control data must be classified",
            &["badge_data", "entry_log", "visitor_data", "physical_access"],
            Severity::Warning,
        ),
        // Requirement 10: Logging/Monitoring
        audit_trail_rule(
            "PCI-DSS-10.1.1",
            ComplianceProfile::PciDss,
            "All access to cardholder data must be logged",
            Severity::Error,
        ),
        temporal_no_expiry_rule(
            "PCI-DSS-10.4.1",
            ComplianceProfile::PciDss,
            "Audit log timestamps must have time handling",
            &["log_timestamp", "event_time", "audit_date", "record_time"],
            Severity::Warning,
        ),
        sensitive_let_rule(
            "PCI-DSS-10.5.1",
            ComplianceProfile::PciDss,
            "Audit trail data must be classified",
            &["audit_trail", "security_log", "access_log", "event_log"],
            Severity::Error,
        ),
        insecure_default_rule(
            "PCI-DSS-10.6.1",
            ComplianceProfile::PciDss,
            "Log review process must be enabled",
            &[
                "log_review",
                "alert_monitoring",
                "siem_enabled",
                "log_analysis",
            ],
            Severity::Warning,
        ),
        // Requirement 11: Testing
        sensitive_let_rule(
            "PCI-DSS-11.1.1",
            ComplianceProfile::PciDss,
            "Wireless access point data must be classified",
            &["wireless_ap", "rogue_ap", "wifi_scan", "wireless_monitor"],
            Severity::Warning,
        ),
        tainted_input_rule(
            "PCI-DSS-11.3.1",
            ComplianceProfile::PciDss,
            "Penetration test input must be taint-tracked",
            &[
                "pentest_input",
                "scan_result",
                "vulnerability_data",
                "exploit_input",
            ],
            Severity::Warning,
        ),
        // Requirement 12: Security Policy
        sensitive_let_rule(
            "PCI-DSS-12.1.1",
            ComplianceProfile::PciDss,
            "Security policy data must be classified",
            &[
                "security_policy",
                "compliance_data",
                "governance_data",
                "policy_document",
            ],
            Severity::Warning,
        ),
    ]
}

// ===========================================================================
// HIPAA rules (18)
// ===========================================================================

fn hipaa_rules() -> Vec<ComplianceRule> {
    vec![
        sensitive_let_rule(
            "HIPAA-164.312-a1",
            ComplianceProfile::Hipaa,
            "PHI must be classified as Secret",
            &["patient", "medical", "health", "diagnosis", "phi", "ssn"],
            Severity::Error,
        ),
        auth_crypto_rule(
            "HIPAA-164.312-a2",
            ComplianceProfile::Hipaa,
            "Health system auth must use Crypto effect",
            &[
                "medical_auth",
                "health_login",
                "patient_verify",
                "clinical_auth",
            ],
            Severity::Error,
        ),
        hardcoded_credential_rule(
            "HIPAA-164.312-c1",
            ComplianceProfile::Hipaa,
            "No hardcoded health system credentials",
            &["patient_id", "medical_id", "health_record_id", "mrn"],
            Severity::Error,
        ),
        declassify_prove_rule(
            "HIPAA-164.312-d",
            ComplianceProfile::Hipaa,
            "PHI declassification requires Prove guard",
            Severity::Error,
        ),
        insecure_network_rule(
            "HIPAA-164.312-e1",
            ComplianceProfile::Hipaa,
            "PHI transmission must use secure channel",
            Severity::Error,
        ),
        sensitive_network_send_rule(
            "HIPAA-164.530-c",
            ComplianceProfile::Hipaa,
            "PHI must not be sent over network without sanitization",
            &["patient", "medical", "health", "phi", "diagnosis"],
            Severity::Error,
        ),
        weak_crypto_rule(
            "HIPAA-164.308-a5",
            ComplianceProfile::Hipaa,
            "Weak crypto not allowed for health data",
            Severity::Error,
        ),
        insecure_url_rule(
            "HIPAA-164.310-d",
            ComplianceProfile::Hipaa,
            "Health system URLs must use HTTPS",
            Severity::Error,
        ),
        audit_trail_rule(
            "HIPAA-164.314-a",
            ComplianceProfile::Hipaa,
            "PHI operations must have audit trail",
            Severity::Warning,
        ),
        trivial_handle_rule(
            "HIPAA-164.316-b",
            ComplianceProfile::Hipaa,
            "Health system errors must not be swallowed",
            Severity::Warning,
        ),
        // --- 8 new rules ---
        hardcoded_ip_rule(
            "HIPAA-164.308-a1",
            ComplianceProfile::Hipaa,
            "No hardcoded IPs in health systems",
            Severity::Warning,
        ),
        debug_code_rule(
            "HIPAA-164.308-a3",
            ComplianceProfile::Hipaa,
            "No debug code in clinical systems",
            Severity::Warning,
        ),
        insecure_default_rule(
            "HIPAA-164.310-a",
            ComplianceProfile::Hipaa,
            "Health system security defaults must be enabled",
            &[
                "encryption_enabled",
                "hipaa_mode",
                "audit_enabled",
                "phi_protection",
                "access_control",
            ],
            Severity::Error,
        ),
        hardcoded_port_rule(
            "HIPAA-164.312-b",
            ComplianceProfile::Hipaa,
            "No hardcoded ports in health systems",
            Severity::Warning,
        ),
        temporal_no_expiry_rule(
            "HIPAA-164.312-c2",
            ComplianceProfile::Hipaa,
            "Health records must have retention handling",
            &[
                "record_date",
                "admission_date",
                "discharge_date",
                "prescription_date",
                "consent_date",
            ],
            Severity::Warning,
        ),
        excessive_grant_rule(
            "HIPAA-164.312-e2",
            ComplianceProfile::Hipaa,
            "Excessive grants in health context",
            Severity::Warning,
        ),
        tainted_input_rule(
            "HIPAA-164.530-a",
            ComplianceProfile::Hipaa,
            "Patient input must be taint-tracked",
            &[
                "patient_input",
                "medical_form",
                "health_data",
                "clinical_input",
            ],
            Severity::Error,
        ),
        sensitive_ffi_rule(
            "HIPAA-164.530-b",
            ComplianceProfile::Hipaa,
            "FFI to health-data functions need enhanced review",
            &["patient", "medical", "health", "clinical", "pharma"],
            Severity::Warning,
        ),
        // --- 15 new HIPAA rules ---
        sensitive_let_rule(
            "HIPAA-164.308-a1",
            ComplianceProfile::Hipaa,
            "Risk analysis data must be classified",
            &[
                "risk_data",
                "threat_data",
                "vulnerability_data",
                "risk_assessment",
            ],
            Severity::Warning,
        ),
        insecure_default_rule(
            "HIPAA-164.308-a2",
            ComplianceProfile::Hipaa,
            "Security management process must be enabled",
            &[
                "security_mgmt",
                "risk_mgmt",
                "hipaa_compliance",
                "security_program",
            ],
            Severity::Error,
        ),
        sensitive_let_rule(
            "HIPAA-164.308-a3",
            ComplianceProfile::Hipaa,
            "Workforce security data must be classified",
            &[
                "workforce_data",
                "employee_access",
                "staff_clearance",
                "personnel_access",
            ],
            Severity::Error,
        ),
        auth_crypto_rule(
            "HIPAA-164.308-a4",
            ComplianceProfile::Hipaa,
            "Information access management must use Crypto",
            &[
                "access_mgmt",
                "phi_access",
                "health_authorize",
                "clinical_access",
            ],
            Severity::Error,
        ),
        sensitive_let_rule(
            "HIPAA-164.308-a5",
            ComplianceProfile::Hipaa,
            "Security awareness data must be classified",
            &[
                "awareness_data",
                "training_data",
                "security_training",
                "compliance_training",
            ],
            Severity::Warning,
        ),
        sensitive_let_rule(
            "HIPAA-164.308-a6",
            ComplianceProfile::Hipaa,
            "Incident response data must be classified",
            &[
                "incident_data",
                "breach_data",
                "security_incident",
                "phi_breach",
            ],
            Severity::Error,
        ),
        sensitive_let_rule(
            "HIPAA-164.308-a7",
            ComplianceProfile::Hipaa,
            "Contingency plan data must be classified",
            &[
                "contingency_data",
                "backup_plan",
                "disaster_recovery",
                "emergency_plan",
            ],
            Severity::Warning,
        ),
        sensitive_let_rule(
            "HIPAA-164.310-a1",
            ComplianceProfile::Hipaa,
            "Facility access control data must be classified",
            &[
                "facility_access",
                "physical_access",
                "badge_data",
                "entry_control",
            ],
            Severity::Warning,
        ),
        sensitive_let_rule(
            "HIPAA-164.310-b1",
            ComplianceProfile::Hipaa,
            "Workstation security data must be classified",
            &[
                "workstation_data",
                "desktop_config",
                "endpoint_data",
                "terminal_data",
            ],
            Severity::Warning,
        ),
        hardcoded_credential_rule(
            "HIPAA-164.312-a3",
            ComplianceProfile::Hipaa,
            "No hardcoded emergency access credentials",
            &[
                "emergency_password",
                "break_glass_key",
                "emergency_credential",
                "override_token",
            ],
            Severity::Error,
        ),
        declassify_prove_rule(
            "HIPAA-164.312-c3",
            ComplianceProfile::Hipaa,
            "PHI declassification requires Prove guard",
            Severity::Error,
        ),
        sensitive_network_send_rule(
            "HIPAA-164.312-e3",
            ComplianceProfile::Hipaa,
            "PHI must not leak over network",
            &["phi", "patient_data", "medical_record", "health_info"],
            Severity::Error,
        ),
        classify_without_audit_rule(
            "HIPAA-164.316-a1",
            ComplianceProfile::Hipaa,
            "PHI classification must produce audit events",
            Severity::Warning,
        ),
        unbounded_recursion_rule(
            "HIPAA-164.316-b1",
            ComplianceProfile::Hipaa,
            "Health system algorithms must have bounded recursion",
            Severity::Warning,
        ),
        temporal_no_expiry_rule(
            "HIPAA-164.530-c",
            ComplianceProfile::Hipaa,
            "Patient consent dates must have temporal handling",
            &[
                "consent_date",
                "authorization_date",
                "notice_date",
                "acknowledgment_date",
            ],
            Severity::Warning,
        ),
    ]
}

// ===========================================================================
// GDPR rules (18)
// ===========================================================================

fn gdpr_rules() -> Vec<ComplianceRule> {
    vec![
        sensitive_let_rule(
            "GDPR-5.1-a",
            ComplianceProfile::Gdpr,
            "Personal data must be classified as Secret",
            &["personal", "gdpr_data", "eu_citizen", "subject_data", "pii"],
            Severity::Error,
        ),
        hardcoded_credential_rule(
            "GDPR-5.1-b",
            ComplianceProfile::Gdpr,
            "No hardcoded personal data",
            &[
                "personal_name",
                "email_address",
                "home_address",
                "phone_number",
                "birth_date",
            ],
            Severity::Error,
        ),
        sensitive_network_send_rule(
            "GDPR-5.1-c",
            ComplianceProfile::Gdpr,
            "Personal data must not be sent over network without sanitization",
            &["personal", "gdpr_data", "subject", "eu_citizen", "pii"],
            Severity::Error,
        ),
        insecure_url_rule(
            "GDPR-5.1-e",
            ComplianceProfile::Gdpr,
            "Data processing URLs must use HTTPS",
            Severity::Error,
        ),
        weak_crypto_rule(
            "GDPR-5.1-f",
            ComplianceProfile::Gdpr,
            "Weak crypto not allowed for personal data",
            Severity::Error,
        ),
        insecure_network_rule(
            "GDPR-25.1",
            ComplianceProfile::Gdpr,
            "Data protection by design: secure channel required",
            Severity::Error,
        ),
        declassify_prove_rule(
            "GDPR-32",
            ComplianceProfile::Gdpr,
            "Declassification of personal data requires Prove guard",
            Severity::Error,
        ),
        audit_trail_rule(
            "GDPR-33",
            ComplianceProfile::Gdpr,
            "Security operations need audit trail for breach notification",
            Severity::Warning,
        ),
        broad_grant_rule(
            "GDPR-35",
            ComplianceProfile::Gdpr,
            "High-risk processing: overly broad grants flagged",
            Severity::Warning,
        ),
        trivial_handle_rule(
            "GDPR-17",
            ComplianceProfile::Gdpr,
            "Data handling errors must not be silently discarded",
            Severity::Warning,
        ),
        // --- 8 new rules ---
        hardcoded_ip_rule(
            "GDPR-5.1-d",
            ComplianceProfile::Gdpr,
            "No hardcoded IPs (data localization)",
            Severity::Warning,
        ),
        debug_code_rule(
            "GDPR-6.1",
            ComplianceProfile::Gdpr,
            "No debug code with personal data",
            Severity::Warning,
        ),
        insecure_default_rule(
            "GDPR-13.1",
            ComplianceProfile::Gdpr,
            "Privacy defaults must be enabled (privacy by default)",
            &[
                "consent_required",
                "data_protection",
                "privacy_mode",
                "gdpr_enabled",
                "anonymize",
            ],
            Severity::Error,
        ),
        hardcoded_port_rule(
            "GDPR-15.1",
            ComplianceProfile::Gdpr,
            "No hardcoded ports in data processing",
            Severity::Warning,
        ),
        temporal_no_expiry_rule(
            "GDPR-17.1",
            ComplianceProfile::Gdpr,
            "Personal data must have retention/expiry handling",
            &[
                "consent_date",
                "data_collected",
                "retention_start",
                "processing_date",
                "erasure_date",
            ],
            Severity::Warning,
        ),
        tainted_input_rule(
            "GDPR-20.1",
            ComplianceProfile::Gdpr,
            "User input must be taint-tracked for GDPR",
            &["user_input", "subject_data", "consent_form", "data_request"],
            Severity::Error,
        ),
        excessive_grant_rule(
            "GDPR-25.2",
            ComplianceProfile::Gdpr,
            "Excessive grants violate data minimization",
            Severity::Warning,
        ),
        sensitive_ffi_rule(
            "GDPR-44.1",
            ComplianceProfile::Gdpr,
            "FFI to data-transfer functions need review",
            &["transfer", "export", "personal", "subject", "consent"],
            Severity::Warning,
        ),
        // --- 10 new GDPR rules ---
        sensitive_let_rule(
            "GDPR-6.1",
            ComplianceProfile::Gdpr,
            "Lawfulness basis data must be classified",
            &[
                "legal_basis",
                "consent_data",
                "legitimate_interest",
                "contract_basis",
            ],
            Severity::Warning,
        ),
        sensitive_let_rule(
            "GDPR-9.1",
            ComplianceProfile::Gdpr,
            "Special category data must be classified",
            &[
                "biometric",
                "genetic",
                "health_data",
                "political_opinion",
                "religious_belief",
            ],
            Severity::Error,
        ),
        sensitive_let_rule(
            "GDPR-13.1",
            ComplianceProfile::Gdpr,
            "Data subject notification data must be classified",
            &[
                "notification_data",
                "privacy_notice",
                "disclosure_info",
                "transparency_data",
            ],
            Severity::Warning,
        ),
        declassify_prove_rule(
            "GDPR-15.1",
            ComplianceProfile::Gdpr,
            "Subject access declassification requires Prove guard",
            Severity::Error,
        ),
        temporal_no_expiry_rule(
            "GDPR-17.2",
            ComplianceProfile::Gdpr,
            "Erasure request dates must have temporal handling",
            &[
                "erasure_request_date",
                "deletion_deadline",
                "retention_end",
                "forget_date",
            ],
            Severity::Warning,
        ),
        sensitive_let_rule(
            "GDPR-33.1",
            ComplianceProfile::Gdpr,
            "Breach notification data must be classified",
            &[
                "breach_notification",
                "incident_report",
                "dpa_notification",
                "breach_record",
            ],
            Severity::Error,
        ),
        insecure_default_rule(
            "GDPR-35.1",
            ComplianceProfile::Gdpr,
            "Data protection impact assessment must be enabled",
            &[
                "dpia_enabled",
                "impact_assessment",
                "risk_assessment",
                "privacy_impact",
            ],
            Severity::Warning,
        ),
        classify_without_audit_rule(
            "GDPR-30.1",
            ComplianceProfile::Gdpr,
            "Processing activity records must be audited",
            Severity::Warning,
        ),
        hardcoded_credential_rule(
            "GDPR-32.1",
            ComplianceProfile::Gdpr,
            "No hardcoded security processing credentials",
            &[
                "processing_key",
                "encryption_credential",
                "pseudonymization_key",
                "anonymization_token",
            ],
            Severity::Error,
        ),
        auth_crypto_rule(
            "GDPR-25.3",
            ComplianceProfile::Gdpr,
            "Data protection by design auth must use Crypto",
            &[
                "privacy_auth",
                "data_protection_login",
                "gdpr_verify",
                "consent_auth",
            ],
            Severity::Error,
        ),
        // --- 6 IFC-mapped rules (leveraging RIINA's information flow lattice) ---
        sensitive_let_rule(
            "GDPR-IFC.1",
            ComplianceProfile::Gdpr,
            "Controller-processor data must be classified (IFC: Sulit level)",
            &[
                "controller_data",
                "processor_data",
                "data_controller",
                "joint_controller",
            ],
            Severity::Error,
        ),
        sensitive_let_rule(
            "GDPR-IFC.2",
            ComplianceProfile::Gdpr,
            "Cross-border transfer data must be classified (IFC: Rahsia level)",
            &[
                "cross_border",
                "third_country",
                "adequacy_data",
                "transfer_impact",
            ],
            Severity::Error,
        ),
        declassify_prove_rule(
            "GDPR-IFC.3",
            ComplianceProfile::Gdpr,
            "Data portability export requires Prove guard (IFC downgrade gate)",
            Severity::Error,
        ),
        sensitive_network_send_rule(
            "GDPR-IFC.4",
            ComplianceProfile::Gdpr,
            "Consent withdrawal data must not leak (IFC: no implicit flow)",
            &[
                "consent_withdrawn",
                "opt_out",
                "withdrawal_record",
                "revocation_data",
            ],
            Severity::Error,
        ),
        classify_without_audit_rule(
            "GDPR-IFC.5",
            ComplianceProfile::Gdpr,
            "Pseudonymization must be audited (IFC label verification)",
            Severity::Warning,
        ),
        sensitive_let_rule(
            "GDPR-IFC.6",
            ComplianceProfile::Gdpr,
            "Automated decision data must be classified (Art 22 profiling)",
            &[
                "automated_decision",
                "profiling_data",
                "algorithmic_decision",
                "scoring_data",
            ],
            Severity::Error,
        ),
    ]
}

// ===========================================================================
// PDPA Malaysia rules (18)
// ===========================================================================

fn pdpa_rules() -> Vec<ComplianceRule> {
    vec![
        // --- Existing 2 rules (preserved) ---
        ComplianceRule {
            id: "PDPA-S7",
            profile: ComplianceProfile::Pdpa,
            description: "User input must be Tainted<_, UserInput>",
            check: Box::new(|expr| {
                if let Expr::Let(name, _, value, _) = expr {
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
            }),
        },
        ComplianceRule {
            id: "PDPA-S24",
            profile: ComplianceProfile::Pdpa,
            description: "No Network effect on personal data without sanitization",
            check: Box::new(|expr| {
                if let Expr::Perform(Effect::Network | Effect::NetworkSecure, arg) = expr {
                    if contains_personal_data_var(arg) {
                        return Some(ComplianceViolation {
                            rule_id: "PDPA-S24",
                            profile: ComplianceProfile::Pdpa,
                            message: "Sending personal data over network without sanitization"
                                .into(),
                            severity: Severity::Error,
                        });
                    }
                }
                None
            }),
        },
        // --- New 8 rules ---
        // --- PDPA (Amendment) Act 2024 (REQ-51 refresh) ---
        // s.4 (amended): biometric data is now SENSITIVE personal data.
        sensitive_let_rule(
            "PDPA-2024-S4-BIO",
            ComplianceProfile::Pdpa,
            "Biometric data is sensitive personal data (2024 Amendment) and must be classified",
            &["biometric", "biometrik", "cap_jari", "fingerprint", "facial_data", "wajah"],
            Severity::Error,
        ),
        // s.12B (new): mandatory breach notification — a breach cannot be
        // notified if security operations leave no audit trail.
        audit_trail_rule(
            "PDPA-2024-S12B",
            ComplianceProfile::Pdpa,
            "Security operations on personal data must leave an audit trail (breach-notification readiness, s.12B)",
            Severity::Error,
        ),
        sensitive_let_rule(
            "PDPA-S6",
            ComplianceProfile::Pdpa,
            "Personal data must be classified (consent principle)",
            &[
                "nama",
                "ic_number",
                "kad_pengenalan",
                "no_telefon",
                "alamat_emel",
            ],
            Severity::Error,
        ),
        hardcoded_credential_rule(
            "PDPA-S8",
            ComplianceProfile::Pdpa,
            "No hardcoded personal data (disclosure principle)",
            &["nama_penuh", "no_ic", "alamat", "no_tel", "emel"],
            Severity::Error,
        ),
        insecure_network_rule(
            "PDPA-S9",
            ComplianceProfile::Pdpa,
            "Personal data transmission must use secure channel",
            Severity::Error,
        ),
        declassify_prove_rule(
            "PDPA-S10",
            ComplianceProfile::Pdpa,
            "Personal data declassification requires Prove guard (retention principle)",
            Severity::Error,
        ),
        weak_crypto_rule(
            "PDPA-S11",
            ComplianceProfile::Pdpa,
            "Weak crypto not allowed for personal data (integrity principle)",
            Severity::Error,
        ),
        auth_crypto_rule(
            "PDPA-S12",
            ComplianceProfile::Pdpa,
            "Access control functions must use Crypto (access principle)",
            &["akses", "capaian", "kebenaran", "pengesahan"],
            Severity::Warning,
        ),
        audit_trail_rule(
            "PDPA-S13-1",
            ComplianceProfile::Pdpa,
            "Personal data operations need audit trail (cross-border transfer)",
            Severity::Warning,
        ),
        trivial_handle_rule(
            "PDPA-S42",
            ComplianceProfile::Pdpa,
            "Error handling for personal data must not be swallowed (breach notification)",
            Severity::Warning,
        ),
        // --- 8 new rules ---
        hardcoded_ip_rule(
            "PDPA-S5",
            ComplianceProfile::Pdpa,
            "No hardcoded IPs in personal data systems",
            Severity::Warning,
        ),
        debug_code_rule(
            "PDPA-S7-1",
            ComplianceProfile::Pdpa,
            "No debug code exposing personal data",
            Severity::Warning,
        ),
        insecure_default_rule(
            "PDPA-S14",
            ComplianceProfile::Pdpa,
            "Data protection defaults must be enabled",
            &[
                "perlindungan",
                "data_protection",
                "consent_enabled",
                "privacy_mode",
                "kebenaran_data",
            ],
            Severity::Error,
        ),
        hardcoded_port_rule(
            "PDPA-S15",
            ComplianceProfile::Pdpa,
            "No hardcoded ports in data systems",
            Severity::Warning,
        ),
        temporal_no_expiry_rule(
            "PDPA-S16",
            ComplianceProfile::Pdpa,
            "Personal data must have retention period",
            &[
                "tarikh_kutip",
                "data_collected",
                "tarikh_persetujuan",
                "consent_date",
                "tarikh_simpan",
            ],
            Severity::Warning,
        ),
        tainted_input_rule(
            "PDPA-S17",
            ComplianceProfile::Pdpa,
            "User input must be taint-tracked",
            &["input_pengguna", "data_borang", "user_input", "form_data"],
            Severity::Error,
        ),
        excessive_grant_rule(
            "PDPA-S18",
            ComplianceProfile::Pdpa,
            "Excessive grants on personal data",
            Severity::Warning,
        ),
        sensitive_ffi_rule(
            "PDPA-S19",
            ComplianceProfile::Pdpa,
            "FFI calls handling personal data need review",
            &["personal", "nama", "ic_number", "data_peribadi", "pengguna"],
            Severity::Warning,
        ),
    ]
}

/// Check if an expression references a variable with personal-data naming.
fn contains_personal_data_var(expr: &Expr) -> bool {
    match expr {
        Expr::Var(name) => {
            let lower = name.to_lowercase();
            lower.contains("personal")
                || lower.contains("user_data")
                || lower.contains("nama")
                || lower.contains("ic_number")
        }
        _ => any_child(expr, &mut contains_personal_data_var),
    }
}

// ===========================================================================
// BNM RMiT rules (18)
// ===========================================================================

fn bnm_rules() -> Vec<ComplianceRule> {
    vec![
        // --- Existing 1 rule (preserved) ---
        ComplianceRule {
            id: "BNM-RMiT-10",
            profile: ComplianceProfile::Bnm,
            description: "Financial crypto must use ConstantTime<_>",
            check: Box::new(|expr| {
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
            }),
        },
        // --- New 9 rules ---
        sensitive_let_rule(
            "BNM-10.18",
            ComplianceProfile::Bnm,
            "Financial data must be Secret-typed",
            &["financial", "banking", "akaun", "transaksi", "baki"],
            Severity::Error,
        ),
        hardcoded_credential_rule(
            "BNM-10.49-b",
            ComplianceProfile::Bnm,
            "No hardcoded financial credentials",
            &["pin_bank", "kata_laluan", "token_bank", "kunci_api"],
            Severity::Error,
        ),
        auth_crypto_rule(
            "BNM-10.50",
            ComplianceProfile::Bnm,
            "Financial auth must use Crypto effect",
            &["pengesahan", "log_masuk", "sahkan", "bank_auth"],
            Severity::Error,
        ),
        audit_trail_rule(
            "BNM-10.51",
            ComplianceProfile::Bnm,
            "Financial transactions must have audit trail",
            Severity::Error,
        ),
        declassify_prove_rule(
            "BNM-10.52",
            ComplianceProfile::Bnm,
            "Financial data declassification requires Prove guard",
            Severity::Error,
        ),
        trivial_handle_rule(
            "BNM-10.54",
            ComplianceProfile::Bnm,
            "Financial error handling must not swallow errors",
            Severity::Warning,
        ),
        ffi_review_rule(
            "BNM-10.55",
            ComplianceProfile::Bnm,
            "Third-party FFI calls require security review",
            Severity::Warning,
        ),
        insecure_network_rule(
            "BNM-10.56",
            ComplianceProfile::Bnm,
            "Financial network communication must use secure channel",
            Severity::Error,
        ),
        insecure_url_rule(
            "BNM-10.58",
            ComplianceProfile::Bnm,
            "Financial system URLs must use HTTPS",
            Severity::Warning,
        ),
        // --- 8 new rules ---
        hardcoded_ip_rule(
            "BNM-10.18-1",
            ComplianceProfile::Bnm,
            "No hardcoded IPs in financial systems",
            Severity::Warning,
        ),
        debug_code_rule(
            "BNM-10.49-c",
            ComplianceProfile::Bnm,
            "No debug code in banking systems",
            Severity::Warning,
        ),
        insecure_default_rule(
            "BNM-10.53",
            ComplianceProfile::Bnm,
            "Financial security defaults must be enabled",
            &[
                "keselamatan",
                "encryption_enabled",
                "audit_mode",
                "tls_required",
                "pengesahan_aktif",
            ],
            Severity::Error,
        ),
        hardcoded_port_rule(
            "BNM-10.57",
            ComplianceProfile::Bnm,
            "No hardcoded ports in banking",
            Severity::Warning,
        ),
        temporal_no_expiry_rule(
            "BNM-10.59",
            ComplianceProfile::Bnm,
            "Financial records must have retention handling",
            &[
                "tarikh_transaksi",
                "transaction_date",
                "statement_date",
                "tarikh_audit",
                "maturity_date",
            ],
            Severity::Warning,
        ),
        tainted_input_rule(
            "BNM-10.60",
            ComplianceProfile::Bnm,
            "Financial user input must be taint-tracked",
            &[
                "input_pelanggan",
                "customer_input",
                "form_bank",
                "transaction_input",
            ],
            Severity::Error,
        ),
        excessive_grant_rule(
            "BNM-10.61",
            ComplianceProfile::Bnm,
            "Excessive grants in financial context",
            Severity::Warning,
        ),
        sensitive_ffi_rule(
            "BNM-10.62",
            ComplianceProfile::Bnm,
            "FFI to financial functions need review",
            &["bank", "financial", "transaksi", "akaun", "payment"],
            Severity::Warning,
        ),
        // --- 2 new BNM rules ---
        classify_without_audit_rule(
            "BNM-10.63",
            ComplianceProfile::Bnm,
            "Financial data classification must be audited",
            Severity::Warning,
        ),
        sensitive_network_send_rule(
            "BNM-10.64",
            ComplianceProfile::Bnm,
            "Financial data must not leak over network",
            &[
                "bank_data",
                "customer_data",
                "akaun_data",
                "transaction_data",
            ],
            Severity::Error,
        ),
    ]
}

// ===========================================================================
// MAS TRM Singapore rules (15)
// ===========================================================================

fn mas_trm_rules() -> Vec<ComplianceRule> {
    vec![
        sensitive_let_rule(
            "MAS-TRM-5.1.1",
            ComplianceProfile::MasTrm,
            "Customer/financial data must be Secret-typed",
            &["customer", "account", "balance", "transaction", "financial"],
            Severity::Error,
        ),
        weak_crypto_rule(
            "MAS-TRM-9.1.1",
            ComplianceProfile::MasTrm,
            "Weak crypto not allowed for financial systems",
            Severity::Error,
        ),
        auth_crypto_rule(
            "MAS-TRM-9.2.1",
            ComplianceProfile::MasTrm,
            "Financial auth must use Crypto effect",
            &["authenticate", "verify", "authorize", "login"],
            Severity::Error,
        ),
        hardcoded_credential_rule(
            "MAS-TRM-9.4.1",
            ComplianceProfile::MasTrm,
            "No hardcoded credentials in financial systems",
            &["password", "token", "api_key", "secret", "credential"],
            Severity::Error,
        ),
        insecure_network_rule(
            "MAS-TRM-11.1.1",
            ComplianceProfile::MasTrm,
            "Financial data transmission must use secure channel",
            Severity::Error,
        ),
        sensitive_network_send_rule(
            "MAS-TRM-11.2.1",
            ComplianceProfile::MasTrm,
            "Customer data must not be sent over network without sanitization",
            &["customer", "account", "financial", "transaction"],
            Severity::Error,
        ),
        audit_trail_rule(
            "MAS-TRM-12.1.1",
            ComplianceProfile::MasTrm,
            "Financial operations must have audit trail",
            Severity::Warning,
        ),
        broad_grant_rule(
            "MAS-TRM-13.1.1",
            ComplianceProfile::MasTrm,
            "Overly broad grants require review in financial systems",
            Severity::Warning,
        ),
        // --- 7 new rules ---
        hardcoded_ip_rule(
            "MAS-TRM-5.1.2",
            ComplianceProfile::MasTrm,
            "No hardcoded IPs in financial systems",
            Severity::Warning,
        ),
        debug_code_rule(
            "MAS-TRM-9.1.2",
            ComplianceProfile::MasTrm,
            "No debug code in financial systems",
            Severity::Warning,
        ),
        insecure_default_rule(
            "MAS-TRM-9.2.2",
            ComplianceProfile::MasTrm,
            "Security defaults must be enabled",
            &[
                "encryption_enabled",
                "mfa_required",
                "audit_enabled",
                "tls_mode",
                "auth_required",
            ],
            Severity::Error,
        ),
        hardcoded_port_rule(
            "MAS-TRM-9.4.2",
            ComplianceProfile::MasTrm,
            "No hardcoded ports in financial systems",
            Severity::Warning,
        ),
        temporal_no_expiry_rule(
            "MAS-TRM-11.1.2",
            ComplianceProfile::MasTrm,
            "Financial data must have retention handling",
            &[
                "transaction_date",
                "statement_date",
                "audit_timestamp",
                "session_created",
                "token_issued",
            ],
            Severity::Warning,
        ),
        tainted_input_rule(
            "MAS-TRM-11.2.2",
            ComplianceProfile::MasTrm,
            "Customer input must be taint-tracked",
            &[
                "customer_input",
                "user_input",
                "form_data",
                "transaction_input",
            ],
            Severity::Error,
        ),
        excessive_grant_rule(
            "MAS-TRM-12.1.2",
            ComplianceProfile::MasTrm,
            "Excessive grants in financial systems",
            Severity::Warning,
        ),
        // --- 5 new MAS TRM rules ---
        sensitive_let_rule(
            "MAS-TRM-6.1.1",
            ComplianceProfile::MasTrm,
            "IT project management data must be classified",
            &[
                "project_data",
                "change_data",
                "release_data",
                "deployment_data",
            ],
            Severity::Warning,
        ),
        declassify_prove_rule(
            "MAS-TRM-7.1.1",
            ComplianceProfile::MasTrm,
            "Financial data declassification requires Prove guard",
            Severity::Error,
        ),
        sensitive_ffi_rule(
            "MAS-TRM-8.1.1",
            ComplianceProfile::MasTrm,
            "Financial service FFI needs review",
            &["banking", "trading", "payment", "settlement", "clearing"],
            Severity::Warning,
        ),
        classify_without_audit_rule(
            "MAS-TRM-10.1.1",
            ComplianceProfile::MasTrm,
            "Financial data classification must be audited",
            Severity::Warning,
        ),
        trivial_handle_rule(
            "MAS-TRM-13.1.2",
            ComplianceProfile::MasTrm,
            "Financial error handling must not swallow errors",
            Severity::Error,
        ),
    ]
}

// ===========================================================================
// NIST 800-53 rules (18)
// ===========================================================================

fn nist_rules() -> Vec<ComplianceRule> {
    vec![
        sensitive_let_rule(
            "NIST-AC-1",
            ComplianceProfile::Nist80053,
            "Sensitive data must be classified as Secret",
            &["classified", "sensitive", "protected", "controlled"],
            Severity::Error,
        ),
        broad_grant_rule(
            "NIST-AC-6",
            ComplianceProfile::Nist80053,
            "Least privilege: overly broad grants flagged",
            Severity::Warning,
        ),
        audit_trail_rule(
            "NIST-AU-2",
            ComplianceProfile::Nist80053,
            "Security operations must produce audit events",
            Severity::Warning,
        ),
        hardcoded_credential_rule(
            "NIST-IA-5",
            ComplianceProfile::Nist80053,
            "No hardcoded authenticators",
            &["password", "token", "credential", "api_key", "secret"],
            Severity::Error,
        ),
        insecure_network_rule(
            "NIST-SC-8",
            ComplianceProfile::Nist80053,
            "Transmission confidentiality: secure channel required",
            Severity::Error,
        ),
        sensitive_let_rule(
            "NIST-SC-12",
            ComplianceProfile::Nist80053,
            "Cryptographic keys must be Secret-typed",
            &["crypto_key", "signing_key", "cert_key", "private_key"],
            Severity::Error,
        ),
        weak_crypto_rule(
            "NIST-SC-13",
            ComplianceProfile::Nist80053,
            "Weak cryptographic algorithms prohibited",
            Severity::Error,
        ),
        insecure_url_rule(
            "NIST-SC-28",
            ComplianceProfile::Nist80053,
            "Data at rest/in transit must use HTTPS",
            Severity::Error,
        ),
        ffi_review_rule(
            "NIST-SI-2",
            ComplianceProfile::Nist80053,
            "FFI calls require flaw remediation review",
            Severity::Warning,
        ),
        tainted_input_rule(
            "NIST-SI-10",
            ComplianceProfile::Nist80053,
            "User input must be taint-tracked for validation",
            &["user_input", "form_data", "request_body", "query_param"],
            Severity::Error,
        ),
        // --- 8 new rules ---
        hardcoded_ip_rule(
            "NIST-AC-2",
            ComplianceProfile::Nist80053,
            "No hardcoded IPs in federal systems",
            Severity::Warning,
        ),
        debug_code_rule(
            "NIST-AU-3",
            ComplianceProfile::Nist80053,
            "No debug code in production",
            Severity::Warning,
        ),
        insecure_default_rule(
            "NIST-CM-6",
            ComplianceProfile::Nist80053,
            "Security configs must not default to false",
            &[
                "fips_mode",
                "encryption_enabled",
                "audit_enabled",
                "tls_required",
                "auth_required",
            ],
            Severity::Error,
        ),
        hardcoded_port_rule(
            "NIST-IA-6",
            ComplianceProfile::Nist80053,
            "No hardcoded ports in federal systems",
            Severity::Warning,
        ),
        temporal_no_expiry_rule(
            "NIST-SC-4",
            ComplianceProfile::Nist80053,
            "Sensitive data must have retention handling",
            &[
                "classification_date",
                "cert_expiry",
                "key_created",
                "session_start",
                "token_timestamp",
            ],
            Severity::Warning,
        ),
        excessive_grant_rule(
            "NIST-AC-6-1",
            ComplianceProfile::Nist80053,
            "Least privilege enforcement",
            Severity::Warning,
        ),
        sensitive_ffi_rule(
            "NIST-SA-11",
            ComplianceProfile::Nist80053,
            "FFI calls require developer security testing",
            &["crypto", "auth", "certificate", "classified", "secure"],
            Severity::Warning,
        ),
        classify_without_audit_rule(
            "NIST-AU-12",
            ComplianceProfile::Nist80053,
            "Classification must produce audit events",
            Severity::Warning,
        ),
        // --- 60 new NIST 800-53 rules ---
        // AC (Access Control) family
        sensitive_let_rule(
            "NIST-AC-3",
            ComplianceProfile::Nist80053,
            "Access control lists must be classified",
            &["access_list", "acl", "permission_list", "role_list"],
            Severity::Error,
        ),
        sensitive_let_rule(
            "NIST-AC-4",
            ComplianceProfile::Nist80053,
            "Information flow data must be classified",
            &[
                "data_flow",
                "information_flow",
                "flow_control",
                "transfer_data",
            ],
            Severity::Error,
        ),
        sensitive_let_rule(
            "NIST-AC-5",
            ComplianceProfile::Nist80053,
            "Separation of duties data must be classified",
            &[
                "separation_duty",
                "duty_roster",
                "role_assignment",
                "privilege_set",
            ],
            Severity::Error,
        ),
        hardcoded_credential_rule(
            "NIST-AC-7",
            ComplianceProfile::Nist80053,
            "No hardcoded login attempt limits",
            &[
                "max_attempts",
                "lockout_threshold",
                "login_limit",
                "failed_attempts",
            ],
            Severity::Warning,
        ),
        insecure_default_rule(
            "NIST-AC-8",
            ComplianceProfile::Nist80053,
            "System use notification must be enabled",
            &[
                "login_banner",
                "system_notification",
                "use_notice",
                "warning_banner",
            ],
            Severity::Warning,
        ),
        sensitive_let_rule(
            "NIST-AC-10",
            ComplianceProfile::Nist80053,
            "Concurrent session data must be classified",
            &[
                "session_limit",
                "concurrent_sessions",
                "active_sessions",
                "session_pool",
            ],
            Severity::Warning,
        ),
        broad_grant_rule(
            "NIST-AC-11",
            ComplianceProfile::Nist80053,
            "Session lock: overly broad grants flagged",
            Severity::Warning,
        ),
        sensitive_let_rule(
            "NIST-AC-14",
            ComplianceProfile::Nist80053,
            "Permitted actions without identification must be classified",
            &[
                "anonymous_action",
                "unauthenticated_access",
                "public_action",
                "guest_permission",
            ],
            Severity::Warning,
        ),
        hardcoded_credential_rule(
            "NIST-AC-17",
            ComplianceProfile::Nist80053,
            "No hardcoded remote access credentials",
            &["remote_password", "vpn_key", "ssh_key", "remote_token"],
            Severity::Error,
        ),
        sensitive_let_rule(
            "NIST-AC-18",
            ComplianceProfile::Nist80053,
            "Wireless access credentials must be classified",
            &[
                "wifi_key",
                "wireless_credential",
                "wpa_key",
                "wireless_token",
            ],
            Severity::Error,
        ),
        sensitive_let_rule(
            "NIST-AC-19",
            ComplianceProfile::Nist80053,
            "Mobile device data must be classified",
            &[
                "mobile_data",
                "device_key",
                "mobile_credential",
                "byod_token",
            ],
            Severity::Error,
        ),
        insecure_default_rule(
            "NIST-AC-20",
            ComplianceProfile::Nist80053,
            "External system connection defaults must be secure",
            &[
                "external_trust",
                "external_connection",
                "partner_access",
                "federation_enabled",
            ],
            Severity::Error,
        ),
        sensitive_network_send_rule(
            "NIST-AC-21",
            ComplianceProfile::Nist80053,
            "Information sharing must not leak classified data",
            &["classified", "controlled", "sensitive", "restricted"],
            Severity::Error,
        ),
        sensitive_let_rule(
            "NIST-AC-22",
            ComplianceProfile::Nist80053,
            "Publicly accessible content must be classified",
            &[
                "public_content",
                "published_data",
                "external_content",
                "shared_resource",
            ],
            Severity::Warning,
        ),
        sensitive_let_rule(
            "NIST-AC-23",
            ComplianceProfile::Nist80053,
            "Data mining protection data must be classified",
            &[
                "mining_data",
                "analytics_raw",
                "bulk_data",
                "aggregation_source",
            ],
            Severity::Warning,
        ),
        sensitive_let_rule(
            "NIST-AC-24",
            ComplianceProfile::Nist80053,
            "Access control decisions must be classified",
            &[
                "access_decision",
                "policy_decision",
                "authorization_result",
                "access_verdict",
            ],
            Severity::Warning,
        ),
        insecure_default_rule(
            "NIST-AC-25",
            ComplianceProfile::Nist80053,
            "Reference monitor must be enabled",
            &[
                "reference_monitor",
                "access_mediation",
                "policy_enforcement",
                "access_guard",
            ],
            Severity::Error,
        ),
        // AU (Audit) family
        sensitive_let_rule(
            "NIST-AU-4",
            ComplianceProfile::Nist80053,
            "Audit storage capacity data must be classified",
            &[
                "audit_storage",
                "log_capacity",
                "audit_buffer",
                "log_retention",
            ],
            Severity::Warning,
        ),
        insecure_default_rule(
            "NIST-AU-5",
            ComplianceProfile::Nist80053,
            "Audit failure response must be enabled",
            &[
                "audit_failure_action",
                "log_overflow_action",
                "audit_alert",
                "audit_shutdown",
            ],
            Severity::Error,
        ),
        sensitive_let_rule(
            "NIST-AU-6",
            ComplianceProfile::Nist80053,
            "Audit review data must be classified",
            &[
                "audit_review",
                "log_analysis",
                "audit_report",
                "security_review",
            ],
            Severity::Warning,
        ),
        hardcoded_credential_rule(
            "NIST-AU-7",
            ComplianceProfile::Nist80053,
            "No hardcoded audit reduction values",
            &[
                "audit_filter",
                "log_filter",
                "audit_threshold",
                "alert_threshold",
            ],
            Severity::Warning,
        ),
        temporal_no_expiry_rule(
            "NIST-AU-8",
            ComplianceProfile::Nist80053,
            "Audit timestamps must have time handling",
            &["audit_timestamp", "log_time", "event_time", "audit_date"],
            Severity::Warning,
        ),
        sensitive_let_rule(
            "NIST-AU-9",
            ComplianceProfile::Nist80053,
            "Audit information must be protected",
            &["audit_data", "log_data", "audit_record", "security_log"],
            Severity::Error,
        ),
        insecure_default_rule(
            "NIST-AU-10",
            ComplianceProfile::Nist80053,
            "Non-repudiation must be enabled",
            &[
                "non_repudiation",
                "signing_enabled",
                "audit_signing",
                "log_integrity",
            ],
            Severity::Error,
        ),
        sensitive_let_rule(
            "NIST-AU-11",
            ComplianceProfile::Nist80053,
            "Audit record retention data must be classified",
            &[
                "retention_policy",
                "log_retention",
                "audit_archive",
                "record_retention",
            ],
            Severity::Warning,
        ),
        hardcoded_credential_rule(
            "NIST-AU-13",
            ComplianceProfile::Nist80053,
            "No hardcoded monitoring parameters",
            &[
                "monitor_target",
                "surveillance_addr",
                "monitoring_endpoint",
                "alert_destination",
            ],
            Severity::Warning,
        ),
        sensitive_let_rule(
            "NIST-AU-14",
            ComplianceProfile::Nist80053,
            "Session audit data must be classified",
            &[
                "session_audit",
                "session_record",
                "session_log",
                "user_session_data",
            ],
            Severity::Warning,
        ),
        classify_without_audit_rule(
            "NIST-AU-16",
            ComplianceProfile::Nist80053,
            "Cross-org audit must produce events",
            Severity::Warning,
        ),
        // IA (Identification/Authentication) family
        auth_crypto_rule(
            "NIST-IA-2",
            ComplianceProfile::Nist80053,
            "User identification must use Crypto effect",
            &["identify_user", "user_auth", "mfa_verify", "identity_check"],
            Severity::Error,
        ),
        auth_crypto_rule(
            "NIST-IA-3",
            ComplianceProfile::Nist80053,
            "Device identification must use Crypto effect",
            &[
                "device_auth",
                "machine_auth",
                "device_verify",
                "hardware_auth",
            ],
            Severity::Error,
        ),
        sensitive_let_rule(
            "NIST-IA-4",
            ComplianceProfile::Nist80053,
            "Identifier management data must be classified",
            &[
                "user_id",
                "identity_record",
                "credential_store",
                "identity_db",
            ],
            Severity::Error,
        ),
        hardcoded_credential_rule(
            "NIST-IA-7",
            ComplianceProfile::Nist80053,
            "No hardcoded cryptographic module auth",
            &["module_key", "hsm_pin", "crypto_module_pass", "fips_key"],
            Severity::Error,
        ),
        auth_crypto_rule(
            "NIST-IA-8",
            ComplianceProfile::Nist80053,
            "Non-org user identification must use Crypto",
            &[
                "external_auth",
                "partner_auth",
                "federated_login",
                "guest_auth",
            ],
            Severity::Error,
        ),
        sensitive_let_rule(
            "NIST-IA-9",
            ComplianceProfile::Nist80053,
            "Service identification data must be classified",
            &[
                "service_id",
                "service_credential",
                "api_identity",
                "service_cert",
            ],
            Severity::Error,
        ),
        hardcoded_credential_rule(
            "NIST-IA-10",
            ComplianceProfile::Nist80053,
            "No hardcoded adaptive identification data",
            &[
                "risk_score",
                "trust_level",
                "auth_strength",
                "assurance_level",
            ],
            Severity::Warning,
        ),
        sensitive_let_rule(
            "NIST-IA-11",
            ComplianceProfile::Nist80053,
            "Re-authentication data must be classified",
            &[
                "reauth_token",
                "session_refresh",
                "revalidation_key",
                "auth_renewal",
            ],
            Severity::Error,
        ),
        temporal_no_expiry_rule(
            "NIST-IA-12",
            ComplianceProfile::Nist80053,
            "Identity proofing must have temporal handling",
            &[
                "identity_proof_date",
                "verification_date",
                "proofing_timestamp",
                "enrollment_date",
            ],
            Severity::Warning,
        ),
        // SC (System/Communications) family
        sensitive_let_rule(
            "NIST-SC-2",
            ComplianceProfile::Nist80053,
            "Application partitioning data must be classified",
            &[
                "partition_key",
                "boundary_data",
                "separation_token",
                "domain_boundary",
            ],
            Severity::Warning,
        ),
        insecure_url_rule(
            "NIST-SC-7",
            ComplianceProfile::Nist80053,
            "Boundary protection: HTTPS required",
            Severity::Error,
        ),
        sensitive_network_send_rule(
            "NIST-SC-8-1",
            ComplianceProfile::Nist80053,
            "Transmission integrity must not leak data",
            &[
                "integrity_data",
                "transit_hash",
                "message_digest",
                "checksum_data",
            ],
            Severity::Error,
        ),
        sensitive_let_rule(
            "NIST-SC-10",
            ComplianceProfile::Nist80053,
            "Network disconnect data must be classified",
            &[
                "session_timeout",
                "disconnect_timer",
                "idle_timeout",
                "connection_limit",
            ],
            Severity::Warning,
        ),
        sensitive_let_rule(
            "NIST-SC-15",
            ComplianceProfile::Nist80053,
            "Collaborative computing data must be classified",
            &[
                "collab_session",
                "shared_workspace",
                "remote_desktop",
                "screen_share",
            ],
            Severity::Warning,
        ),
        sensitive_let_rule(
            "NIST-SC-17",
            ComplianceProfile::Nist80053,
            "PKI certificates must be classified",
            &[
                "pki_cert",
                "ca_cert",
                "root_cert",
                "certificate_chain",
                "tls_cert",
            ],
            Severity::Error,
        ),
        sensitive_let_rule(
            "NIST-SC-18",
            ComplianceProfile::Nist80053,
            "Mobile code must be classified",
            &["mobile_code", "applet", "script_payload", "dynamic_code"],
            Severity::Warning,
        ),
        sensitive_network_send_rule(
            "NIST-SC-19",
            ComplianceProfile::Nist80053,
            "VoIP data must not leak classified info",
            &["voip_data", "sip_credential", "voice_stream", "media_key"],
            Severity::Warning,
        ),
        sensitive_let_rule(
            "NIST-SC-20",
            ComplianceProfile::Nist80053,
            "DNS data must be classified (DNSSEC)",
            &["dns_key", "dnssec_key", "zone_key", "resolver_key"],
            Severity::Error,
        ),
        sensitive_let_rule(
            "NIST-SC-23",
            ComplianceProfile::Nist80053,
            "Session authenticity data must be classified",
            &["session_token", "csrf_token", "session_key", "auth_cookie"],
            Severity::Error,
        ),
        hardcoded_credential_rule(
            "NIST-SC-26",
            ComplianceProfile::Nist80053,
            "No hardcoded honeypot credentials",
            &[
                "honeypot_key",
                "decoy_credential",
                "canary_token",
                "trap_password",
            ],
            Severity::Warning,
        ),
        sensitive_let_rule(
            "NIST-SC-29",
            ComplianceProfile::Nist80053,
            "Heterogeneity data must be classified",
            &[
                "platform_config",
                "diversity_key",
                "heterogeneous_data",
                "variant_config",
            ],
            Severity::Warning,
        ),
        sensitive_let_rule(
            "NIST-SC-36",
            ComplianceProfile::Nist80053,
            "Distributed processing data must be classified",
            &[
                "distributed_key",
                "cluster_token",
                "node_credential",
                "replica_key",
            ],
            Severity::Error,
        ),
        // SI (System Integrity) family
        tainted_input_rule(
            "NIST-SI-3",
            ComplianceProfile::Nist80053,
            "Malicious code protection: input must be taint-tracked",
            &[
                "upload_data",
                "attachment_data",
                "downloaded_file",
                "external_binary",
            ],
            Severity::Error,
        ),
        debug_code_rule(
            "NIST-SI-4",
            ComplianceProfile::Nist80053,
            "System monitoring: no debug code in production",
            Severity::Warning,
        ),
        tainted_input_rule(
            "NIST-SI-5",
            ComplianceProfile::Nist80053,
            "Security alert input must be taint-tracked",
            &[
                "alert_input",
                "advisory_data",
                "threat_feed",
                "vulnerability_report",
            ],
            Severity::Warning,
        ),
        ffi_review_rule(
            "NIST-SI-7",
            ComplianceProfile::Nist80053,
            "Software integrity: FFI calls require verification",
            Severity::Error,
        ),
        tainted_input_rule(
            "NIST-SI-11",
            ComplianceProfile::Nist80053,
            "Error handling input must be taint-tracked",
            &["error_input", "exception_data", "fault_data", "crash_dump"],
            Severity::Warning,
        ),
        hardcoded_ip_rule(
            "NIST-SI-12",
            ComplianceProfile::Nist80053,
            "Information handling: no hardcoded addresses",
            Severity::Warning,
        ),
        tainted_input_rule(
            "NIST-SI-14",
            ComplianceProfile::Nist80053,
            "Non-persistence: input must be taint-tracked",
            &[
                "volatile_input",
                "ephemeral_data",
                "temp_input",
                "scratch_data",
            ],
            Severity::Warning,
        ),
        tainted_input_rule(
            "NIST-SI-16",
            ComplianceProfile::Nist80053,
            "Memory protection: input must be validated",
            &["memory_input", "buffer_data", "stack_input", "heap_data"],
            Severity::Error,
        ),
        // CM (Configuration Management) family
        insecure_default_rule(
            "NIST-CM-2",
            ComplianceProfile::Nist80053,
            "Baseline configuration must be enabled",
            &[
                "baseline_config",
                "system_baseline",
                "config_standard",
                "hardened_config",
            ],
            Severity::Error,
        ),
        hardcoded_credential_rule(
            "NIST-CM-3",
            ComplianceProfile::Nist80053,
            "No hardcoded configuration change control data",
            &[
                "change_key",
                "config_token",
                "deployment_key",
                "release_credential",
            ],
            Severity::Warning,
        ),
        insecure_default_rule(
            "NIST-CM-7",
            ComplianceProfile::Nist80053,
            "Least functionality: unnecessary features disabled",
            &["feature_flag", "optional_service", "debug_mode", "dev_mode"],
            Severity::Warning,
        ),
        // SA (System Acquisition) family
        sensitive_ffi_rule(
            "NIST-SA-4",
            ComplianceProfile::Nist80053,
            "Acquisition process: FFI calls in procurement need review",
            &[
                "vendor",
                "supplier",
                "third_party",
                "acquisition",
                "procurement",
            ],
            Severity::Warning,
        ),
        sensitive_ffi_rule(
            "NIST-SA-9",
            ComplianceProfile::Nist80053,
            "External system services: FFI calls need review",
            &[
                "external_service",
                "cloud_service",
                "saas",
                "outsourced",
                "managed",
            ],
            Severity::Warning,
        ),
    ]
}

// ===========================================================================
// ISO 27001 rules (18)
// ===========================================================================

fn iso27001_rules() -> Vec<ComplianceRule> {
    vec![
        sensitive_let_rule(
            "ISO-A5.1",
            ComplianceProfile::Iso27001,
            "Sensitive data must be classified as Secret",
            &["sensitive", "confidential", "restricted", "internal"],
            Severity::Error,
        ),
        hardcoded_credential_rule(
            "ISO-A6.1",
            ComplianceProfile::Iso27001,
            "No hardcoded credentials",
            &["password", "token", "credential", "api_key"],
            Severity::Error,
        ),
        declassify_prove_rule(
            "ISO-A8.1",
            ComplianceProfile::Iso27001,
            "Asset declassification requires Prove guard",
            Severity::Error,
        ),
        auth_crypto_rule(
            "ISO-A9.1",
            ComplianceProfile::Iso27001,
            "Access control functions must use Crypto",
            &["authenticate", "authorize", "login", "verify"],
            Severity::Error,
        ),
        weak_crypto_rule(
            "ISO-A10.1",
            ComplianceProfile::Iso27001,
            "Weak cryptographic algorithms prohibited",
            Severity::Error,
        ),
        audit_trail_rule(
            "ISO-A12.1",
            ComplianceProfile::Iso27001,
            "Operations security: audit trail required",
            Severity::Warning,
        ),
        insecure_network_rule(
            "ISO-A13.1",
            ComplianceProfile::Iso27001,
            "Communications security: secure channel required",
            Severity::Error,
        ),
        ffi_review_rule(
            "ISO-A14.1",
            ComplianceProfile::Iso27001,
            "System acquisition: FFI calls require review",
            Severity::Warning,
        ),
        trivial_handle_rule(
            "ISO-A16.1",
            ComplianceProfile::Iso27001,
            "Incident management: errors must not be swallowed",
            Severity::Warning,
        ),
        insecure_url_rule(
            "ISO-A18.1",
            ComplianceProfile::Iso27001,
            "Compliance: URLs must use HTTPS",
            Severity::Warning,
        ),
        // --- 8 new rules ---
        hardcoded_ip_rule(
            "ISO-A5.2",
            ComplianceProfile::Iso27001,
            "No hardcoded IPs in information systems",
            Severity::Warning,
        ),
        debug_code_rule(
            "ISO-A7.1",
            ComplianceProfile::Iso27001,
            "No debug code in production",
            Severity::Warning,
        ),
        insecure_default_rule(
            "ISO-A8.2",
            ComplianceProfile::Iso27001,
            "Security defaults must be enabled",
            &[
                "encryption_enabled",
                "access_control",
                "audit_enabled",
                "secure_mode",
                "tls_required",
            ],
            Severity::Error,
        ),
        hardcoded_port_rule(
            "ISO-A9.2",
            ComplianceProfile::Iso27001,
            "No hardcoded ports in information systems",
            Severity::Warning,
        ),
        temporal_no_expiry_rule(
            "ISO-A11.1",
            ComplianceProfile::Iso27001,
            "Data must have retention handling",
            &[
                "classification_date",
                "review_date",
                "access_granted_date",
                "cert_expiry",
                "policy_date",
            ],
            Severity::Warning,
        ),
        tainted_input_rule(
            "ISO-A12.2",
            ComplianceProfile::Iso27001,
            "External input must be taint-tracked",
            &["user_input", "external_data", "api_input", "form_data"],
            Severity::Error,
        ),
        excessive_grant_rule(
            "ISO-A15.1",
            ComplianceProfile::Iso27001,
            "Supplier grants must be minimal",
            Severity::Warning,
        ),
        sensitive_ffi_rule(
            "ISO-A17.1",
            ComplianceProfile::Iso27001,
            "FFI calls in continuity planning need review",
            &["backup", "recovery", "restore", "continuity", "disaster"],
            Severity::Warning,
        ),
        // --- 40 new ISO 27001 rules ---
        // A.5 Information Security Policies
        insecure_default_rule(
            "ISO-A5.3",
            ComplianceProfile::Iso27001,
            "Security policy enforcement must be enabled",
            &[
                "policy_enforcement",
                "security_policy",
                "compliance_check",
                "policy_active",
            ],
            Severity::Error,
        ),
        sensitive_let_rule(
            "ISO-A5.4",
            ComplianceProfile::Iso27001,
            "Policy review data must be classified",
            &[
                "policy_review",
                "policy_document",
                "security_directive",
                "governance_data",
            ],
            Severity::Warning,
        ),
        hardcoded_credential_rule(
            "ISO-A5.5",
            ComplianceProfile::Iso27001,
            "No hardcoded policy parameters",
            &[
                "policy_key",
                "compliance_token",
                "governance_credential",
                "policy_secret",
            ],
            Severity::Warning,
        ),
        // A.6 Organization of Information Security
        sensitive_let_rule(
            "ISO-A6.2",
            ComplianceProfile::Iso27001,
            "Mobile/telework data must be classified",
            &[
                "mobile_data",
                "telework_data",
                "remote_access_data",
                "byod_data",
            ],
            Severity::Error,
        ),
        sensitive_let_rule(
            "ISO-A6.3",
            ComplianceProfile::Iso27001,
            "Contact with authorities data must be classified",
            &[
                "authority_contact",
                "regulator_data",
                "incident_report_data",
                "law_enforcement",
            ],
            Severity::Warning,
        ),
        auth_crypto_rule(
            "ISO-A6.4",
            ComplianceProfile::Iso27001,
            "Special interest group auth must use Crypto",
            &[
                "group_auth",
                "community_login",
                "forum_auth",
                "consortium_verify",
            ],
            Severity::Warning,
        ),
        sensitive_let_rule(
            "ISO-A6.5",
            ComplianceProfile::Iso27001,
            "Project management security data must be classified",
            &[
                "project_secret",
                "project_credential",
                "dev_key",
                "project_token",
            ],
            Severity::Error,
        ),
        // A.7 Human Resource Security
        sensitive_let_rule(
            "ISO-A7.2",
            ComplianceProfile::Iso27001,
            "HR security data must be classified",
            &["employee_data", "staff_record", "hr_data", "personnel_file"],
            Severity::Error,
        ),
        hardcoded_credential_rule(
            "ISO-A7.3",
            ComplianceProfile::Iso27001,
            "No hardcoded HR credentials",
            &[
                "hr_password",
                "personnel_key",
                "employee_token",
                "staff_credential",
            ],
            Severity::Error,
        ),
        temporal_no_expiry_rule(
            "ISO-A7.4",
            ComplianceProfile::Iso27001,
            "Termination dates must have time handling",
            &[
                "termination_date",
                "contract_end",
                "employment_end",
                "offboard_date",
            ],
            Severity::Warning,
        ),
        // A.8 Asset Management
        sensitive_let_rule(
            "ISO-A8.3",
            ComplianceProfile::Iso27001,
            "Media handling data must be classified",
            &[
                "media_data",
                "removable_media",
                "backup_media",
                "archive_media",
            ],
            Severity::Warning,
        ),
        sensitive_let_rule(
            "ISO-A8.4",
            ComplianceProfile::Iso27001,
            "Asset return data must be classified",
            &[
                "asset_return",
                "equipment_data",
                "device_inventory",
                "asset_tracking",
            ],
            Severity::Warning,
        ),
        classify_without_audit_rule(
            "ISO-A8.5",
            ComplianceProfile::Iso27001,
            "Asset classification changes must be audited",
            Severity::Warning,
        ),
        sensitive_let_rule(
            "ISO-A8.6",
            ComplianceProfile::Iso27001,
            "Information labeling data must be classified",
            &[
                "label_data",
                "classification_label",
                "marking_data",
                "sensitivity_label",
            ],
            Severity::Warning,
        ),
        hardcoded_credential_rule(
            "ISO-A8.7",
            ComplianceProfile::Iso27001,
            "No hardcoded asset disposal credentials",
            &[
                "disposal_key",
                "wipe_credential",
                "sanitize_token",
                "decommission_key",
            ],
            Severity::Warning,
        ),
        // A.9 Access Control
        sensitive_let_rule(
            "ISO-A9.3",
            ComplianceProfile::Iso27001,
            "User access provisioning data must be classified",
            &[
                "provisioning_data",
                "access_grant",
                "role_provision",
                "entitlement_data",
            ],
            Severity::Error,
        ),
        sensitive_let_rule(
            "ISO-A9.4",
            ComplianceProfile::Iso27001,
            "Access rights review data must be classified",
            &[
                "access_review",
                "entitlement_review",
                "privilege_audit",
                "rights_review",
            ],
            Severity::Warning,
        ),
        hardcoded_credential_rule(
            "ISO-A9.5",
            ComplianceProfile::Iso27001,
            "No hardcoded access management secrets",
            &[
                "access_password",
                "admin_key",
                "root_credential",
                "superuser_token",
            ],
            Severity::Error,
        ),
        insecure_default_rule(
            "ISO-A9.6",
            ComplianceProfile::Iso27001,
            "Secure logon procedures must be enabled",
            &[
                "logon_secure",
                "login_policy",
                "auth_enforced",
                "mfa_required",
            ],
            Severity::Error,
        ),
        broad_grant_rule(
            "ISO-A9.7",
            ComplianceProfile::Iso27001,
            "Privilege management: overly broad grants flagged",
            Severity::Warning,
        ),
        // A.10 Cryptography
        sensitive_let_rule(
            "ISO-A10.2",
            ComplianceProfile::Iso27001,
            "Key management data must be classified",
            &["key_management", "key_store", "key_escrow", "key_archive"],
            Severity::Error,
        ),
        sensitive_let_rule(
            "ISO-A10.3",
            ComplianceProfile::Iso27001,
            "Encryption policy data must be classified",
            &[
                "encryption_policy",
                "crypto_standard",
                "cipher_config",
                "algorithm_config",
            ],
            Severity::Warning,
        ),
        hardcoded_credential_rule(
            "ISO-A10.4",
            ComplianceProfile::Iso27001,
            "No hardcoded cryptographic material",
            &[
                "master_key",
                "key_material",
                "crypto_seed",
                "key_derivation",
            ],
            Severity::Error,
        ),
        declassify_prove_rule(
            "ISO-A10.5",
            ComplianceProfile::Iso27001,
            "Key declassification requires Prove guard",
            Severity::Error,
        ),
        // A.11 Physical/Environmental (logical checks)
        sensitive_let_rule(
            "ISO-A11.2",
            ComplianceProfile::Iso27001,
            "Equipment security data must be classified",
            &[
                "equipment_data",
                "hardware_config",
                "facility_data",
                "physical_access",
            ],
            Severity::Warning,
        ),
        hardcoded_ip_rule(
            "ISO-A11.3",
            ComplianceProfile::Iso27001,
            "No hardcoded facility addresses",
            Severity::Warning,
        ),
        // A.12 Operations Security
        sensitive_let_rule(
            "ISO-A12.3",
            ComplianceProfile::Iso27001,
            "Capacity management data must be classified",
            &[
                "capacity_data",
                "resource_usage",
                "performance_data",
                "utilization_data",
            ],
            Severity::Warning,
        ),
        audit_trail_rule(
            "ISO-A12.4",
            ComplianceProfile::Iso27001,
            "Logging and monitoring must produce audit trail",
            Severity::Warning,
        ),
        insecure_default_rule(
            "ISO-A12.5",
            ComplianceProfile::Iso27001,
            "Operational software controls must be enabled",
            &[
                "software_install",
                "change_control",
                "release_mgmt",
                "deployment_control",
            ],
            Severity::Warning,
        ),
        ffi_review_rule(
            "ISO-A12.6",
            ComplianceProfile::Iso27001,
            "Technical vulnerability mgmt: FFI calls need review",
            Severity::Warning,
        ),
        // A.13 Communications Security
        sensitive_network_send_rule(
            "ISO-A13.2",
            ComplianceProfile::Iso27001,
            "Information transfer must not leak classified data",
            &[
                "transfer_data",
                "exchange_data",
                "shared_data",
                "exported_data",
            ],
            Severity::Error,
        ),
        insecure_network_rule(
            "ISO-A13.3",
            ComplianceProfile::Iso27001,
            "Electronic messaging must use secure channel",
            Severity::Error,
        ),
        sensitive_let_rule(
            "ISO-A13.4",
            ComplianceProfile::Iso27001,
            "Confidentiality agreement data must be classified",
            &[
                "nda_data",
                "confidentiality_agreement",
                "disclosure_data",
                "secrecy_data",
            ],
            Severity::Warning,
        ),
        // A.14 System Acquisition/Development
        tainted_input_rule(
            "ISO-A14.2",
            ComplianceProfile::Iso27001,
            "Application input must be taint-tracked",
            &[
                "app_input",
                "service_input",
                "transaction_input",
                "business_input",
            ],
            Severity::Error,
        ),
        sensitive_let_rule(
            "ISO-A14.3",
            ComplianceProfile::Iso27001,
            "Test data must be classified",
            &["test_data", "sample_data", "mock_data", "fixture_data"],
            Severity::Warning,
        ),
        unbounded_recursion_rule(
            "ISO-A14.4",
            ComplianceProfile::Iso27001,
            "System development: recursion must have base case",
            Severity::Warning,
        ),
        // A.15 Supplier Relationships
        sensitive_ffi_rule(
            "ISO-A15.2",
            ComplianceProfile::Iso27001,
            "Supplier service delivery FFI needs review",
            &[
                "supplier",
                "vendor",
                "contractor",
                "outsource",
                "third_party",
            ],
            Severity::Warning,
        ),
        sensitive_let_rule(
            "ISO-A15.3",
            ComplianceProfile::Iso27001,
            "ICT supply chain data must be classified",
            &[
                "supply_chain",
                "vendor_data",
                "procurement_data",
                "supplier_credential",
            ],
            Severity::Error,
        ),
        // A.16 Incident Management
        sensitive_let_rule(
            "ISO-A16.2",
            ComplianceProfile::Iso27001,
            "Security event data must be classified",
            &[
                "security_event",
                "incident_data",
                "breach_data",
                "alert_data",
            ],
            Severity::Error,
        ),
        temporal_no_expiry_rule(
            "ISO-A16.3",
            ComplianceProfile::Iso27001,
            "Incident response times must have temporal handling",
            &[
                "incident_time",
                "response_time",
                "breach_date",
                "detection_time",
            ],
            Severity::Warning,
        ),
        // A.18 Compliance
        sensitive_let_rule(
            "ISO-A18.2",
            ComplianceProfile::Iso27001,
            "Privacy compliance data must be classified",
            &["privacy_data", "pii", "personal_data", "data_subject"],
            Severity::Error,
        ),
    ]
}

// ===========================================================================
// DO-178C rules (18)
// ===========================================================================

fn do178c_rules() -> Vec<ComplianceRule> {
    vec![
        unbounded_recursion_rule(
            "DO178C-6.3.1",
            ComplianceProfile::Do178c,
            "Low-level requirements traceability: recursion must have base case",
            Severity::Error,
        ),
        ComplianceRule {
            id: "DO178C-6.3.2",
            profile: ComplianceProfile::Do178c,
            description: "Dead code detection: Unit in non-terminal Let value",
            check: Box::new(|expr| {
                if let Expr::Let(name, _, value, body) = expr {
                    if matches!(value.as_ref(), Expr::Unit) && !matches!(body.as_ref(), Expr::Unit)
                    {
                        return Some(ComplianceViolation {
                            rule_id: "DO178C-6.3.2",
                            profile: ComplianceProfile::Do178c,
                            message: format!("Potential dead code: '{}' bound to Unit with non-trivial continuation", name),
                            severity: Severity::Warning,
                        });
                    }
                }
                None
            }),
        },
        ffi_review_rule(
            "DO178C-6.3.3",
            ComplianceProfile::Do178c,
            "Source code traceability: FFI calls require review",
            Severity::Error,
        ),
        trivial_handle_rule(
            "DO178C-6.4.1",
            ComplianceProfile::Do178c,
            "Test coverage: error handlers must not be trivial",
            Severity::Error,
        ),
        declassify_prove_rule(
            "DO178C-6.4.2",
            ComplianceProfile::Do178c,
            "Decision coverage: declassification requires Prove guard",
            Severity::Error,
        ),
        weak_crypto_rule(
            "DO178C-6.4.3",
            ComplianceProfile::Do178c,
            "MC/DC: weak crypto in safety-critical system",
            Severity::Error,
        ),
        sensitive_let_rule(
            "DO178C-6.4.4",
            ComplianceProfile::Do178c,
            "Data flow: flight data must be classified",
            &[
                "flight",
                "altitude",
                "airspeed",
                "navigation",
                "sensor_data",
            ],
            Severity::Error,
        ),
        broad_grant_rule(
            "DO178C-6.4.5",
            ComplianceProfile::Do178c,
            "Control flow: overly broad grants in safety system",
            Severity::Error,
        ),
        hardcoded_credential_rule(
            "DO178C-6.7.1",
            ComplianceProfile::Do178c,
            "Stack usage: no hardcoded safety-critical values",
            &[
                "altitude_limit",
                "speed_limit",
                "threshold",
                "max_altitude",
                "min_speed",
            ],
            Severity::Warning,
        ),
        insecure_network_rule(
            "DO178C-6.7.2",
            ComplianceProfile::Do178c,
            "Aviation systems must use secure communication channels",
            Severity::Error,
        ),
        // --- 8 new rules ---
        hardcoded_ip_rule(
            "DO178C-6.3.4",
            ComplianceProfile::Do178c,
            "No hardcoded IPs in avionics",
            Severity::Warning,
        ),
        debug_code_rule(
            "DO178C-6.3.5",
            ComplianceProfile::Do178c,
            "No debug code in safety-critical systems",
            Severity::Error,
        ),
        insecure_default_rule(
            "DO178C-6.4.6",
            ComplianceProfile::Do178c,
            "Safety defaults must be enabled",
            &[
                "safety_enabled",
                "redundancy_active",
                "failsafe_mode",
                "monitoring_enabled",
                "watchdog_active",
            ],
            Severity::Error,
        ),
        hardcoded_port_rule(
            "DO178C-6.4.7",
            ComplianceProfile::Do178c,
            "No hardcoded ports in avionics",
            Severity::Warning,
        ),
        temporal_no_expiry_rule(
            "DO178C-6.4.8",
            ComplianceProfile::Do178c,
            "Flight data must have temporal handling",
            &[
                "flight_time",
                "sensor_timestamp",
                "calibration_date",
                "maintenance_date",
                "inspection_date",
            ],
            Severity::Warning,
        ),
        tainted_input_rule(
            "DO178C-6.7.3",
            ComplianceProfile::Do178c,
            "Sensor input must be taint-tracked",
            &[
                "sensor_input",
                "pilot_input",
                "radar_data",
                "telemetry_input",
            ],
            Severity::Error,
        ),
        excessive_grant_rule(
            "DO178C-6.7.4",
            ComplianceProfile::Do178c,
            "Excessive grants in safety system",
            Severity::Error,
        ),
        sensitive_ffi_rule(
            "DO178C-6.7.5",
            ComplianceProfile::Do178c,
            "FFI in safety-critical code needs review",
            &["flight", "navigation", "autopilot", "engine", "control"],
            Severity::Error,
        ),
        // --- 30 new DO-178C rules ---
        // 6.3.x Software Coding
        sensitive_let_rule(
            "DO178C-6.3.6",
            ComplianceProfile::Do178c,
            "Avionics configuration data must be classified",
            &[
                "avionics_config",
                "system_config",
                "aircraft_config",
                "mission_config",
            ],
            Severity::Error,
        ),
        hardcoded_credential_rule(
            "DO178C-6.3.7",
            ComplianceProfile::Do178c,
            "No hardcoded safety parameters",
            &[
                "safety_limit",
                "warning_threshold",
                "caution_limit",
                "alert_value",
            ],
            Severity::Warning,
        ),
        insecure_url_rule(
            "DO178C-6.3.8",
            ComplianceProfile::Do178c,
            "Avionics data links must use HTTPS",
            Severity::Error,
        ),
        auth_crypto_rule(
            "DO178C-6.3.9",
            ComplianceProfile::Do178c,
            "Avionics auth must use Crypto effect",
            &["pilot_auth", "crew_auth", "maintenance_auth", "ground_auth"],
            Severity::Error,
        ),
        sensitive_let_rule(
            "DO178C-6.3.10",
            ComplianceProfile::Do178c,
            "Flight plan data must be classified",
            &["flight_plan", "route_data", "waypoint", "trajectory"],
            Severity::Error,
        ),
        sensitive_let_rule(
            "DO178C-6.3.11",
            ComplianceProfile::Do178c,
            "Engine control data must be classified",
            &["engine_data", "thrust_data", "fuel_data", "propulsion_data"],
            Severity::Error,
        ),
        insecure_default_rule(
            "DO178C-6.3.12",
            ComplianceProfile::Do178c,
            "Safety interlocks must be enabled",
            &[
                "interlock_enabled",
                "safety_lock",
                "arm_safety",
                "inhibit_active",
            ],
            Severity::Error,
        ),
        classify_without_audit_rule(
            "DO178C-6.3.13",
            ComplianceProfile::Do178c,
            "Safety data classification must be audited",
            Severity::Error,
        ),
        // 6.4.x Integration Testing
        sensitive_let_rule(
            "DO178C-6.4.9",
            ComplianceProfile::Do178c,
            "Test coverage data must be classified",
            &[
                "coverage_data",
                "test_result",
                "mc_dc_data",
                "branch_coverage",
            ],
            Severity::Warning,
        ),
        sensitive_let_rule(
            "DO178C-6.4.10",
            ComplianceProfile::Do178c,
            "Requirement traceability data must be classified",
            &[
                "traceability_data",
                "requirement_link",
                "trace_matrix",
                "verification_data",
            ],
            Severity::Warning,
        ),
        tainted_input_rule(
            "DO178C-6.4.11",
            ComplianceProfile::Do178c,
            "Hardware interface input must be taint-tracked",
            &["hardware_input", "bus_data", "arinc_input", "can_data"],
            Severity::Error,
        ),
        hardcoded_credential_rule(
            "DO178C-6.4.12",
            ComplianceProfile::Do178c,
            "No hardcoded test parameters",
            &[
                "test_limit",
                "pass_threshold",
                "tolerance_value",
                "acceptance_criteria",
            ],
            Severity::Warning,
        ),
        trivial_handle_rule(
            "DO178C-6.4.13",
            ComplianceProfile::Do178c,
            "Safety error paths must not be trivial",
            Severity::Error,
        ),
        sensitive_network_send_rule(
            "DO178C-6.4.14",
            ComplianceProfile::Do178c,
            "Flight data must not leak over network",
            &[
                "flight_data",
                "avionics_data",
                "safety_data",
                "mission_data",
            ],
            Severity::Error,
        ),
        insecure_default_rule(
            "DO178C-6.4.15",
            ComplianceProfile::Do178c,
            "Test mode must be disabled in production",
            &["test_mode", "simulation_mode", "debug_flight", "bench_mode"],
            Severity::Error,
        ),
        audit_trail_rule(
            "DO178C-6.4.16",
            ComplianceProfile::Do178c,
            "Safety testing must produce audit trail",
            Severity::Warning,
        ),
        // 6.7.x Verification
        sensitive_let_rule(
            "DO178C-6.7.6",
            ComplianceProfile::Do178c,
            "Verification evidence data must be classified",
            &[
                "evidence_data",
                "proof_data",
                "certification_data",
                "qualification_data",
            ],
            Severity::Warning,
        ),
        tainted_input_rule(
            "DO178C-6.7.7",
            ComplianceProfile::Do178c,
            "Ground station input must be taint-tracked",
            &["ground_input", "atc_input", "datalink_input", "uplink_data"],
            Severity::Error,
        ),
        sensitive_let_rule(
            "DO178C-6.7.8",
            ComplianceProfile::Do178c,
            "Redundancy management data must be classified",
            &[
                "redundancy_data",
                "backup_system",
                "failover_data",
                "standby_data",
            ],
            Severity::Error,
        ),
        hardcoded_ip_rule(
            "DO178C-6.7.9",
            ComplianceProfile::Do178c,
            "No hardcoded network addresses in avionics",
            Severity::Warning,
        ),
        hardcoded_port_rule(
            "DO178C-6.7.10",
            ComplianceProfile::Do178c,
            "No hardcoded ports in avionics comm",
            Severity::Warning,
        ),
        weak_crypto_rule(
            "DO178C-6.7.11",
            ComplianceProfile::Do178c,
            "Weak crypto prohibited in avionics data protection",
            Severity::Error,
        ),
        unbounded_recursion_rule(
            "DO178C-6.7.12",
            ComplianceProfile::Do178c,
            "Safety algorithms must have bounded recursion",
            Severity::Error,
        ),
        declassify_prove_rule(
            "DO178C-6.7.13",
            ComplianceProfile::Do178c,
            "Safety data declassification requires Prove guard",
            Severity::Error,
        ),
        // 6.8.x Configuration Management
        sensitive_let_rule(
            "DO178C-6.8.1",
            ComplianceProfile::Do178c,
            "Configuration identification data must be classified",
            &["config_id", "version_data", "baseline_data", "build_config"],
            Severity::Warning,
        ),
        temporal_no_expiry_rule(
            "DO178C-6.8.2",
            ComplianceProfile::Do178c,
            "Configuration change dates must have temporal handling",
            &[
                "change_date",
                "release_date",
                "certification_date",
                "approval_date",
            ],
            Severity::Warning,
        ),
        hardcoded_credential_rule(
            "DO178C-6.8.3",
            ComplianceProfile::Do178c,
            "No hardcoded configuration management credentials",
            &[
                "config_password",
                "release_key",
                "build_token",
                "deploy_credential",
            ],
            Severity::Warning,
        ),
        insecure_default_rule(
            "DO178C-6.8.4",
            ComplianceProfile::Do178c,
            "Configuration control must be enabled",
            &[
                "config_control",
                "change_control",
                "version_control",
                "baseline_lock",
            ],
            Severity::Error,
        ),
        sensitive_ffi_rule(
            "DO178C-6.8.5",
            ComplianceProfile::Do178c,
            "Configuration tool FFI needs review",
            &["config_tool", "build_tool", "release_tool", "deploy_tool"],
            Severity::Warning,
        ),
        ffi_review_rule(
            "DO178C-6.8.6",
            ComplianceProfile::Do178c,
            "Problem reporting FFI calls require review",
            Severity::Warning,
        ),
    ]
}

// ===========================================================================
// SOX rules (15)
// ===========================================================================

fn sox_rules() -> Vec<ComplianceRule> {
    vec![
        sensitive_let_rule(
            "SOX-302-1",
            ComplianceProfile::Sox,
            "Financial data must be classified as Secret",
            &[
                "revenue",
                "profit",
                "earnings",
                "financial_report",
                "balance_sheet",
            ],
            Severity::Error,
        ),
        auth_crypto_rule(
            "SOX-302-2",
            ComplianceProfile::Sox,
            "Financial system auth must use Crypto",
            &[
                "financial_auth",
                "accounting_login",
                "audit_verify",
                "reporting_auth",
            ],
            Severity::Error,
        ),
        audit_trail_rule(
            "SOX-404-1",
            ComplianceProfile::Sox,
            "Financial operations must have audit trail",
            Severity::Error,
        ),
        hardcoded_credential_rule(
            "SOX-404-2",
            ComplianceProfile::Sox,
            "No hardcoded financial data",
            &[
                "revenue_amount",
                "profit_margin",
                "earning_value",
                "balance_total",
            ],
            Severity::Warning,
        ),
        trivial_handle_rule(
            "SOX-409-1",
            ComplianceProfile::Sox,
            "Financial error handling must not be swallowed",
            Severity::Error,
        ),
        declassify_prove_rule(
            "SOX-802-1",
            ComplianceProfile::Sox,
            "Financial data declassification requires Prove guard",
            Severity::Error,
        ),
        insecure_network_rule(
            "SOX-906-1",
            ComplianceProfile::Sox,
            "Financial reporting must use secure channel",
            Severity::Error,
        ),
        broad_grant_rule(
            "SOX-1102-1",
            ComplianceProfile::Sox,
            "Broad grants in financial system require review",
            Severity::Warning,
        ),
        // --- 7 new rules ---
        hardcoded_ip_rule(
            "SOX-302-3",
            ComplianceProfile::Sox,
            "No hardcoded IPs in financial reporting",
            Severity::Warning,
        ),
        debug_code_rule(
            "SOX-302-4",
            ComplianceProfile::Sox,
            "No debug code in financial systems",
            Severity::Warning,
        ),
        insecure_default_rule(
            "SOX-404-3",
            ComplianceProfile::Sox,
            "Financial security defaults must be enabled",
            &[
                "audit_enabled",
                "reporting_secure",
                "internal_control",
                "sox_compliance",
                "review_required",
            ],
            Severity::Error,
        ),
        hardcoded_port_rule(
            "SOX-404-4",
            ComplianceProfile::Sox,
            "No hardcoded ports in financial systems",
            Severity::Warning,
        ),
        temporal_no_expiry_rule(
            "SOX-409-2",
            ComplianceProfile::Sox,
            "Financial records need retention handling",
            &[
                "report_date",
                "filing_date",
                "audit_date",
                "fiscal_period",
                "statement_date",
            ],
            Severity::Warning,
        ),
        tainted_input_rule(
            "SOX-802-2",
            ComplianceProfile::Sox,
            "Financial input must be taint-tracked",
            &[
                "financial_input",
                "accounting_input",
                "report_data",
                "audit_input",
            ],
            Severity::Error,
        ),
        excessive_grant_rule(
            "SOX-906-2",
            ComplianceProfile::Sox,
            "Excessive grants in financial context",
            Severity::Warning,
        ),
        // --- 3 new SOX rules ---
        sensitive_ffi_rule(
            "SOX-302-5",
            ComplianceProfile::Sox,
            "FFI in financial reporting needs review",
            &["financial", "accounting", "reporting", "audit", "ledger"],
            Severity::Warning,
        ),
        classify_without_audit_rule(
            "SOX-404-5",
            ComplianceProfile::Sox,
            "Financial data classification must be audited",
            Severity::Warning,
        ),
        sensitive_network_send_rule(
            "SOX-906-3",
            ComplianceProfile::Sox,
            "Financial data must not leak over network",
            &[
                "financial_report",
                "earnings_data",
                "revenue_data",
                "balance_data",
            ],
            Severity::Error,
        ),
    ]
}

// ===========================================================================
// CMMC rules (12)
// ===========================================================================

fn cmmc_rules() -> Vec<ComplianceRule> {
    vec![
        sensitive_let_rule(
            "CMMC-AC-1",
            ComplianceProfile::Cmmc,
            "CUI must be classified as Secret",
            &["cui", "controlled_unclassified", "fouo", "sensitive_but"],
            Severity::Error,
        ),
        hardcoded_credential_rule(
            "CMMC-AC-2",
            ComplianceProfile::Cmmc,
            "No hardcoded credentials in defense systems",
            &["password", "token", "credential", "api_key"],
            Severity::Error,
        ),
        insecure_network_rule(
            "CMMC-SC-1",
            ComplianceProfile::Cmmc,
            "Defense systems must use secure channels",
            Severity::Error,
        ),
        weak_crypto_rule(
            "CMMC-SC-2",
            ComplianceProfile::Cmmc,
            "Weak crypto prohibited in defense systems",
            Severity::Error,
        ),
        ffi_review_rule(
            "CMMC-SI-1",
            ComplianceProfile::Cmmc,
            "FFI calls require security review in defense context",
            Severity::Warning,
        ),
        audit_trail_rule(
            "CMMC-AU-1",
            ComplianceProfile::Cmmc,
            "Security operations must have audit trail",
            Severity::Warning,
        ),
        // --- 6 new rules ---
        hardcoded_ip_rule(
            "CMMC-AC-3",
            ComplianceProfile::Cmmc,
            "No hardcoded IPs in defense systems",
            Severity::Warning,
        ),
        debug_code_rule(
            "CMMC-AC-4",
            ComplianceProfile::Cmmc,
            "No debug code in defense systems",
            Severity::Warning,
        ),
        insecure_default_rule(
            "CMMC-SC-3",
            ComplianceProfile::Cmmc,
            "Security defaults in defense context",
            &[
                "fips_enabled",
                "encryption_required",
                "cmmc_mode",
                "secure_boot",
                "access_control",
            ],
            Severity::Error,
        ),
        hardcoded_port_rule(
            "CMMC-SC-4",
            ComplianceProfile::Cmmc,
            "No hardcoded ports in defense systems",
            Severity::Warning,
        ),
        temporal_no_expiry_rule(
            "CMMC-SI-2",
            ComplianceProfile::Cmmc,
            "CUI must have retention handling",
            &[
                "classification_date",
                "cui_created",
                "access_granted",
                "clearance_date",
                "review_date",
            ],
            Severity::Warning,
        ),
        excessive_grant_rule(
            "CMMC-AU-2",
            ComplianceProfile::Cmmc,
            "Excessive grants in defense systems",
            Severity::Warning,
        ),
        // --- 50 new CMMC rules ---
        // AC (Access Control) domain
        sensitive_let_rule(
            "CMMC-AC-5",
            ComplianceProfile::Cmmc,
            "CUI access data must be classified",
            &["access_list", "acl", "permission_data", "clearance_data"],
            Severity::Error,
        ),
        sensitive_let_rule(
            "CMMC-AC-6",
            ComplianceProfile::Cmmc,
            "Information flow enforcement data must be classified",
            &[
                "flow_control",
                "data_flow",
                "boundary_data",
                "transfer_rule",
            ],
            Severity::Error,
        ),
        insecure_default_rule(
            "CMMC-AC-7",
            ComplianceProfile::Cmmc,
            "Separation of duties must be enabled",
            &[
                "duty_separation",
                "role_separation",
                "function_isolation",
                "privilege_separation",
            ],
            Severity::Error,
        ),
        hardcoded_credential_rule(
            "CMMC-AC-8",
            ComplianceProfile::Cmmc,
            "No hardcoded login attempt limits in defense",
            &[
                "max_attempts",
                "lockout_count",
                "failed_login_limit",
                "account_lockout",
            ],
            Severity::Warning,
        ),
        sensitive_let_rule(
            "CMMC-AC-9",
            ComplianceProfile::Cmmc,
            "Session data must be classified",
            &[
                "session_data",
                "session_token",
                "session_key",
                "active_session",
            ],
            Severity::Error,
        ),
        sensitive_network_send_rule(
            "CMMC-AC-10",
            ComplianceProfile::Cmmc,
            "CUI must not be leaked over network",
            &["cui", "controlled_unclassified", "fouo", "sensitive_data"],
            Severity::Error,
        ),
        insecure_default_rule(
            "CMMC-AC-11",
            ComplianceProfile::Cmmc,
            "Remote access controls must be enabled",
            &[
                "remote_access",
                "vpn_enabled",
                "remote_auth",
                "telework_secure",
            ],
            Severity::Error,
        ),
        sensitive_let_rule(
            "CMMC-AC-12",
            ComplianceProfile::Cmmc,
            "Wireless access data must be classified",
            &[
                "wireless_key",
                "wifi_credential",
                "wireless_data",
                "radio_key",
            ],
            Severity::Error,
        ),
        sensitive_let_rule(
            "CMMC-AC-13",
            ComplianceProfile::Cmmc,
            "Mobile device data must be classified",
            &[
                "mobile_device",
                "mobile_key",
                "device_credential",
                "mdm_data",
            ],
            Severity::Error,
        ),
        broad_grant_rule(
            "CMMC-AC-14",
            ComplianceProfile::Cmmc,
            "Access control for CUI: overly broad grants flagged",
            Severity::Error,
        ),
        // AT (Awareness/Training) domain
        sensitive_let_rule(
            "CMMC-AT-1",
            ComplianceProfile::Cmmc,
            "Training records must be classified",
            &[
                "training_record",
                "awareness_data",
                "certification_data",
                "training_log",
            ],
            Severity::Warning,
        ),
        sensitive_let_rule(
            "CMMC-AT-2",
            ComplianceProfile::Cmmc,
            "Role-based training data must be classified",
            &[
                "role_training",
                "security_training",
                "insider_threat_training",
                "cyber_training",
            ],
            Severity::Warning,
        ),
        // AU (Audit) domain
        audit_trail_rule(
            "CMMC-AU-3",
            ComplianceProfile::Cmmc,
            "CUI access must produce audit events",
            Severity::Error,
        ),
        classify_without_audit_rule(
            "CMMC-AU-4",
            ComplianceProfile::Cmmc,
            "Classification changes must be audited",
            Severity::Warning,
        ),
        sensitive_let_rule(
            "CMMC-AU-5",
            ComplianceProfile::Cmmc,
            "Audit log data must be classified",
            &["audit_log", "security_log", "event_log", "access_log"],
            Severity::Error,
        ),
        temporal_no_expiry_rule(
            "CMMC-AU-6",
            ComplianceProfile::Cmmc,
            "Audit timestamps must have temporal handling",
            &["audit_timestamp", "log_time", "event_time", "record_date"],
            Severity::Warning,
        ),
        insecure_default_rule(
            "CMMC-AU-7",
            ComplianceProfile::Cmmc,
            "Audit failure response must be enabled",
            &["audit_alert", "log_overflow", "audit_failure", "log_alert"],
            Severity::Error,
        ),
        // CM (Configuration Management) domain
        insecure_default_rule(
            "CMMC-CM-1",
            ComplianceProfile::Cmmc,
            "Baseline configuration must be enabled",
            &[
                "baseline_config",
                "system_config",
                "hardened_config",
                "standard_config",
            ],
            Severity::Error,
        ),
        hardcoded_credential_rule(
            "CMMC-CM-2",
            ComplianceProfile::Cmmc,
            "No hardcoded configuration management data",
            &[
                "config_key",
                "deployment_credential",
                "change_token",
                "release_key",
            ],
            Severity::Warning,
        ),
        insecure_default_rule(
            "CMMC-CM-3",
            ComplianceProfile::Cmmc,
            "Least functionality: unused features disabled",
            &[
                "feature_enabled",
                "optional_module",
                "debug_enabled",
                "test_mode",
            ],
            Severity::Warning,
        ),
        sensitive_let_rule(
            "CMMC-CM-4",
            ComplianceProfile::Cmmc,
            "Software inventory data must be classified",
            &[
                "software_inventory",
                "installed_software",
                "software_list",
                "app_catalog",
            ],
            Severity::Warning,
        ),
        // IA (Identification/Authentication) domain
        auth_crypto_rule(
            "CMMC-IA-1",
            ComplianceProfile::Cmmc,
            "Defense user auth must use Crypto effect",
            &[
                "defense_auth",
                "dod_login",
                "military_verify",
                "cleared_auth",
            ],
            Severity::Error,
        ),
        auth_crypto_rule(
            "CMMC-IA-2",
            ComplianceProfile::Cmmc,
            "Device authentication must use Crypto",
            &[
                "device_auth",
                "machine_auth",
                "endpoint_verify",
                "hardware_auth",
            ],
            Severity::Error,
        ),
        hardcoded_credential_rule(
            "CMMC-IA-3",
            ComplianceProfile::Cmmc,
            "No hardcoded authenticator data",
            &["authenticator", "mfa_secret", "totp_seed", "auth_token"],
            Severity::Error,
        ),
        sensitive_let_rule(
            "CMMC-IA-4",
            ComplianceProfile::Cmmc,
            "Identity management data must be classified",
            &[
                "identity_data",
                "credential_store",
                "identity_db",
                "user_registry",
            ],
            Severity::Error,
        ),
        temporal_no_expiry_rule(
            "CMMC-IA-5",
            ComplianceProfile::Cmmc,
            "Authentication data must have temporal handling",
            &[
                "auth_expiry",
                "token_expiry",
                "credential_date",
                "cert_valid",
            ],
            Severity::Warning,
        ),
        sensitive_let_rule(
            "CMMC-IA-6",
            ComplianceProfile::Cmmc,
            "Authenticator feedback data must be classified",
            &[
                "auth_feedback",
                "login_response",
                "auth_result",
                "verification_result",
            ],
            Severity::Warning,
        ),
        sensitive_let_rule(
            "CMMC-IA-7",
            ComplianceProfile::Cmmc,
            "Cryptographic module auth data must be classified",
            &["crypto_module", "hsm_data", "fips_module", "tamper_data"],
            Severity::Error,
        ),
        auth_crypto_rule(
            "CMMC-IA-8",
            ComplianceProfile::Cmmc,
            "Non-org user auth must use Crypto",
            &[
                "external_auth",
                "contractor_login",
                "partner_verify",
                "visitor_auth",
            ],
            Severity::Error,
        ),
        // IR (Incident Response) domain
        sensitive_let_rule(
            "CMMC-IR-1",
            ComplianceProfile::Cmmc,
            "Incident response data must be classified",
            &[
                "incident_data",
                "breach_data",
                "security_event",
                "threat_data",
            ],
            Severity::Error,
        ),
        audit_trail_rule(
            "CMMC-IR-2",
            ComplianceProfile::Cmmc,
            "Incident handling must produce audit trail",
            Severity::Error,
        ),
        temporal_no_expiry_rule(
            "CMMC-IR-3",
            ComplianceProfile::Cmmc,
            "Incident timestamps must have temporal handling",
            &[
                "incident_time",
                "breach_date",
                "detection_time",
                "response_time",
            ],
            Severity::Warning,
        ),
        // MA (Maintenance) domain
        sensitive_let_rule(
            "CMMC-MA-1",
            ComplianceProfile::Cmmc,
            "Maintenance data must be classified",
            &[
                "maintenance_data",
                "service_record",
                "repair_data",
                "patch_data",
            ],
            Severity::Warning,
        ),
        ffi_review_rule(
            "CMMC-MA-2",
            ComplianceProfile::Cmmc,
            "Maintenance FFI calls require review",
            Severity::Warning,
        ),
        // MP (Media Protection) domain
        sensitive_let_rule(
            "CMMC-MP-1",
            ComplianceProfile::Cmmc,
            "Media protection data must be classified",
            &[
                "media_data",
                "storage_data",
                "removable_media",
                "backup_media",
            ],
            Severity::Error,
        ),
        declassify_prove_rule(
            "CMMC-MP-2",
            ComplianceProfile::Cmmc,
            "CUI media declassification requires Prove guard",
            Severity::Error,
        ),
        // PE (Physical/Environmental) domain
        sensitive_let_rule(
            "CMMC-PE-1",
            ComplianceProfile::Cmmc,
            "Physical access data must be classified",
            &[
                "physical_access",
                "badge_data",
                "facility_data",
                "entry_data",
            ],
            Severity::Warning,
        ),
        hardcoded_ip_rule(
            "CMMC-PE-2",
            ComplianceProfile::Cmmc,
            "No hardcoded facility addresses",
            Severity::Warning,
        ),
        // PS (Personnel Security) domain
        sensitive_let_rule(
            "CMMC-PS-1",
            ComplianceProfile::Cmmc,
            "Personnel screening data must be classified",
            &[
                "screening_data",
                "background_check",
                "clearance_data",
                "vetting_data",
            ],
            Severity::Error,
        ),
        // RA (Risk Assessment) domain
        sensitive_let_rule(
            "CMMC-RA-1",
            ComplianceProfile::Cmmc,
            "Risk assessment data must be classified",
            &[
                "risk_data",
                "threat_assessment",
                "vulnerability_data",
                "risk_score",
            ],
            Severity::Warning,
        ),
        tainted_input_rule(
            "CMMC-RA-2",
            ComplianceProfile::Cmmc,
            "Vulnerability scan input must be taint-tracked",
            &[
                "scan_input",
                "vulnerability_input",
                "threat_feed",
                "risk_input",
            ],
            Severity::Warning,
        ),
        // RE (Recovery) domain
        sensitive_let_rule(
            "CMMC-RE-1",
            ComplianceProfile::Cmmc,
            "Backup data must be classified",
            &[
                "backup_data",
                "recovery_data",
                "restore_point",
                "snapshot_data",
            ],
            Severity::Error,
        ),
        sensitive_ffi_rule(
            "CMMC-RE-2",
            ComplianceProfile::Cmmc,
            "Recovery FFI calls need review",
            &["backup", "restore", "recovery", "disaster", "failover"],
            Severity::Warning,
        ),
        // SC (System/Communications) domain
        sensitive_let_rule(
            "CMMC-SC-5",
            ComplianceProfile::Cmmc,
            "Boundary protection data must be classified",
            &[
                "boundary_data",
                "firewall_rule",
                "dmz_config",
                "perimeter_data",
            ],
            Severity::Error,
        ),
        insecure_url_rule(
            "CMMC-SC-6",
            ComplianceProfile::Cmmc,
            "CUI communications must use HTTPS",
            Severity::Error,
        ),
        sensitive_network_send_rule(
            "CMMC-SC-7",
            ComplianceProfile::Cmmc,
            "Transmission must not leak CUI",
            &[
                "cui_data",
                "controlled_info",
                "defense_data",
                "classified_transit",
            ],
            Severity::Error,
        ),
        sensitive_let_rule(
            "CMMC-SC-8",
            ComplianceProfile::Cmmc,
            "Cryptographic key data must be classified",
            &[
                "crypto_key",
                "encryption_key",
                "signing_key",
                "key_material",
            ],
            Severity::Error,
        ),
        declassify_prove_rule(
            "CMMC-SC-9",
            ComplianceProfile::Cmmc,
            "Defense data declassification requires Prove guard",
            Severity::Error,
        ),
        // SI (System Integrity) domain
        tainted_input_rule(
            "CMMC-SI-3",
            ComplianceProfile::Cmmc,
            "Defense system input must be taint-tracked",
            &[
                "system_input",
                "command_input",
                "control_input",
                "operator_input",
            ],
            Severity::Error,
        ),
        sensitive_ffi_rule(
            "CMMC-SI-4",
            ComplianceProfile::Cmmc,
            "System monitoring FFI needs review",
            &["monitor", "surveillance", "ids", "intrusion", "detection"],
            Severity::Warning,
        ),
        trivial_handle_rule(
            "CMMC-SI-5",
            ComplianceProfile::Cmmc,
            "Defense error handling must not swallow errors",
            Severity::Error,
        ),
    ]
}

// ===========================================================================
// IEC 62443 rules (12)
// ===========================================================================

fn iec62443_rules() -> Vec<ComplianceRule> {
    vec![
        sensitive_let_rule(
            "IEC62443-SR-1",
            ComplianceProfile::Iec62443,
            "Industrial control data must be classified",
            &["scada", "plc", "hmi", "control_system", "sensor_data"],
            Severity::Error,
        ),
        insecure_network_rule(
            "IEC62443-SR-2",
            ComplianceProfile::Iec62443,
            "ICS communications must use secure channel",
            Severity::Error,
        ),
        hardcoded_credential_rule(
            "IEC62443-SR-3",
            ComplianceProfile::Iec62443,
            "No hardcoded ICS credentials",
            &["password", "token", "credential", "plc_key", "scada_pass"],
            Severity::Error,
        ),
        trivial_handle_rule(
            "IEC62443-SR-4",
            ComplianceProfile::Iec62443,
            "ICS error handling must not swallow errors",
            Severity::Error,
        ),
        ffi_review_rule(
            "IEC62443-SR-5",
            ComplianceProfile::Iec62443,
            "FFI calls in ICS require security review",
            Severity::Warning,
        ),
        weak_crypto_rule(
            "IEC62443-SR-6",
            ComplianceProfile::Iec62443,
            "Weak crypto prohibited in ICS",
            Severity::Error,
        ),
        // --- 6 new rules ---
        hardcoded_ip_rule(
            "IEC62443-SR-7",
            ComplianceProfile::Iec62443,
            "No hardcoded IPs in ICS",
            Severity::Warning,
        ),
        debug_code_rule(
            "IEC62443-SR-8",
            ComplianceProfile::Iec62443,
            "No debug code in ICS",
            Severity::Warning,
        ),
        insecure_default_rule(
            "IEC62443-SR-9",
            ComplianceProfile::Iec62443,
            "ICS security defaults must be enabled",
            &[
                "safety_enabled",
                "scada_secure",
                "plc_auth",
                "hmi_locked",
                "network_segmented",
            ],
            Severity::Error,
        ),
        hardcoded_port_rule(
            "IEC62443-SR-10",
            ComplianceProfile::Iec62443,
            "No hardcoded ports in ICS",
            Severity::Warning,
        ),
        temporal_no_expiry_rule(
            "IEC62443-SR-11",
            ComplianceProfile::Iec62443,
            "ICS data must have retention handling",
            &[
                "sensor_timestamp",
                "calibration_date",
                "maintenance_date",
                "alarm_time",
                "log_date",
            ],
            Severity::Warning,
        ),
        excessive_grant_rule(
            "IEC62443-SR-12",
            ComplianceProfile::Iec62443,
            "Excessive grants in ICS",
            Severity::Warning,
        ),
        // --- 20 new IEC 62443 rules ---
        auth_crypto_rule(
            "IEC62443-SR-13",
            ComplianceProfile::Iec62443,
            "ICS user auth must use Crypto effect",
            &["scada_auth", "plc_login", "hmi_auth", "operator_verify"],
            Severity::Error,
        ),
        declassify_prove_rule(
            "IEC62443-SR-14",
            ComplianceProfile::Iec62443,
            "ICS data declassification requires Prove guard",
            Severity::Error,
        ),
        audit_trail_rule(
            "IEC62443-SR-15",
            ComplianceProfile::Iec62443,
            "ICS operations must produce audit trail",
            Severity::Warning,
        ),
        sensitive_network_send_rule(
            "IEC62443-SR-16",
            ComplianceProfile::Iec62443,
            "ICS data must not leak over network",
            &["scada_data", "plc_data", "sensor_reading", "control_signal"],
            Severity::Error,
        ),
        tainted_input_rule(
            "IEC62443-SR-17",
            ComplianceProfile::Iec62443,
            "ICS operator input must be taint-tracked",
            &[
                "operator_input",
                "control_input",
                "setpoint_input",
                "command_input",
            ],
            Severity::Error,
        ),
        unbounded_recursion_rule(
            "IEC62443-SR-18",
            ComplianceProfile::Iec62443,
            "ICS control algorithms must have bounded recursion",
            Severity::Error,
        ),
        insecure_url_rule(
            "IEC62443-SR-19",
            ComplianceProfile::Iec62443,
            "ICS web interfaces must use HTTPS",
            Severity::Error,
        ),
        classify_without_audit_rule(
            "IEC62443-SR-20",
            ComplianceProfile::Iec62443,
            "ICS data classification must be audited",
            Severity::Warning,
        ),
        broad_grant_rule(
            "IEC62443-SR-21",
            ComplianceProfile::Iec62443,
            "ICS system grants must be minimal",
            Severity::Error,
        ),
        sensitive_let_rule(
            "IEC62443-SR-22",
            ComplianceProfile::Iec62443,
            "ICS network segmentation data must be classified",
            &["zone_data", "conduit_data", "segment_config", "dmz_config"],
            Severity::Error,
        ),
        sensitive_let_rule(
            "IEC62443-SR-23",
            ComplianceProfile::Iec62443,
            "Safety instrumented system data must be classified",
            &[
                "sis_data",
                "safety_system",
                "emergency_shutdown",
                "trip_data",
            ],
            Severity::Error,
        ),
        hardcoded_credential_rule(
            "IEC62443-SR-24",
            ComplianceProfile::Iec62443,
            "No hardcoded ICS maintenance credentials",
            &[
                "maintenance_key",
                "service_credential",
                "engineer_password",
                "tech_token",
            ],
            Severity::Error,
        ),
        sensitive_ffi_rule(
            "IEC62443-SR-25",
            ComplianceProfile::Iec62443,
            "ICS protocol FFI needs review",
            &["modbus", "profinet", "opc_ua", "dnp3", "iec61850"],
            Severity::Warning,
        ),
        sensitive_let_rule(
            "IEC62443-SR-26",
            ComplianceProfile::Iec62443,
            "ICS firmware data must be classified",
            &[
                "firmware_data",
                "plc_program",
                "ladder_logic",
                "control_program",
            ],
            Severity::Error,
        ),
        temporal_no_expiry_rule(
            "IEC62443-SR-27",
            ComplianceProfile::Iec62443,
            "ICS certificate dates must have temporal handling",
            &[
                "cert_expiry",
                "license_date",
                "calibration_due",
                "warranty_date",
            ],
            Severity::Warning,
        ),
        insecure_default_rule(
            "IEC62443-SR-28",
            ComplianceProfile::Iec62443,
            "ICS patch management must be enabled",
            &[
                "patch_mgmt",
                "update_enabled",
                "vulnerability_scan",
                "patch_policy",
            ],
            Severity::Warning,
        ),
        hardcoded_ip_rule(
            "IEC62443-SR-29",
            ComplianceProfile::Iec62443,
            "No hardcoded IPs in ICS network config",
            Severity::Warning,
        ),
        sensitive_let_rule(
            "IEC62443-SR-30",
            ComplianceProfile::Iec62443,
            "ICS incident response data must be classified",
            &[
                "ics_incident",
                "cyber_event",
                "control_breach",
                "safety_event",
            ],
            Severity::Error,
        ),
        auth_crypto_rule(
            "IEC62443-SR-31",
            ComplianceProfile::Iec62443,
            "ICS remote access must use Crypto",
            &["remote_access", "vpn_auth", "remote_maintenance", "dial_in"],
            Severity::Error,
        ),
        sensitive_let_rule(
            "IEC62443-SR-32",
            ComplianceProfile::Iec62443,
            "ICS backup data must be classified",
            &["ics_backup", "config_backup", "plc_backup", "restore_data"],
            Severity::Error,
        ),
    ]
}

// ===========================================================================
// NERC CIP rules (10)
// ===========================================================================

fn nerc_cip_rules() -> Vec<ComplianceRule> {
    vec![
        sensitive_let_rule(
            "NERC-CIP-004",
            ComplianceProfile::NercCip,
            "Grid/energy data must be classified as Secret",
            &[
                "grid",
                "substation",
                "generator",
                "transformer",
                "load_data",
            ],
            Severity::Error,
        ),
        insecure_network_rule(
            "NERC-CIP-005",
            ComplianceProfile::NercCip,
            "Energy grid communications must use secure channel",
            Severity::Error,
        ),
        hardcoded_credential_rule(
            "NERC-CIP-007",
            ComplianceProfile::NercCip,
            "No hardcoded energy system credentials",
            &["password", "token", "scada_key", "grid_pass"],
            Severity::Error,
        ),
        audit_trail_rule(
            "NERC-CIP-010",
            ComplianceProfile::NercCip,
            "Energy system operations must have audit trail",
            Severity::Warning,
        ),
        broad_grant_rule(
            "NERC-CIP-011",
            ComplianceProfile::NercCip,
            "Broad grants in energy systems require review",
            Severity::Warning,
        ),
        // --- 5 new rules ---
        hardcoded_ip_rule(
            "NERC-CIP-003",
            ComplianceProfile::NercCip,
            "No hardcoded IPs in energy grid",
            Severity::Warning,
        ),
        debug_code_rule(
            "NERC-CIP-006",
            ComplianceProfile::NercCip,
            "No debug code in energy systems",
            Severity::Warning,
        ),
        insecure_default_rule(
            "NERC-CIP-008",
            ComplianceProfile::NercCip,
            "Energy security defaults must be enabled",
            &[
                "grid_protection",
                "scada_secure",
                "monitoring_enabled",
                "alarm_active",
                "failsafe_mode",
            ],
            Severity::Error,
        ),
        hardcoded_port_rule(
            "NERC-CIP-009",
            ComplianceProfile::NercCip,
            "No hardcoded ports in grid systems",
            Severity::Warning,
        ),
        temporal_no_expiry_rule(
            "NERC-CIP-012",
            ComplianceProfile::NercCip,
            "Grid data must have retention handling",
            &[
                "outage_date",
                "maintenance_date",
                "inspection_date",
                "meter_timestamp",
                "load_date",
            ],
            Severity::Warning,
        ),
        // --- 10 new NERC CIP rules ---
        auth_crypto_rule(
            "NERC-CIP-013",
            ComplianceProfile::NercCip,
            "Grid operator auth must use Crypto",
            &[
                "grid_auth",
                "operator_login",
                "dispatcher_auth",
                "control_verify",
            ],
            Severity::Error,
        ),
        sensitive_let_rule(
            "NERC-CIP-014",
            ComplianceProfile::NercCip,
            "Physical security data must be classified",
            &[
                "physical_security",
                "perimeter_data",
                "facility_access",
                "camera_data",
            ],
            Severity::Warning,
        ),
        declassify_prove_rule(
            "NERC-CIP-015",
            ComplianceProfile::NercCip,
            "Grid data declassification requires Prove guard",
            Severity::Error,
        ),
        weak_crypto_rule(
            "NERC-CIP-016",
            ComplianceProfile::NercCip,
            "Weak crypto prohibited in energy systems",
            Severity::Error,
        ),
        tainted_input_rule(
            "NERC-CIP-017",
            ComplianceProfile::NercCip,
            "Grid control input must be taint-tracked",
            &[
                "grid_input",
                "dispatch_input",
                "load_input",
                "frequency_input",
            ],
            Severity::Error,
        ),
        sensitive_network_send_rule(
            "NERC-CIP-018",
            ComplianceProfile::NercCip,
            "Grid data must not leak over network",
            &["grid_data", "scada_data", "energy_data", "load_forecast"],
            Severity::Error,
        ),
        ffi_review_rule(
            "NERC-CIP-019",
            ComplianceProfile::NercCip,
            "Energy system FFI calls require review",
            Severity::Warning,
        ),
        classify_without_audit_rule(
            "NERC-CIP-020",
            ComplianceProfile::NercCip,
            "Grid data classification must be audited",
            Severity::Warning,
        ),
        unbounded_recursion_rule(
            "NERC-CIP-021",
            ComplianceProfile::NercCip,
            "Grid algorithms must have bounded recursion",
            Severity::Warning,
        ),
        sensitive_ffi_rule(
            "NERC-CIP-022",
            ComplianceProfile::NercCip,
            "Energy protocol FFI needs review",
            &["iec61850", "dnp3", "modbus", "iccp", "goose"],
            Severity::Warning,
        ),
    ]
}

// ===========================================================================
// FDA 21 CFR Part 11 rules (10)
// ===========================================================================

fn fda_rules() -> Vec<ComplianceRule> {
    vec![
        sensitive_let_rule(
            "FDA-11.10-a",
            ComplianceProfile::Fda21cfr,
            "Electronic health records must be classified",
            &[
                "patient_record",
                "drug_data",
                "clinical",
                "trial_data",
                "pharma",
            ],
            Severity::Error,
        ),
        auth_crypto_rule(
            "FDA-11.10-b",
            ComplianceProfile::Fda21cfr,
            "Clinical system auth must use Crypto",
            &["clinical_auth", "pharma_login", "drug_verify", "trial_auth"],
            Severity::Error,
        ),
        hardcoded_credential_rule(
            "FDA-11.10-c",
            ComplianceProfile::Fda21cfr,
            "No hardcoded clinical system credentials",
            &["password", "token", "credential", "pharma_key"],
            Severity::Error,
        ),
        audit_trail_rule(
            "FDA-11.10-d",
            ComplianceProfile::Fda21cfr,
            "Clinical operations must have audit trail",
            Severity::Error,
        ),
        insecure_network_rule(
            "FDA-11.10-e",
            ComplianceProfile::Fda21cfr,
            "Clinical data transmission must use secure channel",
            Severity::Error,
        ),
        // --- 5 new rules ---
        hardcoded_ip_rule(
            "FDA-11.10-f",
            ComplianceProfile::Fda21cfr,
            "No hardcoded IPs in pharma systems",
            Severity::Warning,
        ),
        debug_code_rule(
            "FDA-11.10-g",
            ComplianceProfile::Fda21cfr,
            "No debug code in clinical systems",
            Severity::Warning,
        ),
        insecure_default_rule(
            "FDA-11.10-h",
            ComplianceProfile::Fda21cfr,
            "Clinical security defaults must be enabled",
            &[
                "validation_enabled",
                "audit_trail",
                "electronic_sig",
                "access_control",
                "data_integrity",
            ],
            Severity::Error,
        ),
        hardcoded_port_rule(
            "FDA-11.10-i",
            ComplianceProfile::Fda21cfr,
            "No hardcoded ports in pharma systems",
            Severity::Warning,
        ),
        temporal_no_expiry_rule(
            "FDA-11.10-j",
            ComplianceProfile::Fda21cfr,
            "Clinical trial data must have retention handling",
            &[
                "trial_date",
                "batch_date",
                "expiry_date",
                "approval_date",
                "manufacturing_date",
            ],
            Severity::Warning,
        ),
        // --- 8 new FDA rules ---
        declassify_prove_rule(
            "FDA-11.10-k",
            ComplianceProfile::Fda21cfr,
            "Clinical data declassification requires Prove guard",
            Severity::Error,
        ),
        weak_crypto_rule(
            "FDA-11.10-l",
            ComplianceProfile::Fda21cfr,
            "Weak crypto prohibited in clinical systems",
            Severity::Error,
        ),
        tainted_input_rule(
            "FDA-11.10-m",
            ComplianceProfile::Fda21cfr,
            "Clinical input must be taint-tracked",
            &[
                "clinical_input",
                "patient_input",
                "lab_input",
                "trial_input",
            ],
            Severity::Error,
        ),
        sensitive_network_send_rule(
            "FDA-11.10-n",
            ComplianceProfile::Fda21cfr,
            "Clinical data must not leak over network",
            &["clinical_data", "trial_data", "patient_data", "drug_data"],
            Severity::Error,
        ),
        trivial_handle_rule(
            "FDA-11.50-a",
            ComplianceProfile::Fda21cfr,
            "Clinical error handling must not swallow errors",
            Severity::Error,
        ),
        classify_without_audit_rule(
            "FDA-11.50-b",
            ComplianceProfile::Fda21cfr,
            "Clinical data classification must be audited",
            Severity::Warning,
        ),
        sensitive_ffi_rule(
            "FDA-11.50-c",
            ComplianceProfile::Fda21cfr,
            "FFI in clinical systems needs review",
            &["clinical", "pharma", "drug", "trial", "lab"],
            Severity::Warning,
        ),
        unbounded_recursion_rule(
            "FDA-11.50-d",
            ComplianceProfile::Fda21cfr,
            "Clinical algorithms must have bounded recursion",
            Severity::Warning,
        ),
    ]
}

// ===========================================================================
// ITAR rules (8)
// ===========================================================================

fn itar_rules() -> Vec<ComplianceRule> {
    vec![
        sensitive_let_rule(
            "ITAR-120.1",
            ComplianceProfile::Itar,
            "Defense/munitions data must be classified as Secret",
            &[
                "munition",
                "weapon",
                "defense",
                "military",
                "export_controlled",
            ],
            Severity::Error,
        ),
        ffi_review_rule(
            "ITAR-120.2",
            ComplianceProfile::Itar,
            "FFI calls require ITAR compliance review",
            Severity::Error,
        ),
        insecure_network_rule(
            "ITAR-120.3",
            ComplianceProfile::Itar,
            "Defense data transmission must use secure channel",
            Severity::Error,
        ),
        broad_grant_rule(
            "ITAR-120.4",
            ComplianceProfile::Itar,
            "Broad grants in defense systems require review",
            Severity::Error,
        ),
        // --- 4 new rules ---
        hardcoded_ip_rule(
            "ITAR-120.5",
            ComplianceProfile::Itar,
            "No hardcoded IPs in defense export systems",
            Severity::Warning,
        ),
        debug_code_rule(
            "ITAR-120.6",
            ComplianceProfile::Itar,
            "No debug code in ITAR systems",
            Severity::Error,
        ),
        insecure_default_rule(
            "ITAR-120.7",
            ComplianceProfile::Itar,
            "Defense security defaults must be enabled",
            &[
                "export_control",
                "classification_enabled",
                "itar_mode",
                "dcs_required",
                "encryption_required",
            ],
            Severity::Error,
        ),
        hardcoded_port_rule(
            "ITAR-120.8",
            ComplianceProfile::Itar,
            "No hardcoded ports in defense systems",
            Severity::Warning,
        ),
        // --- 4 new ITAR rules ---
        declassify_prove_rule(
            "ITAR-121.1",
            ComplianceProfile::Itar,
            "Defense data declassification requires Prove guard",
            Severity::Error,
        ),
        sensitive_network_send_rule(
            "ITAR-121.2",
            ComplianceProfile::Itar,
            "Defense data must not leak over network",
            &["munition", "weapon", "defense_data", "military_data"],
            Severity::Error,
        ),
        hardcoded_credential_rule(
            "ITAR-121.3",
            ComplianceProfile::Itar,
            "No hardcoded ITAR credentials",
            &[
                "export_key",
                "munitions_credential",
                "defense_token",
                "itar_secret",
            ],
            Severity::Error,
        ),
        weak_crypto_rule(
            "ITAR-121.4",
            ComplianceProfile::Itar,
            "Weak crypto prohibited in ITAR systems",
            Severity::Error,
        ),
    ]
}

// ===========================================================================
// ESG/SDG rules (30)
// Environmental, Social, Governance / UN Sustainable Development Goals
// ===========================================================================

fn esg_sdg_rules() -> Vec<ComplianceRule> {
    vec![
        // --- SDG 3: Good Health and Well-being ---
        sensitive_let_rule(
            "ESG-SDG3.1",
            ComplianceProfile::EsgSdg,
            "Health outcome data must be classified",
            &[
                "health_outcome",
                "mortality_rate",
                "disease_prevalence",
                "wellness_metric",
            ],
            Severity::Error,
        ),
        audit_trail_rule(
            "ESG-SDG3.2",
            ComplianceProfile::EsgSdg,
            "Health impact operations require audit trail",
            Severity::Warning,
        ),
        // --- SDG 5: Gender Equality ---
        sensitive_let_rule(
            "ESG-SDG5.1",
            ComplianceProfile::EsgSdg,
            "Gender parity data must be classified",
            &[
                "gender_ratio",
                "pay_gap",
                "gender_parity",
                "diversity_metric",
                "inclusion_score",
            ],
            Severity::Error,
        ),
        declassify_prove_rule(
            "ESG-SDG5.2",
            ComplianceProfile::EsgSdg,
            "Declassification of diversity data requires Prove guard",
            Severity::Error,
        ),
        // --- SDG 7: Affordable and Clean Energy ---
        sensitive_let_rule(
            "ESG-SDG7.1",
            ComplianceProfile::EsgSdg,
            "Energy consumption data must be classified",
            &[
                "energy_consumption",
                "renewable_share",
                "carbon_intensity",
                "grid_emission",
            ],
            Severity::Error,
        ),
        temporal_no_expiry_rule(
            "ESG-SDG7.2",
            ComplianceProfile::EsgSdg,
            "Energy reporting periods must have temporal handling",
            &[
                "reporting_period",
                "measurement_date",
                "baseline_year",
                "target_year",
            ],
            Severity::Warning,
        ),
        // --- SDG 12: Responsible Consumption and Production ---
        sensitive_let_rule(
            "ESG-SDG12.1",
            ComplianceProfile::EsgSdg,
            "Waste and resource data must be classified",
            &[
                "waste_generated",
                "recycling_rate",
                "resource_usage",
                "circular_economy",
            ],
            Severity::Error,
        ),
        hardcoded_credential_rule(
            "ESG-SDG12.2",
            ComplianceProfile::EsgSdg,
            "No hardcoded supply chain credentials",
            &[
                "supply_chain_key",
                "vendor_credential",
                "audit_token",
                "certification_secret",
            ],
            Severity::Error,
        ),
        // --- SDG 13: Climate Action ---
        sensitive_let_rule(
            "ESG-SDG13.1",
            ComplianceProfile::EsgSdg,
            "Carbon emission data must be classified",
            &[
                "carbon_emission",
                "ghg_scope1",
                "ghg_scope2",
                "ghg_scope3",
                "carbon_offset",
            ],
            Severity::Error,
        ),
        insecure_default_rule(
            "ESG-SDG13.2",
            ComplianceProfile::EsgSdg,
            "Climate reporting defaults must be enabled",
            &[
                "climate_reporting",
                "emission_tracking",
                "carbon_accounting",
                "ghg_monitoring",
            ],
            Severity::Error,
        ),
        temporal_no_expiry_rule(
            "ESG-SDG13.3",
            ComplianceProfile::EsgSdg,
            "Climate targets must have temporal handling",
            &[
                "target_date",
                "baseline_date",
                "ndc_deadline",
                "paris_target",
            ],
            Severity::Warning,
        ),
        // --- SDG 16: Peace, Justice and Strong Institutions ---
        sensitive_let_rule(
            "ESG-SDG16.1",
            ComplianceProfile::EsgSdg,
            "Governance and transparency data must be classified",
            &[
                "governance_score",
                "corruption_index",
                "transparency_metric",
                "rule_of_law",
            ],
            Severity::Error,
        ),
        broad_grant_rule(
            "ESG-SDG16.2",
            ComplianceProfile::EsgSdg,
            "Overly broad grants undermine governance controls",
            Severity::Warning,
        ),
        // --- ESG Environmental (E) ---
        sensitive_let_rule(
            "ESG-E.1",
            ComplianceProfile::EsgSdg,
            "Environmental impact data must be classified",
            &[
                "biodiversity_loss",
                "water_usage",
                "deforestation",
                "pollution_level",
            ],
            Severity::Error,
        ),
        classify_without_audit_rule(
            "ESG-E.2",
            ComplianceProfile::EsgSdg,
            "Environmental classification must be audited (anti-greenwashing)",
            Severity::Warning,
        ),
        insecure_network_rule(
            "ESG-E.3",
            ComplianceProfile::EsgSdg,
            "Environmental data transmission must use secure channel",
            Severity::Error,
        ),
        // --- ESG Social (S) ---
        sensitive_let_rule(
            "ESG-S.1",
            ComplianceProfile::EsgSdg,
            "Labor rights data must be classified",
            &[
                "worker_safety",
                "labor_rights",
                "child_labor",
                "living_wage",
                "union_membership",
            ],
            Severity::Error,
        ),
        sensitive_network_send_rule(
            "ESG-S.2",
            ComplianceProfile::EsgSdg,
            "Social impact data must not leak over network",
            &[
                "worker_data",
                "community_impact",
                "human_rights",
                "labor_metric",
            ],
            Severity::Error,
        ),
        tainted_input_rule(
            "ESG-S.3",
            ComplianceProfile::EsgSdg,
            "Stakeholder input must be taint-tracked",
            &[
                "stakeholder_input",
                "community_feedback",
                "worker_complaint",
                "grievance_data",
            ],
            Severity::Error,
        ),
        // --- ESG Governance (G) ---
        auth_crypto_rule(
            "ESG-G.1",
            ComplianceProfile::EsgSdg,
            "ESG report auth must use Crypto",
            &[
                "esg_auth",
                "audit_login",
                "compliance_verify",
                "report_auth",
            ],
            Severity::Error,
        ),
        weak_crypto_rule(
            "ESG-G.2",
            ComplianceProfile::EsgSdg,
            "Weak crypto prohibited for ESG audit data",
            Severity::Error,
        ),
        hardcoded_ip_rule(
            "ESG-G.3",
            ComplianceProfile::EsgSdg,
            "No hardcoded IPs in ESG reporting systems",
            Severity::Warning,
        ),
        debug_code_rule(
            "ESG-G.4",
            ComplianceProfile::EsgSdg,
            "No debug code in ESG compliance systems",
            Severity::Warning,
        ),
        ffi_review_rule(
            "ESG-G.5",
            ComplianceProfile::EsgSdg,
            "FFI calls in ESG systems require review",
            Severity::Warning,
        ),
        trivial_handle_rule(
            "ESG-G.6",
            ComplianceProfile::EsgSdg,
            "ESG data handling errors must not be silently discarded",
            Severity::Warning,
        ),
        // --- SD VISta / Gold Standard alignment ---
        sensitive_let_rule(
            "ESG-SDVISTA.1",
            ComplianceProfile::EsgSdg,
            "Verified impact data must be classified (SD VISta)",
            &[
                "verified_impact",
                "sdvista_metric",
                "gold_standard",
                "verra_credit",
            ],
            Severity::Error,
        ),
        insecure_url_rule(
            "ESG-SDVISTA.2",
            ComplianceProfile::EsgSdg,
            "Impact verification URLs must use HTTPS",
            Severity::Error,
        ),
        hardcoded_credential_rule(
            "ESG-SDVISTA.3",
            ComplianceProfile::EsgSdg,
            "No hardcoded verification credentials",
            &[
                "registry_key",
                "verification_token",
                "carbon_credit_secret",
                "offset_credential",
            ],
            Severity::Error,
        ),
        excessive_grant_rule(
            "ESG-SDVISTA.4",
            ComplianceProfile::EsgSdg,
            "Excessive grants in verification systems flagged",
            Severity::Warning,
        ),
        insecure_default_rule(
            "ESG-SDVISTA.5",
            ComplianceProfile::EsgSdg,
            "Verification defaults must be enabled",
            &[
                "verification_enabled",
                "audit_required",
                "double_counting_check",
                "additionality_check",
            ],
            Severity::Error,
        ),
    ]
}


// ===========================================================================
// EU CRA rules (15) — Regulation (EU) 2024/2847, Annex I
//
// HONESTY SCOPE (do not widen in prose elsewhere): these are machine-checkable
// conditions DERIVED FROM Annex I's essential requirements, checked on the AST.
// Passing them is NOT CRA conformity — most CRA obligations (risk assessment,
// technical documentation, CE marking, the Art. 14 reporting duties) are
// organisational and live outside a compiler. The reporting-process side is
// documented in SECURITY.md; the SBOM/VEX side in scripts/generate-sbom.sh.
// Rule ids cite the Annex I part they derive from.
// ===========================================================================

fn cra_rules() -> Vec<ComplianceRule> {
    vec![
        // Part I §(2)(a): products made available with a secure-by-default
        // configuration.
        insecure_default_rule(
            "CRA-I.2a",
            ComplianceProfile::Cra,
            "Secure by default: security features must not ship disabled",
            &["encryption_enabled", "tls_enabled", "auth_enabled", "selamat"],
            Severity::Error,
        ),
        // Part I §(2)(d): protection from unauthorised access by appropriate
        // control mechanisms (authentication).
        auth_crypto_rule(
            "CRA-I.2d",
            ComplianceProfile::Cra,
            "Access-control functions must use the Crypto effect",
            &["auth", "login", "sahkan_pengguna", "verify_user"],
            Severity::Error,
        ),
        // Part I §(2)(e): confidentiality of stored data — encrypt at rest.
        sensitive_let_rule(
            "CRA-I.2e",
            ComplianceProfile::Cra,
            "Stored secrets/credentials must be classified",
            &["credential", "private_key", "kata_laluan", "secret_config"],
            Severity::Error,
        ),
        // Part I §(2)(e): confidentiality of transmitted data — secure channel.
        insecure_network_rule(
            "CRA-I.2e-net",
            ComplianceProfile::Cra,
            "Data in transit must use a secure channel (NetworkSecure)",
            Severity::Error,
        ),
        // Part I §(2)(e): no plaintext transport endpoints.
        insecure_url_rule(
            "CRA-I.2e-url",
            ComplianceProfile::Cra,
            "Plaintext http:// endpoints are prohibited",
            Severity::Error,
        ),
        // Part I §(2)(f): integrity of data, commands and configuration —
        // sensitive values must not leave over the network unprotected.
        sensitive_network_send_rule(
            "CRA-I.2f",
            ComplianceProfile::Cra,
            "Sensitive values must not be sent raw over the network",
            &["credential", "token", "kunci", "private_key"],
            Severity::Error,
        ),
        // Part I §(2)(g): process only data that is necessary (minimisation) —
        // raw external input must be sanitised before use.
        tainted_input_rule(
            "CRA-I.2g",
            ComplianceProfile::Cra,
            "External input must be sanitised before processing",
            &["user_input", "borang", "form_input", "request_body"],
            Severity::Error,
        ),
        // Part I §(2)(h)+(j): limit attack surfaces / least privilege.
        broad_grant_rule(
            "CRA-I.2h",
            ComplianceProfile::Cra,
            "Broad capability grants (System) violate attack-surface minimisation",
            Severity::Error,
        ),
        // Part I §(2)(i): resilience against denial-of-service.
        unbounded_recursion_rule(
            "CRA-I.2i",
            ComplianceProfile::Cra,
            "Unbounded recursion is a availability/DoS hazard",
            Severity::Warning,
        ),
        // Part I §(2)(l): record and monitor relevant internal activity
        // (security logging).
        audit_trail_rule(
            "CRA-I.2l",
            ComplianceProfile::Cra,
            "Security operations must leave an audit trail (Write effect)",
            Severity::Error,
        ),
        // Part I §(2)(m)/(c): security updates — update paths must verify
        // authenticity cryptographically.
        auth_crypto_rule(
            "CRA-I.2m",
            ComplianceProfile::Cra,
            "Update/download paths must verify signatures (Crypto effect)",
            &["update", "kemaskini", "upgrade", "firmware"],
            Severity::Error,
        ),
        // Part II §(3): vulnerability handling — no debug code in shipped
        // products (tested-before-release discipline).
        debug_code_rule(
            "CRA-II.3",
            ComplianceProfile::Cra,
            "Debug artifacts must not ship in a product placed on the market",
            Severity::Warning,
        ),
        // Part I §(2)(a) baseline: no known-weak cryptography.
        weak_crypto_rule(
            "CRA-I.2a-crypto",
            ComplianceProfile::Cra,
            "Known-weak algorithms (MD5/SHA1/DES/RC4) are prohibited",
            Severity::Error,
        ),
        // Part I §(2)(d): no hardcoded access credentials.
        hardcoded_credential_rule(
            "CRA-I.2d-cred",
            ComplianceProfile::Cra,
            "Hardcoded credentials defeat access-control requirements",
            &["password", "token", "api_key", "kata_laluan"],
            Severity::Error,
        ),
        // Part I §(2)(e): declassification of protected data requires proof.
        declassify_prove_rule(
            "CRA-I.2e-declass",
            ComplianceProfile::Cra,
            "Declassifying protected data requires an explicit proof",
            Severity::Error,
        ),
    ]
}


// ===========================================================================
// EU DORA rules (14) — Regulation (EU) 2022/2554
//
// SAME HONESTY SCOPE as the CRA block above: machine-checkable conditions
// DERIVED FROM DORA's ICT-risk articles, checked on the AST. Passing them is
// not DORA compliance — governance, testing programmes (Arts. 24-27), incident
// REPORTING (Arts. 17-23) and register-of-information duties are
// organisational. Chosen because REQ-33 selects fintech/payments as RIINA's
// primary vertical, whose EU deployments DORA has governed since 2025-01-17.
// Rule ids cite the article they derive from.
// ===========================================================================

fn dora_rules() -> Vec<ComplianceRule> {
    vec![
        // Art. 9(2): protection of ICT systems — security features on by default.
        insecure_default_rule(
            "DORA-9.2",
            ComplianceProfile::Dora,
            "ICT protection mechanisms must not ship disabled",
            &["encryption_enabled", "tls_enabled", "auth_enabled", "mfa_enabled"],
            Severity::Error,
        ),
        // Art. 9(3)(b): strong authentication mechanisms.
        auth_crypto_rule(
            "DORA-9.3b",
            ComplianceProfile::Dora,
            "Financial-system authentication must use the Crypto effect",
            &["auth", "login", "sahkan_pengguna", "payment_auth"],
            Severity::Error,
        ),
        // Art. 9(3)(c): data protected at rest.
        sensitive_let_rule(
            "DORA-9.3c",
            ComplianceProfile::Dora,
            "Financial secrets/credentials at rest must be classified",
            &["credential", "private_key", "account_secret", "kata_laluan"],
            Severity::Error,
        ),
        // Art. 9(3)(c): data protected in transit.
        insecure_network_rule(
            "DORA-9.3c-net",
            ComplianceProfile::Dora,
            "Financial data in transit must use a secure channel",
            Severity::Error,
        ),
        insecure_url_rule(
            "DORA-9.3c-url",
            ComplianceProfile::Dora,
            "Plaintext http:// endpoints are prohibited in ICT services",
            Severity::Error,
        ),
        // Art. 9(3)(a): integrity — sensitive values never leave raw.
        sensitive_network_send_rule(
            "DORA-9.3a",
            ComplianceProfile::Dora,
            "Sensitive financial values must not be sent raw over the network",
            &["credential", "token", "account", "iban"],
            Severity::Error,
        ),
        // Art. 9(4)(c): policies limiting access — least privilege.
        broad_grant_rule(
            "DORA-9.4c",
            ComplianceProfile::Dora,
            "Broad capability grants (System) violate least-privilege access",
            Severity::Error,
        ),
        // Art. 9(4)(c): temporal access control — keys/sessions must expire.
        temporal_no_expiry_rule(
            "DORA-9.4c-exp",
            ComplianceProfile::Dora,
            "Keys and sessions must carry an expiry (Time-effect check)",
            &["key_created", "session_created", "token_created"],
            Severity::Warning,
        ),
        // Art. 9(4)(d): cryptographic controls — no known-weak algorithms.
        weak_crypto_rule(
            "DORA-9.4d",
            ComplianceProfile::Dora,
            "Known-weak algorithms are prohibited in ICT risk controls",
            Severity::Error,
        ),
        // Art. 10: detection — anomalous-activity logging.
        audit_trail_rule(
            "DORA-10.1",
            ComplianceProfile::Dora,
            "Security operations must leave an audit trail for detection",
            Severity::Error,
        ),
        // Art. 9(1): availability/resilience of ICT systems.
        unbounded_recursion_rule(
            "DORA-9.1",
            ComplianceProfile::Dora,
            "Unbounded recursion is an ICT-availability hazard",
            Severity::Warning,
        ),
        // Art. 28: ICT third-party risk — every FFI boundary is third-party ICT.
        ffi_review_rule(
            "DORA-28.1",
            ComplianceProfile::Dora,
            "FFI crosses the ICT third-party boundary and requires review",
            Severity::Warning,
        ),
        // Art. 16(1): input from external sources sanitised before processing.
        tainted_input_rule(
            "DORA-16.1",
            ComplianceProfile::Dora,
            "External input must be sanitised before financial processing",
            &["user_input", "payment_input", "form_input", "request_body"],
            Severity::Error,
        ),
        // Art. 9(4)(a): no hardcoded access credentials in ICT assets.
        hardcoded_credential_rule(
            "DORA-9.4a",
            ComplianceProfile::Dora,
            "Hardcoded credentials violate ICT access-management policy",
            &["password", "token", "api_key", "account_secret"],
            Severity::Error,
        ),
    ]
}


// ===========================================================================
// EU NIS2 rules (13) — Directive (EU) 2022/2555, Art. 21(2)
//
// SAME HONESTY SCOPE as the CRA/DORA blocks: machine-checkable conditions
// DERIVED FROM the Art. 21(2) cybersecurity risk-management measures, checked
// on the AST. Passing them is not NIS2 compliance — governance (Art. 20),
// incident REPORTING to CSIRTs (Art. 23), and the registration duties are
// organisational. NIS2 is a DIRECTIVE: member-state transpositions vary; rule
// ids cite the Art. 21(2) measure they derive from.
// ===========================================================================

fn nis2_rules() -> Vec<ComplianceRule> {
    vec![
        // Art. 21(2)(b): incident handling — detection needs an audit trail.
        audit_trail_rule(
            "NIS2-21.2b",
            ComplianceProfile::Nis2,
            "Security operations must leave an audit trail for incident handling",
            Severity::Error,
        ),
        // Art. 21(2)(d): supply-chain security — FFI is a third-party boundary.
        ffi_review_rule(
            "NIS2-21.2d",
            ComplianceProfile::Nis2,
            "FFI crosses the supply-chain boundary and requires review",
            Severity::Warning,
        ),
        // Art. 21(2)(e): secure development & vulnerability handling.
        debug_code_rule(
            "NIS2-21.2e",
            ComplianceProfile::Nis2,
            "Debug artifacts must not reach production (secure development)",
            Severity::Warning,
        ),
        weak_crypto_rule(
            "NIS2-21.2e-crypto",
            ComplianceProfile::Nis2,
            "Known-weak algorithms are prohibited (secure development)",
            Severity::Error,
        ),
        // Art. 21(2)(g): basic cyber hygiene.
        insecure_default_rule(
            "NIS2-21.2g",
            ComplianceProfile::Nis2,
            "Security features must not ship disabled (cyber hygiene)",
            &["encryption_enabled", "tls_enabled", "auth_enabled", "mfa_enabled"],
            Severity::Error,
        ),
        hardcoded_credential_rule(
            "NIS2-21.2g-cred",
            ComplianceProfile::Nis2,
            "Hardcoded credentials violate basic cyber hygiene",
            &["password", "token", "api_key", "kata_laluan"],
            Severity::Error,
        ),
        // Art. 21(2)(h): cryptography & encryption policies.
        insecure_network_rule(
            "NIS2-21.2h-net",
            ComplianceProfile::Nis2,
            "Data in transit must use a secure channel (encryption policy)",
            Severity::Error,
        ),
        insecure_url_rule(
            "NIS2-21.2h-url",
            ComplianceProfile::Nis2,
            "Plaintext http:// endpoints are prohibited (encryption policy)",
            Severity::Error,
        ),
        sensitive_let_rule(
            "NIS2-21.2h-rest",
            ComplianceProfile::Nis2,
            "Secrets/credentials at rest must be classified (encryption policy)",
            &["credential", "private_key", "kata_laluan", "secret_config"],
            Severity::Error,
        ),
        // Art. 21(2)(i): access control — least privilege, no raw sensitive sends.
        broad_grant_rule(
            "NIS2-21.2i",
            ComplianceProfile::Nis2,
            "Broad capability grants (System) violate access-control policy",
            Severity::Error,
        ),
        sensitive_network_send_rule(
            "NIS2-21.2i-send",
            ComplianceProfile::Nis2,
            "Sensitive values must not be sent raw over the network",
            &["credential", "token", "kunci", "private_key"],
            Severity::Error,
        ),
        // Art. 21(2)(j): MFA / secured authentication.
        auth_crypto_rule(
            "NIS2-21.2j",
            ComplianceProfile::Nis2,
            "Authentication must use the Crypto effect (secured authentication)",
            &["auth", "login", "sahkan_pengguna", "verify_user"],
            Severity::Error,
        ),
        // Art. 21(1): availability of services (proportionate technical measures).
        unbounded_recursion_rule(
            "NIS2-21.1",
            ComplianceProfile::Nis2,
            "Unbounded recursion is an availability hazard",
            Severity::Warning,
        ),
    ]
}

// ===========================================================================
// Structural-walk regressions (silent-gap class)
//
// `any_child` is exhaustive, so a NEW `Expr` variant breaks the build rather
// than silently truncating every predicate. That catches omissions; it does
// NOT catch a listed-but-wrong arm — an arm that drops a child still compiles
// and still silently stops the walk.
//
// These tests close that half: for every container variant, a marker planted
// as a direct child must be found through it. Each predicate also gets a
// negative control, because a predicate that can only answer `true` would
// pass every positive assertion while checking nothing.
// ===========================================================================

#[cfg(test)]
mod walker_tests {
    use super::*;
    use riina_types::{BinOp as Op, SecurityLevel, SessionType, Ty};

    fn ty() -> Ty {
        Ty::Int
    }

    /// One entry per `Expr` variant that has sub-expressions: a label and a
    /// builder that plants `m` as a DIRECT child of that variant.
    fn wrappers(m: Expr) -> Vec<(&'static str, Expr)> {
        let b = |e: Expr| Box::new(e);
        let unit = || Box::new(Expr::Unit);
        vec![
            ("Lam", Expr::Lam("x".into(), ty(), b(m.clone()))),
            ("App/fn", Expr::App(b(m.clone()), unit())),
            ("App/arg", Expr::App(unit(), b(m.clone()))),
            ("Pair/l", Expr::Pair(b(m.clone()), unit())),
            ("Pair/r", Expr::Pair(unit(), b(m.clone()))),
            ("Fst", Expr::Fst(b(m.clone()))),
            ("Snd", Expr::Snd(b(m.clone()))),
            ("Inl", Expr::Inl(b(m.clone()), ty())),
            ("Inr", Expr::Inr(b(m.clone()), ty())),
            (
                "Case/scrutinee",
                Expr::Case(b(m.clone()), "x".into(), unit(), "y".into(), unit()),
            ),
            (
                "Case/left",
                Expr::Case(unit(), "x".into(), b(m.clone()), "y".into(), unit()),
            ),
            (
                "Case/right",
                Expr::Case(unit(), "x".into(), unit(), "y".into(), b(m.clone())),
            ),
            ("If/cond", Expr::If(b(m.clone()), unit(), unit())),
            ("If/then", Expr::If(unit(), b(m.clone()), unit())),
            ("If/else", Expr::If(unit(), unit(), b(m.clone()))),
            ("Let/value", Expr::Let("x".into(), None, b(m.clone()), unit())),
            ("Let/body", Expr::Let("x".into(), None, unit(), b(m.clone()))),
            // `pulang e` — the ordinary RIINA function body. This is the arm
            // whose absence made a correct effectful function scan as pure.
            ("Return", Expr::Return(b(m.clone()))),
            ("Perform", Expr::Perform(Effect::Read, b(m.clone()))),
            ("Handle/body", Expr::Handle(b(m.clone()), "x".into(), unit())),
            (
                "Handle/handler",
                Expr::Handle(unit(), "x".into(), b(m.clone())),
            ),
            ("Ref", Expr::Ref(b(m.clone()), SecurityLevel::Public)),
            ("Deref", Expr::Deref(b(m.clone()))),
            ("Assign/lhs", Expr::Assign(b(m.clone()), unit())),
            ("Assign/rhs", Expr::Assign(unit(), b(m.clone()))),
            ("Classify", Expr::Classify(b(m.clone()))),
            ("Declassify/value", Expr::Declassify(b(m.clone()), unit())),
            ("Declassify/proof", Expr::Declassify(unit(), b(m.clone()))),
            ("Prove", Expr::Prove(b(m.clone()))),
            ("Require", Expr::Require(Effect::Read, b(m.clone()))),
            ("Grant", Expr::Grant(Effect::Read, b(m.clone()))),
            (
                "LetRec/value",
                Expr::LetRec("f".into(), ty(), b(m.clone()), unit()),
            ),
            (
                "LetRec/body",
                Expr::LetRec("f".into(), ty(), unit(), b(m.clone())),
            ),
            (
                "LetRecGroup/member",
                Expr::LetRecGroup(vec![("f".into(), ty(), m.clone())], unit()),
            ),
            (
                "LetRecGroup/cont",
                Expr::LetRecGroup(vec![("f".into(), ty(), Expr::Unit)], b(m.clone())),
            ),
            ("BinOp/l", Expr::BinOp(Op::Add, b(m.clone()), unit())),
            ("BinOp/r", Expr::BinOp(Op::Add, unit(), b(m.clone()))),
            ("ListLit", Expr::ListLit(vec![Expr::Unit, m.clone()])),
            (
                "RecordLit",
                Expr::RecordLit("R".into(), vec![("f".into(), m.clone())]),
            ),
            ("FieldAccess", Expr::FieldAccess(b(m.clone()), "f".into())),
            (
                "FFICall",
                Expr::FFICall {
                    name: "ffi".into(),
                    args: vec![Expr::Unit, m.clone()],
                    ret_ty: ty(),
                },
            ),
            (
                "ActorDecl/init",
                Expr::ActorDecl {
                    name: "A".into(),
                    state_ty: ty(),
                    message_ty: ty(),
                    init_state: b(m.clone()),
                    handler: unit(),
                },
            ),
            (
                "ActorDecl/handler",
                Expr::ActorDecl {
                    name: "A".into(),
                    state_ty: ty(),
                    message_ty: ty(),
                    init_state: unit(),
                    handler: b(m.clone()),
                },
            ),
            ("Spawn/l", Expr::Spawn(b(m.clone()), unit())),
            ("Spawn/r", Expr::Spawn(unit(), b(m.clone()))),
            ("ActorSend/l", Expr::ActorSend(b(m.clone()), unit())),
            ("ActorSend/r", Expr::ActorSend(unit(), b(m.clone()))),
            ("ActorRecv", Expr::ActorRecv(b(m.clone()))),
            ("CRDTMerge/l", Expr::CRDTMerge(b(m.clone()), unit())),
            ("CRDTMerge/r", Expr::CRDTMerge(unit(), b(m.clone()))),
            ("ContentHash", Expr::ContentHash(b(m.clone()))),
            ("ContentVerify/l", Expr::ContentVerify(b(m.clone()), unit())),
            ("ContentVerify/r", Expr::ContentVerify(unit(), b(m.clone()))),
            ("ContractDeploy", Expr::ContractDeploy(b(m.clone()))),
            (
                "TokenTransfer/from",
                Expr::TokenTransfer {
                    from: b(m.clone()),
                    to: unit(),
                    amount: unit(),
                },
            ),
            (
                "TokenTransfer/to",
                Expr::TokenTransfer {
                    from: unit(),
                    to: b(m.clone()),
                    amount: unit(),
                },
            ),
            (
                "TokenTransfer/amount",
                Expr::TokenTransfer {
                    from: unit(),
                    to: unit(),
                    amount: b(m.clone()),
                },
            ),
            ("ZakatCalculate", Expr::ZakatCalculate(b(m.clone()))),
            ("UIDisplay", Expr::UIDisplay(vec![Expr::Unit, m.clone()])),
            ("UIRow", Expr::UIRow(vec![Expr::Unit, m.clone()])),
            ("UIColumn", Expr::UIColumn(vec![Expr::Unit, m.clone()])),
            ("UIText/l", Expr::UIText(b(m.clone()), unit())),
            ("UIText/r", Expr::UIText(unit(), b(m.clone()))),
            ("UIButton/l", Expr::UIButton(b(m.clone()), unit())),
            ("UIButton/r", Expr::UIButton(unit(), b(m.clone()))),
            (
                "UIContrastCheck/l",
                Expr::UIContrastCheck(b(m.clone()), unit()),
            ),
            ("UIContrastCheck/r", Expr::UIContrastCheck(unit(), b(m))),
        ]
    }

    /// Assert `pred` finds `marker` through EVERY container variant, and that
    /// it stays `false` on the leaf that carries no marker (the negative
    /// control — without it a always-`true` predicate would pass).
    fn assert_sees_through(what: &str, marker: Expr, pred: impl Fn(&Expr) -> bool) {
        assert!(
            pred(&marker),
            "{what}: the marker itself must be detected — the test is \
             meaningless otherwise"
        );
        assert!(
            !pred(&Expr::Unit),
            "{what}: NEGATIVE CONTROL FAILED — the predicate reports a hit on \
             a bare `Unit`, so it cannot distinguish anything"
        );
        for (label, wrapped) in wrappers(marker) {
            assert!(
                pred(&wrapped),
                "{what}: the walk does not descend through `{label}` — a \
                 marker planted directly inside it was missed. Every arm of \
                 `any_child` must recurse; an arm that drops its child \
                 silently disables this predicate for that variant."
            );
        }
    }

    #[test]
    fn every_expr_variant_is_walked_for_effects() {
        assert_sees_through(
            "contains_effect",
            Expr::Perform(Effect::Crypto, Box::new(Expr::Unit)),
            |e| contains_effect(e, Effect::Crypto),
        );
    }

    #[test]
    fn every_expr_variant_is_walked_for_security_ops() {
        assert_sees_through(
            "contains_security_op",
            Expr::Classify(Box::new(Expr::Unit)),
            contains_security_op,
        );
    }

    #[test]
    fn every_expr_variant_is_walked_for_branching() {
        assert_sees_through(
            "has_if_or_case",
            Expr::If(
                Box::new(Expr::Bool(true)),
                Box::new(Expr::Unit),
                Box::new(Expr::Unit),
            ),
            has_if_or_case,
        );
    }

    #[test]
    fn every_expr_variant_is_walked_for_matching_vars() {
        let kw = to_owned_keywords(&["rahsia"]);
        assert_sees_through("contains_var_matching", Expr::Var("rahsia".into()), |e| {
            contains_var_matching(e, &kw)
        });
    }

    #[test]
    fn every_expr_variant_is_walked_for_personal_data_vars() {
        assert_sees_through(
            "contains_personal_data_var",
            Expr::Var("nama_pengguna".into()),
            contains_personal_data_var,
        );
    }

    /// The predicates must not fire on unrelated content — a second negative
    /// control, distinguishing "walks everywhere" from "returns true for any
    /// non-trivial tree".
    ///
    /// Some wrappers ARE the construct a given predicate looks for (an `If`
    /// wrapper is itself a branch), so each predicate skips the labels it is
    /// legitimately expected to match on.
    fn assert_quiet_on_unrelated(what: &str, skip: &[&str], pred: impl Fn(&Expr) -> bool) {
        for (label, e) in wrappers(Expr::Var("tidak_berkaitan".into())) {
            if skip.iter().any(|s| label.starts_with(s)) {
                continue;
            }
            assert!(
                !pred(&e),
                "{what} fired on `{label}`, which contains nothing it should match"
            );
        }
    }

    #[test]
    fn walkers_stay_false_on_unrelated_trees() {
        let kw = to_owned_keywords(&["rahsia"]);
        // `Perform` here carries Effect::Read, so it is not a Crypto hit.
        assert_quiet_on_unrelated("contains_effect", &[], |e| {
            contains_effect(e, Effect::Crypto)
        });
        assert_quiet_on_unrelated(
            "contains_security_op",
            &["Classify", "Declassify", "Grant"],
            contains_security_op,
        );
        assert_quiet_on_unrelated("has_if_or_case", &["If", "Case"], has_if_or_case);
        assert_quiet_on_unrelated("contains_var_matching", &[], |e| {
            contains_var_matching(e, &kw)
        });
        assert_quiet_on_unrelated(
            "contains_personal_data_var",
            &[],
            contains_personal_data_var,
        );
    }

    /// `contains_effect` must discriminate BETWEEN effects, not merely detect
    /// that some `Perform` exists.
    #[test]
    fn contains_effect_discriminates_between_effects() {
        let e = Expr::Return(Box::new(Expr::Perform(
            Effect::Crypto,
            Box::new(Expr::Unit),
        )));
        assert!(contains_effect(&e, Effect::Crypto));
        assert!(!contains_effect(&e, Effect::Network));
    }

    /// A `ChoreographyBlock` carries no value sub-expressions; the walk must
    /// terminate there rather than being given a bogus child.
    #[test]
    fn leaf_variants_have_no_children() {
        for leaf in [
            Expr::Unit,
            Expr::Bool(true),
            Expr::Int(1),
            Expr::IntN {
                value: 1,
                bits: 8,
                signed: false,
            },
            Expr::String("s".into()),
            Expr::Var("v".into()),
            Expr::Loc(0),
            Expr::ChoreographyBlock {
                name: "P".into(),
                roles: vec!["A".into(), "B".into()],
                protocol: SessionType::End,
            },
            Expr::UIColor(1, 2, 3),
            Expr::UIStyleDecl {
                padding: None,
                font_size: None,
            },
        ] {
            assert!(
                !any_child(&leaf, &mut |_| true),
                "{leaf:?} was reported to have a sub-expression"
            );
        }
    }
}
