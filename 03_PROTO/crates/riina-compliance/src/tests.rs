// Copyright (c) 2026 The RIINA Authors. All rights reserved.

//! Tests for compliance validation.

use riina_types::{Expr, Ty, Effect};

use crate::{ComplianceProfile, parse_profiles, validate, has_errors};

#[test]
fn parse_profiles_single() {
    let profiles = parse_profiles("pci-dss").unwrap();
    assert_eq!(profiles, vec![ComplianceProfile::PciDss]);
}

#[test]
fn parse_profiles_multiple() {
    let profiles = parse_profiles("pci-dss,pdpa,bnm").unwrap();
    assert_eq!(profiles, vec![ComplianceProfile::PciDss, ComplianceProfile::Pdpa, ComplianceProfile::Bnm]);
}

#[test]
fn parse_profiles_unknown() {
    assert!(parse_profiles("unknown").is_err());
}

#[test]
fn parse_profiles_all_15() {
    assert_eq!(ComplianceProfile::ALL.len(), 15);
}

#[test]
fn pci_dss_3_4_declassify_without_prove() {
    // Declassify(Int(42), Int(0)) — proof is not Prove(_)
    let expr = Expr::Declassify(
        Box::new(Expr::Classify(Box::new(Expr::Int(4242)))),
        Box::new(Expr::Int(0)),
    );
    let violations = validate(&expr, &[ComplianceProfile::PciDss]);
    assert!(violations.iter().any(|v| v.rule_id == "PCI-DSS-3.4"));
    assert!(has_errors(&violations));
}

#[test]
fn pci_dss_3_4_declassify_with_prove_ok() {
    let expr = Expr::Declassify(
        Box::new(Expr::Classify(Box::new(Expr::Int(4242)))),
        Box::new(Expr::Prove(Box::new(Expr::Bool(true)))),
    );
    let violations = validate(&expr, &[ComplianceProfile::PciDss]);
    assert!(!violations.iter().any(|v| v.rule_id == "PCI-DSS-3.4"));
}

#[test]
fn pci_dss_6_5_card_data_not_secret() {
    let expr = Expr::Let(
        "card_number".into(),
        Box::new(Expr::String("4111111111111111".into())),
        Box::new(Expr::Unit),
    );
    let violations = validate(&expr, &[ComplianceProfile::PciDss]);
    assert!(violations.iter().any(|v| v.rule_id == "PCI-DSS-6.5"));
}

#[test]
fn pci_dss_6_5_card_data_classified_ok() {
    let expr = Expr::Let(
        "card_number".into(),
        Box::new(Expr::Classify(Box::new(Expr::String("4111111111111111".into())))),
        Box::new(Expr::Unit),
    );
    let violations = validate(&expr, &[ComplianceProfile::PciDss]);
    assert!(!violations.iter().any(|v| v.rule_id == "PCI-DSS-6.5"));
}

#[test]
fn pci_dss_8_3_auth_without_crypto() {
    let expr = Expr::LetRec(
        "authenticate".into(),
        Ty::Fn(Box::new(Ty::String), Box::new(Ty::Bool), Effect::Pure),
        Box::new(Expr::Lam("pwd".into(), Ty::String, Box::new(Expr::Bool(true)))),
        Box::new(Expr::Unit),
    );
    let violations = validate(&expr, &[ComplianceProfile::PciDss]);
    assert!(violations.iter().any(|v| v.rule_id == "PCI-DSS-8.3"));
}

#[test]
fn pci_dss_8_3_auth_with_crypto_ok() {
    let expr = Expr::LetRec(
        "authenticate".into(),
        Ty::Fn(Box::new(Ty::String), Box::new(Ty::Bool), Effect::Crypto),
        Box::new(Expr::Lam(
            "pwd".into(),
            Ty::String,
            Box::new(Expr::Perform(Effect::Crypto, Box::new(Expr::Var("pwd".into())))),
        )),
        Box::new(Expr::Unit),
    );
    let violations = validate(&expr, &[ComplianceProfile::PciDss]);
    assert!(!violations.iter().any(|v| v.rule_id == "PCI-DSS-8.3"));
}

#[test]
fn pdpa_s7_user_input_not_tainted() {
    let expr = Expr::Let(
        "user_input".into(),
        Box::new(Expr::String("raw data".into())),
        Box::new(Expr::Unit),
    );
    let violations = validate(&expr, &[ComplianceProfile::Pdpa]);
    assert!(violations.iter().any(|v| v.rule_id == "PDPA-S7"));
}

#[test]
fn pdpa_s24_personal_data_over_network() {
    let expr = Expr::Perform(
        Effect::Network,
        Box::new(Expr::Var("personal_data".into())),
    );
    let violations = validate(&expr, &[ComplianceProfile::Pdpa]);
    assert!(violations.iter().any(|v| v.rule_id == "PDPA-S24"));
}

#[test]
fn bnm_rmit_10_crypto_without_constant_time() {
    let expr = Expr::Perform(
        Effect::Crypto,
        Box::new(Expr::Var("payment_hash".into())),
    );
    let violations = validate(&expr, &[ComplianceProfile::Bnm]);
    assert!(violations.iter().any(|v| v.rule_id == "BNM-RMiT-10"));
}

#[test]
fn no_violations_without_profiles() {
    let expr = Expr::Declassify(
        Box::new(Expr::Int(42)),
        Box::new(Expr::Int(0)),
    );
    let violations = validate(&expr, &[]);
    assert!(violations.is_empty());
}

#[test]
fn profile_display_roundtrip() {
    for &p in ComplianceProfile::ALL {
        let slug = p.slug();
        let parsed: ComplianceProfile = slug.parse().unwrap();
        assert_eq!(parsed, p);
    }
}
