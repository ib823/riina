// SPDX-License-Identifier: MPL-2.0
// Copyright (c) 2026 The RIINA Authors. See AUTHORS file.

//! RIINA Formatter
//!
//! Pretty-prints RIINA ASTs with consistent style.
//! RIINA = Rigorous Immutable Invariant — Normalized Axiom

#![forbid(unsafe_code)]

use riina_types::{
    BinOp, Capability, CapabilityKind, Effect, Expr, Program, Sanitizer, SecurityLevel,
    SessionType, TaintSource, TopLevelDecl, Ty,
};

/// Formatter configuration.
pub struct FmtConfig {
    pub indent: usize,
    pub max_width: usize,
}

impl Default for FmtConfig {
    fn default() -> Self {
        Self {
            indent: 4,
            max_width: 100,
        }
    }
}

/// Format a RIINA program from source text.
pub fn format_source(source: &str) -> Result<String, String> {
    let mut parser = riina_parser::Parser::new(source);
    let program = parser
        .parse_program()
        .map_err(|e| format!("Parse error: {e}"))?;
    Ok(format_program(&program, &FmtConfig::default()))
}

/// Format a parsed Program to a string.
pub fn format_program(program: &Program, cfg: &FmtConfig) -> String {
    let mut out = String::new();
    for (i, decl) in program.decls.iter().enumerate() {
        if i > 0 {
            out.push('\n');
        }
        fmt_decl(&mut out, decl, 0, cfg);
        out.push('\n');
    }
    out
}

fn indent(out: &mut String, level: usize, cfg: &FmtConfig) {
    for _ in 0..level * cfg.indent {
        out.push(' ');
    }
}

fn fmt_decl(out: &mut String, decl: &TopLevelDecl, level: usize, cfg: &FmtConfig) {
    match decl {
        TopLevelDecl::Function {
            name,
            params,
            return_ty,
            effect,
            body,
        } => {
            indent(out, level, cfg);
            out.push_str("fungsi ");
            out.push_str(name);
            out.push('(');
            for (i, (pname, pty)) in params.iter().enumerate() {
                if i > 0 {
                    out.push_str(", ");
                }
                out.push_str(pname);
                out.push_str(": ");
                fmt_ty(out, pty);
            }
            out.push(')');
            if *return_ty != Ty::Unit {
                out.push_str(" -> ");
                fmt_ty(out, return_ty);
            }
            if *effect != Effect::Pure {
                out.push_str(" kesan ");
                fmt_effect(out, effect);
            }
            out.push_str(" {\n");
            fmt_expr(out, body, level + 1, cfg);
            out.push('\n');
            indent(out, level, cfg);
            out.push('}');
        }
        TopLevelDecl::Binding { name, value } => {
            indent(out, level, cfg);
            out.push_str("biar ");
            out.push_str(name);
            out.push_str(" = ");
            fmt_expr(out, value, level, cfg);
            out.push(';');
        }
        TopLevelDecl::Expr(e) => {
            indent(out, level, cfg);
            fmt_expr(out, e, level, cfg);
        }
    }
}

fn fmt_expr(out: &mut String, expr: &Expr, level: usize, cfg: &FmtConfig) {
    match expr {
        Expr::Unit => {
            indent(out, level, cfg);
            out.push_str("()");
        }
        Expr::Bool(b) => {
            indent(out, level, cfg);
            out.push_str(if *b { "betul" } else { "salah" });
        }
        Expr::Int(n) => {
            indent(out, level, cfg);
            out.push_str(&n.to_string());
        }
        Expr::String(s) => {
            indent(out, level, cfg);
            out.push('"');
            // Escape special chars
            for c in s.chars() {
                match c {
                    '"' => out.push_str("\\\""),
                    '\\' => out.push_str("\\\\"),
                    '\n' => out.push_str("\\n"),
                    '\t' => out.push_str("\\t"),
                    '\r' => out.push_str("\\r"),
                    c => out.push(c),
                }
            }
            out.push('"');
        }
        Expr::Var(name) => {
            indent(out, level, cfg);
            out.push_str(name);
        }
        Expr::Lam(param, ty, body) => {
            indent(out, level, cfg);
            out.push_str("fungsi(");
            out.push_str(param);
            out.push_str(": ");
            fmt_ty(out, ty);
            out.push_str(") ");
            fmt_expr_inline(out, body, cfg);
        }
        Expr::App(func, arg) => {
            indent(out, level, cfg);
            fmt_expr_inline(out, func, cfg);
            out.push('(');
            fmt_expr_inline(out, arg, cfg);
            out.push(')');
        }
        Expr::Pair(a, b) => {
            indent(out, level, cfg);
            out.push('(');
            fmt_expr_inline(out, a, cfg);
            out.push_str(", ");
            fmt_expr_inline(out, b, cfg);
            out.push(')');
        }
        Expr::Fst(e) => {
            indent(out, level, cfg);
            out.push_str("pertama ");
            fmt_expr_inline(out, e, cfg);
        }
        Expr::Snd(e) => {
            indent(out, level, cfg);
            out.push_str("kedua ");
            fmt_expr_inline(out, e, cfg);
        }
        Expr::Inl(e, ty) => {
            indent(out, level, cfg);
            out.push_str("inl ");
            fmt_expr_inline(out, e, cfg);
            out.push_str(": ");
            fmt_ty(out, ty);
        }
        Expr::Inr(e, ty) => {
            indent(out, level, cfg);
            out.push_str("inr ");
            fmt_expr_inline(out, e, cfg);
            out.push_str(": ");
            fmt_ty(out, ty);
        }
        Expr::Case(scrutinee, x, e1, y, e2) => {
            indent(out, level, cfg);
            out.push_str("padan ");
            fmt_expr_inline(out, scrutinee, cfg);
            out.push_str(" {\n");
            indent(out, level + 1, cfg);
            out.push_str("inl ");
            out.push_str(x);
            out.push_str(" => ");
            fmt_expr_inline(out, e1, cfg);
            out.push_str(",\n");
            indent(out, level + 1, cfg);
            out.push_str("inr ");
            out.push_str(y);
            out.push_str(" => ");
            fmt_expr_inline(out, e2, cfg);
            out.push_str(",\n");
            indent(out, level, cfg);
            out.push('}');
        }
        Expr::If(cond, then_br, else_br) => {
            indent(out, level, cfg);
            out.push_str("kalau ");
            fmt_expr_inline(out, cond, cfg);
            out.push_str(" {\n");
            fmt_expr(out, then_br, level + 1, cfg);
            out.push('\n');
            indent(out, level, cfg);
            out.push_str("} lain {\n");
            fmt_expr(out, else_br, level + 1, cfg);
            out.push('\n');
            indent(out, level, cfg);
            out.push('}');
        }
        Expr::Let(name, value, body) => {
            indent(out, level, cfg);
            out.push_str("biar ");
            out.push_str(name);
            out.push_str(" = ");
            fmt_expr_inline(out, value, cfg);
            out.push_str(";\n");
            fmt_expr(out, body, level, cfg);
        }
        Expr::Perform(eff, e) => {
            indent(out, level, cfg);
            out.push_str("laku ");
            fmt_effect(out, eff);
            out.push(' ');
            fmt_expr_inline(out, e, cfg);
        }
        Expr::Handle(e, x, h) => {
            indent(out, level, cfg);
            out.push_str("kendali ");
            fmt_expr_inline(out, e, cfg);
            out.push_str(" dengan ");
            out.push_str(x);
            out.push_str(" => ");
            fmt_expr_inline(out, h, cfg);
        }
        Expr::Ref(e, lvl) => {
            indent(out, level, cfg);
            out.push_str("ruj ");
            fmt_expr_inline(out, e, cfg);
            out.push_str(" @ ");
            fmt_security_level(out, lvl);
        }
        Expr::Deref(e) => {
            indent(out, level, cfg);
            out.push('!');
            fmt_expr_inline(out, e, cfg);
        }
        Expr::Assign(lhs, rhs) => {
            indent(out, level, cfg);
            fmt_expr_inline(out, lhs, cfg);
            out.push_str(" := ");
            fmt_expr_inline(out, rhs, cfg);
        }
        Expr::Classify(e) => {
            indent(out, level, cfg);
            out.push_str("sulit ");
            fmt_expr_inline(out, e, cfg);
        }
        Expr::Declassify(e, proof) => {
            indent(out, level, cfg);
            out.push_str("dedah ");
            fmt_expr_inline(out, e, cfg);
            out.push_str(" dengan ");
            fmt_expr_inline(out, proof, cfg);
        }
        Expr::Prove(e) => {
            indent(out, level, cfg);
            out.push_str("bukti ");
            fmt_expr_inline(out, e, cfg);
        }
        Expr::Require(eff, e) => {
            indent(out, level, cfg);
            out.push_str("perlukan ");
            fmt_effect(out, eff);
            out.push(' ');
            fmt_expr_inline(out, e, cfg);
        }
        Expr::Grant(eff, e) => {
            indent(out, level, cfg);
            out.push_str("beri ");
            fmt_effect(out, eff);
            out.push(' ');
            fmt_expr_inline(out, e, cfg);
        }
        Expr::Loc(n) => {
            indent(out, level, cfg);
            out.push_str(&format!("loc#{n}"));
        }
        Expr::BinOp(op, lhs, rhs) => {
            indent(out, level, cfg);
            fmt_expr_inline(out, lhs, cfg);
            out.push(' ');
            fmt_binop(out, op);
            out.push(' ');
            fmt_expr_inline(out, rhs, cfg);
        }
    }
}

/// Format an expression inline (no leading indent).
fn fmt_expr_inline(out: &mut String, expr: &Expr, cfg: &FmtConfig) {
    match expr {
        Expr::Unit => out.push_str("()"),
        Expr::Bool(b) => out.push_str(if *b { "betul" } else { "salah" }),
        Expr::Int(n) => out.push_str(&n.to_string()),
        Expr::String(s) => {
            out.push('"');
            for c in s.chars() {
                match c {
                    '"' => out.push_str("\\\""),
                    '\\' => out.push_str("\\\\"),
                    '\n' => out.push_str("\\n"),
                    '\t' => out.push_str("\\t"),
                    '\r' => out.push_str("\\r"),
                    c => out.push(c),
                }
            }
            out.push('"');
        }
        Expr::Var(name) => out.push_str(name),
        Expr::Lam(param, ty, body) => {
            out.push_str("fungsi(");
            out.push_str(param);
            out.push_str(": ");
            fmt_ty(out, ty);
            out.push_str(") ");
            fmt_expr_inline(out, body, cfg);
        }
        Expr::App(func, arg) => {
            fmt_expr_inline(out, func, cfg);
            out.push('(');
            fmt_expr_inline(out, arg, cfg);
            out.push(')');
        }
        Expr::Pair(a, b) => {
            out.push('(');
            fmt_expr_inline(out, a, cfg);
            out.push_str(", ");
            fmt_expr_inline(out, b, cfg);
            out.push(')');
        }
        Expr::Fst(e) => {
            out.push_str("pertama ");
            fmt_expr_inline(out, e, cfg);
        }
        Expr::Snd(e) => {
            out.push_str("kedua ");
            fmt_expr_inline(out, e, cfg);
        }
        Expr::Inl(e, ty) => {
            out.push_str("inl ");
            fmt_expr_inline(out, e, cfg);
            out.push_str(": ");
            fmt_ty(out, ty);
        }
        Expr::Inr(e, ty) => {
            out.push_str("inr ");
            fmt_expr_inline(out, e, cfg);
            out.push_str(": ");
            fmt_ty(out, ty);
        }
        Expr::Case(scrutinee, x, e1, y, e2) => {
            out.push_str("padan ");
            fmt_expr_inline(out, scrutinee, cfg);
            out.push_str(" { inl ");
            out.push_str(x);
            out.push_str(" => ");
            fmt_expr_inline(out, e1, cfg);
            out.push_str(", inr ");
            out.push_str(y);
            out.push_str(" => ");
            fmt_expr_inline(out, e2, cfg);
            out.push_str(" }");
        }
        Expr::If(cond, then_br, else_br) => {
            out.push_str("kalau ");
            fmt_expr_inline(out, cond, cfg);
            out.push_str(" { ");
            fmt_expr_inline(out, then_br, cfg);
            out.push_str(" } lain { ");
            fmt_expr_inline(out, else_br, cfg);
            out.push_str(" }");
        }
        Expr::Let(name, value, body) => {
            out.push_str("biar ");
            out.push_str(name);
            out.push_str(" = ");
            fmt_expr_inline(out, value, cfg);
            out.push_str("; ");
            fmt_expr_inline(out, body, cfg);
        }
        Expr::Perform(eff, e) => {
            out.push_str("laku ");
            fmt_effect(out, eff);
            out.push(' ');
            fmt_expr_inline(out, e, cfg);
        }
        Expr::Handle(e, x, h) => {
            out.push_str("kendali ");
            fmt_expr_inline(out, e, cfg);
            out.push_str(" dengan ");
            out.push_str(x);
            out.push_str(" => ");
            fmt_expr_inline(out, h, cfg);
        }
        Expr::Ref(e, lvl) => {
            out.push_str("ruj ");
            fmt_expr_inline(out, e, cfg);
            out.push_str(" @ ");
            fmt_security_level(out, lvl);
        }
        Expr::Deref(e) => {
            out.push('!');
            fmt_expr_inline(out, e, cfg);
        }
        Expr::Assign(lhs, rhs) => {
            fmt_expr_inline(out, lhs, cfg);
            out.push_str(" := ");
            fmt_expr_inline(out, rhs, cfg);
        }
        Expr::Classify(e) => {
            out.push_str("sulit ");
            fmt_expr_inline(out, e, cfg);
        }
        Expr::Declassify(e, proof) => {
            out.push_str("dedah ");
            fmt_expr_inline(out, e, cfg);
            out.push_str(" dengan ");
            fmt_expr_inline(out, proof, cfg);
        }
        Expr::Prove(e) => {
            out.push_str("bukti ");
            fmt_expr_inline(out, e, cfg);
        }
        Expr::Require(eff, e) => {
            out.push_str("perlukan ");
            fmt_effect(out, eff);
            out.push(' ');
            fmt_expr_inline(out, e, cfg);
        }
        Expr::Grant(eff, e) => {
            out.push_str("beri ");
            fmt_effect(out, eff);
            out.push(' ');
            fmt_expr_inline(out, e, cfg);
        }
        Expr::Loc(n) => out.push_str(&format!("loc#{n}")),
        Expr::BinOp(op, lhs, rhs) => {
            fmt_expr_inline(out, lhs, cfg);
            out.push(' ');
            fmt_binop(out, op);
            out.push(' ');
            fmt_expr_inline(out, rhs, cfg);
        }
    }
}

fn fmt_binop(out: &mut String, op: &BinOp) {
    out.push_str(match op {
        BinOp::Add => "+",
        BinOp::Sub => "-",
        BinOp::Mul => "*",
        BinOp::Div => "/",
        BinOp::Mod => "%",
        BinOp::Eq => "==",
        BinOp::Ne => "!=",
        BinOp::Lt => "<",
        BinOp::Le => "<=",
        BinOp::Gt => ">",
        BinOp::Ge => ">=",
        BinOp::And => "&&",
        BinOp::Or => "||",
    });
}

fn fmt_effect(out: &mut String, eff: &Effect) {
    out.push_str(match eff {
        Effect::Pure => "Bersih",
        Effect::Read => "Baca",
        Effect::Write => "Tulis",
        Effect::FileSystem => "SistemFail",
        Effect::Network => "Rangkaian",
        Effect::NetworkSecure => "RangkaianSelamat",
        Effect::Crypto => "Kripto",
        Effect::Random => "Rawak",
        Effect::System => "Sistem",
        Effect::Time => "Masa",
        Effect::Process => "Proses",
        Effect::Panel => "Panel",
        Effect::Zirah => "Zirah",
        Effect::Benteng => "Benteng",
        Effect::Sandi => "Sandi",
        Effect::Menara => "Menara",
        Effect::Gapura => "Gapura",
    });
}

fn fmt_security_level(out: &mut String, lvl: &SecurityLevel) {
    out.push_str(match lvl {
        SecurityLevel::Public => "Awam",
        SecurityLevel::Internal => "Dalaman",
        SecurityLevel::Session => "Sesi",
        SecurityLevel::User => "Pengguna",
        SecurityLevel::System => "Sistem",
        SecurityLevel::Secret => "Rahsia",
    });
}

fn fmt_ty(out: &mut String, ty: &Ty) {
    match ty {
        Ty::Unit => out.push_str("()"),
        Ty::Bool => out.push_str("Benar"),
        Ty::Int => out.push_str("Nombor"),
        Ty::String => out.push_str("Teks"),
        Ty::Bytes => out.push_str("Bait"),
        Ty::Fn(param, ret, eff) => {
            out.push_str("Fn(");
            fmt_ty(out, param);
            out.push_str(", ");
            fmt_ty(out, ret);
            if *eff != Effect::Pure {
                out.push_str(", ");
                fmt_effect(out, eff);
            }
            out.push(')');
        }
        Ty::Prod(a, b) => {
            out.push('(');
            fmt_ty(out, a);
            out.push_str(", ");
            fmt_ty(out, b);
            out.push(')');
        }
        Ty::Sum(a, b) => {
            out.push_str("Sum<");
            fmt_ty(out, a);
            out.push_str(", ");
            fmt_ty(out, b);
            out.push('>');
        }
        Ty::List(inner) => {
            out.push_str("Senarai<");
            fmt_ty(out, inner);
            out.push('>');
        }
        Ty::Option(inner) => {
            out.push_str("Mungkin<");
            fmt_ty(out, inner);
            out.push('>');
        }
        Ty::Ref(inner, lvl) => {
            out.push_str("Ruj<");
            fmt_ty(out, inner);
            out.push_str(">@");
            fmt_security_level(out, lvl);
        }
        Ty::Secret(inner) => {
            out.push_str("Rahsia<");
            fmt_ty(out, inner);
            out.push('>');
        }
        Ty::Labeled(inner, lvl) => {
            out.push_str("Berlabel<");
            fmt_ty(out, inner);
            out.push_str(", ");
            fmt_security_level(out, lvl);
            out.push('>');
        }
        Ty::Tainted(inner, src) => {
            out.push_str("Tercemar<");
            fmt_ty(out, inner);
            out.push_str(", ");
            fmt_taint_source(out, src);
            out.push('>');
        }
        Ty::Sanitized(inner, san) => {
            out.push_str("Disanitasi<");
            fmt_ty(out, inner);
            out.push_str(", ");
            fmt_sanitizer(out, san);
            out.push('>');
        }
        Ty::Proof(inner) => {
            out.push_str("Bukti<");
            fmt_ty(out, inner);
            out.push('>');
        }
        Ty::Capability(kind) => {
            out.push_str("Keupayaan<");
            fmt_capability_kind(out, kind);
            out.push('>');
        }
        Ty::CapabilityFull(cap) => {
            out.push_str("Keupayaan<");
            fmt_capability(out, cap);
            out.push('>');
        }
        Ty::Chan(st) => {
            out.push_str("Chan<");
            fmt_session_type(out, st);
            out.push('>');
        }
        Ty::SecureChan(st, lvl) => {
            out.push_str("SecureChan<");
            fmt_session_type(out, st);
            out.push_str(", ");
            fmt_security_level(out, lvl);
            out.push('>');
        }
        Ty::ConstantTime(inner) => {
            out.push_str("MasaTetap<");
            fmt_ty(out, inner);
            out.push('>');
        }
        Ty::Zeroizing(inner) => {
            out.push_str("Sifar<");
            fmt_ty(out, inner);
            out.push('>');
        }
        Ty::Any => out.push_str("Any"),
    }
}

fn fmt_taint_source(out: &mut String, src: &TaintSource) {
    out.push_str(match src {
        TaintSource::NetworkExternal => "NetworkExternal",
        TaintSource::NetworkInternal => "NetworkInternal",
        TaintSource::UserInput => "UserInput",
        TaintSource::FileSystem => "FileSystem",
        TaintSource::Database => "Database",
        TaintSource::Environment => "Environment",
        TaintSource::GapuraRequest => "GapuraRequest",
        TaintSource::ZirahEvent => "ZirahEvent",
        TaintSource::ZirahEndpoint => "ZirahEndpoint",
        TaintSource::BentengBiometric => "BentengBiometric",
        TaintSource::SandiSignature => "SandiSignature",
        TaintSource::MenaraDevice => "MenaraDevice",
    });
}

fn fmt_sanitizer(out: &mut String, san: &Sanitizer) {
    out.push_str(match san {
        Sanitizer::HtmlEscape => "HtmlEscape",
        Sanitizer::UrlEncode => "UrlEncode",
        Sanitizer::JsEscape => "JsEscape",
        Sanitizer::CssEscape => "CssEscape",
        Sanitizer::SqlEscape => "SqlEscape",
        Sanitizer::SqlParam => "SqlParam",
        Sanitizer::XssFilter => "XssFilter",
        Sanitizer::PathTraversal => "PathTraversal",
        Sanitizer::CommandEscape => "CommandEscape",
        Sanitizer::LdapEscape => "LdapEscape",
        Sanitizer::XmlEscape => "XmlEscape",
        Sanitizer::JsonValidation => "JsonValidation",
        Sanitizer::XmlValidation => "XmlValidation",
        Sanitizer::EmailValidation => "EmailValidation",
        Sanitizer::PhoneValidation => "PhoneValidation",
        Sanitizer::LengthBound(n) => {
            out.push_str(&format!("LengthBound({n})"));
            return;
        }
        Sanitizer::RangeBound(lo, hi) => {
            out.push_str(&format!("RangeBound({lo}, {hi})"));
            return;
        }
        Sanitizer::RegexMatch(re) => {
            out.push_str(&format!("RegexMatch(\"{re}\")"));
            return;
        }
        Sanitizer::Whitelist(items) => {
            out.push_str("Whitelist(");
            for (i, item) in items.iter().enumerate() {
                if i > 0 {
                    out.push_str(", ");
                }
                out.push_str(&format!("\"{item}\""));
            }
            out.push(')');
            return;
        }
        Sanitizer::HashVerify => "HashVerify",
        Sanitizer::SignatureVerify => "SignatureVerify",
        Sanitizer::MacVerify => "MacVerify",
        Sanitizer::GapuraAuth => "GapuraAuth",
        Sanitizer::ZirahSession => "ZirahSession",
        Sanitizer::BentengBiometric => "BentengBiometric",
        Sanitizer::SandiDecrypt => "SandiDecrypt",
        Sanitizer::MenaraAttestation => "MenaraAttestation",
    });
}

fn fmt_capability_kind(out: &mut String, kind: &CapabilityKind) {
    out.push_str(match kind {
        CapabilityKind::FileRead => "FileRead",
        CapabilityKind::FileWrite => "FileWrite",
        CapabilityKind::FileExecute => "FileExecute",
        CapabilityKind::FileDelete => "FileDelete",
        CapabilityKind::NetConnect => "NetConnect",
        CapabilityKind::NetListen => "NetListen",
        CapabilityKind::NetBind => "NetBind",
        CapabilityKind::ProcSpawn => "ProcSpawn",
        CapabilityKind::ProcSignal => "ProcSignal",
        CapabilityKind::SysTime => "SysTime",
        CapabilityKind::SysRandom => "SysRandom",
        CapabilityKind::SysEnv => "SysEnv",
        CapabilityKind::RootProduct => "RootProduct",
        CapabilityKind::ProductAccess => "ProductAccess",
    });
}

fn fmt_capability(out: &mut String, cap: &Capability) {
    match cap {
        Capability::Basic(k) => fmt_capability_kind(out, k),
        Capability::Revocable(inner) => {
            out.push_str("Revocable(");
            fmt_capability(out, inner);
            out.push(')');
        }
        Capability::TimeBound(inner, t) => {
            out.push_str("TimeBound(");
            fmt_capability(out, inner);
            out.push_str(&format!(", {t})"));
        }
        Capability::Delegated(inner, to) => {
            out.push_str("Delegated(");
            fmt_capability(out, inner);
            out.push_str(&format!(", {to})"));
        }
    }
}

fn fmt_session_type(out: &mut String, st: &SessionType) {
    match st {
        SessionType::End => out.push_str("Tamat"),
        SessionType::Send(ty, cont) => {
            out.push_str("Hantar(");
            fmt_ty(out, ty);
            out.push_str(", ");
            fmt_session_type(out, cont);
            out.push(')');
        }
        SessionType::Recv(ty, cont) => {
            out.push_str("Terima(");
            fmt_ty(out, ty);
            out.push_str(", ");
            fmt_session_type(out, cont);
            out.push(')');
        }
        SessionType::Select(a, b) => {
            out.push_str("Pilih(");
            fmt_session_type(out, a);
            out.push_str(", ");
            fmt_session_type(out, b);
            out.push(')');
        }
        SessionType::Branch(a, b) => {
            out.push_str("Cabang(");
            fmt_session_type(out, a);
            out.push_str(", ");
            fmt_session_type(out, b);
            out.push(')');
        }
        SessionType::Rec(name, body) => {
            out.push_str("Rec(");
            out.push_str(name);
            out.push_str(", ");
            fmt_session_type(out, body);
            out.push(')');
        }
        SessionType::Var(name) => out.push_str(name),
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_format_simple_function() {
        let source = "fungsi tambah(x: Nombor, y: Nombor) -> Nombor { x + y }";
        let result = format_source(source).unwrap();
        assert!(result.contains("fungsi tambah"));
        assert!(result.contains("Nombor"));
    }

    #[test]
    fn test_format_binding() {
        let source = "biar x = 42;";
        let mut parser = riina_parser::Parser::new(source);
        let program = parser.parse_program().unwrap();
        let result = format_program(&program, &FmtConfig::default());
        assert!(result.contains("biar x = 42;"));
    }

    #[test]
    fn test_format_if() {
        let source = "kalau betul { 1 } lain { 0 }";
        let result = format_source(source).unwrap();
        assert!(result.contains("kalau"));
        assert!(result.contains("lain"));
    }

    #[test]
    fn test_format_string_escapes() {
        let cfg = FmtConfig::default();
        let mut out = String::new();
        let expr = Expr::String("hello\nworld".to_string());
        fmt_expr_inline(&mut out, &expr, &cfg);
        assert_eq!(out, "\"hello\\nworld\"");
    }

    #[test]
    fn test_format_effect() {
        let source = "fungsi io() -> Teks kesan Tulis { \"hello\" }";
        let result = format_source(source).unwrap();
        assert!(result.contains("kesan Tulis"));
    }

    #[test]
    fn test_format_security_ref() {
        let cfg = FmtConfig::default();
        let mut out = String::new();
        fmt_ty(&mut out, &Ty::Ref(Box::new(Ty::Int), SecurityLevel::Secret));
        assert_eq!(out, "Ruj<Nombor>@Rahsia");
    }
}
