// SPDX-License-Identifier: MPL-2.0
// Copyright (c) 2026 The RIINA Authors. See AUTHORS file.

//! RIINA Typechecker
//!
//! Implements the typing rules defined in `foundations/Typing.v`.
//! RIINA = Rigorous Immutable Invariant — Normalized Axiom
//!
//! Mode: ULTRA KIASU | FUCKING PARANOID | ZERO TRUST | ZERO LAZINESS

use riina_types::{BinOp, Expr, Ty, SecurityLevel, Effect, Ident};
use std::collections::HashMap;

#[derive(Debug, Clone, PartialEq)]
pub enum TypeError {
    VarNotFound(Ident),
    TypeMismatch { expected: Ty, found: Ty },
    ExpectedFunction(Ty),
    ExpectedProduct(Ty),
    ExpectedSum(Ty),
    ExpectedRef(Ty),
    EffectViolation { allowed: Effect, found: Effect },
    AnnotationMismatch { expected: Ty, found: Ty },
}

impl std::fmt::Display for TypeError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            TypeError::VarNotFound(id) => write!(f, "Variable not found: {}", id),
            TypeError::TypeMismatch { expected, found } => {
                write!(f, "Type mismatch: expected {:?}, found {:?}", expected, found)
            }
            TypeError::ExpectedFunction(ty) => write!(f, "Expected function type, found {:?}", ty),
            TypeError::ExpectedProduct(ty) => write!(f, "Expected product type, found {:?}", ty),
            TypeError::ExpectedSum(ty) => write!(f, "Expected sum type, found {:?}", ty),
            TypeError::ExpectedRef(ty) => write!(f, "Expected reference type, found {:?}", ty),
            TypeError::EffectViolation { allowed, found } => {
                write!(f, "Effect violation: allowed {:?}, found {:?}", allowed, found)
            }
            TypeError::AnnotationMismatch { expected, found } => {
                write!(f, "Annotation mismatch: expected {:?}, found {:?}", expected, found)
            }
        }
    }
}

impl std::error::Error for TypeError {}

#[derive(Clone)]
pub struct Context {
    vars: HashMap<Ident, Ty>,
    level: SecurityLevel,
}

impl Default for Context {
    fn default() -> Self {
        Self::new()
    }
}

impl Context {
    pub fn new() -> Self {
        Self {
            vars: HashMap::new(),
            level: SecurityLevel::Public,
        }
    }

    pub fn extend(&self, name: Ident, ty: Ty) -> Self {
        let mut new_vars = self.vars.clone();
        new_vars.insert(name, ty);
        Self {
            vars: new_vars,
            level: self.level,
        }
    }

    pub fn lookup(&self, name: &Ident) -> Option<&Ty> {
        self.vars.get(name)
    }
}

/// Register builtin function types into a context.
/// Uses Ty::Any for polymorphic builtins.
pub fn register_builtin_types(ctx: &Context) -> Context {
    let mut c = ctx.clone();
    // I/O builtins
    c = c.extend("cetak".to_string(), Ty::Fn(Box::new(Ty::Any), Box::new(Ty::Unit), Effect::System));
    c = c.extend("print".to_string(), Ty::Fn(Box::new(Ty::Any), Box::new(Ty::Unit), Effect::System));
    c = c.extend("cetakln".to_string(), Ty::Fn(Box::new(Ty::Any), Box::new(Ty::Unit), Effect::System));
    c = c.extend("println".to_string(), Ty::Fn(Box::new(Ty::Any), Box::new(Ty::Unit), Effect::System));
    // String
    c = c.extend("gabung_teks".to_string(), Ty::Fn(
        Box::new(Ty::Prod(Box::new(Ty::String), Box::new(Ty::String))),
        Box::new(Ty::String), Effect::Pure));
    c = c.extend("concat".to_string(), Ty::Fn(
        Box::new(Ty::Prod(Box::new(Ty::String), Box::new(Ty::String))),
        Box::new(Ty::String), Effect::Pure));
    c = c.extend("panjang".to_string(), Ty::Fn(Box::new(Ty::String), Box::new(Ty::Int), Effect::Pure));
    c = c.extend("length".to_string(), Ty::Fn(Box::new(Ty::String), Box::new(Ty::Int), Effect::Pure));
    // Conversion
    c = c.extend("ke_teks".to_string(), Ty::Fn(Box::new(Ty::Any), Box::new(Ty::String), Effect::Pure));
    c = c.extend("to_string".to_string(), Ty::Fn(Box::new(Ty::Any), Box::new(Ty::String), Effect::Pure));
    c = c.extend("ke_nombor".to_string(), Ty::Fn(Box::new(Ty::String), Box::new(Ty::Int), Effect::Pure));
    c = c.extend("parse_int".to_string(), Ty::Fn(Box::new(Ty::String), Box::new(Ty::Int), Effect::Pure));
    c = c.extend("ke_bool".to_string(), Ty::Fn(Box::new(Ty::Any), Box::new(Ty::Bool), Effect::Pure));
    c = c.extend("to_bool".to_string(), Ty::Fn(Box::new(Ty::Any), Box::new(Ty::Bool), Effect::Pure));
    // Math
    c = c.extend("mutlak".to_string(), Ty::Fn(Box::new(Ty::Int), Box::new(Ty::Int), Effect::Pure));
    c = c.extend("abs".to_string(), Ty::Fn(Box::new(Ty::Int), Box::new(Ty::Int), Effect::Pure));
    for name in &["minimum", "min", "maksimum", "max", "kuasa", "pow", "gcd", "lcm"] {
        c = c.extend(name.to_string(), Ty::Fn(
            Box::new(Ty::Prod(Box::new(Ty::Int), Box::new(Ty::Int))),
            Box::new(Ty::Int), Effect::Pure));
    }
    c = c.extend("punca".to_string(), Ty::Fn(Box::new(Ty::Int), Box::new(Ty::Int), Effect::Pure));
    c = c.extend("sqrt".to_string(), Ty::Fn(Box::new(Ty::Int), Box::new(Ty::Int), Effect::Pure));
    // Assert
    c = c.extend("tegaskan".to_string(), Ty::Fn(Box::new(Ty::Bool), Box::new(Ty::Unit), Effect::Pure));
    c = c.extend("assert".to_string(), Ty::Fn(Box::new(Ty::Bool), Box::new(Ty::Unit), Effect::Pure));
    c = c.extend("tegaskan_betul".to_string(), Ty::Fn(Box::new(Ty::Bool), Box::new(Ty::Unit), Effect::Pure));
    c = c.extend("assert_true".to_string(), Ty::Fn(Box::new(Ty::Bool), Box::new(Ty::Unit), Effect::Pure));
    c = c.extend("tegaskan_salah".to_string(), Ty::Fn(Box::new(Ty::Bool), Box::new(Ty::Unit), Effect::Pure));
    c = c.extend("assert_false".to_string(), Ty::Fn(Box::new(Ty::Bool), Box::new(Ty::Unit), Effect::Pure));
    c = c.extend("tegaskan_sama".to_string(), Ty::Fn(
        Box::new(Ty::Prod(Box::new(Ty::Any), Box::new(Ty::Any))),
        Box::new(Ty::Unit), Effect::Pure));
    c = c.extend("assert_eq".to_string(), Ty::Fn(
        Box::new(Ty::Prod(Box::new(Ty::Any), Box::new(Ty::Any))),
        Box::new(Ty::Unit), Effect::Pure));
    c = c.extend("tegaskan_beza".to_string(), Ty::Fn(
        Box::new(Ty::Prod(Box::new(Ty::Any), Box::new(Ty::Any))),
        Box::new(Ty::Unit), Effect::Pure));
    c = c.extend("assert_ne".to_string(), Ty::Fn(
        Box::new(Ty::Prod(Box::new(Ty::Any), Box::new(Ty::Any))),
        Box::new(Ty::Unit), Effect::Pure));

    // ── String builtins (teks) ──
    for (bm, en) in &[
        ("teks_belah", "str_split"), ("teks_cantum", "str_join"),
        ("teks_potong", "str_trim"), ("teks_mengandungi", "str_contains"),
        ("teks_ganti", "str_replace"), ("teks_mula_dengan", "str_starts_with"),
        ("teks_akhir_dengan", "str_ends_with"), ("teks_huruf_besar", "str_to_upper"),
        ("teks_huruf_kecil", "str_to_lower"), ("teks_aksara_di", "str_char_at"),
        ("teks_sub", "str_substring"), ("teks_indeks", "str_index_of"),
        ("teks_ulang", "str_repeat"), ("teks_pad_kiri", "str_pad_left"),
        ("teks_pad_kanan", "str_pad_right"), ("teks_baris", "str_lines"),
    ] {
        let ty = Ty::Fn(Box::new(Ty::Any), Box::new(Ty::Any), Effect::Pure);
        c = c.extend(bm.to_string(), ty.clone());
        c = c.extend(en.to_string(), ty);
    }

    // ── List builtins (senarai) ──
    for (bm, en) in &[
        ("senarai_baru", "list_new"), ("senarai_tolak", "list_push"),
        ("senarai_dapat", "list_get"), ("senarai_panjang", "list_len"),
        ("senarai_peta", "list_map"), ("senarai_tapis", "list_filter"),
        ("senarai_lipat", "list_fold"), ("senarai_balik", "list_reverse"),
        ("senarai_susun", "list_sort"), ("senarai_mengandungi", "list_contains"),
        ("senarai_sambung", "list_concat"), ("senarai_kepala", "list_head"),
        ("senarai_ekor", "list_tail"), ("senarai_zip", "list_zip"),
        ("senarai_nombor", "list_enumerate"), ("senarai_rata", "list_flatten"),
        ("senarai_unik", "list_unique"), ("senarai_potong", "list_slice"),
    ] {
        let ty = Ty::Fn(Box::new(Ty::Any), Box::new(Ty::Any), Effect::Pure);
        c = c.extend(bm.to_string(), ty.clone());
        c = c.extend(en.to_string(), ty);
    }

    // ── Map builtins (peta) ──
    for (bm, en) in &[
        ("peta_baru", "map_new"), ("peta_letak", "map_insert"),
        ("peta_dapat", "map_get"), ("peta_buang", "map_remove"),
        ("peta_kunci", "map_keys"), ("peta_nilai", "map_values"),
        ("peta_mengandungi", "map_contains"), ("peta_panjang", "map_len"),
    ] {
        let ty = Ty::Fn(Box::new(Ty::Any), Box::new(Ty::Any), Effect::Pure);
        c = c.extend(bm.to_string(), ty.clone());
        c = c.extend(en.to_string(), ty);
    }

    // ── Set builtins ──
    for (bm, en) in &[
        ("set_baru", "set_new"), ("set_letak", "set_insert"),
        ("set_buang", "set_remove"), ("set_mengandungi", "set_contains"),
        ("set_kesatuan", "set_union"), ("set_persilangan", "set_intersect"),
        ("set_panjang", "set_len"),
    ] {
        let ty = Ty::Fn(Box::new(Ty::Any), Box::new(Ty::Any), Effect::Pure);
        c = c.extend(bm.to_string(), ty.clone());
        c = c.extend(en.to_string(), ty);
    }

    // ── File I/O builtins (fail) — Effect::FileSystem ──
    for (bm, en) in &[
        ("fail_baca", "file_read"), ("fail_tulis", "file_write"),
        ("fail_tambah", "file_append"), ("fail_ada", "file_exists"),
        ("fail_buang", "file_delete"), ("fail_panjang", "file_size"),
        ("fail_senarai", "file_list_dir"), ("fail_baca_baris", "file_read_lines"),
    ] {
        let ty = Ty::Fn(Box::new(Ty::Any), Box::new(Ty::Any), Effect::FileSystem);
        c = c.extend(bm.to_string(), ty.clone());
        c = c.extend(en.to_string(), ty);
    }

    // ── Time builtins (masa) — Effect::Time ──
    for (bm, en) in &[
        ("masa_sekarang", "time_now"), ("masa_sekarang_ms", "time_now_ms"),
        ("masa_format", "time_format"), ("masa_urai", "time_parse"),
        ("masa_tidur", "time_sleep"), ("masa_jam", "time_clock"),
    ] {
        let ty = Ty::Fn(Box::new(Ty::Any), Box::new(Ty::Any), Effect::Time);
        c = c.extend(bm.to_string(), ty.clone());
        c = c.extend(en.to_string(), ty);
    }

    // ── JSON builtins ──
    for (bm, en) in &[
        ("json_urai", "json_parse"), ("json_ke_teks", "json_stringify"),
        ("json_dapat", "json_get"), ("json_letak", "json_set"),
        ("json_ada", "json_has"),
    ] {
        let ty = Ty::Fn(Box::new(Ty::Any), Box::new(Ty::Any), Effect::Pure);
        c = c.extend(bm.to_string(), ty.clone());
        c = c.extend(en.to_string(), ty);
    }

    // ── Extra math builtins ──
    for (bm, en) in &[
        ("baki", "rem"), ("log2", "log2"),
    ] {
        c = c.extend(bm.to_string(), Ty::Fn(Box::new(Ty::Int), Box::new(Ty::Int), Effect::Pure));
        c = c.extend(en.to_string(), Ty::Fn(Box::new(Ty::Int), Box::new(Ty::Int), Effect::Pure));
    }
    // Random — Effect::Random
    c = c.extend("rawak".to_string(), Ty::Fn(Box::new(Ty::Int), Box::new(Ty::Int), Effect::Random));
    c = c.extend("random".to_string(), Ty::Fn(Box::new(Ty::Int), Box::new(Ty::Int), Effect::Random));

    // ── Extra conversion builtins ──
    c = c.extend("bool_ke_nombor".to_string(), Ty::Fn(Box::new(Ty::Bool), Box::new(Ty::Int), Effect::Pure));
    c = c.extend("bool_to_int".to_string(), Ty::Fn(Box::new(Ty::Bool), Box::new(Ty::Int), Effect::Pure));
    c = c.extend("nombor_ke_teks".to_string(), Ty::Fn(Box::new(Ty::Int), Box::new(Ty::String), Effect::Pure));
    c = c.extend("int_to_string".to_string(), Ty::Fn(Box::new(Ty::Int), Box::new(Ty::String), Effect::Pure));

    c
}

/// Check if two types are compatible, considering Ty::Any as a wildcard.
pub fn types_compatible(expected: &Ty, found: &Ty) -> bool {
    if *expected == Ty::Any || *found == Ty::Any {
        return true;
    }
    expected == found
}

pub fn type_check(ctx: &Context, expr: &Expr) -> Result<(Ty, Effect), TypeError> {
    match expr {
        // VERIFIED: Values
        Expr::Unit => Ok((Ty::Unit, Effect::Pure)),
        Expr::Bool(_) => Ok((Ty::Bool, Effect::Pure)),
        Expr::Int(_) => Ok((Ty::Int, Effect::Pure)),
        Expr::String(_) => Ok((Ty::String, Effect::Pure)),
        Expr::Var(x) => {
            let ty = ctx.lookup(x).cloned().ok_or_else(|| TypeError::VarNotFound(x.clone()))?;
            Ok((ty, Effect::Pure))
        },

        // VERIFIED: Functions
        Expr::Lam(x, t1, body) => {
            let new_ctx = ctx.extend(x.clone(), t1.clone());
            let (t2, eff) = type_check(&new_ctx, body)?;
            Ok((Ty::Fn(Box::new(t1.clone()), Box::new(t2), eff), Effect::Pure))
        },
        Expr::App(e1, e2) => {
            let (t1, eff1) = type_check(ctx, e1)?;
            let (t2, eff2) = type_check(ctx, e2)?;
            
            match t1 {
                Ty::Fn(arg_ty, ret_ty, fn_eff) => {
                    if !types_compatible(&arg_ty, &t2) {
                        return Err(TypeError::TypeMismatch { expected: *arg_ty, found: t2 });
                    }
                    // Effect accumulation: eff1 + eff2 + fn_eff
                    let total_eff = eff1.join(eff2).join(fn_eff);
                    Ok((*ret_ty, total_eff))
                },
                _ => Err(TypeError::ExpectedFunction(t1)),
            }
        },

        // VERIFIED: Products
        Expr::Pair(e1, e2) => {
            let (t1, eff1) = type_check(ctx, e1)?;
            let (t2, eff2) = type_check(ctx, e2)?;
            Ok((Ty::Prod(Box::new(t1), Box::new(t2)), eff1.join(eff2)))
        },
        Expr::Fst(e) => {
            let (t, eff) = type_check(ctx, e)?;
            match t {
                Ty::Prod(t1, _) => Ok((*t1, eff)),
                _ => Err(TypeError::ExpectedProduct(t)),
            }
        },
        Expr::Snd(e) => {
            let (t, eff) = type_check(ctx, e)?;
            match t {
                Ty::Prod(_, t2) => Ok((*t2, eff)),
                _ => Err(TypeError::ExpectedProduct(t)),
            }
        },

        // VERIFIED: Sums
        Expr::Inl(e, ty) => {
            match ty {
                Ty::Sum(t1, t2) => {
                     let (te, eff) = type_check(ctx, e)?;
                     if te != **t1 {
                         return Err(TypeError::TypeMismatch { expected: *t1.clone(), found: te });
                     }
                     Ok((Ty::Sum(t1.clone(), t2.clone()), eff))
                },
                _ => Err(TypeError::ExpectedSum(ty.clone())),
            }
        },
        Expr::Inr(e, ty) => {
             match ty {
                Ty::Sum(t1, t2) => {
                     let (te, eff) = type_check(ctx, e)?;
                     if te != **t2 {
                         return Err(TypeError::TypeMismatch { expected: *t2.clone(), found: te });
                     }
                     Ok((Ty::Sum(t1.clone(), t2.clone()), eff))
                },
                _ => Err(TypeError::ExpectedSum(ty.clone())),
            }
        },
        Expr::Case(e, x, e1, y, e2) => {
            let (t, eff) = type_check(ctx, e)?;
            match t {
                Ty::Sum(t_left, t_right) => {
                    let ctx1 = ctx.extend(x.clone(), *t_left);
                    let (t1, eff1) = type_check(&ctx1, e1)?;
                    
                    let ctx2 = ctx.extend(y.clone(), *t_right);
                    let (t2, eff2) = type_check(&ctx2, e2)?;
                    
                    if t1 != t2 {
                        return Err(TypeError::TypeMismatch { expected: t1, found: t2 });
                    }
                    
                    Ok((t1, eff.join(eff1).join(eff2)))
                },
                _ => Err(TypeError::ExpectedSum(t)),
            }
        },

        // VERIFIED: Control
        Expr::If(cond, e2, e3) => {
            let (t_cond, eff1) = type_check(ctx, cond)?;
            if t_cond != Ty::Bool {
                return Err(TypeError::TypeMismatch { expected: Ty::Bool, found: t_cond });
            }
            
            let (t2, eff2) = type_check(ctx, e2)?;
            let (t3, eff3) = type_check(ctx, e3)?;
            
            if t2 != t3 {
                 return Err(TypeError::TypeMismatch { expected: t2, found: t3 });
            }
            
            Ok((t2, eff1.join(eff2).join(eff3)))
        },
        Expr::Let(x, e1, e2) => {
            let (t1, eff1) = type_check(ctx, e1)?;
            let ctx_new = ctx.extend(x.clone(), t1);
            let (t2, eff2) = type_check(&ctx_new, e2)?;
            Ok((t2, eff1.join(eff2)))
        },
        Expr::LetRec(x, ty_ann, e1, e2) => {
            // Typecheck binding with name already in scope (for recursion)
            let ctx_rec = ctx.extend(x.clone(), ty_ann.clone());
            let (t1, eff1) = type_check(&ctx_rec, e1)?;
            // Check that binding type is compatible with annotation
            if !types_compatible(ty_ann, &t1) {
                return Err(TypeError::AnnotationMismatch { expected: ty_ann.clone(), found: t1 });
            }
            let (t2, eff2) = type_check(&ctx_rec, e2)?;
            Ok((t2, eff1.join(eff2)))
        },

        // UNVERIFIED: Effects (Pending formalization in Typing.v)
        Expr::Perform(eff, e) => {
            let (te, eff_e) = type_check(ctx, e)?;
            // TODO: Validate payload type matches effect definition?
            // For now, assume payload is generic or valid.
            // In a real system, 'eff' would have a signature.
            Ok((te, eff_e.join(*eff))) 
        },
        Expr::Handle(e, _x, h) => {
             let (_t_e, _eff_e) = type_check(ctx, e)?;
             // Handle conceptually catches effects.
             // In full calculus, we need effect signatures.
             // Here we approximate: handler 'h' handles 'e'.
             // 'h' typically takes the effect payload or resumption.
             // This is a placeholder for the algebraic effect logic.
             let (t_h, eff_h) = type_check(ctx, h)?;
             // Result type usually matches e if handled fully.
             Ok((t_h, eff_h))
        },

        // UNVERIFIED: References (Pending formalization in Typing.v)
        Expr::Ref(e, l) => {
             let (t, eff) = type_check(ctx, e)?;
             Ok((Ty::Ref(Box::new(t), *l), eff.join(Effect::Write))) // Allocation is a write-like effect?
        },
        Expr::Deref(e) => {
            let (t, eff) = type_check(ctx, e)?;
            match t {
                Ty::Ref(inner, _l) => Ok((*inner, eff.join(Effect::Read))),
                _ => Err(TypeError::ExpectedRef(t)),
            }
        },
        Expr::Assign(e1, e2) => {
            let (t1, eff1) = type_check(ctx, e1)?;
            let (t2, eff2) = type_check(ctx, e2)?;
            match t1 {
                Ty::Ref(inner, _l) => {
                    if *inner != t2 {
                         return Err(TypeError::TypeMismatch { expected: *inner, found: t2 });
                    }
                    Ok((Ty::Unit, eff1.join(eff2).join(Effect::Write)))
                },
                _ => Err(TypeError::ExpectedRef(t1)),
            }
        },

        // UNVERIFIED: Security (Pending formalization in Typing.v)
        Expr::Classify(e) => {
             let (t, eff) = type_check(ctx, e)?;
             Ok((Ty::Secret(Box::new(t)), eff))
        },
        Expr::Declassify(e, _proof) => {
            let (t, eff) = type_check(ctx, e)?;
            match t {
                Ty::Secret(inner) => Ok((*inner, eff)),
                // Assuming we can define what a "proof" is later.
                 _ => Ok((t, eff)) // Declassifying non-secret is identity?
            }
        },
        Expr::Prove(e) => {
             let (t, eff) = type_check(ctx, e)?;
             Ok((Ty::Proof(Box::new(t)), eff))
        },
        
        // UNVERIFIED: Capabilities
        Expr::Require(eff, e) => {
             let (t, e_eff) = type_check(ctx, e)?;
             Ok((t, e_eff.join(*eff)))
        },
        Expr::Grant(_eff, e) => {
             // Grant satisfies a requirement?
             let (t, e_eff) = type_check(ctx, e)?;
             Ok((t, e_eff)) // Does it remove the effect from the context?
        },

        // Locations (runtime-only — corresponds to Coq ELoc)
        Expr::Loc(_) => {
            // Store locations are runtime values; typing requires store typing context.
            // Without store context, we return Ref(Unit, Public) as a conservative type.
            Ok((Ty::Ref(Box::new(Ty::Unit), SecurityLevel::Public), Effect::Pure))
        },

        // FFI call
        Expr::FFICall { name: _, args, ret_ty } => {
            let mut eff = Effect::System; // FFI is always effectful
            for arg in args {
                let (_t, e) = type_check(ctx, arg)?;
                eff = eff.join(e);
            }
            Ok((ret_ty.clone(), eff))
        },

        // Binary operations
        Expr::BinOp(op, e1, e2) => {
            let (t1, eff1) = type_check(ctx, e1)?;
            let (t2, eff2) = type_check(ctx, e2)?;
            let eff = eff1.join(eff2);
            match op {
                BinOp::Add => {
                    if t1 == Ty::String && t2 == Ty::String {
                        Ok((Ty::String, eff))
                    } else if t1 == Ty::Int && t2 == Ty::Int {
                        Ok((Ty::Int, eff))
                    } else {
                        return Err(TypeError::TypeMismatch { expected: t1, found: t2 });
                    }
                }
                BinOp::Sub | BinOp::Mul | BinOp::Div | BinOp::Mod => {
                    if t1 != Ty::Int {
                        return Err(TypeError::TypeMismatch { expected: Ty::Int, found: t1 });
                    }
                    if t2 != Ty::Int {
                        return Err(TypeError::TypeMismatch { expected: Ty::Int, found: t2 });
                    }
                    Ok((Ty::Int, eff))
                }
                BinOp::Eq | BinOp::Ne => {
                    // Eq/Ne work on Int, Bool, and String
                    if t1 != t2 {
                        return Err(TypeError::TypeMismatch { expected: t1, found: t2 });
                    }
                    if t1 != Ty::Int && t1 != Ty::Bool && t1 != Ty::String {
                        return Err(TypeError::TypeMismatch { expected: Ty::Int, found: t1 });
                    }
                    Ok((Ty::Bool, eff))
                }
                BinOp::Lt | BinOp::Le | BinOp::Gt | BinOp::Ge => {
                    if t1 != Ty::Int {
                        return Err(TypeError::TypeMismatch { expected: Ty::Int, found: t1 });
                    }
                    if t2 != Ty::Int {
                        return Err(TypeError::TypeMismatch { expected: Ty::Int, found: t2 });
                    }
                    Ok((Ty::Bool, eff))
                }
                BinOp::And | BinOp::Or => {
                    if t1 != Ty::Bool {
                        return Err(TypeError::TypeMismatch { expected: Ty::Bool, found: t1 });
                    }
                    if t2 != Ty::Bool {
                        return Err(TypeError::TypeMismatch { expected: Ty::Bool, found: t2 });
                    }
                    Ok((Ty::Bool, eff))
                }
            }
        }
    }
}

#[cfg(test)]
mod tests;
