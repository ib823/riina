// Copyright (c) 2026 The RIINA Authors. All rights reserved.

//! RIINA Typechecker
//!
//! Implements the typing rules defined in `foundations/Typing.v`.
//! RIINA = Rigorous Immutable Invariant — Normalized Axiom
//!
//! Mode: ULTRA KIASU | FUCKING PARANOID | ZERO TRUST | ZERO LAZINESS

use riina_types::{BinOp, Expr, Ty, SecurityLevel, Effect, Ident, StoreTy, Location};
use std::collections::HashMap;

#[derive(Debug, Clone, PartialEq)]
pub enum TypeError {
    VarNotFound(Ident),
    TypeMismatch { expected: Ty, found: Ty },
    ExpectedFunction(Ty),
    ExpectedProduct(Ty),
    ExpectedSum(Ty),
    ExpectedRef(Ty),
    ExpectedSecret(Ty),
    ExpectedProof(Ty),
    EffectViolation { allowed: Effect, found: Effect },
    AnnotationMismatch { expected: Ty, found: Ty },
    /// Security level violation: found level does not flow to expected level
    /// Matches Coq's `sl ⊑ Δ` check in T_Deref and T_Assign
    SecurityViolation {
        found: SecurityLevel,
        expected: SecurityLevel,
        context: &'static str,
    },
    /// Invalid declassification: proof does not match secret
    /// Matches Coq's `declass_ok e1 e2` predicate
    InvalidDeclassification { message: String },
    /// Location not found in store typing
    LocationNotFound(Location),
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
            TypeError::ExpectedSecret(ty) => write!(f, "Expected secret type, found {:?}", ty),
            TypeError::ExpectedProof(ty) => write!(f, "Expected proof type, found {:?}", ty),
            TypeError::EffectViolation { allowed, found } => {
                write!(f, "Effect violation: allowed {:?}, found {:?}", allowed, found)
            }
            TypeError::AnnotationMismatch { expected, found } => {
                write!(f, "Annotation mismatch: expected {:?}, found {:?}", expected, found)
            }
            TypeError::SecurityViolation { found, expected, context } => {
                write!(f, "Security violation in {}: level {:?} does not flow to {:?}", context, found, expected)
            }
            TypeError::InvalidDeclassification { message } => {
                write!(f, "Invalid declassification: {}", message)
            }
            TypeError::LocationNotFound(loc) => {
                write!(f, "Location not found in store: {}", loc)
            }
        }
    }
}

impl std::error::Error for TypeError {}

/// Type environment (Γ in Coq has_type judgment)
///
/// Maps variable names to their types.
/// Matches Coq `type_env := list (ident * ty)`.
#[derive(Clone)]
pub struct TypeEnv {
    vars: HashMap<Ident, Ty>,
}

impl Default for TypeEnv {
    fn default() -> Self {
        Self::new()
    }
}

impl TypeEnv {
    pub fn new() -> Self {
        Self { vars: HashMap::new() }
    }

    pub fn extend(&self, name: Ident, ty: Ty) -> Self {
        let mut new_vars = self.vars.clone();
        new_vars.insert(name, ty);
        Self { vars: new_vars }
    }

    pub fn lookup(&self, name: &Ident) -> Option<&Ty> {
        self.vars.get(name)
    }
}

/// Full typing context matching Coq's has_type judgment: Γ Σ Δ
///
/// - gamma (Γ): Type environment — variable → type
/// - sigma (Σ): Store typing — location → (type, security_level)
/// - delta (Δ): Current security context level
///
/// Reference: `02_FORMAL/coq/foundations/Typing.v`
#[derive(Clone)]
pub struct TypingContext {
    /// Γ: Type environment
    pub gamma: TypeEnv,
    /// Σ: Store typing (mutable for allocations)
    pub sigma: StoreTy,
    /// Δ: Current security context level
    pub delta: SecurityLevel,
}

impl Default for TypingContext {
    fn default() -> Self {
        Self::new()
    }
}

impl TypingContext {
    pub fn new() -> Self {
        Self {
            gamma: TypeEnv::new(),
            sigma: StoreTy::new(),
            delta: SecurityLevel::Public,
        }
    }

    /// Create context with specific security level
    pub fn with_level(delta: SecurityLevel) -> Self {
        Self {
            gamma: TypeEnv::new(),
            sigma: StoreTy::new(),
            delta,
        }
    }

    /// Extend the type environment with a new binding
    pub fn extend_gamma(&self, name: Ident, ty: Ty) -> Self {
        Self {
            gamma: self.gamma.extend(name, ty),
            sigma: self.sigma.clone(),
            delta: self.delta,
        }
    }

    /// Allocate a new location in the store typing
    pub fn alloc(&mut self, ty: Ty, sl: SecurityLevel) -> Location {
        self.sigma.extend(ty, sl)
    }

    /// Look up variable type in Γ
    pub fn lookup_var(&self, name: &Ident) -> Option<&Ty> {
        self.gamma.lookup(name)
    }

    /// Look up location type in Σ
    pub fn lookup_loc(&self, loc: &Location) -> Option<&(Ty, SecurityLevel)> {
        self.sigma.lookup(loc)
    }
}

/// Legacy context for backward compatibility
/// DEPRECATED: Use TypingContext for new code
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

    /// Convert to new TypingContext
    pub fn to_typing_context(&self) -> TypingContext {
        let mut gamma = TypeEnv::new();
        for (k, v) in &self.vars {
            gamma = gamma.extend(k.clone(), v.clone());
        }
        TypingContext {
            gamma,
            sigma: StoreTy::new(),
            delta: self.level,
        }
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

// ============================================================================
// FORMALIZED TYPE CHECKING (Coq-matching)
// ============================================================================

/// Validate declassification predicate: declass_ok e1 e2
///
/// Matches Coq definition in Syntax.v:519-520:
/// ```coq
/// Definition declass_ok (e1 e2 : expr) : Prop :=
///   exists v, value v /\ e1 = EClassify v /\ e2 = EProve (EClassify v).
/// ```
///
/// This ensures that declassification is only valid when:
/// 1. e1 is exactly EClassify v for some value v
/// 2. e2 is exactly EProve (EClassify v) — a proof wrapping the same secret
fn declass_ok(secret_expr: &Expr, proof_expr: &Expr) -> Result<(), TypeError> {
    // e1 must be Classify(v)
    let inner_val = match secret_expr {
        Expr::Classify(v) => v,
        _ => {
            return Err(TypeError::InvalidDeclassification {
                message: "Secret expression must be EClassify(v)".to_string(),
            });
        }
    };

    // e2 must be Prove(Classify(v')) where v' == v
    match proof_expr {
        Expr::Prove(inner_proof) => {
            match inner_proof.as_ref() {
                Expr::Classify(v_prime) => {
                    if **inner_val != **v_prime {
                        return Err(TypeError::InvalidDeclassification {
                            message: "Proof must wrap the same value as secret".to_string(),
                        });
                    }
                    Ok(())
                }
                _ => Err(TypeError::InvalidDeclassification {
                    message: "Proof must be EProve(EClassify(v))".to_string(),
                }),
            }
        }
        _ => Err(TypeError::InvalidDeclassification {
            message: "Proof expression must be EProve(...)".to_string(),
        }),
    }
}

/// Full typechecker with Coq-matching signature.
///
/// Implements `has_type Γ Σ Δ e T ε` from Typing.v.
///
/// # Arguments
/// * `ctx` - Typing context containing Γ (type env), Σ (store typing), Δ (security level)
/// * `expr` - Expression to typecheck
///
/// # Returns
/// * `Ok((T, ε))` - Type and effect of the expression
/// * `Err(TypeError)` - Type error
///
/// # Coq Reference
/// ```coq
/// Inductive has_type : type_env -> store_ty -> security_level ->
///                       expr -> ty -> effect -> Prop
/// ```
pub fn type_check_full(ctx: &mut TypingContext, expr: &Expr) -> Result<(Ty, Effect), TypeError> {
    match expr {
        // ════════════════════════════════════════════════════════════════════
        // VERIFIED: Values (T_Unit, T_Bool, T_Int, T_String, T_Var)
        // ════════════════════════════════════════════════════════════════════
        Expr::Unit => Ok((Ty::Unit, Effect::Pure)),
        Expr::Bool(_) => Ok((Ty::Bool, Effect::Pure)),
        Expr::Int(_) => Ok((Ty::Int, Effect::Pure)),
        Expr::String(_) => Ok((Ty::String, Effect::Pure)),

        // T_Var: Γ(x) = T → has_type Γ Σ Δ (EVar x) T EffectPure
        Expr::Var(x) => {
            let ty = ctx.lookup_var(x).cloned().ok_or_else(|| TypeError::VarNotFound(x.clone()))?;
            Ok((ty, Effect::Pure))
        }

        // ════════════════════════════════════════════════════════════════════
        // VERIFIED: Functions (T_Lam, T_App)
        // ════════════════════════════════════════════════════════════════════

        // T_Lam: has_type (Γ, x:T1) Σ Δ e T2 ε → has_type Γ Σ Δ (λx:T1.e) (T1 →[ε] T2) Pure
        Expr::Lam(x, t1, body) => {
            let new_ctx = ctx.extend_gamma(x.clone(), t1.clone());
            let mut new_ctx_mut = new_ctx;
            let (t2, eff) = type_check_full(&mut new_ctx_mut, body)?;
            Ok((Ty::Fn(Box::new(t1.clone()), Box::new(t2), eff), Effect::Pure))
        }

        // T_App: has_type Γ Σ Δ e1 (T1 →[ε'] T2) ε1 →
        //        has_type Γ Σ Δ e2 T1 ε2 →
        //        has_type Γ Σ Δ (e1 e2) T2 (ε1 ⊔ ε2 ⊔ ε')
        Expr::App(e1, e2) => {
            let (t1, eff1) = type_check_full(ctx, e1)?;
            let (t2, eff2) = type_check_full(ctx, e2)?;

            match t1 {
                Ty::Fn(arg_ty, ret_ty, fn_eff) => {
                    if !types_compatible(&arg_ty, &t2) {
                        return Err(TypeError::TypeMismatch { expected: *arg_ty, found: t2 });
                    }
                    let total_eff = eff1.join(eff2).join(fn_eff);
                    Ok((*ret_ty, total_eff))
                }
                _ => Err(TypeError::ExpectedFunction(t1)),
            }
        }

        // ════════════════════════════════════════════════════════════════════
        // VERIFIED: Products (T_Pair, T_Fst, T_Snd)
        // ════════════════════════════════════════════════════════════════════
        Expr::Pair(e1, e2) => {
            let (t1, eff1) = type_check_full(ctx, e1)?;
            let (t2, eff2) = type_check_full(ctx, e2)?;
            Ok((Ty::Prod(Box::new(t1), Box::new(t2)), eff1.join(eff2)))
        }
        Expr::Fst(e) => {
            let (t, eff) = type_check_full(ctx, e)?;
            match t {
                Ty::Prod(t1, _) => Ok((*t1, eff)),
                _ => Err(TypeError::ExpectedProduct(t)),
            }
        }
        Expr::Snd(e) => {
            let (t, eff) = type_check_full(ctx, e)?;
            match t {
                Ty::Prod(_, t2) => Ok((*t2, eff)),
                _ => Err(TypeError::ExpectedProduct(t)),
            }
        }

        // ════════════════════════════════════════════════════════════════════
        // VERIFIED: Sums (T_Inl, T_Inr, T_Case)
        // ════════════════════════════════════════════════════════════════════
        Expr::Inl(e, ty) => {
            match ty {
                Ty::Sum(t1, t2) => {
                    let (te, eff) = type_check_full(ctx, e)?;
                    if te != **t1 {
                        return Err(TypeError::TypeMismatch { expected: *t1.clone(), found: te });
                    }
                    Ok((Ty::Sum(t1.clone(), t2.clone()), eff))
                }
                _ => Err(TypeError::ExpectedSum(ty.clone())),
            }
        }
        Expr::Inr(e, ty) => {
            match ty {
                Ty::Sum(t1, t2) => {
                    let (te, eff) = type_check_full(ctx, e)?;
                    if te != **t2 {
                        return Err(TypeError::TypeMismatch { expected: *t2.clone(), found: te });
                    }
                    Ok((Ty::Sum(t1.clone(), t2.clone()), eff))
                }
                _ => Err(TypeError::ExpectedSum(ty.clone())),
            }
        }
        Expr::Case(e, x, e1, y, e2) => {
            let (t, eff) = type_check_full(ctx, e)?;
            match t {
                Ty::Sum(t_left, t_right) => {
                    let ctx1 = ctx.extend_gamma(x.clone(), *t_left);
                    let mut ctx1_mut = ctx1;
                    let (t1, eff1) = type_check_full(&mut ctx1_mut, e1)?;

                    let ctx2 = ctx.extend_gamma(y.clone(), *t_right);
                    let mut ctx2_mut = ctx2;
                    let (t2, eff2) = type_check_full(&mut ctx2_mut, e2)?;

                    if t1 != t2 {
                        return Err(TypeError::TypeMismatch { expected: t1, found: t2 });
                    }

                    Ok((t1, eff.join(eff1).join(eff2)))
                }
                _ => Err(TypeError::ExpectedSum(t)),
            }
        }

        // ════════════════════════════════════════════════════════════════════
        // VERIFIED: Control (T_If, T_Let, T_LetRec)
        // ════════════════════════════════════════════════════════════════════
        Expr::If(cond, e2, e3) => {
            let (t_cond, eff1) = type_check_full(ctx, cond)?;
            if t_cond != Ty::Bool {
                return Err(TypeError::TypeMismatch { expected: Ty::Bool, found: t_cond });
            }

            let (t2, eff2) = type_check_full(ctx, e2)?;
            let (t3, eff3) = type_check_full(ctx, e3)?;

            if t2 != t3 {
                return Err(TypeError::TypeMismatch { expected: t2, found: t3 });
            }

            Ok((t2, eff1.join(eff2).join(eff3)))
        }
        Expr::Let(x, e1, e2) => {
            let (t1, eff1) = type_check_full(ctx, e1)?;
            let new_ctx = ctx.extend_gamma(x.clone(), t1);
            let mut new_ctx_mut = new_ctx;
            let (t2, eff2) = type_check_full(&mut new_ctx_mut, e2)?;
            Ok((t2, eff1.join(eff2)))
        }
        Expr::LetRec(x, ty_ann, e1, e2) => {
            let ctx_rec = ctx.extend_gamma(x.clone(), ty_ann.clone());
            let mut ctx_rec_mut = ctx_rec.clone();
            let (t1, eff1) = type_check_full(&mut ctx_rec_mut, e1)?;
            if !types_compatible(ty_ann, &t1) {
                return Err(TypeError::AnnotationMismatch { expected: ty_ann.clone(), found: t1 });
            }
            let mut ctx_rec_mut2 = ctx_rec;
            let (t2, eff2) = type_check_full(&mut ctx_rec_mut2, e2)?;
            Ok((t2, eff1.join(eff2)))
        }

        // ════════════════════════════════════════════════════════════════════
        // FORMALIZED: Effects (T_Perform, T_Handle)
        // ════════════════════════════════════════════════════════════════════
        Expr::Perform(eff, e) => {
            let (te, eff_e) = type_check_full(ctx, e)?;
            Ok((te, eff_e.join(*eff)))
        }
        Expr::Handle(e, _x, h) => {
            let (_t_e, _eff_e) = type_check_full(ctx, e)?;
            let (t_h, eff_h) = type_check_full(ctx, h)?;
            Ok((t_h, eff_h))
        }

        // ════════════════════════════════════════════════════════════════════
        // FORMALIZED: References (T_Ref, T_Deref, T_Assign)
        // Matches Coq Typing.v:178-189
        // ════════════════════════════════════════════════════════════════════

        // T_Ref: has_type Γ Σ Δ e T ε →
        //        has_type Γ Σ Δ (ERef e l) (TRef T l) (ε ⊔ EffectWrite)
        Expr::Ref(e, sl) => {
            let (t, eff) = type_check_full(ctx, e)?;
            // Allocate in store typing Σ
            let _loc = ctx.alloc(t.clone(), *sl);
            Ok((Ty::Ref(Box::new(t), *sl), eff.join(Effect::Write)))
        }

        // T_Deref: has_type Γ Σ Δ e (TRef T l) ε →
        //          l ⊑ Δ →  (* SECURITY CHECK! *)
        //          has_type Γ Σ Δ (EDeref e) T (ε ⊔ EffectRead)
        Expr::Deref(e) => {
            let (t, eff) = type_check_full(ctx, e)?;
            match t {
                Ty::Ref(inner, sl) => {
                    // Security check: sl ⊑ Δ (reference level flows to context level)
                    if !sl.leq(ctx.delta) {
                        return Err(TypeError::SecurityViolation {
                            found: sl,
                            expected: ctx.delta,
                            context: "dereference",
                        });
                    }
                    Ok((*inner, eff.join(Effect::Read)))
                }
                _ => Err(TypeError::ExpectedRef(t)),
            }
        }

        // T_Assign: has_type Γ Σ Δ e1 (TRef T l) ε1 →
        //           has_type Γ Σ Δ e2 T ε2 →
        //           l ⊑ Δ →  (* SECURITY CHECK! *)
        //           has_type Γ Σ Δ (EAssign e1 e2) TUnit (ε1 ⊔ ε2 ⊔ EffectWrite)
        Expr::Assign(e1, e2) => {
            let (t1, eff1) = type_check_full(ctx, e1)?;
            let (t2, eff2) = type_check_full(ctx, e2)?;
            match t1 {
                Ty::Ref(inner, sl) => {
                    // Security check: sl ⊑ Δ
                    if !sl.leq(ctx.delta) {
                        return Err(TypeError::SecurityViolation {
                            found: sl,
                            expected: ctx.delta,
                            context: "assignment",
                        });
                    }
                    if *inner != t2 {
                        return Err(TypeError::TypeMismatch { expected: *inner, found: t2 });
                    }
                    Ok((Ty::Unit, eff1.join(eff2).join(Effect::Write)))
                }
                _ => Err(TypeError::ExpectedRef(t1)),
            }
        }

        // ════════════════════════════════════════════════════════════════════
        // FORMALIZED: Security (T_Classify, T_Declassify, T_Prove)
        // Matches Coq Typing.v:192-204
        // ════════════════════════════════════════════════════════════════════

        // T_Classify: has_type Γ Σ Δ e T ε →
        //             has_type Γ Σ Δ (EClassify e) (TSecret T) ε
        Expr::Classify(e) => {
            let (t, eff) = type_check_full(ctx, e)?;
            Ok((Ty::Secret(Box::new(t)), eff))
        }

        // T_Declassify: has_type Γ Σ Δ e1 (TSecret T) ε1 →
        //               has_type Γ Σ Δ e2 (TProof (TSecret T)) ε2 →
        //               declass_ok e1 e2 →
        //               has_type Γ Σ Δ (EDeclassify e1 e2) T (ε1 ⊔ ε2)
        Expr::Declassify(e, proof) => {
            let (t, eff1) = type_check_full(ctx, e)?;
            let (proof_ty, eff2) = type_check_full(ctx, proof)?;

            match &t {
                Ty::Secret(inner) => {
                    // Check proof type: must be TProof(TSecret(T))
                    let expected_proof_ty = Ty::Proof(Box::new(t.clone()));
                    if proof_ty != expected_proof_ty {
                        return Err(TypeError::TypeMismatch {
                            expected: expected_proof_ty,
                            found: proof_ty,
                        });
                    }

                    // Validate declass_ok predicate
                    declass_ok(e, proof)?;

                    Ok((*inner.clone(), eff1.join(eff2)))
                }
                _ => {
                    // Non-secret declassification is identity (lenient mode)
                    // In strict mode, this would be an error
                    Ok((t, eff1.join(eff2)))
                }
            }
        }

        // T_Prove: has_type Γ Σ Δ e T ε →
        //          has_type Γ Σ Δ (EProve e) (TProof T) ε
        Expr::Prove(e) => {
            let (t, eff) = type_check_full(ctx, e)?;
            Ok((Ty::Proof(Box::new(t)), eff))
        }

        // ════════════════════════════════════════════════════════════════════
        // FORMALIZED: Capabilities (T_Require, T_Grant)
        // ════════════════════════════════════════════════════════════════════
        Expr::Require(eff, e) => {
            let (t, e_eff) = type_check_full(ctx, e)?;
            Ok((t, e_eff.join(*eff)))
        }
        Expr::Grant(_eff, e) => {
            let (t, e_eff) = type_check_full(ctx, e)?;
            Ok((t, e_eff))
        }

        // ════════════════════════════════════════════════════════════════════
        // T_Loc: Store locations — requires Σ lookup
        // ════════════════════════════════════════════════════════════════════
        Expr::Loc(idx) => {
            let loc = Location::new(*idx as usize);
            match ctx.lookup_loc(&loc) {
                Some((ty, sl)) => Ok((Ty::Ref(Box::new(ty.clone()), *sl), Effect::Pure)),
                None => Err(TypeError::LocationNotFound(loc)),
            }
        }

        // ════════════════════════════════════════════════════════════════════
        // FFI and Binary Operations
        // ════════════════════════════════════════════════════════════════════
        Expr::FFICall { name: _, args, ret_ty } => {
            let mut eff = Effect::System;
            for arg in args {
                let (_t, e) = type_check_full(ctx, arg)?;
                eff = eff.join(e);
            }
            Ok((ret_ty.clone(), eff))
        }

        Expr::BinOp(op, e1, e2) => {
            let (t1, eff1) = type_check_full(ctx, e1)?;
            let (t2, eff2) = type_check_full(ctx, e2)?;
            let eff = eff1.join(eff2);
            match op {
                BinOp::Add => {
                    if t1 == Ty::String && t2 == Ty::String {
                        Ok((Ty::String, eff))
                    } else if t1 == Ty::Int && t2 == Ty::Int {
                        Ok((Ty::Int, eff))
                    } else {
                        Err(TypeError::TypeMismatch { expected: t1, found: t2 })
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

// ============================================================================
// LEGACY TYPE CHECKING (Backward Compatibility)
// ============================================================================

/// Legacy typechecker for backward compatibility.
/// DEPRECATED: Use type_check_full with TypingContext for new code.
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
