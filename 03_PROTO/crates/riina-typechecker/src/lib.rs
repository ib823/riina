// Copyright (c) 2026 The RIINA Authors. All rights reserved.

//! RIINA Typechecker
//!
//! Implements the typing rules defined in `foundations/Typing.v`.
//! RIINA = Rigorous Immutable Invariant, No Assumptions
//!
//! Mode: ULTRA KIASU | FUCKING PARANOID | ZERO TRUST | ZERO LAZINESS

use riina_types::{
    BinOp, Effect, Expr, Ident, Linearity, Location, SecurityLevel, SessionType, StoreTy, Ty, Usage,
};
use std::collections::{HashMap, HashSet};

pub mod multiparty;
pub mod program;
pub use program::check_program;

#[derive(Debug, Clone, PartialEq)]
pub enum TypeError {
    VarNotFound(Ident),
    TypeMismatch {
        expected: Ty,
        found: Ty,
    },
    ExpectedFunction(Ty),
    ExpectedProduct(Ty),
    ExpectedSum(Ty),
    ExpectedRef(Ty),
    ExpectedSecret(Ty),
    ExpectedProof(Ty),
    EffectViolation {
        allowed: Effect,
        found: Effect,
    },
    AnnotationMismatch {
        expected: Ty,
        found: Ty,
    },
    /// Security level violation: found level does not flow to expected level
    /// Matches Coq's `sl ⊑ Δ` check in T_Deref and T_Assign
    SecurityViolation {
        found: SecurityLevel,
        expected: SecurityLevel,
        context: &'static str,
    },
    /// Invalid declassification: proof does not match secret
    /// Matches Coq's `declass_ok e1 e2` predicate
    InvalidDeclassification {
        message: String,
    },
    /// Capability violation: an effect gate is required without a matching grant
    CapabilityViolation {
        required: Effect,
        message: String,
    },
    /// Location not found in store typing
    LocationNotFound(Location),
    /// Implicit information flow violation: branching on secret data
    /// and writing to a lower-security reference inside the branch.
    /// Matches Denning-style implicit flow prevention.
    ImplicitFlowViolation {
        branch_level: SecurityLevel,
        target_level: SecurityLevel,
        context: &'static str,
    },
    /// Tainted data flowing to sensitive sink without sanitization
    /// Matches Coq SQLInjectionPrevention.v:92 (taint_safe predicate)
    TaintViolation {
        taint_source: riina_types::TaintSource,
        required_sanitizer: riina_types::Sanitizer,
        context: &'static str,
    },
    /// Wrong sanitizer used for sensitive sink
    /// Matches Coq XSSPrevention.v:74 (context-specific encoding)
    SanitizerMismatch {
        expected: riina_types::Sanitizer,
        found: riina_types::Sanitizer,
        context: &'static str,
    },
    /// Constant-time violation: ConstantTime<T> value used in a context
    /// that would create a timing side-channel (branch condition, array index).
    /// This enforces the constant-time discipline: code processing
    /// ConstantTime values must not branch on them or use them as indices.
    ConstantTimeViolation {
        context: &'static str,
    },
    /// Linearity violation: variable used incorrectly given its linearity qualifier.
    /// Matches Coq LinearTypes.v linearity_check.
    LinearityViolation {
        var: Ident,
        linearity: Linearity,
        usage: Usage,
        message: String,
    },
    /// Expected an actor type but found something else
    ExpectedActor(Ty),
    /// Expected a CRDT type but found something else
    ExpectedCRDT(Ty),
    /// CRDT merge type mismatch: left and right operands have different CRDT types
    CRDTMismatch {
        left: Ty,
        right: Ty,
    },
    /// Choreography validation error
    ChoreographyError {
        message: String,
    },
    /// Crypto-agility (REQ-48): a program selects an algorithm the active policy
    /// marks Deprecated (e.g. a classical primitive past its NIST IR 8547 date).
    /// Mirrors the Coq `accepts` judgment in crypto/AlgorithmPolicy.v — an
    /// accepted program uses no deprecated algorithm.
    DeprecatedAlgorithm {
        algorithm: String,
        message: String,
    },
}

impl std::fmt::Display for TypeError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            TypeError::VarNotFound(id) => write!(f, "Variable not found: {}", id),
            TypeError::TypeMismatch { expected, found } => {
                write!(
                    f,
                    "Type mismatch: expected {:?}, found {:?}",
                    expected, found
                )
            }
            TypeError::ExpectedFunction(ty) => write!(f, "Expected function type, found {:?}", ty),
            TypeError::ExpectedProduct(ty) => write!(f, "Expected product type, found {:?}", ty),
            TypeError::ExpectedSum(ty) => write!(f, "Expected sum type, found {:?}", ty),
            TypeError::ExpectedRef(ty) => write!(f, "Expected reference type, found {:?}", ty),
            TypeError::ExpectedSecret(ty) => write!(f, "Expected secret type, found {:?}", ty),
            TypeError::ExpectedProof(ty) => write!(f, "Expected proof type, found {:?}", ty),
            TypeError::EffectViolation { allowed, found } => {
                write!(
                    f,
                    "Effect violation: allowed {:?}, found {:?}",
                    allowed, found
                )
            }
            TypeError::AnnotationMismatch { expected, found } => {
                write!(
                    f,
                    "Annotation mismatch: expected {:?}, found {:?}",
                    expected, found
                )
            }
            TypeError::SecurityViolation {
                found,
                expected,
                context,
            } => {
                write!(
                    f,
                    "Security violation in {}: level {:?} does not flow to {:?}",
                    context, found, expected
                )
            }
            TypeError::InvalidDeclassification { message } => {
                write!(f, "Invalid declassification: {}", message)
            }
            TypeError::CapabilityViolation { required, message } => {
                write!(f, "Capability violation for {:?}: {}", required, message)
            }
            TypeError::LocationNotFound(loc) => {
                write!(f, "Location not found in store: {}", loc)
            }
            TypeError::ImplicitFlowViolation {
                branch_level,
                target_level,
                context,
            } => {
                write!(
                    f,
                    "Implicit flow violation in {}: branching on {:?} data cannot write to {:?} reference",
                    context, branch_level, target_level
                )
            }
            TypeError::TaintViolation {
                taint_source,
                required_sanitizer,
                context,
            } => {
                write!(
                    f,
                    "Taint violation in {}: {:?} data requires {:?} sanitization before use",
                    context, taint_source, required_sanitizer
                )
            }
            TypeError::SanitizerMismatch {
                expected,
                found,
                context,
            } => {
                write!(
                    f,
                    "Sanitizer mismatch in {}: expected {:?}, found {:?}",
                    context, expected, found
                )
            }
            TypeError::ConstantTimeViolation { context } => {
                write!(
                    f,
                    "Constant-time violation: ConstantTime value used in {} (creates timing side-channel)",
                    context
                )
            }
            TypeError::LinearityViolation {
                var,
                linearity,
                usage,
                message,
            } => {
                write!(
                    f,
                    "Linearity violation for '{}': {:?} variable has {:?} usage — {}",
                    var, linearity, usage, message
                )
            }
            TypeError::ExpectedActor(ty) => write!(f, "Expected actor type, found {:?}", ty),
            TypeError::ExpectedCRDT(ty) => write!(f, "Expected CRDT type, found {:?}", ty),
            TypeError::CRDTMismatch { left, right } => {
                write!(
                    f,
                    "CRDT merge type mismatch: left {:?}, right {:?}",
                    left, right
                )
            }
            TypeError::ChoreographyError { message } => {
                write!(f, "Choreography error: {}", message)
            }
            TypeError::DeprecatedAlgorithm { algorithm, message } => {
                write!(f, "Deprecated crypto algorithm '{}': {}", algorithm, message)
            }
        }
    }
}

impl std::error::Error for TypeError {}

impl TypeError {
    /// Return a human-readable fix hint for this error.
    /// Used by `riinac check --json` to help AI agents fix code.
    #[must_use]
    pub fn fix_hint(&self) -> Option<String> {
        Some(match self {
            TypeError::TypeMismatch { expected, found } => {
                format!(
                    "Convert with ke_nombor()/ke_teks()/ke_bool(), or change the annotation from {:?} to {:?}",
                    expected, found
                )
            }
            TypeError::VarNotFound(name) => {
                format!("Did you mean a different variable? Check spelling of '{name}'")
            }
            TypeError::EffectViolation { allowed: _, found } => {
                format!(
                    "Add 'kesan {:?}' to the function signature, or remove the {:?} operation",
                    found, found
                )
            }
            TypeError::SecurityViolation {
                found,
                expected,
                context,
            } => {
                format!(
                    "In {context}: level {:?} does not flow to {:?}. Use 'dedah' with a proof to declassify, or raise the context security level",
                    found, expected
                )
            }
            TypeError::ExpectedFunction(ty) => {
                format!(
                    "'{:?}' is not a function. Check that you are calling a function, not a value",
                    ty
                )
            }
            TypeError::ExpectedSecret(_) => {
                "Wrap the value with sulit(value) or Rahsia(value) to make it secret".to_string()
            }
            TypeError::InvalidDeclassification { .. } => {
                "Provide a valid Bukti proof term: dedah(sulit(value), bukti(sulit(value)))"
                    .to_string()
            }
            TypeError::CapabilityViolation { required, .. } => {
                format!(
                    "Add a prior or enclosing 'beri {:?} ...' before the guarded operation, or remove the matching 'perlu {:?}'",
                    required, required
                )
            }
            TypeError::AnnotationMismatch { expected, found } => {
                format!(
                    "Function body evaluates to {:?} but is declared as {:?}. Change the return type annotation or fix the body",
                    found, expected
                )
            }
            TypeError::ExpectedRef(_) => {
                "Use 'ruj' to create a reference first: biar r = ruj value @Awam;".to_string()
            }
            TypeError::LocationNotFound(_) => {
                "Location not in store typing — ensure the reference was allocated with 'ruj'"
                    .to_string()
            }
            TypeError::ExpectedProduct(_) => {
                "Expected a pair/tuple (T1, T2). Use fst/snd only on pairs".to_string()
            }
            TypeError::ExpectedSum(_) => {
                "Expected a sum type. Use inl/inr constructors".to_string()
            }
            TypeError::ExpectedProof(_) => {
                "Expected a Bukti<T> proof type. Use bukti(expr) to create one".to_string()
            }
            TypeError::ImplicitFlowViolation {
                branch_level,
                target_level,
                ..
            } => {
                format!(
                    "Cannot write to {:?}-level reference inside a branch guarded by {:?}-level data. \
                     Use a {:?}-level reference or declassify the condition first",
                    target_level, branch_level, branch_level
                )
            }
            TypeError::TaintViolation {
                taint_source,
                required_sanitizer,
                ..
            } => {
                format!(
                    "Sanitize the {:?} input with {:?} first. Example: biar bersih = sanitize_sql(input);",
                    taint_source, required_sanitizer
                )
            }
            TypeError::SanitizerMismatch { expected, .. } => {
                format!("Use the correct sanitizer for this context: {:?}", expected)
            }
            TypeError::ConstantTimeViolation { context } => {
                format!(
                    "Do not use ConstantTime values in {context}. \
                     Use constant-time comparison functions instead of branching on secret data"
                )
            }
            TypeError::LinearityViolation { linearity, .. } => {
                match linearity {
                    Linearity::Linear => "Linear variables must be used exactly once. Remove duplicate uses or change linearity to Affine/Unrestricted".to_string(),
                    Linearity::Affine => "Affine variables can be used at most once. Remove duplicate uses or change linearity to Unrestricted".to_string(),
                    Linearity::Relevant => "Relevant variables must be used at least once. Add a use or change linearity to Unrestricted".to_string(),
                    Linearity::Unrestricted => "Unrestricted variables have no usage constraints — this error should not occur".to_string(),
                }
            }
            TypeError::ExpectedActor(_) => {
                "Expected an Actor type. Use 'aktor' to declare an actor first".to_string()
            }
            TypeError::ExpectedCRDT(_) => {
                "Expected a CRDT type. Use CRDT(T, Op) type annotation".to_string()
            }
            TypeError::CRDTMismatch { .. } => {
                "Both operands of CRDT merge must have the same CRDT type".to_string()
            }
            TypeError::ChoreographyError { .. } => {
                "Choreography blocks require at least 2 roles and a well-formed protocol".to_string()
            }
            TypeError::DeprecatedAlgorithm { .. } => {
                "This algorithm is deprecated by policy; migrate to a current algorithm \
                 (see docs/MEMORY_SAFETY_ROADMAP.md and the crypto agility policy)".to_string()
            }
        })
    }

    /// Return an error code for this error type.
    #[must_use]
    pub fn error_code(&self) -> &'static str {
        match self {
            TypeError::VarNotFound(_) => "T0001",
            TypeError::TypeMismatch { .. } => "T0002",
            TypeError::ExpectedFunction(_) => "T0003",
            TypeError::ExpectedProduct(_) => "T0004",
            TypeError::ExpectedSum(_) => "T0005",
            TypeError::ExpectedRef(_) => "T0006",
            TypeError::ExpectedSecret(_) => "T0007",
            TypeError::ExpectedProof(_) => "T0008",
            TypeError::EffectViolation { .. } => "E0001",
            TypeError::AnnotationMismatch { .. } => "T0009",
            TypeError::SecurityViolation { .. } => "S0001",
            TypeError::InvalidDeclassification { .. } => "S0002",
            TypeError::ImplicitFlowViolation { .. } => "S0003",
            TypeError::CapabilityViolation { .. } => "CAP0001",
            TypeError::LocationNotFound(_) => "T0010",
            TypeError::TaintViolation { .. } => "TAINT001",
            TypeError::SanitizerMismatch { .. } => "TAINT002",
            TypeError::ConstantTimeViolation { .. } => "CT0001",
            TypeError::LinearityViolation { .. } => "LIN0001",
            TypeError::ExpectedActor(_) => "J0001",
            TypeError::ExpectedCRDT(_) => "J0002",
            TypeError::CRDTMismatch { .. } => "J0003",
            TypeError::ChoreographyError { .. } => "J0004",
            TypeError::DeprecatedAlgorithm { .. } => "K0001",
        }
    }

    /// Return a reference to the Coq typing rule related to this error.
    #[must_use]
    pub fn coq_rule(&self) -> Option<&'static str> {
        match self {
            TypeError::TypeMismatch { .. } => Some("T_App (Typing.v:142)"),
            TypeError::ExpectedFunction(_) => {
                Some("T_App (Typing.v:142) — e1 must have function type")
            }
            TypeError::EffectViolation { .. } => {
                Some("effect_sub (EffectSystem.v:89) — effect hierarchy")
            }
            TypeError::SecurityViolation { context, .. } => match *context {
                "dereference" => Some("T_Deref (Typing.v:178) — sl must flow to delta"),
                "assignment" => Some("T_Assign (Typing.v:183) — sl must flow to delta"),
                _ => Some("Information flow lattice (Syntax.v:48)"),
            },
            TypeError::InvalidDeclassification { .. } => {
                Some("T_Declassify (Typing.v:196) — declass_ok predicate")
            }
            TypeError::ImplicitFlowViolation { .. } => {
                Some("Denning implicit flow — Δ elevated in branch (NonInterference.v)")
            }
            TypeError::CapabilityViolation { .. } => Some("T_Require/T_Grant (Typing.v:207-213)"),
            TypeError::ExpectedRef(_) => Some("T_Deref (Typing.v:178) — operand must be TRef"),
            TypeError::ExpectedSecret(_) => {
                Some("T_Classify (Typing.v:192) — operand must be TSecret")
            }
            TypeError::TaintViolation { .. } => {
                Some("SQLInjectionPrevention.v:92 — taint_safe predicate")
            }
            TypeError::SanitizerMismatch { .. } => {
                Some("XSSPrevention.v:74 — context-specific encoding required")
            }
            TypeError::ConstantTimeViolation { .. } => {
                Some("ConstantTimeSecurity.v:56 — ct_safe predicate forbids branching on CT values")
            }
            TypeError::LinearityViolation { .. } => {
                Some("LinearTypes.v:172 — linearity_check enforces usage constraints")
            }
            _ => None,
        }
    }
}

/// Type environment (Γ in Coq has_type judgment)
///
/// Maps variable names to their types, with optional linearity qualifiers.
/// Matches Coq `type_env := list (ident * ty)` (basic) and
/// `LEntry := (nat * LTy * Linearity * Usage)` (linear extension).
#[derive(Clone)]
pub struct TypeEnv {
    vars: HashMap<Ident, Ty>,
    /// Linearity tracking: (linearity qualifier, current usage count).
    /// Only populated for variables with non-Unrestricted linearity.
    linearity: HashMap<Ident, (Linearity, Usage)>,
}

impl Default for TypeEnv {
    fn default() -> Self {
        Self::new()
    }
}

impl TypeEnv {
    pub fn new() -> Self {
        Self {
            vars: HashMap::new(),
            linearity: HashMap::new(),
        }
    }

    /// Iterate the bindings (name → type). Used by tooling that needs to walk
    /// the registered builtins, e.g. the stdlib API-doc generator.
    pub fn iter(&self) -> impl Iterator<Item = (&Ident, &Ty)> {
        self.vars.iter()
    }

    /// Extend with an unrestricted (default) binding.
    pub fn extend(&self, name: Ident, ty: Ty) -> Self {
        let mut new_vars = self.vars.clone();
        new_vars.insert(name, ty);
        Self {
            vars: new_vars,
            linearity: self.linearity.clone(),
        }
    }

    /// Extend with an explicit linearity qualifier.
    /// Linear/Affine/Relevant bindings start at Usage::Zero.
    pub fn extend_linear(&self, name: Ident, ty: Ty, lin: Linearity) -> Self {
        let mut new_vars = self.vars.clone();
        new_vars.insert(name.clone(), ty);
        let mut new_lin = self.linearity.clone();
        if lin != Linearity::Unrestricted {
            new_lin.insert(name, (lin, Usage::Zero));
        }
        Self {
            vars: new_vars,
            linearity: new_lin,
        }
    }

    pub fn lookup(&self, name: &Ident) -> Option<&Ty> {
        self.vars.get(name)
    }

    /// Record a use of a variable. Returns error if the variable has been
    /// consumed beyond its linearity allows.
    pub fn record_use(&mut self, name: &Ident) -> Result<(), TypeError> {
        if let Some((lin, usage)) = self.linearity.get_mut(name) {
            let new_usage = usage.increment();
            // Linear: exactly once → reject second use
            if *lin == Linearity::Linear && new_usage == Usage::Many {
                return Err(TypeError::LinearityViolation {
                    var: name.clone(),
                    linearity: *lin,
                    usage: new_usage,
                    message: "linear variable used more than once".to_string(),
                });
            }
            // Affine: at most once → reject second use
            if *lin == Linearity::Affine && new_usage == Usage::Many {
                return Err(TypeError::LinearityViolation {
                    var: name.clone(),
                    linearity: *lin,
                    usage: new_usage,
                    message: "affine variable used more than once".to_string(),
                });
            }
            *usage = new_usage;
        }
        Ok(())
    }

    /// Check linearity constraints at scope exit.
    /// Call this after type-checking the body where the binding was in scope.
    pub fn check_linearity_at_exit(&self, name: &Ident) -> Result<(), TypeError> {
        if let Some((lin, usage)) = self.linearity.get(name) {
            match lin {
                Linearity::Linear if *usage != Usage::One => {
                    return Err(TypeError::LinearityViolation {
                        var: name.clone(),
                        linearity: *lin,
                        usage: *usage,
                        message: format!(
                            "linear variable must be used exactly once, but was used {:?}",
                            usage
                        ),
                    });
                }
                Linearity::Relevant if *usage == Usage::Zero => {
                    return Err(TypeError::LinearityViolation {
                        var: name.clone(),
                        linearity: *lin,
                        usage: *usage,
                        message: "relevant variable must be used at least once".to_string(),
                    });
                }
                _ => {} // Affine: Zero or One is fine; Unrestricted: anything is fine
            }
        }
        Ok(())
    }

    /// Get linearity info for a variable, if tracked.
    pub fn get_linearity(&self, name: &Ident) -> Option<(Linearity, Usage)> {
        self.linearity.get(name).copied()
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
    /// Granted capabilities: effects authorized by enclosing Grant expressions
    /// Matches Coq T_Grant/T_Require (Typing.v:209-215)
    pub granted: HashSet<Effect>,
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
            granted: HashSet::new(),
        }
    }

    /// Create context with specific security level
    pub fn with_level(delta: SecurityLevel) -> Self {
        Self {
            gamma: TypeEnv::new(),
            sigma: StoreTy::new(),
            delta,
            granted: HashSet::new(),
        }
    }

    /// Extend the type environment with a new binding
    pub fn extend_gamma(&self, name: Ident, ty: Ty) -> Self {
        Self {
            gamma: self.gamma.extend(name, ty),
            sigma: self.sigma.clone(),
            delta: self.delta,
            granted: self.granted.clone(),
        }
    }

    /// Extend gamma with an explicit linearity qualifier.
    /// Used for `let lin x = e1 in e2` where x has restricted usage.
    pub fn extend_gamma_linear(&self, name: Ident, ty: Ty, lin: Linearity) -> Self {
        Self {
            gamma: self.gamma.extend_linear(name, ty, lin),
            sigma: self.sigma.clone(),
            delta: self.delta,
            granted: self.granted.clone(),
        }
    }

    /// Create context with an additional granted capability
    pub fn with_grant(&self, eff: Effect) -> Self {
        let mut granted = self.granted.clone();
        granted.insert(eff);
        Self {
            gamma: self.gamma.clone(),
            sigma: self.sigma.clone(),
            delta: self.delta,
            granted,
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

    /// Iterate the bindings (name → type). Used by tooling that walks the
    /// registered builtins, e.g. the stdlib API-doc generator.
    pub fn iter(&self) -> impl Iterator<Item = (&Ident, &Ty)> {
        self.vars.iter()
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
            granted: HashSet::new(),
        }
    }
}

/// Register builtin function types into a context.
/// Uses Ty::Any for polymorphic builtins.
pub fn register_builtin_types(ctx: &Context) -> Context {
    let mut c = ctx.clone();
    // I/O builtins. Printing to stdout is a Write effect (`Tulis`), matching the
    // documented effect vocabulary and the example corpus — a function that
    // prints declares `kesan Tulis`.
    c = c.extend(
        "cetak".to_string(),
        Ty::Fn(Box::new(Ty::Any), Box::new(Ty::Unit), Effect::Write),
    );
    c = c.extend(
        "print".to_string(),
        Ty::Fn(Box::new(Ty::Any), Box::new(Ty::Unit), Effect::Write),
    );
    c = c.extend(
        "cetakln".to_string(),
        Ty::Fn(Box::new(Ty::Any), Box::new(Ty::Unit), Effect::Write),
    );
    // `cetak_baris` ("print line") is the BM name the example corpus uses for a
    // line-terminated print; same signature as `cetakln`.
    c = c.extend(
        "cetak_baris".to_string(),
        Ty::Fn(Box::new(Ty::Any), Box::new(Ty::Unit), Effect::Write),
    );
    c = c.extend(
        "println".to_string(),
        Ty::Fn(Box::new(Ty::Any), Box::new(Ty::Unit), Effect::Write),
    );
    // String
    c = c.extend(
        "gabung_teks".to_string(),
        Ty::Fn(
            Box::new(Ty::Prod(Box::new(Ty::String), Box::new(Ty::String))),
            Box::new(Ty::String),
            Effect::Pure,
        ),
    );
    c = c.extend(
        "concat".to_string(),
        Ty::Fn(
            Box::new(Ty::Prod(Box::new(Ty::String), Box::new(Ty::String))),
            Box::new(Ty::String),
            Effect::Pure,
        ),
    );
    c = c.extend(
        "panjang".to_string(),
        Ty::Fn(Box::new(Ty::String), Box::new(Ty::Int), Effect::Pure),
    );
    c = c.extend(
        "length".to_string(),
        Ty::Fn(Box::new(Ty::String), Box::new(Ty::Int), Effect::Pure),
    );
    // Range constructors `a..b` / `a..=b`: (Int, Int) -> List<Int>.
    c = c.extend(
        "julat".to_string(),
        Ty::Fn(
            Box::new(Ty::Prod(Box::new(Ty::Int), Box::new(Ty::Int))),
            Box::new(Ty::List(Box::new(Ty::Int))),
            Effect::Pure,
        ),
    );
    c = c.extend(
        "julat_inklusif".to_string(),
        Ty::Fn(
            Box::new(Ty::Prod(Box::new(Ty::Int), Box::new(Ty::Int))),
            Box::new(Ty::List(Box::new(Ty::Int))),
            Effect::Pure,
        ),
    );
    // Sum (Option/Result) introspection for constructor-pattern desugaring.
    c = c.extend(
        "adalah_kiri".to_string(),
        Ty::Fn(Box::new(Ty::Any), Box::new(Ty::Bool), Effect::Pure),
    );
    c = c.extend(
        "adalah_kanan".to_string(),
        Ty::Fn(Box::new(Ty::Any), Box::new(Ty::Bool), Effect::Pure),
    );
    c = c.extend(
        "nilai_kiri".to_string(),
        Ty::Fn(Box::new(Ty::Any), Box::new(Ty::Any), Effect::Pure),
    );
    c = c.extend(
        "nilai_kanan".to_string(),
        Ty::Fn(Box::new(Ty::Any), Box::new(Ty::Any), Effect::Pure),
    );
    // Conversion
    c = c.extend(
        "ke_teks".to_string(),
        Ty::Fn(Box::new(Ty::Any), Box::new(Ty::String), Effect::Pure),
    );
    c = c.extend(
        "to_string".to_string(),
        Ty::Fn(Box::new(Ty::Any), Box::new(Ty::String), Effect::Pure),
    );
    c = c.extend(
        "ke_nombor".to_string(),
        Ty::Fn(Box::new(Ty::String), Box::new(Ty::Int), Effect::Pure),
    );
    c = c.extend(
        "parse_int".to_string(),
        Ty::Fn(Box::new(Ty::String), Box::new(Ty::Int), Effect::Pure),
    );
    // Arbitrary-precision integer constructor (numeric-tower BigInt slice):
    // parse a base-10 string of any length into a `BigInt`.
    for nm in ["besar", "bigint"] {
        c = c.extend(
            nm.to_string(),
            Ty::Fn(Box::new(Ty::String), Box::new(Ty::BigInt), Effect::Pure),
        );
    }
    // Arbitrary-precision decimal constructor (numeric-tower decimal slice):
    // parse a decimal literal string into a `Decimal`.
    for nm in ["perpuluhan", "decimal"] {
        c = c.extend(
            nm.to_string(),
            Ty::Fn(Box::new(Ty::String), Box::new(Ty::Decimal), Effect::Pure),
        );
    }
    // Fixed-scale decimal / money (numeric-tower fixed-point slice): `wang` parses
    // a literal (scale inferred from the digits); `titik_tetap` takes a
    // `(literal, scale)` pair and rounds half-to-even to that scale.
    for nm in ["wang", "money"] {
        c = c.extend(
            nm.to_string(),
            Ty::Fn(Box::new(Ty::String), Box::new(Ty::Fixed), Effect::Pure),
        );
    }
    for nm in ["titik_tetap", "fixed"] {
        c = c.extend(
            nm.to_string(),
            Ty::Fn(
                Box::new(Ty::Prod(Box::new(Ty::String), Box::new(Ty::Int))),
                Box::new(Ty::Fixed),
                Effect::Pure,
            ),
        );
    }
    // Binary fixed-point / Q-format: `qmn((literal, frac_bits)) -> Qmn`.
    for nm in ["qmn", "binary_fixed"] {
        c = c.extend(
            nm.to_string(),
            Ty::Fn(
                Box::new(Ty::Prod(Box::new(Ty::String), Box::new(Ty::Int))),
                Box::new(Ty::FixedBin),
                Effect::Pure,
            ),
        );
    }
    // Unicode NFC normalization (UAX #15): `String -> String`, pure.
    for nm in ["nfc", "ke_nfc"] {
        c = c.extend(
            nm.to_string(),
            Ty::Fn(Box::new(Ty::String), Box::new(Ty::String), Effect::Pure),
        );
    }
    // UTS #39 confusable skeleton (`String -> String`) + detection
    // (`(String, String) -> Bool`), both pure.
    for nm in ["skeleton", "rangka"] {
        c = c.extend(
            nm.to_string(),
            Ty::Fn(Box::new(Ty::String), Box::new(Ty::String), Effect::Pure),
        );
    }
    for nm in ["adalah_keliru", "is_confusable"] {
        c = c.extend(
            nm.to_string(),
            Ty::Fn(
                Box::new(Ty::Prod(Box::new(Ty::String), Box::new(Ty::String))),
                Box::new(Ty::Bool),
                Effect::Pure,
            ),
        );
    }
    // Virtual-filesystem builtins (verified access-control via riina-os VFS).
    // `vfs_mula`/`vfs_jadi_pengguna` take an Int (byte quota / uid); `vfs_tulis`
    // a `(path, data)` pair; `vfs_baca`/`vfs_padam` a path. All carry filesystem
    // effects (not the capability-gated `System`) so they are usable directly.
    let unit_ty = || Box::new(Ty::Unit);
    for nm in ["vfs_mula", "vfs_init", "vfs_jadi_pengguna", "vfs_become_user"] {
        c = c.extend(
            nm.to_string(),
            Ty::Fn(Box::new(Ty::Int), unit_ty(), Effect::FileSystem),
        );
    }
    for nm in ["vfs_tulis", "vfs_write"] {
        c = c.extend(
            nm.to_string(),
            Ty::Fn(
                Box::new(Ty::Prod(Box::new(Ty::String), Box::new(Ty::String))),
                unit_ty(),
                Effect::Write,
            ),
        );
    }
    for nm in ["vfs_baca", "vfs_read"] {
        c = c.extend(
            nm.to_string(),
            Ty::Fn(Box::new(Ty::String), Box::new(Ty::String), Effect::Read),
        );
    }
    for nm in ["vfs_padam", "vfs_delete"] {
        c = c.extend(
            nm.to_string(),
            Ty::Fn(Box::new(Ty::String), Box::new(Ty::Bool), Effect::Write),
        );
    }
    // Network builtins (real TCP gated by the verified RFC 793 state machine
    // in riina-os `net`). `jaring_sambung` takes "host:port" and returns a
    // connection id; `jaring_hantar` a `(conn, data)` pair returning the byte
    // count; `jaring_terima` a `(conn, max_bytes)` pair returning the data;
    // `jaring_tutup` a connection id. All carry the Network effect.
    for nm in ["jaring_sambung", "net_connect"] {
        c = c.extend(
            nm.to_string(),
            Ty::Fn(Box::new(Ty::String), Box::new(Ty::Int), Effect::Network),
        );
    }
    for nm in ["jaring_hantar", "net_send"] {
        c = c.extend(
            nm.to_string(),
            Ty::Fn(
                Box::new(Ty::Prod(Box::new(Ty::Int), Box::new(Ty::String))),
                Box::new(Ty::Int),
                Effect::Network,
            ),
        );
    }
    for nm in ["jaring_terima", "net_recv"] {
        c = c.extend(
            nm.to_string(),
            Ty::Fn(
                Box::new(Ty::Prod(Box::new(Ty::Int), Box::new(Ty::Int))),
                Box::new(Ty::String),
                Effect::Network,
            ),
        );
    }
    for nm in ["jaring_tutup", "net_close"] {
        c = c.extend(
            nm.to_string(),
            Ty::Fn(Box::new(Ty::Int), Box::new(Ty::Bool), Effect::Network),
        );
    }
    // Passive open: `jaring_dengar` binds "host:port" and returns a listener
    // id; `jaring_alamat` reports its actual local address (ephemeral-port
    // discovery); `jaring_terima_sambungan` blocks for one connection and
    // returns a connection id usable with hantar/terima/tutup.
    for nm in ["jaring_dengar", "net_listen"] {
        c = c.extend(
            nm.to_string(),
            Ty::Fn(Box::new(Ty::String), Box::new(Ty::Int), Effect::Network),
        );
    }
    for nm in ["jaring_alamat", "net_local_addr"] {
        c = c.extend(
            nm.to_string(),
            Ty::Fn(Box::new(Ty::Int), Box::new(Ty::String), Effect::Network),
        );
    }
    for nm in ["jaring_terima_sambungan", "net_accept"] {
        c = c.extend(
            nm.to_string(),
            Ty::Fn(Box::new(Ty::Int), Box::new(Ty::Int), Effect::Network),
        );
    }
    // TLS 1.3 record protection (real AEAD via riina-tls on riina-core):
    // `jaring_tls_kunci` installs keys from `(conn, traffic_secret)`;
    // `jaring_tls_hantar` seals `(conn, data)`; `jaring_tls_terima` opens the
    // next record on a conn. NetworkSecure effect — these are the encrypted
    // paths, distinguished from the plaintext `jaring_*` Network ones.
    // A real TLS 1.3 handshake over an established connection (ECDHE + key
    // schedule + Finished): `Nombor -> Benar`, NetworkSecure.
    for nm in ["jaring_tls_jabat", "net_tls_handshake"] {
        c = c.extend(
            nm.to_string(),
            Ty::Fn(Box::new(Ty::Int), Box::new(Ty::Bool), Effect::NetworkSecure),
        );
    }
    // Authentication (RFC 7250 raw public keys + §4.4.3 CertificateVerify):
    // identity takes a hex seed and returns the hex credential; percaya pins a
    // hex credential; jabat_sah runs the authenticated handshake; disahkan
    // reports whether the full Coq tls_connected conjunction holds.
    for nm in ["jaring_tls_identiti", "net_tls_identity"] {
        c = c.extend(
            nm.to_string(),
            Ty::Fn(
                Box::new(Ty::String),
                Box::new(Ty::String),
                Effect::NetworkSecure,
            ),
        );
    }
    for nm in ["jaring_tls_percaya", "net_tls_trust"] {
        c = c.extend(
            nm.to_string(),
            Ty::Fn(Box::new(Ty::String), Box::new(Ty::Bool), Effect::NetworkSecure),
        );
    }
    for nm in ["jaring_tls_jabat_sah", "net_tls_handshake_auth"] {
        c = c.extend(
            nm.to_string(),
            Ty::Fn(Box::new(Ty::Int), Box::new(Ty::Bool), Effect::NetworkSecure),
        );
    }
    for nm in ["jaring_tls_disahkan", "net_tls_is_authenticated"] {
        c = c.extend(
            nm.to_string(),
            Ty::Fn(Box::new(Ty::Int), Box::new(Ty::Bool), Effect::NetworkSecure),
        );
    }
    for nm in ["jaring_tls_kunci", "net_tls_keys"] {
        c = c.extend(
            nm.to_string(),
            Ty::Fn(
                Box::new(Ty::Prod(Box::new(Ty::Int), Box::new(Ty::String))),
                Box::new(Ty::Bool),
                Effect::NetworkSecure,
            ),
        );
    }
    for nm in ["jaring_tls_hantar", "net_tls_send"] {
        c = c.extend(
            nm.to_string(),
            Ty::Fn(
                Box::new(Ty::Prod(Box::new(Ty::Int), Box::new(Ty::String))),
                Box::new(Ty::Int),
                Effect::NetworkSecure,
            ),
        );
    }
    for nm in ["jaring_tls_terima", "net_tls_recv"] {
        c = c.extend(
            nm.to_string(),
            Ty::Fn(Box::new(Ty::Int), Box::new(Ty::String), Effect::NetworkSecure),
        );
    }
    for nm in ["jaring_tutup_dengar", "net_close_listener"] {
        c = c.extend(
            nm.to_string(),
            Ty::Fn(Box::new(Ty::Int), Box::new(Ty::Bool), Effect::Network),
        );
    }
    // Durable key-value store (REQ-73 persistence). All carry FileSystem: a
    // put/delete is fsynced to disk before it returns.
    for nm in ["simpan_buka", "store_open"] {
        c = c.extend(
            nm.to_string(),
            Ty::Fn(Box::new(Ty::String), Box::new(Ty::Int), Effect::FileSystem),
        );
    }
    for nm in ["simpan_letak", "store_put"] {
        c = c.extend(
            nm.to_string(),
            Ty::Fn(
                Box::new(Ty::Prod(
                    Box::new(Ty::Int),
                    Box::new(Ty::Prod(Box::new(Ty::String), Box::new(Ty::String))),
                )),
                Box::new(Ty::Bool),
                Effect::FileSystem,
            ),
        );
    }
    for nm in ["simpan_dapat", "store_get"] {
        c = c.extend(
            nm.to_string(),
            Ty::Fn(
                Box::new(Ty::Prod(Box::new(Ty::Int), Box::new(Ty::String))),
                Box::new(Ty::String),
                Effect::FileSystem,
            ),
        );
    }
    for nm in ["simpan_ada", "store_has"] {
        c = c.extend(
            nm.to_string(),
            Ty::Fn(
                Box::new(Ty::Prod(Box::new(Ty::Int), Box::new(Ty::String))),
                Box::new(Ty::Bool),
                Effect::FileSystem,
            ),
        );
    }
    for nm in ["simpan_padam", "store_delete"] {
        c = c.extend(
            nm.to_string(),
            Ty::Fn(
                Box::new(Ty::Prod(Box::new(Ty::Int), Box::new(Ty::String))),
                Box::new(Ty::Bool),
                Effect::FileSystem,
            ),
        );
    }
    for nm in ["simpan_kunci", "store_keys"] {
        c = c.extend(
            nm.to_string(),
            Ty::Fn(
                Box::new(Ty::Int),
                Box::new(Ty::List(Box::new(Ty::String))),
                Effect::FileSystem,
            ),
        );
    }
    for nm in ["simpan_padat", "store_compact"] {
        c = c.extend(
            nm.to_string(),
            Ty::Fn(Box::new(Ty::Int), Box::new(Ty::Bool), Effect::FileSystem),
        );
    }
    for nm in ["simpan_tutup", "store_close"] {
        c = c.extend(
            nm.to_string(),
            Ty::Fn(Box::new(Ty::Int), Box::new(Ty::Bool), Effect::FileSystem),
        );
    }
    // Real HTTP/1.1 above the verified TCP machine (REQ-73). Parsing is Pure;
    // only `http_minta` touches the network. These are DISTINCT from the
    // modelled `http_get`/`http_post` sinks below, which open no socket.
    for nm in ["http_hurai_kaedah", "http_parse_method"] {
        c = c.extend(
            nm.to_string(),
            Ty::Fn(Box::new(Ty::String), Box::new(Ty::String), Effect::Pure),
        );
    }
    for nm in ["http_hurai_laluan", "http_parse_target"] {
        c = c.extend(
            nm.to_string(),
            Ty::Fn(Box::new(Ty::String), Box::new(Ty::String), Effect::Pure),
        );
    }
    for nm in ["http_hurai_jasad", "http_parse_body"] {
        c = c.extend(
            nm.to_string(),
            Ty::Fn(Box::new(Ty::String), Box::new(Ty::String), Effect::Pure),
        );
    }
    for nm in ["http_hurai_kepala", "http_parse_header"] {
        c = c.extend(
            nm.to_string(),
            Ty::Fn(
                Box::new(Ty::Prod(Box::new(Ty::String), Box::new(Ty::String))),
                Box::new(Ty::String),
                Effect::Pure,
            ),
        );
    }
    for nm in ["http_balas", "http_build_response"] {
        c = c.extend(
            nm.to_string(),
            Ty::Fn(
                Box::new(Ty::Prod(Box::new(Ty::Int), Box::new(Ty::String))),
                Box::new(Ty::String),
                Effect::Pure,
            ),
        );
    }
    for nm in ["http_minta", "http_request"] {
        c = c.extend(
            nm.to_string(),
            Ty::Fn(
                Box::new(Ty::Prod(Box::new(Ty::String), Box::new(Ty::String))),
                Box::new(Ty::String),
                Effect::Network,
            ),
        );
    }
    // Pure TLS acceptance policy (Coq NET_001_03 no-downgrade + NET_001_08
    // cipher strength): `(version, cipher_suite) -> Bool`, no I/O.
    for nm in ["tls_dasar_ok", "tls_policy_ok"] {
        c = c.extend(
            nm.to_string(),
            Ty::Fn(
                Box::new(Ty::Prod(Box::new(Ty::String), Box::new(Ty::String))),
                Box::new(Ty::Bool),
                Effect::Pure,
            ),
        );
    }
    c = c.extend(
        "ke_bool".to_string(),
        Ty::Fn(Box::new(Ty::Any), Box::new(Ty::Bool), Effect::Pure),
    );
    c = c.extend(
        "to_bool".to_string(),
        Ty::Fn(Box::new(Ty::Any), Box::new(Ty::Bool), Effect::Pure),
    );
    // Math
    c = c.extend(
        "mutlak".to_string(),
        Ty::Fn(Box::new(Ty::Int), Box::new(Ty::Int), Effect::Pure),
    );
    c = c.extend(
        "abs".to_string(),
        Ty::Fn(Box::new(Ty::Int), Box::new(Ty::Int), Effect::Pure),
    );
    for name in &[
        "minimum", "min", "maksimum", "max", "kuasa", "pow", "gcd", "lcm",
    ] {
        c = c.extend(
            name.to_string(),
            Ty::Fn(
                Box::new(Ty::Prod(Box::new(Ty::Int), Box::new(Ty::Int))),
                Box::new(Ty::Int),
                Effect::Pure,
            ),
        );
    }
    c = c.extend(
        "punca".to_string(),
        Ty::Fn(Box::new(Ty::Int), Box::new(Ty::Int), Effect::Pure),
    );
    c = c.extend(
        "sqrt".to_string(),
        Ty::Fn(Box::new(Ty::Int), Box::new(Ty::Int), Effect::Pure),
    );
    // Assert
    c = c.extend(
        "tegaskan".to_string(),
        Ty::Fn(Box::new(Ty::Bool), Box::new(Ty::Unit), Effect::Pure),
    );
    c = c.extend(
        "assert".to_string(),
        Ty::Fn(Box::new(Ty::Bool), Box::new(Ty::Unit), Effect::Pure),
    );
    c = c.extend(
        "tegaskan_betul".to_string(),
        Ty::Fn(Box::new(Ty::Bool), Box::new(Ty::Unit), Effect::Pure),
    );
    c = c.extend(
        "assert_true".to_string(),
        Ty::Fn(Box::new(Ty::Bool), Box::new(Ty::Unit), Effect::Pure),
    );
    c = c.extend(
        "tegaskan_salah".to_string(),
        Ty::Fn(Box::new(Ty::Bool), Box::new(Ty::Unit), Effect::Pure),
    );
    c = c.extend(
        "assert_false".to_string(),
        Ty::Fn(Box::new(Ty::Bool), Box::new(Ty::Unit), Effect::Pure),
    );
    c = c.extend(
        "tegaskan_sama".to_string(),
        Ty::Fn(
            Box::new(Ty::Prod(Box::new(Ty::Any), Box::new(Ty::Any))),
            Box::new(Ty::Unit),
            Effect::Pure,
        ),
    );
    c = c.extend(
        "assert_eq".to_string(),
        Ty::Fn(
            Box::new(Ty::Prod(Box::new(Ty::Any), Box::new(Ty::Any))),
            Box::new(Ty::Unit),
            Effect::Pure,
        ),
    );
    c = c.extend(
        "tegaskan_beza".to_string(),
        Ty::Fn(
            Box::new(Ty::Prod(Box::new(Ty::Any), Box::new(Ty::Any))),
            Box::new(Ty::Unit),
            Effect::Pure,
        ),
    );
    c = c.extend(
        "assert_ne".to_string(),
        Ty::Fn(
            Box::new(Ty::Prod(Box::new(Ty::Any), Box::new(Ty::Any))),
            Box::new(Ty::Unit),
            Effect::Pure,
        ),
    );

    // ── String builtins (teks) ──
    for (bm, en) in &[
        ("teks_belah", "str_split"),
        ("teks_cantum", "str_join"),
        ("teks_potong", "str_trim"),
        ("teks_mengandungi", "str_contains"),
        ("teks_ganti", "str_replace"),
        ("teks_mula_dengan", "str_starts_with"),
        ("teks_akhir_dengan", "str_ends_with"),
        ("teks_huruf_besar", "str_to_upper"),
        ("teks_huruf_kecil", "str_to_lower"),
        ("teks_aksara_di", "str_char_at"),
        ("teks_sub", "str_substring"),
        ("teks_indeks", "str_index_of"),
        ("teks_ulang", "str_repeat"),
        ("teks_pad_kiri", "str_pad_left"),
        ("teks_pad_kanan", "str_pad_right"),
        ("teks_baris", "str_lines"),
    ] {
        let ty = Ty::Fn(Box::new(Ty::Any), Box::new(Ty::Any), Effect::Pure);
        c = c.extend(bm.to_string(), ty.clone());
        c = c.extend(en.to_string(), ty);
    }

    // ── List builtins (senarai) ──
    for (bm, en) in &[
        ("senarai_baru", "list_new"),
        ("senarai_tolak", "list_push"),
        ("senarai_dapat", "list_get"),
        ("senarai_panjang", "list_len"),
        ("senarai_peta", "list_map"),
        ("senarai_tapis", "list_filter"),
        ("senarai_lipat", "list_fold"),
        ("senarai_balik", "list_reverse"),
        ("senarai_susun", "list_sort"),
        ("senarai_mengandungi", "list_contains"),
        ("senarai_sambung", "list_concat"),
        ("senarai_kepala", "list_head"),
        ("senarai_ekor", "list_tail"),
        ("senarai_zip", "list_zip"),
        ("senarai_nombor", "list_enumerate"),
        ("senarai_rata", "list_flatten"),
        ("senarai_unik", "list_unique"),
        ("senarai_potong", "list_slice"),
    ] {
        let ty = Ty::Fn(Box::new(Ty::Any), Box::new(Ty::Any), Effect::Pure);
        c = c.extend(bm.to_string(), ty.clone());
        c = c.extend(en.to_string(), ty);
    }

    // ── Map builtins (peta) ──
    for (bm, en) in &[
        ("peta_baru", "map_new"),
        ("peta_letak", "map_insert"),
        ("peta_dapat", "map_get"),
        ("peta_buang", "map_remove"),
        ("peta_kunci", "map_keys"),
        ("peta_nilai", "map_values"),
        ("peta_mengandungi", "map_contains"),
        ("peta_panjang", "map_len"),
    ] {
        let ty = Ty::Fn(Box::new(Ty::Any), Box::new(Ty::Any), Effect::Pure);
        c = c.extend(bm.to_string(), ty.clone());
        c = c.extend(en.to_string(), ty);
    }

    // ── Set builtins ──
    for (bm, en) in &[
        ("set_baru", "set_new"),
        ("set_letak", "set_insert"),
        ("set_buang", "set_remove"),
        ("set_mengandungi", "set_contains"),
        ("set_kesatuan", "set_union"),
        ("set_persilangan", "set_intersect"),
        ("set_panjang", "set_len"),
    ] {
        let ty = Ty::Fn(Box::new(Ty::Any), Box::new(Ty::Any), Effect::Pure);
        c = c.extend(bm.to_string(), ty.clone());
        c = c.extend(en.to_string(), ty);
    }

    // ── File I/O builtins (fail) — Effect::FileSystem ──
    // Content-reading builtins are hardened (Gate C stdlib hardening): the path
    // must be a `String`, so a `Tainted` untrusted path is rejected at the I/O
    // boundary (path-traversal prevention, Coq `TaintSystemCorrectness.v`
    // `file_path_traversal_impossible` — the filesystem corollary of
    // `path_traversal_impossible`); and the returned contents are
    // `Tainted<String, FileSystem>` — an untrusted source that must be sanitized
    // before reaching any sink (Coq taint safety). The prototype↔Coq parity is
    // exercised by `taint_path_traversal_prevention_parity_all_file_ops`.
    for (bm, en) in &[("fail_baca", "file_read"), ("fail_baca_baris", "file_read_lines")] {
        let ty = Ty::Fn(
            Box::new(Ty::String),
            Box::new(Ty::Tainted(
                Box::new(Ty::String),
                riina_types::TaintSource::FileSystem,
            )),
            Effect::FileSystem,
        );
        c = c.extend(bm.to_string(), ty.clone());
        c = c.extend(en.to_string(), ty);
    }
    // Single-path file ops take a `String` path (a `Tainted` untrusted path is
    // rejected — path-traversal prevention, consistent with `file_read`) and now
    // carry precise result types: exists→Bool, delete→Unit, size→Int. `list_dir`
    // stays `Any` (a directory listing; a later slice can make it a tainted list).
    for (bm, en, ret) in &[
        ("fail_ada", "file_exists", Ty::Bool),
        ("fail_buang", "file_delete", Ty::Unit),
        ("fail_panjang", "file_size", Ty::Int),
        ("fail_senarai", "file_list_dir", Ty::Any),
    ] {
        let ty = Ty::Fn(Box::new(Ty::String), Box::new(ret.clone()), Effect::FileSystem);
        c = c.extend(bm.to_string(), ty.clone());
        c = c.extend(en.to_string(), ty);
    }
    // Write/append take a `(path, data)` pair (the runtime `extract_pair_strings`
    // and the C `(Teks, Teks) -> ()` shape). Precise typing: the **path** is a
    // plain `String` so a `Tainted` untrusted path is rejected (path-traversal
    // prevention, like the single-path ops), the **data** is a `String` (declassify
    // tainted content before writing it to a sink), and the result is `Unit`.
    for (bm, en) in &[("fail_tulis", "file_write"), ("fail_tambah", "file_append")] {
        let ty = Ty::Fn(
            Box::new(Ty::Prod(Box::new(Ty::String), Box::new(Ty::String))),
            Box::new(Ty::Unit),
            Effect::FileSystem,
        );
        c = c.extend(bm.to_string(), ty.clone());
        c = c.extend(en.to_string(), ty);
    }

    // ── Time builtins (masa) — precise types matching the runtime
    // (`riina-codegen/src/builtins/masa.rs` + the C emit). Was `Any → Any` (the
    // "Time interface — Unclear" stdlib row). The clocks are `Unit -> Int`
    // (the runtime value is a `Builtin`, i.e. a function, so this is sound — a
    // bare `Int` would type-check programs the untyped interpreter then rejects);
    // `sleep` takes a millisecond `Int`; `format`/`parse` take a `(value, format)`
    // pair. The `()` zero-arg-thunk *materialisation* at runtime is a separate,
    // codebase-wide item (the interpreter evaluates a bare builtin `Var` to its
    // `Builtin` value, like `baca_garisan`).
    let unit_to_int = || Ty::Fn(Box::new(Ty::Unit), Box::new(Ty::Int), Effect::Time);
    for (bm, en, ty) in [
        ("masa_sekarang", "time_now", unit_to_int()),
        // `masa_unix` — alias used by the example corpus (REQ-55): same clock.
        ("masa_unix", "time_unix", unit_to_int()),
        ("masa_sekarang_ms", "time_now_ms", unit_to_int()),
        ("masa_jam", "time_clock", unit_to_int()),
        (
            "masa_tidur",
            "time_sleep",
            Ty::Fn(Box::new(Ty::Int), Box::new(Ty::Unit), Effect::Time),
        ),
        (
            "masa_format",
            "time_format",
            Ty::Fn(
                Box::new(Ty::Prod(Box::new(Ty::Int), Box::new(Ty::String))),
                Box::new(Ty::String),
                Effect::Time,
            ),
        ),
        (
            "masa_urai",
            "time_parse",
            Ty::Fn(
                Box::new(Ty::Prod(Box::new(Ty::String), Box::new(Ty::String))),
                Box::new(Ty::Int),
                Effect::Time,
            ),
        ),
    ] {
        c = c.extend(bm.to_string(), ty.clone());
        c = c.extend(en.to_string(), ty);
    }

    // ── JSON builtins ──
    for (bm, en) in &[
        ("json_urai", "json_parse"),
        ("json_ke_teks", "json_stringify"),
        ("json_dapat", "json_get"),
        ("json_letak", "json_set"),
        ("json_ada", "json_has"),
    ] {
        let ty = Ty::Fn(Box::new(Ty::Any), Box::new(Ty::Any), Effect::Pure);
        c = c.extend(bm.to_string(), ty.clone());
        c = c.extend(en.to_string(), ty);
    }

    // ── Extra math builtins ──
    for (bm, en) in &[("baki", "rem"), ("log2", "log2")] {
        c = c.extend(
            bm.to_string(),
            Ty::Fn(Box::new(Ty::Int), Box::new(Ty::Int), Effect::Pure),
        );
        c = c.extend(
            en.to_string(),
            Ty::Fn(Box::new(Ty::Int), Box::new(Ty::Int), Effect::Pure),
        );
    }
    // Random — Effect::Random
    c = c.extend(
        "rawak".to_string(),
        Ty::Fn(Box::new(Ty::Int), Box::new(Ty::Int), Effect::Random),
    );
    c = c.extend(
        "random".to_string(),
        Ty::Fn(Box::new(Ty::Int), Box::new(Ty::Int), Effect::Random),
    );

    // ── Extra conversion builtins ──
    c = c.extend(
        "bool_ke_nombor".to_string(),
        Ty::Fn(Box::new(Ty::Bool), Box::new(Ty::Int), Effect::Pure),
    );
    c = c.extend(
        "bool_to_int".to_string(),
        Ty::Fn(Box::new(Ty::Bool), Box::new(Ty::Int), Effect::Pure),
    );
    c = c.extend(
        "nombor_ke_teks".to_string(),
        Ty::Fn(Box::new(Ty::Int), Box::new(Ty::String), Effect::Pure),
    );
    c = c.extend(
        "int_to_string".to_string(),
        Ty::Fn(Box::new(Ty::Int), Box::new(Ty::String), Effect::Pure),
    );

    // ── DOMAIN SECURITY: Taint Sources (return tainted data) ──

    // User input → Tainted<String, UserInput>
    c = c.extend(
        "read_line".to_string(),
        Ty::Fn(
            Box::new(Ty::Unit),
            Box::new(Ty::Tainted(
                Box::new(Ty::String),
                riina_types::TaintSource::UserInput,
            )),
            Effect::System,
        ),
    );
    c = c.extend(
        "baca_baris".to_string(),
        Ty::Fn(
            Box::new(Ty::Unit),
            Box::new(Ty::Tainted(
                Box::new(Ty::String),
                riina_types::TaintSource::UserInput,
            )),
            Effect::System,
        ),
    );
    // `baca_garisan` — read one line of input as plain text. A real
    // `Unit -> Teks` function, like the `masa_*` clocks beside it. It used to
    // be bound to its RESULT type `Teks`, because a zero-arg call dropped its
    // `()` and left a bare `Var`; that typed the call site as a string while
    // the runtime value was the un-applied builtin (master plan REQ-68).
    c = c.extend(
        "baca_garisan".to_string(),
        Ty::Fn(Box::new(Ty::Unit), Box::new(Ty::String), Effect::System),
    );

    // HTTP request body → Tainted<String, NetworkExternal>
    c = c.extend(
        "http_body".to_string(),
        Ty::Fn(
            Box::new(Ty::Any),
            Box::new(Ty::Tainted(
                Box::new(Ty::String),
                riina_types::TaintSource::NetworkExternal,
            )),
            Effect::Network,
        ),
    );
    c = c.extend(
        "badan_http".to_string(),
        Ty::Fn(
            Box::new(Ty::Any),
            Box::new(Ty::Tainted(
                Box::new(Ty::String),
                riina_types::TaintSource::NetworkExternal,
            )),
            Effect::Network,
        ),
    );

    // ── DOMAIN SECURITY: Sanitizers (Tainted → Sanitized) ──

    // SQL sanitizer
    c = c.extend(
        "sanitize_sql".to_string(),
        Ty::Fn(
            Box::new(Ty::Tainted(
                Box::new(Ty::String),
                riina_types::TaintSource::UserInput,
            )),
            Box::new(Ty::Sanitized(
                Box::new(Ty::String),
                riina_types::Sanitizer::SqlParam,
            )),
            Effect::Pure,
        ),
    );
    c = c.extend(
        "sanitasi_sql".to_string(),
        Ty::Fn(
            Box::new(Ty::Tainted(
                Box::new(Ty::String),
                riina_types::TaintSource::UserInput,
            )),
            Box::new(Ty::Sanitized(
                Box::new(Ty::String),
                riina_types::Sanitizer::SqlParam,
            )),
            Effect::Pure,
        ),
    );

    // HTML sanitizer
    c = c.extend(
        "sanitize_html".to_string(),
        Ty::Fn(
            Box::new(Ty::Tainted(
                Box::new(Ty::String),
                riina_types::TaintSource::UserInput,
            )),
            Box::new(Ty::Sanitized(
                Box::new(Ty::String),
                riina_types::Sanitizer::HtmlEscape,
            )),
            Effect::Pure,
        ),
    );
    c = c.extend(
        "sanitasi_html".to_string(),
        Ty::Fn(
            Box::new(Ty::Tainted(
                Box::new(Ty::String),
                riina_types::TaintSource::UserInput,
            )),
            Box::new(Ty::Sanitized(
                Box::new(Ty::String),
                riina_types::Sanitizer::HtmlEscape,
            )),
            Effect::Pure,
        ),
    );

    // JavaScript sanitizer
    c = c.extend(
        "sanitize_js".to_string(),
        Ty::Fn(
            Box::new(Ty::Tainted(
                Box::new(Ty::String),
                riina_types::TaintSource::UserInput,
            )),
            Box::new(Ty::Sanitized(
                Box::new(Ty::String),
                riina_types::Sanitizer::JsEscape,
            )),
            Effect::Pure,
        ),
    );
    c = c.extend(
        "sanitasi_js".to_string(),
        Ty::Fn(
            Box::new(Ty::Tainted(
                Box::new(Ty::String),
                riina_types::TaintSource::UserInput,
            )),
            Box::new(Ty::Sanitized(
                Box::new(Ty::String),
                riina_types::Sanitizer::JsEscape,
            )),
            Effect::Pure,
        ),
    );

    // Command sanitizer
    c = c.extend(
        "sanitize_command".to_string(),
        Ty::Fn(
            Box::new(Ty::Tainted(
                Box::new(Ty::String),
                riina_types::TaintSource::UserInput,
            )),
            Box::new(Ty::Sanitized(
                Box::new(Ty::String),
                riina_types::Sanitizer::CommandEscape,
            )),
            Effect::Pure,
        ),
    );
    c = c.extend(
        "sanitasi_perintah".to_string(),
        Ty::Fn(
            Box::new(Ty::Tainted(
                Box::new(Ty::String),
                riina_types::TaintSource::UserInput,
            )),
            Box::new(Ty::Sanitized(
                Box::new(Ty::String),
                riina_types::Sanitizer::CommandEscape,
            )),
            Effect::Pure,
        ),
    );

    // LDAP sanitizer
    c = c.extend(
        "sanitize_ldap".to_string(),
        Ty::Fn(
            Box::new(Ty::Tainted(
                Box::new(Ty::String),
                riina_types::TaintSource::UserInput,
            )),
            Box::new(Ty::Sanitized(
                Box::new(Ty::String),
                riina_types::Sanitizer::LdapEscape,
            )),
            Effect::Pure,
        ),
    );
    c = c.extend(
        "sanitasi_ldap".to_string(),
        Ty::Fn(
            Box::new(Ty::Tainted(
                Box::new(Ty::String),
                riina_types::TaintSource::UserInput,
            )),
            Box::new(Ty::Sanitized(
                Box::new(Ty::String),
                riina_types::Sanitizer::LdapEscape,
            )),
            Effect::Pure,
        ),
    );

    // ── DOMAIN SECURITY: Sensitive Sinks (require Sanitized) ──

    // SQL execution — REQUIRES Sanitized<String, SqlParam>
    c = c.extend(
        "sql_execute".to_string(),
        Ty::Fn(
            Box::new(Ty::Sanitized(
                Box::new(Ty::String),
                riina_types::Sanitizer::SqlParam,
            )),
            Box::new(Ty::Any), // Query results
            Effect::System,
        ),
    );
    c = c.extend(
        "sql_laksana".to_string(),
        Ty::Fn(
            Box::new(Ty::Sanitized(
                Box::new(Ty::String),
                riina_types::Sanitizer::SqlParam,
            )),
            Box::new(Ty::Any),
            Effect::System,
        ),
    );

    // HTML rendering — REQUIRES Sanitized<String, HtmlEscape>
    c = c.extend(
        "html_render".to_string(),
        Ty::Fn(
            Box::new(Ty::Sanitized(
                Box::new(Ty::String),
                riina_types::Sanitizer::HtmlEscape,
            )),
            Box::new(Ty::String),
            Effect::Pure,
        ),
    );
    c = c.extend(
        "html_papar".to_string(),
        Ty::Fn(
            Box::new(Ty::Sanitized(
                Box::new(Ty::String),
                riina_types::Sanitizer::HtmlEscape,
            )),
            Box::new(Ty::String),
            Effect::Pure,
        ),
    );

    // JavaScript eval — REQUIRES Sanitized<String, JsEscape>
    c = c.extend(
        "js_eval".to_string(),
        Ty::Fn(
            Box::new(Ty::Sanitized(
                Box::new(Ty::String),
                riina_types::Sanitizer::JsEscape,
            )),
            Box::new(Ty::Any),
            Effect::System,
        ),
    );
    c = c.extend(
        "js_nilai".to_string(),
        Ty::Fn(
            Box::new(Ty::Sanitized(
                Box::new(Ty::String),
                riina_types::Sanitizer::JsEscape,
            )),
            Box::new(Ty::Any),
            Effect::System,
        ),
    );

    // Shell command execution — REQUIRES Sanitized<String, CommandEscape>
    c = c.extend(
        "shell_exec".to_string(),
        Ty::Fn(
            Box::new(Ty::Sanitized(
                Box::new(Ty::String),
                riina_types::Sanitizer::CommandEscape,
            )),
            Box::new(Ty::Int), // Exit code
            Effect::System,
        ),
    );
    c = c.extend(
        "shell_laksana".to_string(),
        Ty::Fn(
            Box::new(Ty::Sanitized(
                Box::new(Ty::String),
                riina_types::Sanitizer::CommandEscape,
            )),
            Box::new(Ty::Int),
            Effect::System,
        ),
    );

    // LDAP search — REQUIRES Sanitized<String, LdapEscape>
    c = c.extend(
        "ldap_search".to_string(),
        Ty::Fn(
            Box::new(Ty::Sanitized(
                Box::new(Ty::String),
                riina_types::Sanitizer::LdapEscape,
            )),
            Box::new(Ty::Any), // Search results
            Effect::System,
        ),
    );
    c = c.extend(
        "ldap_cari".to_string(),
        Ty::Fn(
            Box::new(Ty::Sanitized(
                Box::new(Ty::String),
                riina_types::Sanitizer::LdapEscape,
            )),
            Box::new(Ty::Any),
            Effect::System,
        ),
    );

    // ── TASK #4: Enhanced XSS Prevention ──

    // URL sanitizer (for safe redirects/links)
    c = c.extend(
        "sanitize_url".to_string(),
        Ty::Fn(
            Box::new(Ty::Tainted(
                Box::new(Ty::String),
                riina_types::TaintSource::UserInput,
            )),
            Box::new(Ty::Sanitized(
                Box::new(Ty::String),
                riina_types::Sanitizer::UrlEncode,
            )),
            Effect::Pure,
        ),
    );
    c = c.extend(
        "sanitasi_url".to_string(),
        Ty::Fn(
            Box::new(Ty::Tainted(
                Box::new(Ty::String),
                riina_types::TaintSource::UserInput,
            )),
            Box::new(Ty::Sanitized(
                Box::new(Ty::String),
                riina_types::Sanitizer::UrlEncode,
            )),
            Effect::Pure,
        ),
    );

    // CSS sanitizer (for safe style injection)
    c = c.extend(
        "sanitize_css".to_string(),
        Ty::Fn(
            Box::new(Ty::Tainted(
                Box::new(Ty::String),
                riina_types::TaintSource::UserInput,
            )),
            Box::new(Ty::Sanitized(
                Box::new(Ty::String),
                riina_types::Sanitizer::CssEscape,
            )),
            Effect::Pure,
        ),
    );
    c = c.extend(
        "sanitasi_css".to_string(),
        Ty::Fn(
            Box::new(Ty::Tainted(
                Box::new(Ty::String),
                riina_types::TaintSource::UserInput,
            )),
            Box::new(Ty::Sanitized(
                Box::new(Ty::String),
                riina_types::Sanitizer::CssEscape,
            )),
            Effect::Pure,
        ),
    );

    // ── DOM Manipulation (context-aware) ──

    // Safe innerHTML setter — REQUIRES HtmlEscape
    c = c.extend(
        "dom_set_html".to_string(),
        Ty::Fn(
            Box::new(Ty::Prod(
                Box::new(Ty::Any), // DOM element
                Box::new(Ty::Sanitized(
                    Box::new(Ty::String),
                    riina_types::Sanitizer::HtmlEscape,
                )),
            )),
            Box::new(Ty::Unit),
            Effect::System,
        ),
    );
    c = c.extend(
        "dom_tetap_html".to_string(),
        Ty::Fn(
            Box::new(Ty::Prod(
                Box::new(Ty::Any),
                Box::new(Ty::Sanitized(
                    Box::new(Ty::String),
                    riina_types::Sanitizer::HtmlEscape,
                )),
            )),
            Box::new(Ty::Unit),
            Effect::System,
        ),
    );

    // Safe attribute setter — REQUIRES HtmlEscape
    c = c.extend(
        "dom_set_attr".to_string(),
        Ty::Fn(
            Box::new(Ty::Prod(
                Box::new(Ty::Any), // DOM element
                Box::new(Ty::Prod(
                    Box::new(Ty::String), // Attribute name
                    Box::new(Ty::Sanitized(
                        Box::new(Ty::String),
                        riina_types::Sanitizer::HtmlEscape,
                    )),
                )),
            )),
            Box::new(Ty::Unit),
            Effect::System,
        ),
    );
    c = c.extend(
        "dom_tetap_atribut".to_string(),
        Ty::Fn(
            Box::new(Ty::Prod(
                Box::new(Ty::Any),
                Box::new(Ty::Prod(
                    Box::new(Ty::String),
                    Box::new(Ty::Sanitized(
                        Box::new(Ty::String),
                        riina_types::Sanitizer::HtmlEscape,
                    )),
                )),
            )),
            Box::new(Ty::Unit),
            Effect::System,
        ),
    );

    // ── Input Validation (pre-sanitization) ──

    // Length-bounded input validation
    c = c.extend(
        "validate_length".to_string(),
        Ty::Fn(
            Box::new(Ty::Prod(
                Box::new(Ty::Tainted(
                    Box::new(Ty::String),
                    riina_types::TaintSource::UserInput,
                )),
                Box::new(Ty::Int), // Max length
            )),
            Box::new(Ty::Option(Box::new(Ty::Tainted(
                Box::new(Ty::String),
                riina_types::TaintSource::UserInput,
            )))),
            Effect::Pure,
        ),
    );
    c = c.extend(
        "sahkan_panjang".to_string(),
        Ty::Fn(
            Box::new(Ty::Prod(
                Box::new(Ty::Tainted(
                    Box::new(Ty::String),
                    riina_types::TaintSource::UserInput,
                )),
                Box::new(Ty::Int),
            )),
            Box::new(Ty::Option(Box::new(Ty::Tainted(
                Box::new(Ty::String),
                riina_types::TaintSource::UserInput,
            )))),
            Effect::Pure,
        ),
    );

    // Unicode normalization (prevents homograph attacks)
    c = c.extend(
        "normalize_unicode".to_string(),
        Ty::Fn(
            Box::new(Ty::Tainted(
                Box::new(Ty::String),
                riina_types::TaintSource::UserInput,
            )),
            Box::new(Ty::Tainted(
                Box::new(Ty::String),
                riina_types::TaintSource::UserInput,
            )),
            Effect::Pure,
        ),
    );
    c = c.extend(
        "normal_unicode".to_string(),
        Ty::Fn(
            Box::new(Ty::Tainted(
                Box::new(Ty::String),
                riina_types::TaintSource::UserInput,
            )),
            Box::new(Ty::Tainted(
                Box::new(Ty::String),
                riina_types::TaintSource::UserInput,
            )),
            Effect::Pure,
        ),
    );

    // Strip null bytes (prevents injection bypass)
    c = c.extend(
        "strip_nulls".to_string(),
        Ty::Fn(
            Box::new(Ty::Tainted(
                Box::new(Ty::String),
                riina_types::TaintSource::UserInput,
            )),
            Box::new(Ty::Tainted(
                Box::new(Ty::String),
                riina_types::TaintSource::UserInput,
            )),
            Effect::Pure,
        ),
    );
    c = c.extend(
        "buang_null".to_string(),
        Ty::Fn(
            Box::new(Ty::Tainted(
                Box::new(Ty::String),
                riina_types::TaintSource::UserInput,
            )),
            Box::new(Ty::Tainted(
                Box::new(Ty::String),
                riina_types::TaintSource::UserInput,
            )),
            Effect::Pure,
        ),
    );

    // ── TASK #5: CSRF Protection ──
    // Matches Coq CSRFProtection.v (20 Qed proofs)
    // All 5 CSRF protections: token validation, same-site cookies, origin check,
    // referer check, double-submit pattern

    // Generate CSRF token (cryptographically secure random token)
    // Spec: CSRFProtection.v — csrf_token_validation
    c = c.extend(
        "csrf_generate".to_string(),
        Ty::Fn(
            Box::new(Ty::Unit),
            Box::new(Ty::String), // Base64-encoded token
            Effect::Random,       // Cryptographic randomness required
        ),
    );
    c = c.extend(
        "csrf_jana".to_string(),
        Ty::Fn(Box::new(Ty::Unit), Box::new(Ty::String), Effect::Random),
    );

    // Validate CSRF token (request token vs session token)
    // Spec: CSRFProtection.v — csrf_double_submit
    c = c.extend(
        "csrf_validate".to_string(),
        Ty::Fn(
            Box::new(Ty::Prod(
                Box::new(Ty::String), // Request token
                Box::new(Ty::String), // Session token
            )),
            Box::new(Ty::Bool), // Validation result
            Effect::Pure,
        ),
    );
    c = c.extend(
        "csrf_sahkan".to_string(),
        Ty::Fn(
            Box::new(Ty::Prod(Box::new(Ty::String), Box::new(Ty::String))),
            Box::new(Ty::Bool),
            Effect::Pure,
        ),
    );

    // Check origin header (same-origin policy enforcement)
    // Spec: CSRFProtection.v — csrf_origin_check
    c = c.extend(
        "csrf_check_origin".to_string(),
        Ty::Fn(
            Box::new(Ty::Prod(
                Box::new(Ty::String), // Request origin
                Box::new(Ty::String), // Expected origin
            )),
            Box::new(Ty::Bool),
            Effect::Pure,
        ),
    );
    c = c.extend(
        "csrf_semak_origin".to_string(),
        Ty::Fn(
            Box::new(Ty::Prod(Box::new(Ty::String), Box::new(Ty::String))),
            Box::new(Ty::Bool),
            Effect::Pure,
        ),
    );

    // Check referer header
    // Spec: CSRFProtection.v — csrf_referer_check
    c = c.extend(
        "csrf_check_referer".to_string(),
        Ty::Fn(
            Box::new(Ty::Prod(
                Box::new(Ty::String), // Request referer
                Box::new(Ty::String), // Expected referer
            )),
            Box::new(Ty::Bool),
            Effect::Pure,
        ),
    );
    c = c.extend(
        "csrf_semak_referer".to_string(),
        Ty::Fn(
            Box::new(Ty::Prod(Box::new(Ty::String), Box::new(Ty::String))),
            Box::new(Ty::Bool),
            Effect::Pure,
        ),
    );

    // ── HTTP Methods with CSRF Protection ──

    // Safe GET request (no CSRF token required — safe method)
    c = c.extend(
        "http_get".to_string(),
        Ty::Fn(
            Box::new(Ty::String), // URL only (no token needed)
            Box::new(Ty::Any),    // Response
            Effect::Network,
        ),
    );
    c = c.extend(
        "http_dapat".to_string(),
        Ty::Fn(Box::new(Ty::String), Box::new(Ty::Any), Effect::Network),
    );

    // State-changing POST (CSRF token REQUIRED in type signature)
    // Type: (URL, (body, csrf_token)) -> Response
    // The nested pair forces callers to provide a CSRF token
    c = c.extend(
        "http_post".to_string(),
        Ty::Fn(
            Box::new(Ty::Prod(
                Box::new(Ty::String), // URL
                Box::new(Ty::Prod(
                    Box::new(Ty::Any),    // Request body
                    Box::new(Ty::String), // CSRF token (REQUIRED)
                )),
            )),
            Box::new(Ty::Any), // Response
            Effect::Network,
        ),
    );
    c = c.extend(
        "http_hantar".to_string(),
        Ty::Fn(
            Box::new(Ty::Prod(
                Box::new(Ty::String),
                Box::new(Ty::Prod(Box::new(Ty::Any), Box::new(Ty::String))),
            )),
            Box::new(Ty::Any),
            Effect::Network,
        ),
    );

    // State-changing PUT (CSRF token REQUIRED)
    // Type: (URL, (body, csrf_token)) -> Response
    c = c.extend(
        "http_put".to_string(),
        Ty::Fn(
            Box::new(Ty::Prod(
                Box::new(Ty::String), // URL
                Box::new(Ty::Prod(
                    Box::new(Ty::Any),    // Request body
                    Box::new(Ty::String), // CSRF token (REQUIRED)
                )),
            )),
            Box::new(Ty::Any),
            Effect::Network,
        ),
    );
    c = c.extend(
        "http_kemaskini".to_string(),
        Ty::Fn(
            Box::new(Ty::Prod(
                Box::new(Ty::String),
                Box::new(Ty::Prod(Box::new(Ty::Any), Box::new(Ty::String))),
            )),
            Box::new(Ty::Any),
            Effect::Network,
        ),
    );

    // State-changing DELETE (CSRF token REQUIRED)
    // Type: (URL, csrf_token) -> Response
    // DELETE has no body, so just URL + token
    c = c.extend(
        "http_delete".to_string(),
        Ty::Fn(
            Box::new(Ty::Prod(
                Box::new(Ty::String), // URL
                Box::new(Ty::String), // CSRF token (REQUIRED)
            )),
            Box::new(Ty::Any),
            Effect::Network,
        ),
    );
    c = c.extend(
        "http_padam".to_string(),
        Ty::Fn(
            Box::new(Ty::Prod(Box::new(Ty::String), Box::new(Ty::String))),
            Box::new(Ty::Any),
            Effect::Network,
        ),
    );

    // ── TASK #6: Extended Domain Security Enforcement ──
    // 5 new OWASP attack classes: Path Traversal, XML/XXE, SSRF,
    // Email Header Injection, Unsafe Deserialization

    // ── 6a: Path Traversal (CWE-22) ──
    // Spec: TaintSystemCorrectness.v — path_traversal_impossible
    // Spec: VerifiedFileSystem.v

    // Path sanitizer: Tainted → Sanitized<String, PathTraversal>
    c = c.extend(
        "sanitize_path".to_string(),
        Ty::Fn(
            Box::new(Ty::Tainted(
                Box::new(Ty::String),
                riina_types::TaintSource::UserInput,
            )),
            Box::new(Ty::Sanitized(
                Box::new(Ty::String),
                riina_types::Sanitizer::PathTraversal,
            )),
            Effect::Pure,
        ),
    );
    c = c.extend(
        "sanitasi_laluan".to_string(),
        Ty::Fn(
            Box::new(Ty::Tainted(
                Box::new(Ty::String),
                riina_types::TaintSource::UserInput,
            )),
            Box::new(Ty::Sanitized(
                Box::new(Ty::String),
                riina_types::Sanitizer::PathTraversal,
            )),
            Effect::Pure,
        ),
    );

    // Safe file read — REQUIRES Sanitized<String, PathTraversal>
    c = c.extend(
        "file_read_safe".to_string(),
        Ty::Fn(
            Box::new(Ty::Sanitized(
                Box::new(Ty::String),
                riina_types::Sanitizer::PathTraversal,
            )),
            Box::new(Ty::Any), // File contents
            Effect::Read,
        ),
    );
    c = c.extend(
        "fail_baca_selamat".to_string(),
        Ty::Fn(
            Box::new(Ty::Sanitized(
                Box::new(Ty::String),
                riina_types::Sanitizer::PathTraversal,
            )),
            Box::new(Ty::Any),
            Effect::Read,
        ),
    );

    // Safe file write — REQUIRES Sanitized<String, PathTraversal>
    c = c.extend(
        "file_write_safe".to_string(),
        Ty::Fn(
            Box::new(Ty::Prod(
                Box::new(Ty::Sanitized(
                    Box::new(Ty::String),
                    riina_types::Sanitizer::PathTraversal,
                )),
                Box::new(Ty::Any), // Data to write
            )),
            Box::new(Ty::Unit),
            Effect::Write,
        ),
    );
    c = c.extend(
        "fail_tulis_selamat".to_string(),
        Ty::Fn(
            Box::new(Ty::Prod(
                Box::new(Ty::Sanitized(
                    Box::new(Ty::String),
                    riina_types::Sanitizer::PathTraversal,
                )),
                Box::new(Ty::Any),
            )),
            Box::new(Ty::Unit),
            Effect::Write,
        ),
    );

    // Safe file delete — REQUIRES Sanitized<String, PathTraversal>
    c = c.extend(
        "file_delete_safe".to_string(),
        Ty::Fn(
            Box::new(Ty::Sanitized(
                Box::new(Ty::String),
                riina_types::Sanitizer::PathTraversal,
            )),
            Box::new(Ty::Bool), // Success
            Effect::Write,
        ),
    );
    c = c.extend(
        "fail_buang_selamat".to_string(),
        Ty::Fn(
            Box::new(Ty::Sanitized(
                Box::new(Ty::String),
                riina_types::Sanitizer::PathTraversal,
            )),
            Box::new(Ty::Bool),
            Effect::Write,
        ),
    );

    // ── 6b: XML Injection / XXE (CWE-611) ──
    // Spec: InjectionPrevention.v — inj_005_xxe_impossible

    // XML sanitizer: Tainted → Sanitized<String, XmlEscape>
    c = c.extend(
        "sanitize_xml".to_string(),
        Ty::Fn(
            Box::new(Ty::Tainted(
                Box::new(Ty::String),
                riina_types::TaintSource::UserInput,
            )),
            Box::new(Ty::Sanitized(
                Box::new(Ty::String),
                riina_types::Sanitizer::XmlEscape,
            )),
            Effect::Pure,
        ),
    );
    c = c.extend(
        "sanitasi_xml".to_string(),
        Ty::Fn(
            Box::new(Ty::Tainted(
                Box::new(Ty::String),
                riina_types::TaintSource::UserInput,
            )),
            Box::new(Ty::Sanitized(
                Box::new(Ty::String),
                riina_types::Sanitizer::XmlEscape,
            )),
            Effect::Pure,
        ),
    );

    // Safe XML parse — REQUIRES Sanitized<String, XmlEscape>
    c = c.extend(
        "xml_parse_safe".to_string(),
        Ty::Fn(
            Box::new(Ty::Sanitized(
                Box::new(Ty::String),
                riina_types::Sanitizer::XmlEscape,
            )),
            Box::new(Ty::Any), // Parsed XML tree
            Effect::Pure,
        ),
    );
    c = c.extend(
        "xml_urai_selamat".to_string(),
        Ty::Fn(
            Box::new(Ty::Sanitized(
                Box::new(Ty::String),
                riina_types::Sanitizer::XmlEscape,
            )),
            Box::new(Ty::Any),
            Effect::Pure,
        ),
    );

    // XML query — REQUIRES Sanitized<String, XmlEscape>
    c = c.extend(
        "xml_query".to_string(),
        Ty::Fn(
            Box::new(Ty::Sanitized(
                Box::new(Ty::String),
                riina_types::Sanitizer::XmlEscape,
            )),
            Box::new(Ty::Any), // Query results
            Effect::Pure,
        ),
    );
    c = c.extend(
        "xml_cari".to_string(),
        Ty::Fn(
            Box::new(Ty::Sanitized(
                Box::new(Ty::String),
                riina_types::Sanitizer::XmlEscape,
            )),
            Box::new(Ty::Any),
            Effect::Pure,
        ),
    );

    // ── 6c: SSRF (CWE-918) ──
    // Spec: WebSecurity.v — web_005_ssrf_impossible

    // URL validator: Tainted → Sanitized<String, UrlAllowlist>
    c = c.extend(
        "validate_url".to_string(),
        Ty::Fn(
            Box::new(Ty::Tainted(
                Box::new(Ty::String),
                riina_types::TaintSource::UserInput,
            )),
            Box::new(Ty::Sanitized(
                Box::new(Ty::String),
                riina_types::Sanitizer::UrlAllowlist,
            )),
            Effect::Pure,
        ),
    );
    c = c.extend(
        "sahkan_url".to_string(),
        Ty::Fn(
            Box::new(Ty::Tainted(
                Box::new(Ty::String),
                riina_types::TaintSource::UserInput,
            )),
            Box::new(Ty::Sanitized(
                Box::new(Ty::String),
                riina_types::Sanitizer::UrlAllowlist,
            )),
            Effect::Pure,
        ),
    );

    // Safe HTTP fetch — REQUIRES Sanitized<String, UrlAllowlist>
    c = c.extend(
        "http_fetch_safe".to_string(),
        Ty::Fn(
            Box::new(Ty::Sanitized(
                Box::new(Ty::String),
                riina_types::Sanitizer::UrlAllowlist,
            )),
            Box::new(Ty::Any), // Response
            Effect::Network,
        ),
    );
    c = c.extend(
        "http_ambil_selamat".to_string(),
        Ty::Fn(
            Box::new(Ty::Sanitized(
                Box::new(Ty::String),
                riina_types::Sanitizer::UrlAllowlist,
            )),
            Box::new(Ty::Any),
            Effect::Network,
        ),
    );

    // Safe HTTP redirect — REQUIRES Sanitized<String, UrlAllowlist>
    c = c.extend(
        "http_redirect_safe".to_string(),
        Ty::Fn(
            Box::new(Ty::Sanitized(
                Box::new(Ty::String),
                riina_types::Sanitizer::UrlAllowlist,
            )),
            Box::new(Ty::Unit),
            Effect::Network,
        ),
    );
    c = c.extend(
        "http_arah_selamat".to_string(),
        Ty::Fn(
            Box::new(Ty::Sanitized(
                Box::new(Ty::String),
                riina_types::Sanitizer::UrlAllowlist,
            )),
            Box::new(Ty::Unit),
            Effect::Network,
        ),
    );

    // ── 6d: Email Header Injection (CWE-93) ──
    // Spec: InjectionPrevention.v — inj_011_email_header_safe

    // Email sanitizer: Tainted → Sanitized<String, EmailValidation>
    c = c.extend(
        "sanitize_email".to_string(),
        Ty::Fn(
            Box::new(Ty::Tainted(
                Box::new(Ty::String),
                riina_types::TaintSource::UserInput,
            )),
            Box::new(Ty::Sanitized(
                Box::new(Ty::String),
                riina_types::Sanitizer::EmailValidation,
            )),
            Effect::Pure,
        ),
    );
    c = c.extend(
        "sanitasi_emel".to_string(),
        Ty::Fn(
            Box::new(Ty::Tainted(
                Box::new(Ty::String),
                riina_types::TaintSource::UserInput,
            )),
            Box::new(Ty::Sanitized(
                Box::new(Ty::String),
                riina_types::Sanitizer::EmailValidation,
            )),
            Effect::Pure,
        ),
    );

    // Email send — REQUIRES Sanitized<String, EmailValidation>
    c = c.extend(
        "email_send".to_string(),
        Ty::Fn(
            Box::new(Ty::Prod(
                Box::new(Ty::Sanitized(
                    Box::new(Ty::String),
                    riina_types::Sanitizer::EmailValidation,
                )),
                Box::new(Ty::String), // Message body
            )),
            Box::new(Ty::Bool), // Success
            Effect::Network,
        ),
    );
    c = c.extend(
        "emel_hantar".to_string(),
        Ty::Fn(
            Box::new(Ty::Prod(
                Box::new(Ty::Sanitized(
                    Box::new(Ty::String),
                    riina_types::Sanitizer::EmailValidation,
                )),
                Box::new(Ty::String),
            )),
            Box::new(Ty::Bool),
            Effect::Network,
        ),
    );

    // Email set header — REQUIRES Sanitized<String, EmailValidation>
    c = c.extend(
        "email_set_header".to_string(),
        Ty::Fn(
            Box::new(Ty::Prod(
                Box::new(Ty::String), // Header name
                Box::new(Ty::Sanitized(
                    Box::new(Ty::String),
                    riina_types::Sanitizer::EmailValidation,
                )),
            )),
            Box::new(Ty::Unit),
            Effect::Pure,
        ),
    );
    c = c.extend(
        "emel_tetap_kepala".to_string(),
        Ty::Fn(
            Box::new(Ty::Prod(
                Box::new(Ty::String),
                Box::new(Ty::Sanitized(
                    Box::new(Ty::String),
                    riina_types::Sanitizer::EmailValidation,
                )),
            )),
            Box::new(Ty::Unit),
            Effect::Pure,
        ),
    );

    // ── 6e: Unsafe Deserialization (CWE-502) ──
    // Spec: DeserializationSafety.v — rce_prevention_active

    // JSON sanitizer: Tainted → Sanitized<String, JsonValidation>
    c = c.extend(
        "sanitize_json".to_string(),
        Ty::Fn(
            Box::new(Ty::Tainted(
                Box::new(Ty::String),
                riina_types::TaintSource::UserInput,
            )),
            Box::new(Ty::Sanitized(
                Box::new(Ty::String),
                riina_types::Sanitizer::JsonValidation,
            )),
            Effect::Pure,
        ),
    );
    c = c.extend(
        "sanitasi_json".to_string(),
        Ty::Fn(
            Box::new(Ty::Tainted(
                Box::new(Ty::String),
                riina_types::TaintSource::UserInput,
            )),
            Box::new(Ty::Sanitized(
                Box::new(Ty::String),
                riina_types::Sanitizer::JsonValidation,
            )),
            Effect::Pure,
        ),
    );

    // Safe JSON parse — REQUIRES Sanitized<String, JsonValidation>
    c = c.extend(
        "json_parse_safe".to_string(),
        Ty::Fn(
            Box::new(Ty::Sanitized(
                Box::new(Ty::String),
                riina_types::Sanitizer::JsonValidation,
            )),
            Box::new(Ty::Any), // Parsed value
            Effect::Pure,
        ),
    );
    c = c.extend(
        "json_urai_selamat".to_string(),
        Ty::Fn(
            Box::new(Ty::Sanitized(
                Box::new(Ty::String),
                riina_types::Sanitizer::JsonValidation,
            )),
            Box::new(Ty::Any),
            Effect::Pure,
        ),
    );

    // Safe deserialize — REQUIRES Sanitized<String, JsonValidation>
    c = c.extend(
        "deserialize_safe".to_string(),
        Ty::Fn(
            Box::new(Ty::Sanitized(
                Box::new(Ty::String),
                riina_types::Sanitizer::JsonValidation,
            )),
            Box::new(Ty::Any), // Deserialized object
            Effect::Pure,
        ),
    );
    c = c.extend(
        "nyahsiri_selamat".to_string(),
        Ty::Fn(
            Box::new(Ty::Sanitized(
                Box::new(Ty::String),
                riina_types::Sanitizer::JsonValidation,
            )),
            Box::new(Ty::Any),
            Effect::Pure,
        ),
    );

    // Crypto-agility selection builtins (REQ-48): take an algorithm-name string,
    // return a crypto handle (`Any`), effect Crypto. The deprecation check fires
    // at these call sites — the App arm's `deprecated_algorithm_at_selection`,
    // mirroring `CUse` in crypto/AlgorithmPolicy.v.
    for nm in [
        "guna_kripto",
        "use_crypto",
        "pilih_algo",
        "select_algorithm",
        "cipher",
        "sifer",
        "hash_dengan",
        "hash_with",
    ] {
        c = c.extend(
            nm.to_string(),
            Ty::Fn(Box::new(Ty::String), Box::new(Ty::Any), Effect::Crypto),
        );
    }

    c
}

/// Select the result type when joining two branch types that are already known
/// to be [`types_compatible`], preferring the more concrete type. If one side
/// is `Any` (RIINA's wildcard, produced for example by unannotated
/// Option/Result payloads), the other more concrete type is used; otherwise the
/// first is returned (they are compatible, so either is acceptable).
fn join_branch_types(t1: Ty, t2: Ty) -> Ty {
    match (&t1, &t2) {
        (Ty::Any, _) => t2,
        (_, Ty::Any) => t1,
        _ => t1,
    }
}

/// Refine an incompatible function-application argument error.
///
/// A sink whose parameter type is `Sanitized<_, required>` (e.g. `sql_execute`,
/// `ldap_search`, `xml_parse_safe`) produces a taint-specific diagnostic that
/// mirrors the Coq injection-prevention theorems in
/// `domains/TaintSystemCorrectness.v`, rather than a generic `TypeMismatch`:
/// - a `Tainted<_, src>` argument ⇒ `TaintViolation` (unsanitized data at a sink),
/// - a `Sanitized<_, other>` argument with the wrong sanitizer ⇒ `SanitizerMismatch`.
///
/// Any other incompatibility falls back to `TypeMismatch`.
fn sink_argument_error(arg_ty: Ty, found: Ty) -> TypeError {
    if let Ty::Sanitized(_, required) = &arg_ty {
        match &found {
            Ty::Tainted(_, src) => {
                return TypeError::TaintViolation {
                    taint_source: *src,
                    required_sanitizer: required.clone(),
                    context: "sink argument",
                };
            }
            Ty::Sanitized(_, found_san) if found_san != required => {
                return TypeError::SanitizerMismatch {
                    expected: required.clone(),
                    found: found_san.clone(),
                    context: "sink argument",
                };
            }
            _ => {}
        }
    }
    TypeError::TypeMismatch {
        expected: arg_ty,
        found,
    }
}

/// IFC sink discipline (REQ-27): data classified above `Public` may not reach a
/// public sink without declassification. Covers the sinks whose argument (or an
/// `Any`-typed position inside it) would otherwise swallow secret/labeled data:
///   - print sinks  `cetak`/`cetakln`/`cetak_baris`/`print`/`println` (arg `Any`)
///   - network-send `http_post`/`http_hantar`/`http_put` (body is `Any` inside
///     the `(URL, (body, csrf))` pair)
///   - file-write   `file_write`/`fail_tulis`/`file_append`/`fail_tambah`
///     (data is a concrete `String`, so a raw `Secret`/`Labeled` is already a
///     `TypeMismatch`; routing it here yields the *clear* `SecurityViolation`).
///
/// Coq forbids this flow: a `TSecret` value re-enters public typing only through
/// `T_Declassify` with a matching proof (`declass_ok`;
/// `properties/Declassification.v` `logical_relation_declassify_proven` /
/// `declassify_requires_public_context`), and a non-`Public` `Labeled` value
/// dereferenced from a secret reference carries the source level by the no-read-up
/// rule (`foundations/Typing.v` `T_Deref`). Reaching a Public sink without
/// declassifying is a `SecurityViolation` (secret data on a Public channel), not
/// a generic `TypeMismatch`. The check is conservative: a secret anywhere in the
/// sink argument (incl. the URL or CSRF position) is rejected — none of those
/// should be secret-derived either.
/// Crypto-agility (REQ-48): the algorithm-deprecation policy.
///
/// This is the Rust counterpart of the Coq `accepts` judgment in
/// `02_FORMAL/coq/crypto/AlgorithmPolicy.v`. That development proves the check
/// is SOUND (an accepted program uses no deprecated algorithm) and COMPLETE (it
/// accepts every program that uses only current algorithms, so a rejection is
/// always a real deprecated use — no false positives), and that deprecating one
/// algorithm only affects programs that use it. The check below is the
/// operational realisation of `accepts pol (CUse a)` = `pol a = Current`.
///
/// The policy is data, not code: `DEPRECATED` is the classified list. Advancing
/// a deprecation date is editing this table, exactly as the mechanized
/// `tighten` lemma models — "P-256 after 2030" is a policy change, and by
/// `deprecation_is_local` it cannot break a program that does not use P-256.
pub mod crypto_policy {
    /// Algorithm names that are deprecated by the active policy. Matched
    /// case-insensitively against the algorithm string a program selects.
    ///
    /// Grounds (NIST IR 8547 / general hygiene): the classical primitives are
    /// slated for removal by 2035, and the broken ones are already unsafe. This
    /// list is the migration lever — a language can make selecting one a
    /// compile-time error, which a library cannot.
    pub const DEPRECATED: &[&str] = &[
        // Broken — deprecated unconditionally.
        "md5", "sha1", "sha-1", "des", "3des", "triple-des", "rc4", "md4",
        // Classical asymmetric — NIST IR 8547 removal target (2035), migrate to PQC/hybrid.
        "rsa1024", "rsa-1024", "dsa1024",
    ];

    /// The mechanized `pol a = Current` check: is this algorithm name currently
    /// allowed? A name not in `DEPRECATED` is `Current`.
    #[must_use]
    pub fn is_current(algorithm: &str) -> bool {
        let a = algorithm.to_ascii_lowercase();
        !DEPRECATED.iter().any(|d| a == *d)
    }

    /// A one-line rationale for a rejected algorithm, for the diagnostic.
    #[must_use]
    pub fn deprecation_reason(algorithm: &str) -> &'static str {
        let a = algorithm.to_ascii_lowercase();
        match a.as_str() {
            "md5" | "sha1" | "sha-1" | "md4" => "cryptographically broken (collisions)",
            "des" | "3des" | "triple-des" => "inadequate key size / sweet32",
            "rc4" => "biased keystream, prohibited by RFC 7465",
            _ => "scheduled for removal (NIST IR 8547); migrate to a PQC or hybrid algorithm",
        }
    }
}

/// Crypto-agility sink (REQ-48): a crypto-selection builtin whose string
/// argument names a deprecated algorithm is rejected. Mirrors the Coq
/// `accepts pol (CUse a)` rule — the check runs at the algorithm-selection site,
/// exactly where `CUse` sits in the model. Recognised selection builtins are
/// the ones that take an algorithm name: `guna_kripto`/`use_crypto`,
/// `pilih_algo`/`select_algorithm`, `cipher`/`sifer`, `hash_dengan`/`hash_with`.
fn deprecated_algorithm_at_selection(callee: &Expr, arg: &Expr) -> Option<TypeError> {
    let Expr::Var(name) = callee else { return None };
    let is_selection = matches!(
        name.as_str(),
        "guna_kripto"
            | "use_crypto"
            | "pilih_algo"
            | "select_algorithm"
            | "cipher"
            | "sifer"
            | "hash_dengan"
            | "hash_with"
    );
    if !is_selection {
        return None;
    }
    let Expr::String(algo) = arg else { return None };
    if crypto_policy::is_current(algo) {
        return None;
    }
    Some(TypeError::DeprecatedAlgorithm {
        algorithm: algo.clone(),
        message: crypto_policy::deprecation_reason(algo).to_string(),
    })
}

fn secrecy_at_sink(callee: &Expr, arg_ty: &Ty) -> Option<TypeError> {
    let Expr::Var(name) = callee else { return None };
    let context = match name.as_str() {
        "cetak" | "cetakln" | "cetak_baris" | "print" | "println" => {
            "print sink: declassify (dedah) the secret before printing it"
        }
        // `http_kemaskini` is the BM alias of `http_put` (REQ-27 audit
        // 2026-06-12: it was registered but missing here — a secret body
        // passed the checker). GET/DELETE carry no `Any` body, but their
        // URL/token positions are still exfiltration channels; checking here
        // (before unification) upgrades the opaque TypeMismatch a raw secret
        // would produce into an actionable SecurityViolation.
        "http_post" | "http_hantar" | "http_put" | "http_kemaskini" | "http_get"
        | "http_dapat" | "http_delete" | "http_padam" => {
            "network sink: declassify (dedah) the secret before sending it over the network"
        }
        // The sanitized-path variants (`*_selamat`/`*_safe`) have an
        // `Any`-typed DATA position, so unlike the plain file writes a raw
        // secret sailed through unification (REQ-27 audit 2026-06-12).
        "file_write" | "fail_tulis" | "file_append" | "fail_tambah"
        | "file_write_safe" | "fail_tulis_selamat" => {
            "file-write sink: declassify (dedah) the secret before writing it to a file"
        }
        // A failing assertion renders BOTH operands into the runtime error
        // message (`assert_eq failed: {:?} != {:?}` — builtins/ujian.rs), so
        // an assert on a secret is an error-message sink.
        "assert_eq" | "tegaskan_sama" | "assert_ne" | "tegaskan_beza" => {
            "assertion sink: a failing assertion prints its operands; declassify (dedah) the secret before asserting on it"
        }
        _ => return None,
    };
    let found = ty_secrecy_level(arg_ty)?;
    Some(TypeError::SecurityViolation {
        found,
        expected: SecurityLevel::Public,
        context,
    })
}

/// The highest above-`Public` secrecy carried by `ty` in a data position, or
/// `None` if every leaf is `Public`/unlabeled.
///
/// `Secret<_>` is the lattice top (`SecurityLevel::Secret`); `Labeled(_, l)`
/// contributes `l` when `l != Public`; `SecureChan(_, l)` contributes its own
/// channel level. Recurses through EVERY container a sink could serialize:
/// products, sums, lists, options, the security/taint wrappers, refs,
/// constant-time/zeroizing wrappers, proof witnesses, raw pointers, and the
/// JALINAN / blockchain / Syariah containers (`ContentAddressed`, `Actor`,
/// `CRDT`, `Supervisor`, `SmartContract`, `Token`, `SyariahCompliant`).
///
/// Deliberately does NOT recurse into `Fn` (serializing a closure renders the
/// function value, not its captured data — a secret RESULT is caught at the
/// call site, where the result type is what reaches the sink) nor into
/// `Chan`/`Choreography` (session payloads are governed by the session/IFC
/// rules, not by this scan). `Any` is not treated as secret-bearing — the
/// check is syntactic on the inferred argument type, which is why
/// `propagate_secrecy_through_builtin` exists to re-carry labels through
/// `Any`-typed builtins.
///
/// The match is EXHAUSTIVE on purpose: this walk is exactly as deep as the
/// sink rule, so a missed container is a leak path, and a new `Ty` variant
/// must fail the build here rather than silently open one.
fn ty_secrecy_level(ty: &Ty) -> Option<SecurityLevel> {
    fn join(a: Option<SecurityLevel>, b: Option<SecurityLevel>) -> Option<SecurityLevel> {
        match (a, b) {
            (Some(x), Some(y)) => Some(if x.leq(y) { y } else { x }),
            (x, None) => x,
            (None, y) => y,
        }
    }
    // EXHAUSTIVE by construction — no wildcard arm. This walk is the depth of
    // the sink rule: a container it does not descend into answers "no secret",
    // and `secrecy_at_sink` then lets the value reach `cetak`/`http_post`/
    // `file_write`. It previously ended in `_ => None`, so every JALINAN /
    // blockchain / Syariah container (`ContentAddressed`, `Token`,
    // `SyariahCompliant`, `SmartContract`, `Supervisor`, `CRDT`, `Actor`) and
    // `RawPtr` silently laundered a secret past the check. Adding a `Ty`
    // variant must fail the build here rather than open a new leak path.
    match ty {
        Ty::Secret(inner) => join(Some(SecurityLevel::Secret), ty_secrecy_level(inner)),
        Ty::Labeled(inner, l) => {
            let here = (*l != SecurityLevel::Public).then_some(*l);
            join(here, ty_secrecy_level(inner))
        }
        // A secure channel's own level is part of its secrecy, not just its
        // payload's.
        Ty::SecureChan(_, l) => (*l != SecurityLevel::Public).then_some(*l),

        // Two-component containers: a secret in EITHER position is a secret.
        Ty::Prod(a, b) | Ty::Sum(a, b) | Ty::Actor(a, b) | Ty::CRDT(a, b) => {
            join(ty_secrecy_level(a), ty_secrecy_level(b))
        }

        // Single-component containers: secrecy travels with the payload.
        Ty::List(inner)
        | Ty::Option(inner)
        | Ty::Tainted(inner, _)
        | Ty::Sanitized(inner, _)
        | Ty::Ref(inner, _)
        | Ty::ConstantTime(inner)
        | Ty::Zeroizing(inner)
        | Ty::Proof(inner)
        | Ty::RawPtr(inner)
        | Ty::ContentAddressed(inner)
        | Ty::Supervisor(inner)
        | Ty::SmartContract(inner)
        | Ty::Token(inner)
        | Ty::SyariahCompliant(inner) => ty_secrecy_level(inner),

        // A function is NOT secret because it can return a secret: printing a
        // function value renders the closure, it does not evaluate the body, so
        // no secret is materialised at the sink. The secret is caught at the
        // call site instead, where the result type is what reaches the sink.
        // Deliberate, and now explicit rather than a wildcard's side effect.
        Ty::Fn(_, _, _) => None,

        // `Chan` carries a session type, not a value type — its payload
        // secrecy is enforced by the session/IFC rules, not by this scan.
        Ty::Chan(_) | Ty::Choreography(_, _) => None,

        // Ground types and capability/FFI/UI handles hold no payload.
        Ty::Unit
        | Ty::Bool
        | Ty::Int
        | Ty::IntN { .. }
        | Ty::BigInt
        | Ty::Decimal
        | Ty::Fixed
        | Ty::FixedBin
        | Ty::String
        | Ty::Bytes
        | Ty::Capability(_)
        | Ty::CapabilityFull(_)
        | Ty::Any
        | Ty::CChar
        | Ty::CInt
        | Ty::CVoid
        | Ty::Color
        | Ty::Element
        | Ty::Layout
        | Ty::UIStyle
        | Ty::AccessibleText => None,
    }
}

/// REQ-27 (laundering fix, 2026-06-12): builtins with `Any`-typed positions
/// are opaque to unification, so a secret routed through a pure
/// data-transforming builtin came out unlabeled and walked straight past
/// `secrecy_at_sink` — `cetak(ke_teks(pin))` and
/// `cetak(senarai_tolak((l, pin)))` type-checked while `cetak(pin)` was
/// rejected. These conversions/containers cannot remove secrecy, only move it,
/// so their result must re-carry the argument's level — the same label-join
/// discipline the Coq development applies through elimination forms
/// (Declassification.v: only `T_Declassify` with `declass_ok` lowers a label).
fn is_secrecy_propagating_builtin(name: &str) -> bool {
    const EXACT: &[&str] = &[
        "ke_teks",
        "to_string",
        "ke_bool",
        "to_bool",
        "gabung_teks",
        "nilai_kiri",
        "nilai_kanan",
        "adalah_kiri",
        "adalah_kanan",
    ];
    const PREFIXES: &[&str] = &[
        "str_", "teks_", "list_", "senarai_", "map_", "peta_", "set_", "json_",
    ];
    EXACT.contains(&name) || PREFIXES.iter().any(|p| name.starts_with(p))
}

/// If `callee` is a secrecy-propagating builtin and the argument carries an
/// above-`Public` level, the result type re-carries that level (top joins to
/// `Secret<_>`, intermediate levels to `Labeled(_, l)`). No-op when the result
/// already carries at least that level, and for user functions (their bodies
/// are checked directly; only opaque builtins need the conservative join).
fn propagate_secrecy_through_builtin(callee: &Expr, arg_ty: &Ty, ret_ty: Ty) -> Ty {
    let Expr::Var(name) = callee else {
        return ret_ty;
    };
    if !is_secrecy_propagating_builtin(name) {
        return ret_ty;
    }
    let Some(level) = ty_secrecy_level(arg_ty) else {
        return ret_ty;
    };
    if matches!(ty_secrecy_level(&ret_ty), Some(existing) if level.leq(existing)) {
        return ret_ty;
    }
    if level == SecurityLevel::Secret {
        Ty::Secret(Box::new(ret_ty))
    } else {
        Ty::Labeled(Box::new(ret_ty), level)
    }
}

/// Check if two types are compatible, considering:
/// - Ty::Any as a wildcard
/// - Tainted cannot flow to Sanitized (taint violation)
/// - Sanitized must match exact sanitizer (sanitizer mismatch)
/// - Sanitized can flow to plain type (safe subtyping)
pub fn types_compatible(expected: &Ty, found: &Ty) -> bool {
    // Wildcard — Any matches anything
    if *expected == Ty::Any || *found == Ty::Any {
        return true;
    }

    // Exact match
    if expected == found {
        return true;
    }

    // Sized integers interoperate with the default `Int` (numeric-tower slice):
    // a plain integer literal may initialize a sized binding, and a sized value
    // may be used where `Int` is expected. Same-width/signedness is the exact
    // match above; differing sized types stay incompatible. Width-aware
    // narrowing/overflow checking is a later numeric-tower phase.
    if matches!(
        (expected, found),
        (Ty::Int, Ty::IntN { .. }) | (Ty::IntN { .. }, Ty::Int)
    ) {
        return true;
    }

    // ════════════════════════════════════════════════════════════════════
    // DOMAIN SECURITY: Taint Checking
    // ════════════════════════════════════════════════════════════════════

    // REJECT: Tainted → Sanitized (TAINT VIOLATION)
    // User input cannot flow to sensitive sink without sanitization
    if let (Ty::Sanitized(_, _), Ty::Tainted(_, _)) = (expected, found) {
        return false; // Will trigger TypeError::TypeMismatch → needs better error
    }

    // SANITIZER EXACT MATCH: Sanitized<T, S1> requires Sanitized<T, S2> where S1 == S2
    // SQL sink requires SqlParam sanitizer, not HtmlEscape
    if let (Ty::Sanitized(inner1, san1), Ty::Sanitized(inner2, san2)) = (expected, found) {
        return san1 == san2 && types_compatible(inner1, inner2);
    }

    // SAFE SUBTYPING: Sanitized → Plain Type
    // Sanitized data can be used as plain string (sanitization removes taint)
    match (expected, found) {
        (Ty::String, Ty::Sanitized(inner, _)) if **inner == Ty::String => {
            return true;
        }
        (Ty::Int, Ty::Sanitized(inner, _)) if **inner == Ty::Int => {
            return true;
        }
        _ => {}
    }

    // TAINT SOURCE COMPATIBILITY: Any Tainted matches expected Tainted
    // Sanitizers accept any tainted data, regardless of source
    // Tainted<String, NetworkExternal> matches Tainted<String, UserInput>
    if let (Ty::Tainted(inner1, _), Ty::Tainted(inner2, _)) = (expected, found) {
        return types_compatible(inner1, inner2);
    }

    // ════════════════════════════════════════════════════════════════════
    // Structural Recursion
    // ════════════════════════════════════════════════════════════════════

    match (expected, found) {
        // Function types: contravariant in argument, covariant in return
        (Ty::Fn(a1, r1, e1), Ty::Fn(a2, r2, e2)) => {
            // Effect subsumption: a function whose body has a *smaller* effect
            // (`e2`, found) satisfies a declaration of a *wider* effect (`e1`,
            // expected) — you may always declare more effect than you use (e.g. a
            // `kesan Baca` stub whose body is actually Pure). Argument/return
            // types must be compatible as before.
            types_compatible(a1, a2) && types_compatible(r1, r2) && e2.level() <= e1.level()
        }

        // Product types: covariant in both components
        (Ty::Prod(l1, r1), Ty::Prod(l2, r2)) => {
            types_compatible(l1, l2) && types_compatible(r1, r2)
        }

        // Sum types: covariant in both branches
        (Ty::Sum(l1, r1), Ty::Sum(l2, r2)) => types_compatible(l1, l2) && types_compatible(r1, r2),

        // List types: covariant in element
        (Ty::List(t1), Ty::List(t2)) => types_compatible(t1, t2),

        // Option types: covariant in element
        (Ty::Option(t1), Ty::Option(t2)) => types_compatible(t1, t2),

        // Option <-> Sum: `Option<T>` is structurally `Sum(T, _)`. The Option/
        // Result constructors (`Ada`/`Ok`/...) desugar to `Inl`/`Inr` producing a
        // `Sum`, which must unify with a declared `Mungkin<T>` (Option) return
        // type. The left arm must match the element; the right arm is unconstrained
        // (the None/Tiada payload is unused).
        (Ty::Option(t1), Ty::Sum(l2, _)) | (Ty::Sum(l2, _), Ty::Option(t1)) => {
            types_compatible(t1, l2)
        }

        // Reference types: covariant in inner type, must match security level
        (Ty::Ref(t1, sl1), Ty::Ref(t2, sl2)) => sl1 == sl2 && types_compatible(t1, t2),

        // Secret types: covariant in inner type
        (Ty::Secret(t1), Ty::Secret(t2)) => types_compatible(t1, t2),

        // Labeled types: covariant in inner type, must match security level
        (Ty::Labeled(t1, sl1), Ty::Labeled(t2, sl2)) => sl1 == sl2 && types_compatible(t1, t2),

        // JALINAN / J6 structural types
        (Ty::Actor(s1, m1), Ty::Actor(s2, m2)) => {
            types_compatible(s1, s2) && types_compatible(m1, m2)
        }
        (Ty::ContentAddressed(t1), Ty::ContentAddressed(t2))
        | (Ty::Supervisor(t1), Ty::Supervisor(t2))
        | (Ty::SmartContract(t1), Ty::SmartContract(t2))
        | (Ty::Token(t1), Ty::Token(t2))
        | (Ty::SyariahCompliant(t1), Ty::SyariahCompliant(t2)) => types_compatible(t1, t2),
        (Ty::CRDT(v1, op1), Ty::CRDT(v2, op2)) => {
            types_compatible(v1, v2) && types_compatible(op1, op2)
        }
        (Ty::Choreography(roles1, proto1), Ty::Choreography(roles2, proto2)) => {
            roles1 == roles2 && proto1 == proto2
        }

        // No match
        _ => false,
    }
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
        Expr::Prove(inner_proof) => match inner_proof.as_ref() {
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
        },
        _ => Err(TypeError::InvalidDeclassification {
            message: "Proof expression must be EProve(...)".to_string(),
        }),
    }
}

/// Extract the security level associated with a type.
///
/// This is used for implicit flow tracking: when branching on an expression
/// whose type carries a security level, we elevate Δ in the branch bodies
/// to prevent information leakage through control flow.
///
/// - `Secret(T)` → Secret (classified data)
/// - `Labeled(T, l)` → l (explicitly labeled data)
/// - `Ref(T, l)` after deref → l (reference security level)
/// - All other types → Public (no security restriction)
fn security_level_of_type(ty: &Ty) -> SecurityLevel {
    match ty {
        Ty::Secret(_) => SecurityLevel::Secret,
        Ty::Labeled(_, l) => *l,
        _ => SecurityLevel::Public,
    }
}

/// Strip security labels from a type to get the underlying data type.
/// Used by BinOp and If to work with Labeled values transparently.
fn strip_label(ty: &Ty) -> (&Ty, SecurityLevel) {
    match ty {
        Ty::Labeled(inner, sl) => (inner.as_ref(), *sl),
        Ty::Secret(inner) => (inner.as_ref(), SecurityLevel::Secret),
        _ => (ty, SecurityLevel::Public),
    }
}

/// Strip a ConstantTime wrapper, returning (inner_type, was_ct).
/// Used by BinOp to propagate constant-time discipline through arithmetic.
fn strip_constant_time(ty: &Ty) -> (&Ty, bool) {
    match ty {
        Ty::ConstantTime(inner) => (inner.as_ref(), true),
        _ => (ty, false),
    }
}

/// Result type of integer arithmetic over two operand types (numeric tower).
///
/// A sized operand (`Ty::IntN`) makes the result that same sized type, so the
/// width propagates through `+`/`-`/`*`/`/`/`%` and the codegen/interpreter can
/// wrap at the declared width. A plain `Int` literal adapts to the sized operand
/// (`x: u8 + 1` is `u8`). Two sized operands must agree on width **and**
/// signedness — `u8 + u16` is rejected (returns `None`), unlike the looser
/// `Int`↔`IntN` initialiser compatibility, because silent width mixing would
/// lose bits. Returns `None` when either operand is not an integer.
fn int_arith_result(a: &Ty, b: &Ty) -> Option<Ty> {
    match (a, b) {
        (
            Ty::IntN {
                bits: b1,
                signed: s1,
            },
            Ty::IntN {
                bits: b2,
                signed: s2,
            },
        ) => (b1 == b2 && s1 == s2).then_some(Ty::IntN {
            bits: *b1,
            signed: *s1,
        }),
        (Ty::IntN { bits, signed }, Ty::Int) | (Ty::Int, Ty::IntN { bits, signed }) => {
            Some(Ty::IntN {
                bits: *bits,
                signed: *signed,
            })
        }
        (Ty::Int, Ty::Int) => Some(Ty::Int),
        // Arbitrary-precision integers form their own arithmetic domain; they do
        // not mix with fixed-width ints (convert explicitly via `besar`).
        (Ty::BigInt, Ty::BigInt) => Some(Ty::BigInt),
        // Decimals likewise form their own domain.
        (Ty::Decimal, Ty::Decimal) => Some(Ty::Decimal),
        // Fixed-scale decimals (`wang`/`titik_tetap`) form their own domain too.
        (Ty::Fixed, Ty::Fixed) => Some(Ty::Fixed),
        // Binary fixed-point (`qmn`) likewise.
        (Ty::FixedBin, Ty::FixedBin) => Some(Ty::FixedBin),
        _ => None,
    }
}

/// True when both operands are sized integers (`Ty::IntN`) but disagree on width
/// or signedness (e.g. `u8` and `u16`). Such a mix is rejected by arithmetic to
/// avoid silently dropping bits; a sized type mixed with a plain `Int` is fine.
fn mixed_int_width(a: &Ty, b: &Ty) -> bool {
    matches!(
        (a, b),
        (
            Ty::IntN { bits: b1, signed: s1 },
            Ty::IntN { bits: b2, signed: s2 },
        ) if b1 != b2 || s1 != s2
    )
}

// ============================================================================
// SESSION TYPE HELPERS (JALINAN Phase 6)
// ============================================================================

/// Compute the dual of a session type.
/// Send ↔ Recv, Select ↔ Branch, End ↔ End, Rec/Var preserved.
pub fn session_dual(s: &SessionType) -> SessionType {
    match s {
        SessionType::End => SessionType::End,
        SessionType::Send(ty, cont) => SessionType::Recv(ty.clone(), Box::new(session_dual(cont))),
        SessionType::Recv(ty, cont) => SessionType::Send(ty.clone(), Box::new(session_dual(cont))),
        SessionType::Select(l, r) => {
            SessionType::Branch(Box::new(session_dual(l)), Box::new(session_dual(r)))
        }
        SessionType::Branch(l, r) => {
            SessionType::Select(Box::new(session_dual(l)), Box::new(session_dual(r)))
        }
        SessionType::Rec(x, body) => SessionType::Rec(x.clone(), Box::new(session_dual(body))),
        SessionType::Var(x) => SessionType::Var(x.clone()),
    }
}

/// Check if two session types are dual to each other.
pub fn is_dual(s1: &SessionType, s2: &SessionType) -> bool {
    session_dual(s1) == *s2
}

/// A session type is well-formed (closed) when every recursion `Var` is bound by
/// an enclosing `Rec`. A free session variable makes duality/projection
/// meaningless, so the choreography checker rejects it.
pub fn session_well_formed(s: &SessionType) -> bool {
    fn go(s: &SessionType, bound: &mut Vec<Ident>) -> bool {
        match s {
            SessionType::End => true,
            SessionType::Send(_, k) | SessionType::Recv(_, k) => go(k, bound),
            SessionType::Select(a, b) | SessionType::Branch(a, b) => {
                go(a, bound) && go(b, bound)
            }
            SessionType::Rec(x, body) => {
                bound.push(x.clone());
                let r = go(body, bound);
                bound.pop();
                r
            }
            SessionType::Var(x) => bound.iter().any(|b| b == x),
        }
    }
    go(s, &mut Vec::new())
}

/// Project a choreography's global protocol onto one role's local session type.
///
/// The parser writes the stored `protocol` from the *first* role's perspective
/// (role-relative: `A -> B : T` becomes `Send T` when `A` is `roles[0]` and
/// `Recv T` when `B` is `roles[0]`). For a two-party choreography the first
/// role's local type is therefore the protocol itself and the second role's is
/// its dual — this is the binary-session specialisation of the Coq
/// `project` fixpoint (`ChoreographyTypes.v`), and the projected endpoints are
/// dual by construction (cf. `CT_103_projection_preserves_duality`).
///
/// Returns `None` for a role not in `roles`, or for choreographies with more
/// than two roles (a binary `SessionType` cannot express an N-party local type;
/// full multiparty projection is tracked as future work).
pub fn project_choreography(
    roles: &[Ident],
    protocol: &SessionType,
    role: &str,
) -> Option<SessionType> {
    let idx = roles.iter().position(|r| r == role)?;
    if roles.len() != 2 {
        return None;
    }
    match idx {
        0 => Some(protocol.clone()),
        1 => Some(session_dual(protocol)),
        _ => None,
    }
}

/// Verify that a choreography's roles and protocol compose safely: roles are
/// distinct (≥2) and the protocol is closed, and — for the two-party case —
/// projecting onto each role yields dual (compatible) local types, which
/// guarantees deadlock-free composition (Coq `ST_020_dual_communicate` /
/// `CT_117_choreography_deadlock_free`). Returns a human-readable reason on
/// failure. Three-or-more-party protocols are accepted structurally
/// (well-formed + distinct roles) but not yet projected (binary session types
/// cannot express the per-role views — see `project_choreography`).
pub fn choreography_compatible(roles: &[Ident], protocol: &SessionType) -> Result<(), String> {
    if roles.len() < 2 {
        return Err("a choreography requires at least 2 roles".to_string());
    }
    for (i, r) in roles.iter().enumerate() {
        if roles[i + 1..].iter().any(|o| o == r) {
            return Err(format!("duplicate role '{r}' in choreography"));
        }
    }
    if !session_well_formed(protocol) {
        return Err("protocol has a free (unbound) session variable".to_string());
    }
    if roles.len() == 2 {
        let p0 = project_choreography(roles, protocol, &roles[0])
            .expect("two-role projection is total for index 0");
        let p1 = project_choreography(roles, protocol, &roles[1])
            .expect("two-role projection is total for index 1");
        if !is_dual(&p0, &p1) {
            return Err(format!(
                "projected endpoints for roles '{}' and '{}' are not dual",
                roles[0], roles[1]
            ));
        }
    }
    Ok(())
}

/// Session type subtyping.
/// - Send: covariant in payload, covariant in continuation
/// - Recv: contravariant in payload, covariant in continuation
/// - Select/Branch: covariant in both branches
pub fn session_subtype(sub: &SessionType, sup: &SessionType) -> bool {
    match (sub, sup) {
        (SessionType::End, SessionType::End) => true,
        (SessionType::Send(t1, c1), SessionType::Send(t2, c2)) => {
            types_compatible(t1, t2) && session_subtype(c1, c2)
        }
        (SessionType::Recv(t1, c1), SessionType::Recv(t2, c2)) => {
            // Contravariant in payload: sup's payload must be subtype of sub's
            types_compatible(t2, t1) && session_subtype(c1, c2)
        }
        (SessionType::Select(l1, r1), SessionType::Select(l2, r2)) => {
            session_subtype(l1, l2) && session_subtype(r1, r2)
        }
        (SessionType::Branch(l1, r1), SessionType::Branch(l2, r2)) => {
            session_subtype(l1, l2) && session_subtype(r1, r2)
        }
        (SessionType::Rec(x1, b1), SessionType::Rec(x2, b2)) => x1 == x2 && session_subtype(b1, b2),
        (SessionType::Var(x1), SessionType::Var(x2)) => x1 == x2,
        _ => false,
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
        // Sized integer literal `42u8` types as the distinct `Ty::IntN`, not the
        // default `Ty::Int` (numeric tower).
        Expr::IntN { bits, signed, .. } => Ok((
            Ty::IntN {
                bits: *bits,
                signed: *signed,
            },
            Effect::Pure,
        )),
        Expr::String(_) => Ok((Ty::String, Effect::Pure)),

        // List literal `[e1, e2, ...]`: every element must share a type; the
        // result is `List<elem>`. An empty `[]` is `List<Any>`. The effect is
        // the join of the element effects.
        Expr::ListLit(elems) => {
            let mut elem_ty = Ty::Any;
            let mut eff = Effect::Pure;
            for (i, e) in elems.iter().enumerate() {
                let (t, ef) = type_check_full(ctx, e)?;
                eff = eff.join(ef);
                if i == 0 {
                    elem_ty = t;
                } else if elem_ty != Ty::Any && t != Ty::Any && t != elem_ty {
                    return Err(TypeError::TypeMismatch {
                        expected: elem_ty.clone(),
                        found: t,
                    });
                }
            }
            Ok((Ty::List(Box::new(elem_ty)), eff))
        }

        // Record literal — structural, no nominal type yet, so the result type
        // is `Any`. Field expressions are still checked (for their effects).
        Expr::RecordLit(_name, fields) => {
            let mut eff = Effect::Pure;
            for (_f, e) in fields {
                let (_t, ef) = type_check_full(ctx, e)?;
                eff = eff.join(ef);
            }
            Ok((Ty::Any, eff))
        }

        // Field access — the base is checked (for effects); the field type is
        // `Any` (records are structural with no field-type table yet).
        Expr::FieldAccess(base, _field) => {
            let (_t, eff) = type_check_full(ctx, base)?;
            Ok((Ty::Any, eff))
        }

        // T_Var: Γ(x) = T → has_type Γ Σ Δ (EVar x) T EffectPure
        Expr::Var(x) => {
            let ty = ctx
                .lookup_var(x)
                .cloned()
                .ok_or_else(|| TypeError::VarNotFound(x.clone()))?;
            // A3: Record usage for linearity tracking.
            // Linear/Affine variables error on second use.
            ctx.gamma.record_use(x)?;
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
            Ok((
                Ty::Fn(Box::new(t1.clone()), Box::new(t2), eff),
                Effect::Pure,
            ))
        }

        // T_App: has_type Γ Σ Δ e1 (T1 →[ε'] T2) ε1 →
        //        has_type Γ Σ Δ e2 T1 ε2 →
        //        has_type Γ Σ Δ (e1 e2) T2 (ε1 ⊔ ε2 ⊔ ε')
        Expr::App(e1, e2) => {
            let (t1, eff1) = type_check_full(ctx, e1)?;
            let (t2, eff2) = type_check_full(ctx, e2)?;

            match t1 {
                Ty::Fn(arg_ty, ret_ty, fn_eff) => {
                    // IFC (REQ-27): secret/labeled data may not reach a public
                    // print/network/file-write sink without declassification.
                    // Checked before unification so it wins over a generic
                    // TypeMismatch (e.g. Secret vs the concrete file-write arg).
                    if let Some(err) = secrecy_at_sink(e1, &t2) {
                        return Err(err);
                    }
                    // Crypto-agility (REQ-48): reject selecting a deprecated
                    // algorithm. Coq: crypto/AlgorithmPolicy.v `accepts`.
                    if let Some(err) = deprecated_algorithm_at_selection(e1, e2) {
                        return Err(err);
                    }
                    if !types_compatible(&arg_ty, &t2) {
                        return Err(sink_argument_error(*arg_ty, t2));
                    }
                    // Gate C (hybrid POLA): once a program opts into the
                    // capability discipline (granted set non-empty), a
                    // reach-extending Network/Process operation requires the
                    // matching capability granted in scope. Mirrors the opt-in
                    // `T_Require` rule; a function declaring `kesan Rangkaian`/
                    // `kesan Proses` auto-grants it in its body.
                    //
                    // The gated set covers the reach-extending effects
                    // (Network/Process) and the secret/entropy/OS effects
                    // (Crypto/Random/System). This is now *sound* for compound
                    // declarations: a function declaring `kesan (Kripto, Tulis,
                    // Rawak)` grants every component (via `effect_set` on the
                    // function decl), so a legitimate compound-effect function
                    // (e.g. `crypto_ops.rii`) is no longer a false positive. File
                    // I/O stays at effect+taint typing (not capability-gated).
                    if matches!(
                        fn_eff,
                        Effect::Network
                            | Effect::NetworkSecure
                            | Effect::Process
                            | Effect::Crypto
                            | Effect::Random
                            | Effect::System
                    ) && !ctx.granted.is_empty()
                        && !ctx.granted.contains(&fn_eff)
                    {
                        return Err(TypeError::CapabilityViolation {
                            required: fn_eff,
                            message: format!(
                                "{fn_eff:?} operation requires a granted {fn_eff:?} capability in scope"
                            ),
                        });
                    }
                    let total_eff = eff1.join(eff2).join(fn_eff);
                    // REQ-27: a pure data-transforming builtin re-carries its
                    // argument's secrecy (laundering fix — see
                    // propagate_secrecy_through_builtin).
                    let ret_ty = propagate_secrecy_through_builtin(e1, &t2, *ret_ty);
                    Ok((ret_ty, total_eff))
                }
                // Applying an `Any`-typed callee (e.g. a closure passed as an
                // `Any` parameter, or a higher-order builtin result) yields `Any`.
                Ty::Any => Ok((Ty::Any, eff1.join(eff2))),
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
                // Projecting a component of an `Any`-typed value (e.g. a closure
                // parameter bound from a `untuk (a, b)` destructure) yields `Any`.
                Ty::Any => Ok((Ty::Any, eff)),
                _ => Err(TypeError::ExpectedProduct(t)),
            }
        }
        Expr::Snd(e) => {
            let (t, eff) = type_check_full(ctx, e)?;
            match t {
                Ty::Prod(_, t2) => Ok((*t2, eff)),
                Ty::Any => Ok((Ty::Any, eff)),
                _ => Err(TypeError::ExpectedProduct(t)),
            }
        }

        // ════════════════════════════════════════════════════════════════════
        // VERIFIED: Sums (T_Inl, T_Inr, T_Case)
        // ════════════════════════════════════════════════════════════════════
        Expr::Inl(e, ty) => match ty {
            Ty::Sum(t1, t2) => {
                let (te, eff) = type_check_full(ctx, e)?;
                if te != **t1 {
                    return Err(TypeError::TypeMismatch {
                        expected: *t1.clone(),
                        found: te,
                    });
                }
                Ok((Ty::Sum(t1.clone(), t2.clone()), eff))
            }
            // Unannotated injection (from `Some(x)`/`Ok(x)` desugaring, carrying
            // `Ty::Any`): infer the left arm from the payload; right arm open.
            Ty::Any => {
                let (te, eff) = type_check_full(ctx, e)?;
                Ok((Ty::Sum(Box::new(te), Box::new(Ty::Any)), eff))
            }
            _ => Err(TypeError::ExpectedSum(ty.clone())),
        },
        Expr::Inr(e, ty) => match ty {
            Ty::Sum(t1, t2) => {
                let (te, eff) = type_check_full(ctx, e)?;
                if te != **t2 {
                    return Err(TypeError::TypeMismatch {
                        expected: *t2.clone(),
                        found: te,
                    });
                }
                Ok((Ty::Sum(t1.clone(), t2.clone()), eff))
            }
            // Unannotated injection (from `Err(x)`/`None` desugaring): infer the
            // right arm from the payload; left arm open.
            Ty::Any => {
                let (te, eff) = type_check_full(ctx, e)?;
                Ok((Ty::Sum(Box::new(Ty::Any), Box::new(te)), eff))
            }
            _ => Err(TypeError::ExpectedSum(ty.clone())),
        },
        // REQ-12: IFC-aware case analysis — elevate Δ in branches
        Expr::Case(e, x, e1, y, e2) => {
            let (t, eff) = type_check_full(ctx, e)?;
            // Normalize the scrutinee to a (left, right) pair of branch-binder
            // types. `Sum` is the native form; `Option<T>` is `(T, Unit)` (Ada
            // carries T, Tidak carries Unit); `Any` binds both as `Any`.
            let sum_arms: Option<(Ty, Ty)> = match &t {
                Ty::Sum(l, r) => Some(((**l).clone(), (**r).clone())),
                Ty::Option(inner) => Some(((**inner).clone(), Ty::Unit)),
                Ty::Any => Some((Ty::Any, Ty::Any)),
                _ => None,
            };
            match sum_arms {
                Some((t_left, t_right)) => {
                    let scrutinee_level = security_level_of_type(&t);
                    let branch_delta = ctx.delta.join(scrutinee_level);

                    let mut ctx1 = TypingContext {
                        gamma: ctx.gamma.extend(x.clone(), t_left),
                        sigma: ctx.sigma.clone(),
                        delta: branch_delta,
                        granted: ctx.granted.clone(),
                    };
                    let (t1, eff1) = type_check_full(&mut ctx1, e1)?;

                    let mut ctx2 = TypingContext {
                        gamma: ctx.gamma.extend(y.clone(), t_right),
                        sigma: ctx.sigma.clone(),
                        delta: branch_delta,
                        granted: ctx.granted.clone(),
                    };
                    let (t2, eff2) = type_check_full(&mut ctx2, e2)?;

                    // Branch result types must agree. `Any` (from unannotated
                    // Option/Result payloads, e.g. a `padan` arm that returns the
                    // bound payload) unifies with the concrete branch type; the
                    // result is the more concrete of the two.
                    if !types_compatible(&t1, &t2) {
                        return Err(TypeError::TypeMismatch {
                            expected: t1,
                            found: t2,
                        });
                    }
                    let result_ty = join_branch_types(t1, t2);

                    Ok((result_ty, eff.join(eff1).join(eff2)))
                }
                None => Err(TypeError::ExpectedSum(t)),
            }
        }

        // ════════════════════════════════════════════════════════════════════
        // FORMALIZED: Control (T_If, T_Let, T_LetRec)
        // REQ-12: IFC-aware branching — elevate Δ in branch bodies
        // ════════════════════════════════════════════════════════════════════
        Expr::If(cond, e2, e3) => {
            let (t_cond, eff1) = type_check_full(ctx, cond)?;

            // IFC: Accept both Bool and Labeled(Bool, level) as condition.
            // Strip label to check inner type is Bool, but preserve the
            // security level for branch elevation.
            let (inner_cond, cond_label_level) = strip_label(&t_cond);

            // A2: ConstantTime enforcement — reject CT values as branch conditions.
            // Branching on a ConstantTime value creates a timing side-channel
            // because the branch taken reveals information about the value.
            if matches!(inner_cond, Ty::ConstantTime(_)) {
                return Err(TypeError::ConstantTimeViolation {
                    context: "branch condition",
                });
            }

            // The condition must be Bool; `Any` (the wildcard, e.g. from a method
            // call or indexing that the structural checker types as Any) is also
            // accepted.
            if *inner_cond != Ty::Bool && *inner_cond != Ty::Any {
                return Err(TypeError::TypeMismatch {
                    expected: Ty::Bool,
                    found: inner_cond.clone(),
                });
            }

            // IFC: Elevate Δ in branches based on condition's security level.
            // If the condition was derived from high-security data (e.g.,
            // comparing a secret-labeled value), the branches must execute at
            // that elevated security level to prevent implicit flows through
            // control structure.
            //
            // Before this fix, cond_level was always Public because t_cond
            // was always Ty::Bool. Now Deref propagates labels and BinOp
            // preserves them, so a comparison of secret data produces
            // Labeled(Bool, Secret), and cond_label_level = Secret.
            let cond_level = cond_label_level;
            let branch_delta = ctx.delta.join(cond_level);

            let mut branch_ctx = TypingContext {
                gamma: ctx.gamma.clone(),
                sigma: ctx.sigma.clone(),
                delta: branch_delta,
                granted: ctx.granted.clone(),
            };

            let (t2, eff2) = type_check_full(&mut branch_ctx, e2)?;
            let mut branch_ctx2 = TypingContext {
                gamma: ctx.gamma.clone(),
                sigma: ctx.sigma.clone(),
                delta: branch_delta,
                granted: ctx.granted.clone(),
            };
            let (t3, eff3) = type_check_full(&mut branch_ctx2, e3)?;

            // Branch types must agree; `Any` (e.g. from a `padan` arm returning
            // an unannotated Option/Result payload) unifies with the concrete
            // branch type. The result is the more concrete of the two.
            if !types_compatible(&t2, &t3) {
                return Err(TypeError::TypeMismatch {
                    expected: t2,
                    found: t3,
                });
            }
            let result_ty = join_branch_types(t2, t3);

            Ok((result_ty, eff1.join(eff2).join(eff3)))
        }
        // ── Loops and mutable locals (compiler-level; no Coq counterpart yet) ──
        //
        // T_While: Γ ⊢ cond : Bool, ε₁ →  Γ ⊢ body : _, ε₂ →
        //          Γ ⊢ (while cond body) : Unit, ε₁ ⊔ ε₂
        //
        // The body's own type is discarded (a loop body is evaluated for its
        // effects), and the loop itself always yields `()`. Effects are the join
        // of both — a body that prints makes the loop `Tulis`, once, however many
        // times it runs.
        Expr::While(cond, body) => {
            let (t_cond, eff_cond) = type_check_full(ctx, cond)?;
            let (inner_cond, _) = strip_label(&t_cond);
            if !matches!(inner_cond, Ty::Bool | Ty::Any) {
                return Err(TypeError::TypeMismatch {
                    expected: Ty::Bool,
                    found: t_cond,
                });
            }
            let (_t_body, eff_body) = type_check_full(ctx, body)?;
            Ok((Ty::Unit, eff_cond.join(eff_body)))
        }
        // `putus` / `lanjut` never yield to their evaluation context, so — like
        // `pulang` — they take type `Any` and unify with any sibling branch type.
        // The parser has already rejected them outside a loop.
        Expr::Break | Expr::Continue => Ok((Ty::Any, Effect::Pure)),

        // T_LetMut: Γ ⊢ e₁ : T, ε₁ →  Γ, x:Ref(T,Awam) ⊢ e₂ : U, ε₂ →
        //           Γ ⊢ (biar ubah x = e₁; e₂) : U, ε₁ ⊔ ε₂
        //
        // NOTE the absent `⊔ EffectWrite`: unlike T_Ref/T_Deref/T_Assign (which
        // mirror Coq `Typing.v` and must not be weakened), a slot is not first
        // class. `SlotGet`/`SlotSet` name a binder directly, so the cell can
        // never be aliased, returned or stored — reading and writing it is
        // unobservable outside the binding, the standard encapsulated-state
        // argument. A local counter therefore stays `kesan Bersih`.
        Expr::LetMut(x, e1, e2) => {
            let (t1, eff1) = type_check_full(ctx, e1)?;
            let mut inner = ctx.extend_gamma(x.clone(), Ty::Ref(Box::new(t1), SecurityLevel::Public));
            let (t2, eff2) = type_check_full(&mut inner, e2)?;
            Ok((t2, eff1.join(eff2)))
        }
        Expr::SlotGet(x) => {
            let ty = ctx
                .lookup_var(x)
                .cloned()
                .ok_or_else(|| TypeError::VarNotFound(x.clone()))?;
            match ty {
                Ty::Ref(inner, _) => Ok((*inner, Effect::Pure)),
                other => Ok((other, Effect::Pure)),
            }
        }
        Expr::SlotSet(x, e) => {
            let (t_val, eff) = type_check_full(ctx, e)?;
            let slot_ty = ctx
                .lookup_var(x)
                .cloned()
                .ok_or_else(|| TypeError::VarNotFound(x.clone()))?;
            if let Ty::Ref(inner, _) = slot_ty {
                let (assigned, _) = strip_label(&t_val);
                if !types_compatible(&inner, assigned) {
                    return Err(TypeError::TypeMismatch {
                        expected: *inner,
                        found: assigned.clone(),
                    });
                }
            }
            Ok((Ty::Unit, eff))
        }
        Expr::Let(x, linearity, e1, e2) => {
            let (t1, eff1) = type_check_full(ctx, e1)?;
            let new_ctx = match linearity {
                Some(lin) => ctx.extend_gamma_linear(x.clone(), t1, *lin),
                None => ctx.extend_gamma(x.clone(), t1),
            };
            let mut new_ctx_mut = new_ctx;
            let (t2, eff2) = type_check_full(&mut new_ctx_mut, e2)?;
            // A3: Check linearity constraints at scope exit.
            // Linear variables must have been used exactly once; Relevant at least once.
            new_ctx_mut.gamma.check_linearity_at_exit(x)?;
            Ok((t2, eff1.join(eff2)))
        }
        // `pulang e` — early return. Its operand is type-checked (and its effect
        // propagated), but the return expression itself never yields to its
        // evaluation context, so it has type `Any` (unifies with any sibling
        // branch/sequence type via `types_compatible`).
        Expr::Return(e) => {
            let (_t, eff) = type_check_full(ctx, e)?;
            Ok((Ty::Any, eff))
        }
        Expr::LetRec(x, ty_ann, e1, e2) => {
            let ctx_rec = ctx.extend_gamma(x.clone(), ty_ann.clone());
            // Grant the function's declared effect so Require inside body is authorized.
            // For multi-param: ty_ann is Fn(_, _, eff). For zero-param: ty_ann is the
            // return type, but e1's body effect will be checked at program level.
            // We extract effect from ty_ann if it's Fn, or from the body's computed effect.
            let ctx_rec = match ty_ann {
                Ty::Fn(_, _, fn_eff) => ctx_rec.with_grant(*fn_eff),
                _ => ctx_rec,
            };
            let mut ctx_rec_mut = ctx_rec.clone();
            let (t1, eff1) = type_check_full(&mut ctx_rec_mut, e1)?;
            if !types_compatible(ty_ann, &t1) {
                return Err(TypeError::AnnotationMismatch {
                    expected: ty_ann.clone(),
                    found: t1,
                });
            }
            let mut ctx_rec_mut2 = ctx_rec;
            let (t2, eff2) = type_check_full(&mut ctx_rec_mut2, e2)?;
            Ok((t2, eff1.join(eff2)))
        }

        // Mutually-recursive group (REQ-44 forward references): all group names
        // are in scope in every body AND the continuation. Grant every declared
        // effect (over-granting only admits MORE programs — the body-effect <=
        // declared discipline is enforced separately in validate_top_level_decls,
        // so this never falsely rejects). Recursion soundness is mechanized in
        // foundations/RecursionSafety.v.
        Expr::LetRecGroup(bindings, cont) => {
            let mut ctx_rec = ctx.clone();
            for (name, ty_ann, _) in bindings {
                ctx_rec = ctx_rec.extend_gamma(name.clone(), ty_ann.clone());
            }
            for (_, ty_ann, _) in bindings {
                if let Ty::Fn(_, _, fn_eff) = ty_ann {
                    ctx_rec = ctx_rec.with_grant(*fn_eff);
                }
            }
            let mut eff = Effect::Pure;
            for (_, ty_ann, e1) in bindings {
                let mut c = ctx_rec.clone();
                let (t1, eff1) = type_check_full(&mut c, e1)?;
                if !types_compatible(ty_ann, &t1) {
                    return Err(TypeError::AnnotationMismatch {
                        expected: ty_ann.clone(),
                        found: t1,
                    });
                }
                eff = eff.join(eff1);
            }
            let mut c2 = ctx_rec;
            let (t2, eff2) = type_check_full(&mut c2, cont)?;
            Ok((t2, eff.join(eff2)))
        }

        // ════════════════════════════════════════════════════════════════════
        // FORMALIZED: Effects (T_Perform, T_Handle)
        // ════════════════════════════════════════════════════════════════════
        Expr::Perform(eff, e) => {
            let (te, eff_e) = type_check_full(ctx, e)?;
            Ok((te, eff_e.join(*eff)))
        }
        Expr::Handle(e, x, h) => {
            let (t_e, eff_e) = type_check_full(ctx, e)?;
            // Coq T_Handle (Typing.v:172-175): handler binds x : T in h
            let mut h_ctx = ctx.extend_gamma(x.clone(), t_e);
            let (t_h, eff_h) = type_check_full(&mut h_ctx, h)?;
            // Coq: result effect is effect_join ε1 ε2
            Ok((t_h, eff_e.join(eff_h)))
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
                    // IFC: Propagate security label to the result value.
                    // Dereferencing a Secret-level reference produces a Labeled value,
                    // so downstream expressions (BinOp, If) can track the data's origin.
                    // This is essential for implicit flow prevention: if we compare a
                    // secret-derived value and branch on the result, the branch delta
                    // must be elevated.
                    let result_ty = if sl != SecurityLevel::Public {
                        Ty::Labeled(inner, sl)
                    } else {
                        *inner
                    };
                    Ok((result_ty, eff.join(Effect::Read)))
                }
                // `!` is overloaded: on a Bool it is logical negation (the corpus
                // writes `!cond`); `Any` (unknown) is likewise treated as boolean.
                Ty::Bool => Ok((Ty::Bool, eff)),
                Ty::Any => Ok((Ty::Any, eff)),
                _ => Err(TypeError::ExpectedRef(t)),
            }
        }

        // T_Assign: has_type Γ Σ Δ e1 (TRef T l) ε1 →
        //           has_type Γ Σ Δ e2 T ε2 →
        //           Δ ⊑ l →  (* NO-WRITE-DOWN: Bell-LaPadula *-property *)
        //           has_type Γ Σ Δ (EAssign e1 e2) TUnit (ε1 ⊔ ε2 ⊔ EffectWrite)
        //
        // IFC enforcement (REQ-12): The security context Δ must flow to the
        // reference level l. This prevents implicit information flows where
        // a branch guarded by secret data writes to a public reference.
        // Combined with T_Deref (l ⊑ Δ, no-read-up), this gives Bell-LaPadula.
        Expr::Assign(e1, e2) => {
            let (t1, eff1) = type_check_full(ctx, e1)?;
            let (t2, eff2) = type_check_full(ctx, e2)?;
            match t1 {
                Ty::Ref(inner, sl) => {
                    // IFC check: Δ ⊑ sl (no-write-down)
                    // Program counter security level must flow to reference level.
                    // Prevents: secret-context code writing to public references.
                    if !ctx.delta.leq(sl) {
                        return Err(TypeError::ImplicitFlowViolation {
                            branch_level: ctx.delta,
                            target_level: sl,
                            context: "assignment",
                        });
                    }
                    // Strip labels from assigned value for type compatibility.
                    // A Labeled(Int, Secret) value is assignable to Ref(Int, Secret).
                    let (inner_t2, _) = strip_label(&t2);
                    if *inner != *inner_t2 {
                        return Err(TypeError::TypeMismatch {
                            expected: *inner,
                            found: inner_t2.clone(),
                        });
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
                    // Strict mode: matches Coq T_Declassify (Typing.v:198-202)
                    // Coq rule requires e1 : TSecret(T) — no alternative case
                    Err(TypeError::ExpectedSecret(t))
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
            // T_Require: if granted set is populated, enforce capability check.
            // Program-level validate_capabilities provides the authoritative check;
            // type-level enforcement is an additional guard when grant context is available.
            if !ctx.granted.is_empty() && !ctx.granted.contains(eff) {
                return Err(TypeError::CapabilityViolation {
                    required: *eff,
                    message: format!("effect {:?} required but not granted in current scope", eff),
                });
            }
            let (t, e_eff) = type_check_full(ctx, e)?;
            Ok((t, e_eff.join(*eff)))
        }
        Expr::Grant(eff, e) => {
            // T_Grant: typecheck body with eff added to granted set
            let mut grant_ctx = ctx.with_grant(*eff);
            let (t, e_eff) = type_check_full(&mut grant_ctx, e)?;
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
        Expr::FFICall {
            name: _,
            args,
            ret_ty,
        } => {
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

            // IFC: Strip security labels for type checking, but track the
            // maximum security level of operands. The result inherits this level.
            // This ensures that comparing secret-derived values produces a
            // Labeled(Bool, Secret) result, which triggers branch elevation in If.
            let (inner1, sl1) = strip_label(&t1);
            let (inner2, sl2) = strip_label(&t2);
            let max_sl = sl1.join(sl2);

            // A2: Strip ConstantTime wrappers for type checking, but propagate
            // the CT tag through arithmetic/comparison so CT values can't silently
            // escape the constant-time discipline via BinOp.
            let (inner1, ct1) = strip_constant_time(inner1);
            let (inner2, ct2) = strip_constant_time(inner2);
            let any_ct = ct1 || ct2;

            // Helper: wrap result type with security label and/or CT tag
            let label_result = |ty: Ty| -> Ty {
                let ty = if any_ct {
                    Ty::ConstantTime(Box::new(ty))
                } else {
                    ty
                };
                if max_sl != SecurityLevel::Public {
                    Ty::Labeled(Box::new(ty), max_sl)
                } else {
                    ty
                }
            };

            match op {
                BinOp::Add => {
                    // `+` is overloaded for Int (addition) and String
                    // (concatenation). If either operand is `Any` (its concrete
                    // type unknown, e.g. a list element from `senarai_dapat`), the
                    // result type is also `Any` rather than eagerly committing to
                    // String — which would wrongly reject an Int at use sites.
                    if *inner1 == Ty::Any || *inner2 == Ty::Any {
                        Ok((label_result(Ty::Any), eff))
                    } else if *inner1 == Ty::String && *inner2 == Ty::String {
                        Ok((label_result(Ty::String), eff))
                    } else if *inner1 == Ty::BigInt && *inner2 == Ty::BigInt {
                        Ok((label_result(Ty::BigInt), eff))
                    } else if *inner1 == Ty::Decimal && *inner2 == Ty::Decimal {
                        Ok((label_result(Ty::Decimal), eff))
                    } else if *inner1 == Ty::Fixed && *inner2 == Ty::Fixed {
                        Ok((label_result(Ty::Fixed), eff))
                    } else if *inner1 == Ty::FixedBin && *inner2 == Ty::FixedBin {
                        Ok((label_result(Ty::FixedBin), eff))
                    } else if types_compatible(&Ty::Int, inner1)
                        && types_compatible(&Ty::Int, inner2)
                    {
                        // Numeric tower: a sized operand propagates its width to the
                        // result; a plain `Int` literal adapts. Two sized operands of
                        // different width/signedness are rejected (silent bit loss).
                        if mixed_int_width(inner1, inner2) {
                            return Err(TypeError::TypeMismatch {
                                expected: inner1.clone(),
                                found: inner2.clone(),
                            });
                        }
                        Ok((
                            label_result(int_arith_result(inner1, inner2).unwrap_or(Ty::Int)),
                            eff,
                        ))
                    } else if types_compatible(&Ty::String, inner1)
                        && types_compatible(&Ty::String, inner2)
                    {
                        Ok((label_result(Ty::String), eff))
                    } else if let (Ty::List(e1), Ty::List(e2)) = (inner1, inner2) {
                        // `+` also concatenates lists (`[x] + akum`). The element
                        // types must be compatible; the result keeps the more
                        // concrete element type.
                        if types_compatible(e1, e2) {
                            Ok((label_result(Ty::List(Box::new(join_branch_types(
                                (**e1).clone(),
                                (**e2).clone(),
                            )))), eff))
                        } else {
                            Err(TypeError::TypeMismatch {
                                expected: inner1.clone(),
                                found: inner2.clone(),
                            })
                        }
                    } else {
                        Err(TypeError::TypeMismatch {
                            expected: inner1.clone(),
                            found: inner2.clone(),
                        })
                    }
                }
                BinOp::Sub | BinOp::Mul | BinOp::Div | BinOp::Mod => {
                    // A2: integer division and modulo have data-dependent latency
                    // on real ISAs, so a ConstantTime operand would leak through
                    // timing exactly like a secret-dependent branch. Reject CT
                    // div/mod (Sub/Mul are constant-time and keep the CT tag).
                    if any_ct && matches!(op, BinOp::Div | BinOp::Mod) {
                        return Err(TypeError::ConstantTimeViolation {
                            context: "variable-time division or modulo",
                        });
                    }
                    // Arbitrary-precision integer / decimal arithmetic (each its
                    // own domain, distinct from `Int` and from each other).
                    if (*inner1 == Ty::BigInt && *inner2 == Ty::BigInt)
                        || (*inner1 == Ty::Decimal && *inner2 == Ty::Decimal)
                        || (*inner1 == Ty::Fixed && *inner2 == Ty::Fixed)
                        || (*inner1 == Ty::FixedBin && *inner2 == Ty::FixedBin)
                    {
                        return Ok((label_result(inner1.clone()), eff));
                    }
                    if !types_compatible(&Ty::Int, inner1) {
                        return Err(TypeError::TypeMismatch {
                            expected: Ty::Int,
                            found: inner1.clone(),
                        });
                    }
                    if !types_compatible(&Ty::Int, inner2) {
                        return Err(TypeError::TypeMismatch {
                            expected: Ty::Int,
                            found: inner2.clone(),
                        });
                    }
                    // Numeric tower: reject mixing two different sized widths;
                    // otherwise propagate the sized width (a plain `Int` adapts).
                    if mixed_int_width(inner1, inner2) {
                        return Err(TypeError::TypeMismatch {
                            expected: inner1.clone(),
                            found: inner2.clone(),
                        });
                    }
                    Ok((
                        label_result(int_arith_result(inner1, inner2).unwrap_or(Ty::Int)),
                        eff,
                    ))
                }
                BinOp::Eq | BinOp::Ne => {
                    if !types_compatible(inner1, inner2) {
                        return Err(TypeError::TypeMismatch {
                            expected: inner1.clone(),
                            found: inner2.clone(),
                        });
                    }
                    if !types_compatible(&Ty::Int, inner1)
                        && !types_compatible(&Ty::Bool, inner1)
                        && !types_compatible(&Ty::String, inner1)
                        && *inner1 != Ty::BigInt
                        && *inner1 != Ty::Decimal
                        && *inner1 != Ty::Fixed
                        && *inner1 != Ty::FixedBin
                    {
                        return Err(TypeError::TypeMismatch {
                            expected: Ty::Int,
                            found: inner1.clone(),
                        });
                    }
                    Ok((label_result(Ty::Bool), eff))
                }
                BinOp::Lt | BinOp::Le | BinOp::Gt | BinOp::Ge => {
                    // Ordering is defined for fixed-width ints, BigInt, Decimal,
                    // Fixed, and FixedBin.
                    if (*inner1 == Ty::BigInt && *inner2 == Ty::BigInt)
                        || (*inner1 == Ty::Decimal && *inner2 == Ty::Decimal)
                        || (*inner1 == Ty::Fixed && *inner2 == Ty::Fixed)
                        || (*inner1 == Ty::FixedBin && *inner2 == Ty::FixedBin)
                    {
                        return Ok((label_result(Ty::Bool), eff));
                    }
                    if !types_compatible(&Ty::Int, inner1) {
                        return Err(TypeError::TypeMismatch {
                            expected: Ty::Int,
                            found: inner1.clone(),
                        });
                    }
                    if !types_compatible(&Ty::Int, inner2) {
                        return Err(TypeError::TypeMismatch {
                            expected: Ty::Int,
                            found: inner2.clone(),
                        });
                    }
                    Ok((label_result(Ty::Bool), eff))
                }
                BinOp::And | BinOp::Or => {
                    if !types_compatible(&Ty::Bool, inner1) {
                        return Err(TypeError::TypeMismatch {
                            expected: Ty::Bool,
                            found: inner1.clone(),
                        });
                    }
                    if !types_compatible(&Ty::Bool, inner2) {
                        return Err(TypeError::TypeMismatch {
                            expected: Ty::Bool,
                            found: inner2.clone(),
                        });
                    }
                    Ok((label_result(Ty::Bool), eff))
                }
            }
        }

        // ════════════════════════════════════════════════════════════════════
        // JALINAN Phase 6: Session Types, Actors, Choreography, CRDTs
        // ════════════════════════════════════════════════════════════════════
        Expr::ActorDecl {
            name: _,
            state_ty,
            message_ty,
            init_state,
            handler,
        } => {
            // Type-check init_state: must match declared state_ty
            let (init_ty, eff1) = type_check_full(ctx, init_state)?;
            if !types_compatible(state_ty, &init_ty) {
                return Err(TypeError::TypeMismatch {
                    expected: state_ty.clone(),
                    found: init_ty,
                });
            }
            // Type-check handler: must be Fn(message_ty) -> state_ty
            let (handler_ty, eff2) = type_check_full(ctx, handler)?;
            match &handler_ty {
                Ty::Fn(arg, ret, _) => {
                    if !types_compatible(message_ty, arg) {
                        return Err(TypeError::TypeMismatch {
                            expected: message_ty.clone(),
                            found: *arg.clone(),
                        });
                    }
                    if !types_compatible(state_ty, ret) {
                        return Err(TypeError::TypeMismatch {
                            expected: state_ty.clone(),
                            found: *ret.clone(),
                        });
                    }
                }
                _ => return Err(TypeError::ExpectedFunction(handler_ty)),
            }
            Ok((
                Ty::Actor(Box::new(state_ty.clone()), Box::new(message_ty.clone())),
                eff1.join(eff2),
            ))
        }

        Expr::ChoreographyBlock {
            name: _,
            roles,
            protocol,
        } => {
            // Parse → project → check: the protocol must be closed, its roles
            // distinct, and (for the two-party case) its per-role projections
            // dual. This wires the projection pipeline into typechecking.
            if let Err(reason) = choreography_compatible(roles, protocol) {
                return Err(TypeError::ChoreographyError {
                    message: format!("ill-formed choreography: {reason}"),
                });
            }
            Ok((
                Ty::Choreography(roles.clone(), protocol.clone()),
                Effect::Pure,
            ))
        }

        Expr::Spawn(actor_expr, init_state_expr) => {
            let (actor_ty, eff1) = type_check_full(ctx, actor_expr)?;
            let (init_ty, eff2) = type_check_full(ctx, init_state_expr)?;
            match &actor_ty {
                Ty::Actor(state_ty, msg_ty) => {
                    if !types_compatible(state_ty, &init_ty) {
                        return Err(TypeError::TypeMismatch {
                            expected: *state_ty.clone(),
                            found: init_ty,
                        });
                    }
                    Ok((
                        Ty::Actor(state_ty.clone(), msg_ty.clone()),
                        eff1.join(eff2).join(Effect::Process),
                    ))
                }
                _ => Err(TypeError::ExpectedActor(actor_ty)),
            }
        }

        Expr::ActorSend(actor_expr, msg_expr) => {
            let (actor_ty, eff1) = type_check_full(ctx, actor_expr)?;
            let (msg_ty, eff2) = type_check_full(ctx, msg_expr)?;
            match &actor_ty {
                Ty::Actor(_, expected_msg) => {
                    if !types_compatible(expected_msg, &msg_ty) {
                        return Err(TypeError::TypeMismatch {
                            expected: *expected_msg.clone(),
                            found: msg_ty,
                        });
                    }
                    Ok((Ty::Unit, eff1.join(eff2).join(Effect::Network)))
                }
                _ => Err(TypeError::ExpectedActor(actor_ty)),
            }
        }

        Expr::ActorRecv(actor_expr) => {
            let (actor_ty, eff) = type_check_full(ctx, actor_expr)?;
            match &actor_ty {
                Ty::Actor(_, msg_ty) => Ok((*msg_ty.clone(), eff.join(Effect::Network))),
                _ => Err(TypeError::ExpectedActor(actor_ty)),
            }
        }

        Expr::CRDTMerge(left, right) => {
            let (left_ty, eff1) = type_check_full(ctx, left)?;
            let (right_ty, eff2) = type_check_full(ctx, right)?;
            match (&left_ty, &right_ty) {
                (Ty::CRDT(t1, op1), Ty::CRDT(t2, op2)) => {
                    if !types_compatible(t1, t2) || !types_compatible(op1, op2) {
                        return Err(TypeError::CRDTMismatch {
                            left: left_ty,
                            right: right_ty,
                        });
                    }
                    Ok((Ty::CRDT(t1.clone(), op1.clone()), eff1.join(eff2)))
                }
                (Ty::CRDT(_, _), _) => Err(TypeError::ExpectedCRDT(right_ty)),
                _ => Err(TypeError::ExpectedCRDT(left_ty)),
            }
        }

        Expr::ContentHash(expr) => {
            let (inner_ty, eff) = type_check_full(ctx, expr)?;
            Ok((
                Ty::ContentAddressed(Box::new(inner_ty)),
                eff.join(Effect::Crypto),
            ))
        }

        Expr::ContentVerify(expected_hash, value) => {
            let (expected_ty, eff1) = type_check_full(ctx, expected_hash)?;
            let (value_ty, eff2) = type_check_full(ctx, value)?;
            let expected = Ty::ContentAddressed(Box::new(value_ty.clone()));
            match expected_ty {
                Ty::ContentAddressed(inner_ty) => {
                    if !types_compatible(&inner_ty, &value_ty) {
                        return Err(TypeError::TypeMismatch {
                            expected,
                            found: Ty::ContentAddressed(inner_ty),
                        });
                    }
                    Ok((Ty::Bool, eff1.join(eff2).join(Effect::Crypto)))
                }
                found => Err(TypeError::TypeMismatch { expected, found }),
            }
        }

        Expr::ContractDeploy(contract) => {
            let (inner_ty, eff) = type_check_full(ctx, contract)?;
            Ok((
                Ty::SmartContract(Box::new(inner_ty)),
                eff.join(Effect::NetworkSecure),
            ))
        }

        Expr::TokenTransfer { from, to, amount } => {
            let (from_ty, eff1) = type_check_full(ctx, from)?;
            let (to_ty, eff2) = type_check_full(ctx, to)?;
            let (amount_ty, eff3) = type_check_full(ctx, amount)?;
            match (&from_ty, &to_ty) {
                (Ty::Token(from_inner), Ty::Token(to_inner)) => {
                    if !types_compatible(from_inner, to_inner) {
                        return Err(TypeError::TypeMismatch {
                            expected: Ty::Token(from_inner.clone()),
                            found: to_ty,
                        });
                    }
                    if !types_compatible(from_inner, &amount_ty) {
                        return Err(TypeError::TypeMismatch {
                            expected: *from_inner.clone(),
                            found: amount_ty,
                        });
                    }
                    Ok((
                        Ty::Token(from_inner.clone()),
                        eff1.join(eff2).join(eff3).join(Effect::NetworkSecure),
                    ))
                }
                (Ty::Token(_), _) => Err(TypeError::TypeMismatch {
                    expected: from_ty,
                    found: to_ty,
                }),
                _ => Err(TypeError::TypeMismatch {
                    expected: Ty::Token(Box::new(amount_ty)),
                    found: from_ty,
                }),
            }
        }

        Expr::ZakatCalculate(value) => {
            let (value_ty, eff) = type_check_full(ctx, value)?;
            match value_ty {
                Ty::Int => Ok((Ty::Int, eff)),
                Ty::Token(inner) if types_compatible(&Ty::Int, inner.as_ref()) => {
                    Ok((Ty::Token(inner), eff))
                }
                found => Err(TypeError::TypeMismatch {
                    expected: Ty::Int,
                    found,
                }),
            }
        }

        // ════════════════════════════════════════════════════════════════════
        // CAHAYA Phase J5: UI Primitives
        // ════════════════════════════════════════════════════════════════════
        Expr::UIDisplay(elems) | Expr::UIRow(elems) | Expr::UIColumn(elems) => {
            let mut eff = Effect::Pure;
            for e in elems {
                let (_, e_eff) = type_check_full(ctx, e)?;
                eff = eff.join(e_eff);
            }
            Ok((Ty::Element, eff))
        }

        Expr::UIText(content, color) => {
            let (_, eff1) = type_check_full(ctx, content)?;
            let (color_ty, eff2) = type_check_full(ctx, color)?;
            if !types_compatible(&Ty::Color, &color_ty) {
                return Err(TypeError::TypeMismatch {
                    expected: Ty::Color,
                    found: color_ty,
                });
            }
            Ok((Ty::Element, eff1.join(eff2)))
        }

        Expr::UIButton(label, handler) => {
            let (_, eff1) = type_check_full(ctx, label)?;
            let (_, eff2) = type_check_full(ctx, handler)?;
            Ok((Ty::Element, eff1.join(eff2)))
        }

        Expr::UIColor(_, _, _) => Ok((Ty::Color, Effect::Pure)),

        Expr::UIStyleDecl { .. } => Ok((Ty::UIStyle, Effect::Pure)),

        Expr::UIContrastCheck(fg, bg) => {
            let (fg_ty, eff1) = type_check_full(ctx, fg)?;
            let (bg_ty, eff2) = type_check_full(ctx, bg)?;
            if !types_compatible(&Ty::Color, &fg_ty) {
                return Err(TypeError::TypeMismatch {
                    expected: Ty::Color,
                    found: fg_ty,
                });
            }
            if !types_compatible(&Ty::Color, &bg_ty) {
                return Err(TypeError::TypeMismatch {
                    expected: Ty::Color,
                    found: bg_ty,
                });
            }
            Ok((Ty::Bool, eff1.join(eff2)))
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
        // Sized integer literal `42u8` types as the distinct `Ty::IntN` (numeric tower).
        Expr::IntN { bits, signed, .. } => Ok((
            Ty::IntN {
                bits: *bits,
                signed: *signed,
            },
            Effect::Pure,
        )),
        Expr::String(_) => Ok((Ty::String, Effect::Pure)),
        // List literal `[e1, ...]` — all elements share a type; result `List<T>`.
        Expr::ListLit(elems) => {
            let mut elem_ty = Ty::Any;
            let mut eff = Effect::Pure;
            for (i, e) in elems.iter().enumerate() {
                let (t, ef) = type_check(ctx, e)?;
                eff = eff.join(ef);
                if i == 0 {
                    elem_ty = t;
                } else if elem_ty != Ty::Any && t != Ty::Any && t != elem_ty {
                    return Err(TypeError::TypeMismatch {
                        expected: elem_ty.clone(),
                        found: t,
                    });
                }
            }
            Ok((Ty::List(Box::new(elem_ty)), eff))
        }
        // Record literal / field access — structural, typed as `Any`.
        Expr::RecordLit(_name, fields) => {
            let mut eff = Effect::Pure;
            for (_f, e) in fields {
                let (_t, ef) = type_check(ctx, e)?;
                eff = eff.join(ef);
            }
            Ok((Ty::Any, eff))
        }
        Expr::FieldAccess(base, _field) => {
            let (_t, eff) = type_check(ctx, base)?;
            Ok((Ty::Any, eff))
        }
        Expr::Var(x) => {
            let ty = ctx
                .lookup(x)
                .cloned()
                .ok_or_else(|| TypeError::VarNotFound(x.clone()))?;
            Ok((ty, Effect::Pure))
        }

        // VERIFIED: Functions
        Expr::Lam(x, t1, body) => {
            let new_ctx = ctx.extend(x.clone(), t1.clone());
            let (t2, eff) = type_check(&new_ctx, body)?;
            Ok((
                Ty::Fn(Box::new(t1.clone()), Box::new(t2), eff),
                Effect::Pure,
            ))
        }
        Expr::App(e1, e2) => {
            let (t1, eff1) = type_check(ctx, e1)?;
            let (t2, eff2) = type_check(ctx, e2)?;

            match t1 {
                Ty::Fn(arg_ty, ret_ty, fn_eff) => {
                    // IFC (REQ-27): secret/labeled data may not reach a public
                    // print/network/file-write sink without declassification.
                    if let Some(err) = secrecy_at_sink(e1, &t2) {
                        return Err(err);
                    }
                    // Crypto-agility (REQ-48): reject selecting a deprecated
                    // algorithm. Coq: crypto/AlgorithmPolicy.v `accepts`.
                    if let Some(err) = deprecated_algorithm_at_selection(e1, e2) {
                        return Err(err);
                    }
                    if !types_compatible(&arg_ty, &t2) {
                        return Err(sink_argument_error(*arg_ty, t2));
                    }
                    // Effect accumulation: eff1 + eff2 + fn_eff
                    let total_eff = eff1.join(eff2).join(fn_eff);
                    // REQ-27: a pure data-transforming builtin re-carries its
                    // argument's secrecy (laundering fix — see
                    // propagate_secrecy_through_builtin).
                    let ret_ty = propagate_secrecy_through_builtin(e1, &t2, *ret_ty);
                    Ok((ret_ty, total_eff))
                }
                Ty::Any => Ok((Ty::Any, eff1.join(eff2))),
                _ => Err(TypeError::ExpectedFunction(t1)),
            }
        }

        // VERIFIED: Products
        Expr::Pair(e1, e2) => {
            let (t1, eff1) = type_check(ctx, e1)?;
            let (t2, eff2) = type_check(ctx, e2)?;
            Ok((Ty::Prod(Box::new(t1), Box::new(t2)), eff1.join(eff2)))
        }
        Expr::Fst(e) => {
            let (t, eff) = type_check(ctx, e)?;
            match t {
                Ty::Prod(t1, _) => Ok((*t1, eff)),
                Ty::Any => Ok((Ty::Any, eff)),
                _ => Err(TypeError::ExpectedProduct(t)),
            }
        }
        Expr::Snd(e) => {
            let (t, eff) = type_check(ctx, e)?;
            match t {
                Ty::Prod(_, t2) => Ok((*t2, eff)),
                Ty::Any => Ok((Ty::Any, eff)),
                _ => Err(TypeError::ExpectedProduct(t)),
            }
        }

        // VERIFIED: Sums
        Expr::Inl(e, ty) => match ty {
            Ty::Sum(t1, t2) => {
                let (te, eff) = type_check(ctx, e)?;
                if te != **t1 {
                    return Err(TypeError::TypeMismatch {
                        expected: *t1.clone(),
                        found: te,
                    });
                }
                Ok((Ty::Sum(t1.clone(), t2.clone()), eff))
            }
            Ty::Any => {
                let (te, eff) = type_check(ctx, e)?;
                Ok((Ty::Sum(Box::new(te), Box::new(Ty::Any)), eff))
            }
            _ => Err(TypeError::ExpectedSum(ty.clone())),
        },
        Expr::Inr(e, ty) => match ty {
            Ty::Sum(t1, t2) => {
                let (te, eff) = type_check(ctx, e)?;
                if te != **t2 {
                    return Err(TypeError::TypeMismatch {
                        expected: *t2.clone(),
                        found: te,
                    });
                }
                Ok((Ty::Sum(t1.clone(), t2.clone()), eff))
            }
            Ty::Any => {
                let (te, eff) = type_check(ctx, e)?;
                Ok((Ty::Sum(Box::new(Ty::Any), Box::new(te)), eff))
            }
            _ => Err(TypeError::ExpectedSum(ty.clone())),
        },
        Expr::Case(e, x, e1, y, e2) => {
            let (t, eff) = type_check(ctx, e)?;
            // Normalize Sum / Option<T> / Any to a (left, right) binder pair.
            let sum_arms: Option<(Ty, Ty)> = match &t {
                Ty::Sum(l, r) => Some(((**l).clone(), (**r).clone())),
                Ty::Option(inner) => Some(((**inner).clone(), Ty::Unit)),
                Ty::Any => Some((Ty::Any, Ty::Any)),
                _ => None,
            };
            match sum_arms {
                Some((t_left, t_right)) => {
                    let ctx1 = ctx.extend(x.clone(), t_left);
                    let (t1, eff1) = type_check(&ctx1, e1)?;

                    let ctx2 = ctx.extend(y.clone(), t_right);
                    let (t2, eff2) = type_check(&ctx2, e2)?;

                    if !types_compatible(&t1, &t2) {
                        return Err(TypeError::TypeMismatch {
                            expected: t1,
                            found: t2,
                        });
                    }
                    let result_ty = join_branch_types(t1, t2);

                    Ok((result_ty, eff.join(eff1).join(eff2)))
                }
                None => Err(TypeError::ExpectedSum(t)),
            }
        }

        // VERIFIED: Control
        Expr::If(cond, e2, e3) => {
            let (t_cond, eff1) = type_check(ctx, cond)?;
            if t_cond != Ty::Bool && t_cond != Ty::Any {
                return Err(TypeError::TypeMismatch {
                    expected: Ty::Bool,
                    found: t_cond,
                });
            }

            let (t2, eff2) = type_check(ctx, e2)?;
            let (t3, eff3) = type_check(ctx, e3)?;

            if !types_compatible(&t2, &t3) {
                return Err(TypeError::TypeMismatch {
                    expected: t2,
                    found: t3,
                });
            }
            let result_ty = join_branch_types(t2, t3);

            Ok((result_ty, eff1.join(eff2).join(eff3)))
        }
        // See `type_check_full` for the rules; this legacy path mirrors them.
        Expr::While(cond, body) => {
            let (t_cond, eff_cond) = type_check(ctx, cond)?;
            if t_cond != Ty::Bool && t_cond != Ty::Any {
                return Err(TypeError::TypeMismatch {
                    expected: Ty::Bool,
                    found: t_cond,
                });
            }
            let (_t_body, eff_body) = type_check(ctx, body)?;
            Ok((Ty::Unit, eff_cond.join(eff_body)))
        }
        Expr::Break | Expr::Continue => Ok((Ty::Any, Effect::Pure)),
        Expr::LetMut(x, e1, e2) => {
            let (t1, eff1) = type_check(ctx, e1)?;
            let ctx_new = ctx.extend(x.clone(), Ty::Ref(Box::new(t1), SecurityLevel::Public));
            let (t2, eff2) = type_check(&ctx_new, e2)?;
            Ok((t2, eff1.join(eff2)))
        }
        Expr::SlotGet(x) => {
            let ty = ctx
                .lookup(x)
                .cloned()
                .ok_or_else(|| TypeError::VarNotFound(x.clone()))?;
            match ty {
                Ty::Ref(inner, _) => Ok((*inner, Effect::Pure)),
                other => Ok((other, Effect::Pure)),
            }
        }
        Expr::SlotSet(_x, e) => {
            let (_t, eff) = type_check(ctx, e)?;
            Ok((Ty::Unit, eff))
        }
        Expr::Let(x, _, e1, e2) => {
            let (t1, eff1) = type_check(ctx, e1)?;
            let ctx_new = ctx.extend(x.clone(), t1);
            let (t2, eff2) = type_check(&ctx_new, e2)?;
            Ok((t2, eff1.join(eff2)))
        }
        // `pulang e` — early return; type `Any` (see type_check_full).
        Expr::Return(e) => {
            let (_t, eff) = type_check(ctx, e)?;
            Ok((Ty::Any, eff))
        }
        Expr::LetRec(x, ty_ann, e1, e2) => {
            // Typecheck binding with name already in scope (for recursion)
            let ctx_rec = ctx.extend(x.clone(), ty_ann.clone());
            let (t1, eff1) = type_check(&ctx_rec, e1)?;
            // Check that binding type is compatible with annotation
            if !types_compatible(ty_ann, &t1) {
                return Err(TypeError::AnnotationMismatch {
                    expected: ty_ann.clone(),
                    found: t1,
                });
            }
            let (t2, eff2) = type_check(&ctx_rec, e2)?;
            Ok((t2, eff1.join(eff2)))
        }

        // Mutually-recursive group (REQ-44) — plain checker path.
        Expr::LetRecGroup(bindings, cont) => {
            let mut ctx_rec = ctx.clone();
            for (name, ty_ann, _) in bindings {
                ctx_rec = ctx_rec.extend(name.clone(), ty_ann.clone());
            }
            let mut eff = Effect::Pure;
            for (_, ty_ann, e1) in bindings {
                let (t1, eff1) = type_check(&ctx_rec, e1)?;
                if !types_compatible(ty_ann, &t1) {
                    return Err(TypeError::AnnotationMismatch {
                        expected: ty_ann.clone(),
                        found: t1,
                    });
                }
                eff = eff.join(eff1);
            }
            let (t2, eff2) = type_check(&ctx_rec, cont)?;
            Ok((t2, eff.join(eff2)))
        }

        // UNVERIFIED: Effects (Pending formalization in Typing.v)
        Expr::Perform(eff, e) => {
            let (te, eff_e) = type_check(ctx, e)?;
            // Matches Coq T_Perform (Typing.v:168): `e : T ! ε  ⊢  perform eff e : T ! (ε ⊔ eff)`.
            // The payload type passes through unchanged and the performed effect is
            // joined. RIINA's effect model has no per-effect payload *signature*
            // (T_Perform takes no signature premise), so there is deliberately no
            // payload-vs-signature validation here — adding one would be a Rust rule
            // with no Coq counterpart, violating Gate B enforcement parity. (The
            // `type_check_full` Perform arm is identical.)
            Ok((te, eff_e.join(*eff)))
        }
        Expr::Handle(e, x, h) => {
            let (t_e, eff_e) = type_check(ctx, e)?;
            // Coq T_Handle: handler binds x : T in h, result effect is join
            let h_ctx = ctx.extend(x.clone(), t_e);
            let (t_h, eff_h) = type_check(&h_ctx, h)?;
            Ok((t_h, eff_e.join(eff_h)))
        }

        // UNVERIFIED: References (Pending formalization in Typing.v)
        Expr::Ref(e, l) => {
            let (t, eff) = type_check(ctx, e)?;
            Ok((Ty::Ref(Box::new(t), *l), eff.join(Effect::Write))) // Allocation is a write-like effect?
        }
        Expr::Deref(e) => {
            let (t, eff) = type_check(ctx, e)?;
            match t {
                Ty::Ref(inner, _l) => Ok((*inner, eff.join(Effect::Read))),
                // `!` as logical negation on Bool/Any (see type_check_full).
                Ty::Bool => Ok((Ty::Bool, eff)),
                Ty::Any => Ok((Ty::Any, eff)),
                _ => Err(TypeError::ExpectedRef(t)),
            }
        }
        Expr::Assign(e1, e2) => {
            let (t1, eff1) = type_check(ctx, e1)?;
            let (t2, eff2) = type_check(ctx, e2)?;
            match t1 {
                Ty::Ref(inner, _l) => {
                    if *inner != t2 {
                        return Err(TypeError::TypeMismatch {
                            expected: *inner,
                            found: t2,
                        });
                    }
                    Ok((Ty::Unit, eff1.join(eff2).join(Effect::Write)))
                }
                _ => Err(TypeError::ExpectedRef(t1)),
            }
        }

        // UNVERIFIED: Security (Pending formalization in Typing.v)
        Expr::Classify(e) => {
            let (t, eff) = type_check(ctx, e)?;
            Ok((Ty::Secret(Box::new(t)), eff))
        }
        Expr::Declassify(e, _proof) => {
            let (t, eff) = type_check(ctx, e)?;
            match t {
                Ty::Secret(inner) => Ok((*inner, eff)),
                // Assuming we can define what a "proof" is later.
                _ => Err(TypeError::ExpectedSecret(t)), // Matches Coq T_Declassify: requires TSecret(T)
            }
        }
        Expr::Prove(e) => {
            let (t, eff) = type_check(ctx, e)?;
            Ok((Ty::Proof(Box::new(t)), eff))
        }

        // UNVERIFIED: Capabilities
        Expr::Require(eff, e) => {
            let (t, e_eff) = type_check(ctx, e)?;
            Ok((t, e_eff.join(*eff)))
        }
        Expr::Grant(_eff, e) => {
            // Grant satisfies a requirement?
            let (t, e_eff) = type_check(ctx, e)?;
            Ok((t, e_eff)) // Does it remove the effect from the context?
        }

        // Locations (runtime-only — corresponds to Coq ELoc)
        Expr::Loc(_) => {
            // Store locations are runtime values; typing requires store typing context.
            // Without store context, we return Ref(Unit, Public) as a conservative type.
            Ok((
                Ty::Ref(Box::new(Ty::Unit), SecurityLevel::Public),
                Effect::Pure,
            ))
        }

        // FFI call
        Expr::FFICall {
            name: _,
            args,
            ret_ty,
        } => {
            let mut eff = Effect::System; // FFI is always effectful
            for arg in args {
                let (_t, e) = type_check(ctx, arg)?;
                eff = eff.join(e);
            }
            Ok((ret_ty.clone(), eff))
        }

        // Binary operations
        Expr::BinOp(op, e1, e2) => {
            let (t1, eff1) = type_check(ctx, e1)?;
            let (t2, eff2) = type_check(ctx, e2)?;
            let eff = eff1.join(eff2);
            match op {
                BinOp::Add => {
                    if t1 == Ty::Any || t2 == Ty::Any {
                        Ok((Ty::Any, eff))
                    } else if t1 == Ty::String && t2 == Ty::String {
                        Ok((Ty::String, eff))
                    } else if t1 == Ty::Int && t2 == Ty::Int {
                        Ok((Ty::Int, eff))
                    } else {
                        Err(TypeError::TypeMismatch {
                            expected: t1,
                            found: t2,
                        })
                    }
                }
                BinOp::Sub | BinOp::Mul | BinOp::Div | BinOp::Mod => {
                    if t1 != Ty::Int && t1 != Ty::Any {
                        return Err(TypeError::TypeMismatch {
                            expected: Ty::Int,
                            found: t1,
                        });
                    }
                    if t2 != Ty::Int && t2 != Ty::Any {
                        return Err(TypeError::TypeMismatch {
                            expected: Ty::Int,
                            found: t2,
                        });
                    }
                    Ok((Ty::Int, eff))
                }
                BinOp::Eq | BinOp::Ne => {
                    // Eq/Ne work on Int, Bool, and String
                    if t1 != t2 {
                        return Err(TypeError::TypeMismatch {
                            expected: t1,
                            found: t2,
                        });
                    }
                    if t1 != Ty::Int && t1 != Ty::Bool && t1 != Ty::String {
                        return Err(TypeError::TypeMismatch {
                            expected: Ty::Int,
                            found: t1,
                        });
                    }
                    Ok((Ty::Bool, eff))
                }
                BinOp::Lt | BinOp::Le | BinOp::Gt | BinOp::Ge => {
                    if t1 != Ty::Int {
                        return Err(TypeError::TypeMismatch {
                            expected: Ty::Int,
                            found: t1,
                        });
                    }
                    if t2 != Ty::Int {
                        return Err(TypeError::TypeMismatch {
                            expected: Ty::Int,
                            found: t2,
                        });
                    }
                    Ok((Ty::Bool, eff))
                }
                BinOp::And | BinOp::Or => {
                    if t1 != Ty::Bool {
                        return Err(TypeError::TypeMismatch {
                            expected: Ty::Bool,
                            found: t1,
                        });
                    }
                    if t2 != Ty::Bool {
                        return Err(TypeError::TypeMismatch {
                            expected: Ty::Bool,
                            found: t2,
                        });
                    }
                    Ok((Ty::Bool, eff))
                }
            }
        }

        // ════════════════════════════════════════════════════════════════════
        // JALINAN Phase 6: Session Types, Actors, Choreography, CRDTs
        // ════════════════════════════════════════════════════════════════════
        Expr::ActorDecl {
            name: _,
            state_ty,
            message_ty,
            init_state,
            handler,
        } => {
            let (init_ty, eff1) = type_check(ctx, init_state)?;
            if !types_compatible(state_ty, &init_ty) {
                return Err(TypeError::TypeMismatch {
                    expected: state_ty.clone(),
                    found: init_ty,
                });
            }
            let (handler_ty, eff2) = type_check(ctx, handler)?;
            match &handler_ty {
                Ty::Fn(arg, ret, _) => {
                    if !types_compatible(message_ty, arg) {
                        return Err(TypeError::TypeMismatch {
                            expected: message_ty.clone(),
                            found: *arg.clone(),
                        });
                    }
                    if !types_compatible(state_ty, ret) {
                        return Err(TypeError::TypeMismatch {
                            expected: state_ty.clone(),
                            found: *ret.clone(),
                        });
                    }
                }
                _ => return Err(TypeError::ExpectedFunction(handler_ty)),
            }
            Ok((
                Ty::Actor(Box::new(state_ty.clone()), Box::new(message_ty.clone())),
                eff1.join(eff2),
            ))
        }

        Expr::ChoreographyBlock {
            name: _,
            roles,
            protocol,
        } => {
            // Parse → project → check: the protocol must be closed, its roles
            // distinct, and (for the two-party case) its per-role projections
            // dual. This wires the projection pipeline into typechecking.
            if let Err(reason) = choreography_compatible(roles, protocol) {
                return Err(TypeError::ChoreographyError {
                    message: format!("ill-formed choreography: {reason}"),
                });
            }
            Ok((
                Ty::Choreography(roles.clone(), protocol.clone()),
                Effect::Pure,
            ))
        }

        Expr::Spawn(actor_expr, init_state_expr) => {
            let (actor_ty, eff1) = type_check(ctx, actor_expr)?;
            let (init_ty, eff2) = type_check(ctx, init_state_expr)?;
            match &actor_ty {
                Ty::Actor(state_ty, msg_ty) => {
                    if !types_compatible(state_ty, &init_ty) {
                        return Err(TypeError::TypeMismatch {
                            expected: *state_ty.clone(),
                            found: init_ty,
                        });
                    }
                    Ok((
                        Ty::Actor(state_ty.clone(), msg_ty.clone()),
                        eff1.join(eff2).join(Effect::Process),
                    ))
                }
                _ => Err(TypeError::ExpectedActor(actor_ty)),
            }
        }

        Expr::ActorSend(actor_expr, msg_expr) => {
            let (actor_ty, eff1) = type_check(ctx, actor_expr)?;
            let (msg_ty, eff2) = type_check(ctx, msg_expr)?;
            match &actor_ty {
                Ty::Actor(_, expected_msg) => {
                    if !types_compatible(expected_msg, &msg_ty) {
                        return Err(TypeError::TypeMismatch {
                            expected: *expected_msg.clone(),
                            found: msg_ty,
                        });
                    }
                    Ok((Ty::Unit, eff1.join(eff2).join(Effect::Network)))
                }
                _ => Err(TypeError::ExpectedActor(actor_ty)),
            }
        }

        Expr::ActorRecv(actor_expr) => {
            let (actor_ty, eff) = type_check(ctx, actor_expr)?;
            match &actor_ty {
                Ty::Actor(_, msg_ty) => Ok((*msg_ty.clone(), eff.join(Effect::Network))),
                _ => Err(TypeError::ExpectedActor(actor_ty)),
            }
        }

        Expr::CRDTMerge(left, right) => {
            let (left_ty, eff1) = type_check(ctx, left)?;
            let (right_ty, eff2) = type_check(ctx, right)?;
            match (&left_ty, &right_ty) {
                (Ty::CRDT(t1, op1), Ty::CRDT(t2, op2)) => {
                    if !types_compatible(t1, t2) || !types_compatible(op1, op2) {
                        return Err(TypeError::CRDTMismatch {
                            left: left_ty,
                            right: right_ty,
                        });
                    }
                    Ok((Ty::CRDT(t1.clone(), op1.clone()), eff1.join(eff2)))
                }
                (Ty::CRDT(_, _), _) => Err(TypeError::ExpectedCRDT(right_ty)),
                _ => Err(TypeError::ExpectedCRDT(left_ty)),
            }
        }

        Expr::ContentHash(expr) => {
            let (inner_ty, eff) = type_check(ctx, expr)?;
            Ok((
                Ty::ContentAddressed(Box::new(inner_ty)),
                eff.join(Effect::Crypto),
            ))
        }

        Expr::ContentVerify(expected_hash, value) => {
            let (expected_ty, eff1) = type_check(ctx, expected_hash)?;
            let (value_ty, eff2) = type_check(ctx, value)?;
            let expected = Ty::ContentAddressed(Box::new(value_ty.clone()));
            match expected_ty {
                Ty::ContentAddressed(inner_ty) => {
                    if !types_compatible(&inner_ty, &value_ty) {
                        return Err(TypeError::TypeMismatch {
                            expected,
                            found: Ty::ContentAddressed(inner_ty),
                        });
                    }
                    Ok((Ty::Bool, eff1.join(eff2).join(Effect::Crypto)))
                }
                found => Err(TypeError::TypeMismatch { expected, found }),
            }
        }

        Expr::ContractDeploy(contract) => {
            let (inner_ty, eff) = type_check(ctx, contract)?;
            Ok((
                Ty::SmartContract(Box::new(inner_ty)),
                eff.join(Effect::NetworkSecure),
            ))
        }

        Expr::TokenTransfer { from, to, amount } => {
            let (from_ty, eff1) = type_check(ctx, from)?;
            let (to_ty, eff2) = type_check(ctx, to)?;
            let (amount_ty, eff3) = type_check(ctx, amount)?;
            match (&from_ty, &to_ty) {
                (Ty::Token(from_inner), Ty::Token(to_inner)) => {
                    if !types_compatible(from_inner, to_inner) {
                        return Err(TypeError::TypeMismatch {
                            expected: Ty::Token(from_inner.clone()),
                            found: to_ty,
                        });
                    }
                    if !types_compatible(from_inner, &amount_ty) {
                        return Err(TypeError::TypeMismatch {
                            expected: *from_inner.clone(),
                            found: amount_ty,
                        });
                    }
                    Ok((
                        Ty::Token(from_inner.clone()),
                        eff1.join(eff2).join(eff3).join(Effect::NetworkSecure),
                    ))
                }
                (Ty::Token(_), _) => Err(TypeError::TypeMismatch {
                    expected: from_ty,
                    found: to_ty,
                }),
                _ => Err(TypeError::TypeMismatch {
                    expected: Ty::Token(Box::new(amount_ty)),
                    found: from_ty,
                }),
            }
        }

        Expr::ZakatCalculate(value) => {
            let (value_ty, eff) = type_check(ctx, value)?;
            match value_ty {
                Ty::Int => Ok((Ty::Int, eff)),
                Ty::Token(inner) if types_compatible(&Ty::Int, inner.as_ref()) => {
                    Ok((Ty::Token(inner), eff))
                }
                found => Err(TypeError::TypeMismatch {
                    expected: Ty::Int,
                    found,
                }),
            }
        }

        // CAHAYA Phase J5: UI Primitives
        Expr::UIDisplay(elems) | Expr::UIRow(elems) | Expr::UIColumn(elems) => {
            let mut eff = Effect::Pure;
            for e in elems {
                let (_, e_eff) = type_check(ctx, e)?;
                eff = eff.join(e_eff);
            }
            Ok((Ty::Element, eff))
        }

        Expr::UIText(content, color) => {
            let (_, eff1) = type_check(ctx, content)?;
            let (color_ty, eff2) = type_check(ctx, color)?;
            if !types_compatible(&Ty::Color, &color_ty) {
                return Err(TypeError::TypeMismatch {
                    expected: Ty::Color,
                    found: color_ty,
                });
            }
            Ok((Ty::Element, eff1.join(eff2)))
        }

        Expr::UIButton(label, handler) => {
            let (_, eff1) = type_check(ctx, label)?;
            let (_, eff2) = type_check(ctx, handler)?;
            Ok((Ty::Element, eff1.join(eff2)))
        }

        Expr::UIColor(_, _, _) => Ok((Ty::Color, Effect::Pure)),

        Expr::UIStyleDecl { .. } => Ok((Ty::UIStyle, Effect::Pure)),

        Expr::UIContrastCheck(fg, bg) => {
            let (fg_ty, eff1) = type_check(ctx, fg)?;
            let (bg_ty, eff2) = type_check(ctx, bg)?;
            if !types_compatible(&Ty::Color, &fg_ty) {
                return Err(TypeError::TypeMismatch {
                    expected: Ty::Color,
                    found: fg_ty,
                });
            }
            if !types_compatible(&Ty::Color, &bg_ty) {
                return Err(TypeError::TypeMismatch {
                    expected: Ty::Color,
                    found: bg_ty,
                });
            }
            Ok((Ty::Bool, eff1.join(eff2)))
        }
    }
}

#[cfg(test)]
mod tests;
