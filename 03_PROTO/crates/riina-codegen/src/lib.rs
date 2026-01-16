//! RIINA Code Generator
//!
//! Translates typed RIINA AST to executable representation, maintaining
//! formal correspondence with the Coq specification in `02_FORMAL/coq/`.
//!
//! # Architecture
//!
//! The code generator uses a multi-phase architecture:
//!
//! ```text
//! ┌─────────────────────────────────────────────────────────────────────┐
//! │                     RIINA Code Generator                            │
//! │                                                                     │
//! │   Expr (AST)                                                        │
//! │       │                                                             │
//! │       ▼                                                             │
//! │   ┌────────────────────┐                                           │
//! │   │   lower::Lower     │  AST → IR translation                     │
//! │   │   (25 expr forms)  │  Type-directed, preserves semantics       │
//! │   └────────────────────┘                                           │
//! │       │                                                             │
//! │       ▼                                                             │
//! │   ┌────────────────────┐                                           │
//! │   │   ir::Program      │  SSA-form intermediate representation     │
//! │   │   (basic blocks,   │  Explicit control flow, security labels   │
//! │   │    instructions)   │  Effect annotations preserved             │
//! │   └────────────────────┘                                           │
//! │       │                                                             │
//! │       ├─────────────────────────┐                                   │
//! │       ▼                         ▼                                   │
//! │   ┌────────────────┐    ┌────────────────┐                         │
//! │   │ interp::Interp │    │  emit::Emit    │                         │
//! │   │ (reference)    │    │  (C backend)   │                         │
//! │   └────────────────┘    └────────────────┘                         │
//! │       │                         │                                   │
//! │       ▼                         ▼                                   │
//! │   value::Value              C source code                          │
//! │   (runtime result)          (portable output)                      │
//! │                                                                     │
//! └─────────────────────────────────────────────────────────────────────┘
//! ```
//!
//! # Correspondence with Coq
//!
//! Each translation rule corresponds to a lemma in `02_FORMAL/coq/`:
//!
//! | Rust Module | Coq File | Preservation Property |
//! |-------------|----------|----------------------|
//! | `lower`     | `properties/Compilation.v` | Type preservation |
//! | `interp`    | `foundations/Semantics.v`  | Semantic equivalence |
//! | `ir`        | `foundations/IR.v`         | IR well-formedness |
//!
//! # Mode: ULTRA KIASU | FUCKING PARANOID | ZERO TRUST
//!
//! Every translation is:
//! - **Total**: All 25 expression forms handled exhaustively
//! - **Correct**: Corresponds to Coq small-step semantics
//! - **Secure**: Security labels preserved through translation
//! - **Traced**: Effect annotations maintained for verification
//!
//! RIINA = Rigorous Immutable Integrity No-attack Assured
//! Named for: Reena + Isaac + Imaan
//!
//! "Security proven. Family driven."

#![forbid(unsafe_code)]
#![warn(clippy::all)]

pub mod ir;
pub mod value;
pub mod lower;
pub mod interp;

#[cfg(feature = "c-emit")]
pub mod emit;

// Re-export primary interface
pub use ir::{Instruction, BasicBlock, Function, Program};
pub use value::Value;
pub use lower::Lower;
pub use interp::Interpreter;

/// Result type for code generation operations
pub type Result<T> = std::result::Result<T, Error>;

/// Code generation error
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Error {
    /// Variable not found in scope
    UnboundVariable(String),
    /// Type mismatch during lowering
    TypeMismatch {
        expected: String,
        found: String,
        context: String,
    },
    /// Effect violation detected
    EffectViolation {
        allowed: riina_types::Effect,
        found: riina_types::Effect,
    },
    /// Security label violation
    SecurityViolation {
        context_level: riina_types::SecurityLevel,
        data_level: riina_types::SecurityLevel,
    },
    /// Invalid operation
    InvalidOperation(String),
    /// Division by zero
    DivisionByZero,
    /// Reference error
    InvalidReference(String),
    /// Effect not handled
    UnhandledEffect(riina_types::Effect),
    /// Capability not held
    MissingCapability(riina_types::Effect),
}

impl std::fmt::Display for Error {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::UnboundVariable(name) => write!(f, "unbound variable: {name}"),
            Self::TypeMismatch { expected, found, context } => {
                write!(f, "type mismatch in {context}: expected {expected}, found {found}")
            }
            Self::EffectViolation { allowed, found } => {
                write!(f, "effect violation: allowed {allowed:?}, found {found:?}")
            }
            Self::SecurityViolation { context_level, data_level } => {
                write!(f, "security violation: context {context_level:?}, data {data_level:?}")
            }
            Self::InvalidOperation(msg) => write!(f, "invalid operation: {msg}"),
            Self::DivisionByZero => write!(f, "division by zero"),
            Self::InvalidReference(msg) => write!(f, "invalid reference: {msg}"),
            Self::UnhandledEffect(eff) => write!(f, "unhandled effect: {eff:?}"),
            Self::MissingCapability(eff) => write!(f, "missing capability for effect: {eff:?}"),
        }
    }
}

impl std::error::Error for Error {}

/// Compile an expression to a value using the reference interpreter
///
/// This is the primary entry point for executing RIINA programs.
/// Uses the reference interpreter which corresponds exactly to
/// the Coq operational semantics.
///
/// # Arguments
///
/// * `expr` - The typed RIINA expression to execute
///
/// # Returns
///
/// * `Ok(Value)` - The computed value
/// * `Err(Error)` - Compilation or runtime error
///
/// # Correspondence
///
/// This function implements the `eval` relation from
/// `02_FORMAL/coq/foundations/Semantics.v`:
///
/// ```text
/// Lemma eval_deterministic : forall e v1 v2,
///   eval e v1 -> eval e v2 -> v1 = v2.
/// ```
pub fn eval(expr: &riina_types::Expr) -> Result<Value> {
    let mut interp = Interpreter::new();
    interp.eval(expr)
}

/// Compile an expression to IR
///
/// Translates the AST to SSA-form intermediate representation.
/// This IR can be further processed by backends (interpreter, C emission).
///
/// # Arguments
///
/// * `expr` - The RIINA expression to compile
///
/// # Returns
///
/// * `Ok(Program)` - The compiled IR program
/// * `Err(Error)` - Compilation error
pub fn compile(expr: &riina_types::Expr) -> Result<Program> {
    let mut lower = Lower::new();
    lower.compile(expr)
}

#[cfg(test)]
mod tests {
    use super::*;
    use riina_types::Expr;

    #[test]
    fn test_eval_unit() {
        let result = eval(&Expr::Unit);
        assert_eq!(result, Ok(Value::Unit));
    }

    #[test]
    fn test_eval_bool_true() {
        let result = eval(&Expr::Bool(true));
        assert_eq!(result, Ok(Value::Bool(true)));
    }

    #[test]
    fn test_eval_bool_false() {
        let result = eval(&Expr::Bool(false));
        assert_eq!(result, Ok(Value::Bool(false)));
    }

    #[test]
    fn test_eval_int() {
        let result = eval(&Expr::Int(42));
        assert_eq!(result, Ok(Value::Int(42)));
    }

    #[test]
    fn test_eval_string() {
        let result = eval(&Expr::String("hello".to_string()));
        assert_eq!(result, Ok(Value::String("hello".to_string())));
    }
}
