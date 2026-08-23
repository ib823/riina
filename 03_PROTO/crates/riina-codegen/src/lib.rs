// Copyright (c) 2026 The RIINA Authors. All rights reserved.

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
//! RIINA = Rigorous Immutable Invariant, No Assumptions
//!
//! "QED Eternum."

#![forbid(unsafe_code)]
#![warn(clippy::all)]

pub mod android_build;
pub mod backend;
pub mod bigint;
pub mod builtins;
pub mod decimal;
pub mod ct_verify;
pub mod fixed;
pub mod fixed_bin;
pub mod emit;
pub mod ffi;
pub mod interp;
pub mod ios_build;
pub mod ir;
pub mod jni;
pub mod lower;
pub mod mobile;
pub mod platform;
pub mod swift_bridge;
pub mod toolchain;
pub mod unicode_confusables;
pub mod unicode_confusables_data;
pub mod unicode_nfc;
pub mod unicode_nfc_data;
pub mod value;
pub mod wasm;
pub mod wasm_encode;

// Re-export primary interface
pub use backend::{backend_for_target, Backend, BackendOutput, Target};
pub use emit::{emit_c, CEmitter};
pub use interp::Interpreter;
pub use ir::{BasicBlock, Function, Instruction, Program};
pub use lower::Lower;

/// Builtins the **WASM** backend actually implements (canonical names).
///
/// The WASM emitter dispatches on these names; anything else now fails closed
/// (REQ-78) instead of emitting a silent stub. Kept as an explicit list so the
/// generated `docs/api/STDLIB.md` can tell `native-only` from `compiled`
/// rather than claiming every C-compiled builtin also runs on WASM — it does
/// not, and it used to say so.
///
/// Correspondence with the emitter is pinned behaviourally by
/// `wasm_supported_builtins_all_compile` in `riina-codegen`'s tests.
pub const WASM_SUPPORTED_BUILTINS: &[&str] = &[
    "cetak",
    "cetakln",
    "ke_teks",
    "nombor_ke_teks",
    "gabung_teks",
    "besar",
    "perpuluhan",
    "wang",
    "titik_tetap",
    "qmn",
];

/// Does the **WASM** backend implement this builtin?
///
/// `false` while [`codegen_supports_builtin`] is `true` means **native-only**:
/// `riinac build` works, `riinac build --target wasm32/wasm64` fails closed.
/// Accepts either surface spelling.
#[must_use]
pub fn wasm_supports_builtin(name: &str) -> bool {
    lower::builtin_canonical(name).is_some_and(|c| WASM_SUPPORTED_BUILTINS.contains(&c))
}

/// Does the compiled-backend pipeline (C / WASM) implement this builtin?
///
/// `false` means **interpreter-only**: the typechecker accepts the call and
/// `riinac run` executes it, but `riinac build` / `emit-c` / `--target wasm*`
/// fail closed with `unbound variable: <name>` — lowering never binds it.
///
/// `true` means the C backend implements it. It does NOT imply WASM does —
/// ask [`wasm_supports_builtin`] for that (REQ-78). The
/// gap is invisible in a type signature, which is why `docs/api/STDLIB.md`
/// renders a Backend column generated from this function (master plan REQ-70).
///
/// Accepts either surface spelling (Bahasa Melayu or English), e.g. both
/// `gabung_teks` and `concat`.
pub fn codegen_supports_builtin(name: &str) -> bool {
    lower::builtin_canonical(name).is_some()
}
pub use value::Value;

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
    /// The lowered IR violates the constant-time discipline (a secret-dependent
    /// branch, or a variable-time operation on a `ConstantTime` value). Carries
    /// the human-readable description of each violation found.
    ConstantTimeViolation(Vec<String>),
    /// Non-error control-flow signal: an early `pulang` (return) is unwinding to
    /// the nearest enclosing function-application boundary, carrying its value.
    /// This is never surfaced to the user — it is always caught when a closure
    /// body is evaluated (see the interpreter's `App` rule). A `pulang` at top
    /// level (outside any function) is caught by the top-level `eval` entry.
    /// Boxed to keep `Error` small (it is the only otherwise-large variant).
    Return(Box<Value>),
    /// Non-error control-flow signal: `putus` (break) is unwinding to the
    /// innermost enclosing loop, which discards it and stops iterating. Never
    /// surfaced to the user — the parser rejects `putus` outside a loop, and the
    /// interpreter's `While` rule always catches it.
    Break,
    /// Non-error control-flow signal: `lanjut` (continue) is unwinding to the
    /// innermost enclosing loop, which discards it and starts the next
    /// iteration. Caught exactly like [`Error::Break`].
    Continue,
}

impl std::fmt::Display for Error {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::UnboundVariable(name) => write!(f, "unbound variable: {name}"),
            Self::TypeMismatch {
                expected,
                found,
                context,
            } => {
                write!(
                    f,
                    "type mismatch in {context}: expected {expected}, found {found}"
                )
            }
            Self::EffectViolation { allowed, found } => {
                write!(f, "effect violation: allowed {allowed:?}, found {found:?}")
            }
            Self::SecurityViolation {
                context_level,
                data_level,
            } => {
                write!(
                    f,
                    "security violation: context {context_level:?}, data {data_level:?}"
                )
            }
            Self::InvalidOperation(msg) => write!(f, "invalid operation: {msg}"),
            Self::DivisionByZero => write!(f, "division by zero"),
            Self::InvalidReference(msg) => write!(f, "invalid reference: {msg}"),
            Self::UnhandledEffect(eff) => write!(f, "unhandled effect: {eff:?}"),
            Self::MissingCapability(eff) => write!(f, "missing capability for effect: {eff:?}"),
            Self::ConstantTimeViolation(msgs) => {
                write!(f, "constant-time violation(s): {}", msgs.join("; "))
            }
            Self::Return(_) => write!(f, "internal: uncaught early-return signal"),
            Self::Break => write!(f, "internal: uncaught `putus` signal"),
            Self::Continue => write!(f, "internal: uncaught `lanjut` signal"),
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

/// Evaluate with built-in functions (cetak, panjang, etc.) pre-registered.
pub fn eval_with_builtins(expr: &riina_types::Expr) -> Result<Value> {
    let mut interp = Interpreter::new();
    interp.eval_with_builtins(expr)
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
    let program = lower.compile(expr)?;
    // Per-program constant-time gate over the lowered IR: independently certify
    // that the artifact has no secret-dependent branch or variable-time operation
    // on a `ConstantTime` value (defense-in-depth behind the source-level A2
    // typecheck). Valid programs — including constant-time ones with no such
    // hazard — pass unchanged.
    if let Err(violations) = crate::ct_verify::verify_constant_time(&program) {
        return Err(Error::ConstantTimeViolation(
            violations
                .iter()
                .map(crate::ct_verify::CtViolation::message)
                .collect(),
        ));
    }
    Ok(program)
}

/// Compile an expression to C source code
///
/// Complete pipeline from AST to portable C99 code.
/// The generated C code can be compiled with any C99 compiler.
///
/// # Arguments
///
/// * `expr` - The RIINA expression to compile
///
/// # Returns
///
/// * `Ok(String)` - The generated C source code
/// * `Err(Error)` - Compilation error
///
/// # Example
///
/// ```
/// use riina_types::Expr;
/// let expr = Expr::Int(42);
/// let c_code = riina_codegen::compile_to_c(&expr).unwrap();
/// assert!(c_code.contains("42"));
/// ```
pub fn compile_to_c(expr: &riina_types::Expr) -> Result<String> {
    let program = compile(expr)?;
    emit_c(&program)
}

#[cfg(test)]
mod tests {
    use super::*;
    use riina_types::{Expr, Ty};

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

    // ==================== Integration Tests ====================

    /// Test end-to-end: eval produces expected result
    #[test]
    fn test_integration_eval_identity() {
        // Test using identity function: (λx:Int. x) 42
        let expr = Expr::App(
            Box::new(Expr::Lam(
                "x".to_string(),
                Ty::Int,
                Box::new(Expr::Var("x".to_string())),
            )),
            Box::new(Expr::Int(42)),
        );

        // Direct eval
        let eval_result = eval(&expr).unwrap();
        assert_eq!(eval_result, Value::Int(42));

        // Verify IR compilation also works
        let program = compile(&expr).unwrap();
        assert!(!program.functions.is_empty());
    }

    /// Test full pipeline: AST -> IR -> C code produces valid output
    #[test]
    fn test_integration_full_pipeline_to_c() {
        let expr = Expr::Pair(Box::new(Expr::Int(1)), Box::new(Expr::Bool(true)));

        let c_code = compile_to_c(&expr).unwrap();

        // Verify C code structure
        assert!(c_code.contains("#include"));
        assert!(c_code.contains("riina_pair"));
        assert!(c_code.contains("main"));
    }

    /// Test error propagation through the pipeline
    #[test]
    fn test_integration_unbound_variable_error() {
        let expr = Expr::Var("undefined_var".to_string());

        let result = eval(&expr);

        assert!(matches!(result, Err(Error::UnboundVariable(name)) if name == "undefined_var"));
    }

    /// Test error display formatting
    #[test]
    fn test_error_display_formatting() {
        let errors = vec![
            Error::UnboundVariable("x".to_string()),
            Error::TypeMismatch {
                expected: "Int".to_string(),
                found: "Bool".to_string(),
                context: "addition".to_string(),
            },
            Error::DivisionByZero,
            Error::InvalidOperation("test op".to_string()),
            Error::InvalidReference("ref error".to_string()),
        ];

        for error in errors {
            let display = format!("{}", error);
            assert!(!display.is_empty());
            // Verify Error trait is implemented
            let _: &dyn std::error::Error = &error;
        }
    }

    /// Test complex nested expression through full pipeline
    #[test]
    fn test_integration_nested_let_bindings() {
        // let x = 10 in let y = 20 in (x, y)
        let expr = Expr::Let(
            "x".to_string(),
            None,
            Box::new(Expr::Int(10)),
            Box::new(Expr::Let(
                "y".to_string(),
                None,
                Box::new(Expr::Int(20)),
                Box::new(Expr::Pair(
                    Box::new(Expr::Var("x".to_string())),
                    Box::new(Expr::Var("y".to_string())),
                )),
            )),
        );

        let result = eval(&expr).unwrap();
        // Result should be a pair (10, 20)
        assert!(matches!(result, Value::Pair(_, _)));

        // Also verify compile and C emission work
        let program = compile(&expr).unwrap();
        assert!(!program.functions.is_empty());

        let c_code = compile_to_c(&expr).unwrap();
        assert!(c_code.contains("riina_pair"));
    }

    /// Test lambda and application through pipeline
    #[test]
    fn test_integration_lambda_application() {
        // (λx:Int. x) 42
        let expr = Expr::App(
            Box::new(Expr::Lam(
                "x".to_string(),
                Ty::Int,
                Box::new(Expr::Var("x".to_string())),
            )),
            Box::new(Expr::Int(42)),
        );

        let result = eval(&expr).unwrap();
        assert_eq!(result, Value::Int(42));
    }

    /// Test conditional branching through pipeline
    #[test]
    fn test_integration_conditional_true_branch() {
        // if true then 1 else 2
        let expr = Expr::If(
            Box::new(Expr::Bool(true)),
            Box::new(Expr::Int(1)),
            Box::new(Expr::Int(2)),
        );

        let result = eval(&expr).unwrap();
        assert_eq!(result, Value::Int(1));

        // Verify IR generation handles branches
        let program = compile(&expr).unwrap();
        let main = program.function(ir::FuncId::MAIN).unwrap();
        // Should have multiple blocks for branching
        assert!(!main.blocks.is_empty());
    }

    /// Test conditional branching false branch
    #[test]
    fn test_integration_conditional_false_branch() {
        // if false then 1 else 2
        let expr = Expr::If(
            Box::new(Expr::Bool(false)),
            Box::new(Expr::Int(1)),
            Box::new(Expr::Int(2)),
        );

        let result = eval(&expr).unwrap();
        assert_eq!(result, Value::Int(2));
    }

    /// Test sum types through full pipeline
    #[test]
    fn test_integration_sum_type_inl() {
        // inl 42
        let expr = Expr::Inl(
            Box::new(Expr::Int(42)),
            Ty::Int, // right type placeholder
        );

        let result = eval(&expr).unwrap();
        assert!(result.is_left());

        if let Some(inner) = result.as_left() {
            assert_eq!(*inner, Value::Int(42));
        }
    }

    /// Test pair projection through pipeline
    #[test]
    fn test_integration_pair_projections() {
        // fst (1, 2)
        let pair = Expr::Pair(Box::new(Expr::Int(1)), Box::new(Expr::Int(2)));

        let fst_result = eval(&Expr::Fst(Box::new(pair.clone()))).unwrap();
        let snd_result = eval(&Expr::Snd(Box::new(pair))).unwrap();

        assert_eq!(fst_result, Value::Int(1));
        assert_eq!(snd_result, Value::Int(2));
    }

    /// Test module re-exports are accessible
    #[test]
    fn test_module_reexports() {
        // Verify all re-exported types are accessible
        let _instr: Instruction = Instruction::Const(ir::Constant::Unit);
        let _block: BasicBlock = BasicBlock::new(ir::BlockId::new(0));
        let _program: Program = Program::new();
        let _value: Value = Value::Unit;
        let _lower: Lower = Lower::new();
        let _interp: Interpreter = Interpreter::new();
        let _emitter: CEmitter = CEmitter::new();
    }

    /// Test security operations through pipeline
    #[test]
    fn test_integration_classify() {
        // classify 42
        let expr = Expr::Classify(Box::new(Expr::Int(42)));

        let result = eval(&expr).unwrap();
        // Result should be a secret value
        assert!(matches!(result, Value::Secret(_)));
    }

    /// Test prove and declassify operations
    #[test]
    fn test_integration_prove() {
        // prove 42
        let expr = Expr::Prove(Box::new(Expr::Int(42)));

        let result = eval(&expr).unwrap();
        assert!(matches!(result, Value::Proof(_)));
    }
}
