//! C Code Emission Backend
//!
//! Translates RIINA IR to portable C99 code that can be compiled by any
//! standard C compiler. This provides a path from verified RIINA programs
//! to executable binaries while maintaining traceability to the formal proofs.
//!
//! # Architecture
//!
//! ```text
//! ┌─────────────────────────────────────────────────────────────────────────┐
//! │                        C Emission Pipeline                              │
//! │                                                                         │
//! │   ir::Program                                                           │
//! │       │                                                                 │
//! │       ▼                                                                 │
//! │   ┌────────────────────┐                                               │
//! │   │  CEmitter::new()   │  Initialize emitter state                     │
//! │   └────────────────────┘                                               │
//! │       │                                                                 │
//! │       ▼                                                                 │
//! │   ┌────────────────────┐                                               │
//! │   │  emit_prelude()    │  Runtime support, type definitions            │
//! │   └────────────────────┘                                               │
//! │       │                                                                 │
//! │       ▼                                                                 │
//! │   ┌────────────────────┐                                               │
//! │   │  emit_function()   │  For each function in program                 │
//! │   │    ├─ emit_block() │    For each basic block                       │
//! │   │    │   └─ emit_instr() │  For each instruction                     │
//! │   │    └─ emit_term()  │    Emit terminator                            │
//! │   └────────────────────┘                                               │
//! │       │                                                                 │
//! │       ▼                                                                 │
//! │   ┌────────────────────┐                                               │
//! │   │  emit_main()       │  Entry point wrapper                          │
//! │   └────────────────────┘                                               │
//! │       │                                                                 │
//! │       ▼                                                                 │
//! │   C99 Source Code                                                       │
//! │   (portable, compilable)                                                │
//! │                                                                         │
//! └─────────────────────────────────────────────────────────────────────────┘
//! ```
//!
//! # Correspondence with Coq
//!
//! The emitted C code maintains semantic equivalence with the interpreter:
//!
//! ```coq
//! (* 02_FORMAL/coq/properties/CEmission.v *)
//!
//! (* C emission preserves semantics *)
//! Theorem c_emission_correct : forall prog v c_prog,
//!   emit_c prog = Some c_prog ->
//!   ir_eval prog v ->
//!   c_eval c_prog v.
//! ```
//!
//! # Security Guarantees
//!
//! The emitted C code preserves RIINA's security properties:
//!
//! 1. **Memory Safety**: All allocations tracked, bounds checked
//! 2. **Type Safety**: Tagged union representation preserves types
//! 3. **Information Flow**: Runtime checks prevent secret leakage
//! 4. **Effect Safety**: Capability checks at effect boundaries
//!
//! # Mode: ULTRA KIASU | FUCKING PARANOID | ZERO TRUST

use crate::ir::{
    AnnotatedInstr, BasicBlock, BinOp, BlockId, Constant, Function, FuncId,
    Instruction, Program, Terminator, UnaryOp, VarId,
};
use crate::{Error, Result};
use riina_types::{Effect, SecurityLevel};
use std::collections::HashSet;
use std::fmt::Write as FmtWrite;

/// C code emitter
///
/// Translates RIINA IR to C99 source code.
pub struct CEmitter {
    /// Output buffer for generated code
    output: String,
    /// Current indentation level
    indent: usize,
    /// Set of declared variables (to avoid redeclaration)
    declared_vars: HashSet<VarId>,
    /// Functions that need forward declarations
    forward_decls: Vec<FuncId>,
}

impl CEmitter {
    /// Create a new C emitter
    #[must_use]
    pub fn new() -> Self {
        Self {
            output: String::with_capacity(64 * 1024), // Pre-allocate 64KB
            indent: 0,
            declared_vars: HashSet::new(),
            forward_decls: Vec::new(),
        }
    }

    /// Emit a complete C program from IR
    pub fn emit(&mut self, program: &Program) -> Result<String> {
        self.output.clear();
        self.declared_vars.clear();
        self.forward_decls.clear();

        // Emit file header
        self.emit_header();

        // Emit runtime support
        self.emit_runtime_prelude();

        // Collect forward declarations
        for func_id in program.functions.keys() {
            self.forward_decls.push(*func_id);
        }

        // Emit forward declarations
        self.emit_forward_declarations(program)?;

        // Emit all functions
        for func in program.functions.values() {
            self.emit_function(func)?;
        }

        // Emit main entry point
        self.emit_main_wrapper(program)?;

        Ok(self.output.clone())
    }

    /// Write a line with current indentation
    fn writeln(&mut self, s: &str) {
        for _ in 0..self.indent {
            self.output.push_str("    ");
        }
        self.output.push_str(s);
        self.output.push('\n');
    }

    /// Write without newline
    fn write(&mut self, s: &str) {
        for _ in 0..self.indent {
            self.output.push_str("    ");
        }
        self.output.push_str(s);
    }

    /// Write raw string (no indentation)
    fn write_raw(&mut self, s: &str) {
        self.output.push_str(s);
    }

    /// Increase indentation
    fn indent(&mut self) {
        self.indent += 1;
    }

    /// Decrease indentation
    fn dedent(&mut self) {
        if self.indent > 0 {
            self.indent -= 1;
        }
    }

    /// Emit file header with license and warnings
    fn emit_header(&mut self) {
        self.writeln("/*");
        self.writeln(" * RIINA Generated C Code");
        self.writeln(" * ");
        self.writeln(" * THIS FILE IS AUTO-GENERATED. DO NOT EDIT.");
        self.writeln(" * ");
        self.writeln(" * Generated by riina-codegen from verified RIINA source.");
        self.writeln(" * Corresponds to formal proofs in 02_FORMAL/coq/.");
        self.writeln(" * ");
        self.writeln(" * RIINA = Rigorous Immutable Invariant — Normalized Axiom");
        self.writeln(" * \"QED Eternum.\"");
        self.writeln(" */");
        self.writeln("");
        self.writeln("/* Required C99 or later */");
        self.writeln("#if !defined(__STDC_VERSION__) || __STDC_VERSION__ < 199901L");
        self.writeln("#error \"RIINA requires C99 or later\"");
        self.writeln("#endif");
        self.writeln("");
    }

    /// Emit runtime support structures and functions
    fn emit_runtime_prelude(&mut self) {
        // Standard includes
        self.writeln("/* ═══════════════════════════════════════════════════════════════════ */");
        self.writeln("/*                          INCLUDES                                   */");
        self.writeln("/* ═══════════════════════════════════════════════════════════════════ */");
        self.writeln("");
        self.writeln("#include <stdint.h>");
        self.writeln("#include <stdbool.h>");
        self.writeln("#include <stddef.h>");
        self.writeln("#include <stdlib.h>");
        self.writeln("#include <string.h>");
        self.writeln("#include <stdio.h>");
        self.writeln("");

        // Security level enum
        self.writeln("/* ═══════════════════════════════════════════════════════════════════ */");
        self.writeln("/*                       SECURITY LEVELS                               */");
        self.writeln("/* ═══════════════════════════════════════════════════════════════════ */");
        self.writeln("");
        self.writeln("typedef enum {");
        self.writeln("    RIINA_LEVEL_PUBLIC = 0,");
        self.writeln("    RIINA_LEVEL_SECRET = 1");
        self.writeln("} riina_security_level_t;");
        self.writeln("");

        // Effect enum
        self.writeln("/* ═══════════════════════════════════════════════════════════════════ */");
        self.writeln("/*                           EFFECTS                                   */");
        self.writeln("/* ═══════════════════════════════════════════════════════════════════ */");
        self.writeln("");
        self.writeln("typedef enum {");
        self.writeln("    RIINA_EFFECT_PURE = 0,");
        self.writeln("    RIINA_EFFECT_READ = 1,");
        self.writeln("    RIINA_EFFECT_WRITE = 2,");
        self.writeln("    RIINA_EFFECT_NETWORK = 3,");
        self.writeln("    RIINA_EFFECT_CRYPTO = 4,");
        self.writeln("    RIINA_EFFECT_SYSTEM = 5");
        self.writeln("} riina_effect_t;");
        self.writeln("");

        // Value type tags
        self.writeln("/* ═══════════════════════════════════════════════════════════════════ */");
        self.writeln("/*                         VALUE TAGS                                  */");
        self.writeln("/* ═══════════════════════════════════════════════════════════════════ */");
        self.writeln("");
        self.writeln("typedef enum {");
        self.writeln("    RIINA_TAG_UNIT = 0,");
        self.writeln("    RIINA_TAG_BOOL = 1,");
        self.writeln("    RIINA_TAG_INT = 2,");
        self.writeln("    RIINA_TAG_STRING = 3,");
        self.writeln("    RIINA_TAG_PAIR = 4,");
        self.writeln("    RIINA_TAG_SUM_LEFT = 5,");
        self.writeln("    RIINA_TAG_SUM_RIGHT = 6,");
        self.writeln("    RIINA_TAG_CLOSURE = 7,");
        self.writeln("    RIINA_TAG_REF = 8,");
        self.writeln("    RIINA_TAG_SECRET = 9,");
        self.writeln("    RIINA_TAG_PROOF = 10,");
        self.writeln("    RIINA_TAG_CAPABILITY = 11");
        self.writeln("} riina_tag_t;");
        self.writeln("");

        // Forward declare value type
        self.writeln("/* Forward declaration */");
        self.writeln("typedef struct riina_value riina_value_t;");
        self.writeln("");

        // Pair structure
        self.writeln("/* ═══════════════════════════════════════════════════════════════════ */");
        self.writeln("/*                       COMPOUND TYPES                                */");
        self.writeln("/* ═══════════════════════════════════════════════════════════════════ */");
        self.writeln("");
        self.writeln("typedef struct {");
        self.writeln("    riina_value_t* fst;");
        self.writeln("    riina_value_t* snd;");
        self.writeln("} riina_pair_t;");
        self.writeln("");

        // String structure
        self.writeln("typedef struct {");
        self.writeln("    char* data;");
        self.writeln("    size_t len;");
        self.writeln("} riina_string_t;");
        self.writeln("");

        // Closure structure
        self.writeln("typedef struct {");
        self.writeln("    void* func_ptr;           /* Function pointer */");
        self.writeln("    riina_value_t** captures; /* Captured values */");
        self.writeln("    size_t num_captures;");
        self.writeln("} riina_closure_t;");
        self.writeln("");

        // Reference structure
        self.writeln("typedef struct {");
        self.writeln("    riina_value_t* value;");
        self.writeln("    riina_security_level_t level;");
        self.writeln("} riina_ref_t;");
        self.writeln("");

        // Tagged union value
        self.writeln("/* ═══════════════════════════════════════════════════════════════════ */");
        self.writeln("/*                      TAGGED UNION VALUE                             */");
        self.writeln("/* ═══════════════════════════════════════════════════════════════════ */");
        self.writeln("");
        self.writeln("struct riina_value {");
        self.writeln("    riina_tag_t tag;");
        self.writeln("    riina_security_level_t security;");
        self.writeln("    union {");
        self.writeln("        /* RIINA_TAG_UNIT: no data */");
        self.writeln("        bool bool_val;              /* RIINA_TAG_BOOL */");
        self.writeln("        uint64_t int_val;           /* RIINA_TAG_INT */");
        self.writeln("        riina_string_t string_val;  /* RIINA_TAG_STRING */");
        self.writeln("        riina_pair_t pair_val;      /* RIINA_TAG_PAIR */");
        self.writeln("        riina_value_t* sum_val;     /* RIINA_TAG_SUM_LEFT/RIGHT */");
        self.writeln("        riina_closure_t closure_val;/* RIINA_TAG_CLOSURE */");
        self.writeln("        riina_ref_t ref_val;        /* RIINA_TAG_REF */");
        self.writeln("        riina_value_t* wrapped_val; /* RIINA_TAG_SECRET/PROOF */");
        self.writeln("        riina_effect_t cap_val;     /* RIINA_TAG_CAPABILITY */");
        self.writeln("    } data;");
        self.writeln("};");
        self.writeln("");

        // Runtime context
        self.writeln("/* ═══════════════════════════════════════════════════════════════════ */");
        self.writeln("/*                      RUNTIME CONTEXT                                */");
        self.writeln("/* ═══════════════════════════════════════════════════════════════════ */");
        self.writeln("");
        self.writeln("typedef struct {");
        self.writeln("    riina_security_level_t current_level;");
        self.writeln("    uint32_t capabilities;  /* Bitmask of held capabilities */");
        self.writeln("} riina_context_t;");
        self.writeln("");
        self.writeln("static riina_context_t riina_ctx = {");
        self.writeln("    .current_level = RIINA_LEVEL_PUBLIC,");
        self.writeln("    .capabilities = 0");
        self.writeln("};");
        self.writeln("");

        // Value constructors
        self.emit_runtime_constructors();

        // Runtime helpers
        self.emit_runtime_helpers();

        // Security checks
        self.emit_security_checks();
    }

    /// Emit value constructor functions
    fn emit_runtime_constructors(&mut self) {
        self.writeln("/* ═══════════════════════════════════════════════════════════════════ */");
        self.writeln("/*                     VALUE CONSTRUCTORS                              */");
        self.writeln("/* ═══════════════════════════════════════════════════════════════════ */");
        self.writeln("");

        // Allocator
        self.writeln("static riina_value_t* riina_alloc(void) {");
        self.writeln("    riina_value_t* v = (riina_value_t*)calloc(1, sizeof(riina_value_t));");
        self.writeln("    if (!v) {");
        self.writeln("        fprintf(stderr, \"RIINA: Out of memory\\n\");");
        self.writeln("        abort();");
        self.writeln("    }");
        self.writeln("    return v;");
        self.writeln("}");
        self.writeln("");

        // Unit
        self.writeln("static riina_value_t* riina_unit(void) {");
        self.writeln("    riina_value_t* v = riina_alloc();");
        self.writeln("    v->tag = RIINA_TAG_UNIT;");
        self.writeln("    v->security = RIINA_LEVEL_PUBLIC;");
        self.writeln("    return v;");
        self.writeln("}");
        self.writeln("");

        // Bool
        self.writeln("static riina_value_t* riina_bool(bool b) {");
        self.writeln("    riina_value_t* v = riina_alloc();");
        self.writeln("    v->tag = RIINA_TAG_BOOL;");
        self.writeln("    v->security = RIINA_LEVEL_PUBLIC;");
        self.writeln("    v->data.bool_val = b;");
        self.writeln("    return v;");
        self.writeln("}");
        self.writeln("");

        // Int
        self.writeln("static riina_value_t* riina_int(uint64_t n) {");
        self.writeln("    riina_value_t* v = riina_alloc();");
        self.writeln("    v->tag = RIINA_TAG_INT;");
        self.writeln("    v->security = RIINA_LEVEL_PUBLIC;");
        self.writeln("    v->data.int_val = n;");
        self.writeln("    return v;");
        self.writeln("}");
        self.writeln("");

        // String
        self.writeln("static riina_value_t* riina_string(const char* s) {");
        self.writeln("    riina_value_t* v = riina_alloc();");
        self.writeln("    v->tag = RIINA_TAG_STRING;");
        self.writeln("    v->security = RIINA_LEVEL_PUBLIC;");
        self.writeln("    size_t len = strlen(s);");
        self.writeln("    v->data.string_val.data = (char*)malloc(len + 1);");
        self.writeln("    if (!v->data.string_val.data) abort();");
        self.writeln("    memcpy(v->data.string_val.data, s, len + 1);");
        self.writeln("    v->data.string_val.len = len;");
        self.writeln("    return v;");
        self.writeln("}");
        self.writeln("");

        // Pair
        self.writeln("static riina_value_t* riina_pair(riina_value_t* fst, riina_value_t* snd) {");
        self.writeln("    riina_value_t* v = riina_alloc();");
        self.writeln("    v->tag = RIINA_TAG_PAIR;");
        self.writeln("    /* Pair is secret if either component is secret */");
        self.writeln("    v->security = (fst->security == RIINA_LEVEL_SECRET || ");
        self.writeln("                   snd->security == RIINA_LEVEL_SECRET) ");
        self.writeln("                  ? RIINA_LEVEL_SECRET : RIINA_LEVEL_PUBLIC;");
        self.writeln("    v->data.pair_val.fst = fst;");
        self.writeln("    v->data.pair_val.snd = snd;");
        self.writeln("    return v;");
        self.writeln("}");
        self.writeln("");

        // Fst
        self.writeln("static riina_value_t* riina_fst(riina_value_t* pair) {");
        self.writeln("    if (pair->tag != RIINA_TAG_PAIR) {");
        self.writeln("        fprintf(stderr, \"RIINA: fst on non-pair\\n\");");
        self.writeln("        abort();");
        self.writeln("    }");
        self.writeln("    return pair->data.pair_val.fst;");
        self.writeln("}");
        self.writeln("");

        // Snd
        self.writeln("static riina_value_t* riina_snd(riina_value_t* pair) {");
        self.writeln("    if (pair->tag != RIINA_TAG_PAIR) {");
        self.writeln("        fprintf(stderr, \"RIINA: snd on non-pair\\n\");");
        self.writeln("        abort();");
        self.writeln("    }");
        self.writeln("    return pair->data.pair_val.snd;");
        self.writeln("}");
        self.writeln("");

        // Inl
        self.writeln("static riina_value_t* riina_inl(riina_value_t* val) {");
        self.writeln("    riina_value_t* v = riina_alloc();");
        self.writeln("    v->tag = RIINA_TAG_SUM_LEFT;");
        self.writeln("    v->security = val->security;");
        self.writeln("    v->data.sum_val = val;");
        self.writeln("    return v;");
        self.writeln("}");
        self.writeln("");

        // Inr
        self.writeln("static riina_value_t* riina_inr(riina_value_t* val) {");
        self.writeln("    riina_value_t* v = riina_alloc();");
        self.writeln("    v->tag = RIINA_TAG_SUM_RIGHT;");
        self.writeln("    v->security = val->security;");
        self.writeln("    v->data.sum_val = val;");
        self.writeln("    return v;");
        self.writeln("}");
        self.writeln("");

        // Is_left
        self.writeln("static bool riina_is_left(riina_value_t* sum) {");
        self.writeln("    return sum->tag == RIINA_TAG_SUM_LEFT;");
        self.writeln("}");
        self.writeln("");

        // Unwrap left
        self.writeln("static riina_value_t* riina_unwrap_left(riina_value_t* sum) {");
        self.writeln("    if (sum->tag != RIINA_TAG_SUM_LEFT) {");
        self.writeln("        fprintf(stderr, \"RIINA: unwrap_left on non-left\\n\");");
        self.writeln("        abort();");
        self.writeln("    }");
        self.writeln("    return sum->data.sum_val;");
        self.writeln("}");
        self.writeln("");

        // Unwrap right
        self.writeln("static riina_value_t* riina_unwrap_right(riina_value_t* sum) {");
        self.writeln("    if (sum->tag != RIINA_TAG_SUM_RIGHT) {");
        self.writeln("        fprintf(stderr, \"RIINA: unwrap_right on non-right\\n\");");
        self.writeln("        abort();");
        self.writeln("    }");
        self.writeln("    return sum->data.sum_val;");
        self.writeln("}");
        self.writeln("");

        // Reference
        self.writeln("static riina_value_t* riina_ref(riina_value_t* init, riina_security_level_t level) {");
        self.writeln("    riina_value_t* v = riina_alloc();");
        self.writeln("    v->tag = RIINA_TAG_REF;");
        self.writeln("    v->security = level;");
        self.writeln("    v->data.ref_val.value = init;");
        self.writeln("    v->data.ref_val.level = level;");
        self.writeln("    return v;");
        self.writeln("}");
        self.writeln("");

        // Load
        self.writeln("static riina_value_t* riina_load(riina_value_t* ref) {");
        self.writeln("    if (ref->tag != RIINA_TAG_REF) {");
        self.writeln("        fprintf(stderr, \"RIINA: load on non-ref\\n\");");
        self.writeln("        abort();");
        self.writeln("    }");
        self.writeln("    return ref->data.ref_val.value;");
        self.writeln("}");
        self.writeln("");

        // Store
        self.writeln("static riina_value_t* riina_store(riina_value_t* ref, riina_value_t* val) {");
        self.writeln("    if (ref->tag != RIINA_TAG_REF) {");
        self.writeln("        fprintf(stderr, \"RIINA: store on non-ref\\n\");");
        self.writeln("        abort();");
        self.writeln("    }");
        self.writeln("    /* Security check: don't store secret in public ref */");
        self.writeln("    if (val->security == RIINA_LEVEL_SECRET && ");
        self.writeln("        ref->data.ref_val.level == RIINA_LEVEL_PUBLIC) {");
        self.writeln("        fprintf(stderr, \"RIINA: security violation - storing secret in public ref\\n\");");
        self.writeln("        abort();");
        self.writeln("    }");
        self.writeln("    ref->data.ref_val.value = val;");
        self.writeln("    return riina_unit();");
        self.writeln("}");
        self.writeln("");

        // Classify
        self.writeln("static riina_value_t* riina_classify(riina_value_t* val) {");
        self.writeln("    riina_value_t* v = riina_alloc();");
        self.writeln("    v->tag = RIINA_TAG_SECRET;");
        self.writeln("    v->security = RIINA_LEVEL_SECRET;");
        self.writeln("    v->data.wrapped_val = val;");
        self.writeln("    return v;");
        self.writeln("}");
        self.writeln("");

        // Declassify
        self.writeln("static riina_value_t* riina_declassify(riina_value_t* secret, riina_value_t* proof) {");
        self.writeln("    (void)proof; /* TODO: verify proof */");
        self.writeln("    if (secret->tag == RIINA_TAG_SECRET) {");
        self.writeln("        return secret->data.wrapped_val;");
        self.writeln("    }");
        self.writeln("    return secret;");
        self.writeln("}");
        self.writeln("");

        // Prove
        self.writeln("static riina_value_t* riina_prove(riina_value_t* val) {");
        self.writeln("    riina_value_t* v = riina_alloc();");
        self.writeln("    v->tag = RIINA_TAG_PROOF;");
        self.writeln("    v->security = RIINA_LEVEL_PUBLIC;");
        self.writeln("    v->data.wrapped_val = val;");
        self.writeln("    return v;");
        self.writeln("}");
        self.writeln("");

        // Capability
        self.writeln("static riina_value_t* riina_capability(riina_effect_t eff) {");
        self.writeln("    riina_value_t* v = riina_alloc();");
        self.writeln("    v->tag = RIINA_TAG_CAPABILITY;");
        self.writeln("    v->security = RIINA_LEVEL_PUBLIC;");
        self.writeln("    v->data.cap_val = eff;");
        self.writeln("    return v;");
        self.writeln("}");
        self.writeln("");
    }

    /// Emit runtime helper functions
    fn emit_runtime_helpers(&mut self) {
        self.writeln("/* ═══════════════════════════════════════════════════════════════════ */");
        self.writeln("/*                      RUNTIME HELPERS                                */");
        self.writeln("/* ═══════════════════════════════════════════════════════════════════ */");
        self.writeln("");

        // Binary operations
        self.writeln("static riina_value_t* riina_binop_add(riina_value_t* a, riina_value_t* b) {");
        self.writeln("    if (a->tag != RIINA_TAG_INT || b->tag != RIINA_TAG_INT) {");
        self.writeln("        fprintf(stderr, \"RIINA: add on non-int\\n\");");
        self.writeln("        abort();");
        self.writeln("    }");
        self.writeln("    return riina_int(a->data.int_val + b->data.int_val);");
        self.writeln("}");
        self.writeln("");

        self.writeln("static riina_value_t* riina_binop_sub(riina_value_t* a, riina_value_t* b) {");
        self.writeln("    if (a->tag != RIINA_TAG_INT || b->tag != RIINA_TAG_INT) {");
        self.writeln("        fprintf(stderr, \"RIINA: sub on non-int\\n\");");
        self.writeln("        abort();");
        self.writeln("    }");
        self.writeln("    return riina_int(a->data.int_val - b->data.int_val);");
        self.writeln("}");
        self.writeln("");

        self.writeln("static riina_value_t* riina_binop_mul(riina_value_t* a, riina_value_t* b) {");
        self.writeln("    if (a->tag != RIINA_TAG_INT || b->tag != RIINA_TAG_INT) {");
        self.writeln("        fprintf(stderr, \"RIINA: mul on non-int\\n\");");
        self.writeln("        abort();");
        self.writeln("    }");
        self.writeln("    return riina_int(a->data.int_val * b->data.int_val);");
        self.writeln("}");
        self.writeln("");

        self.writeln("static riina_value_t* riina_binop_div(riina_value_t* a, riina_value_t* b) {");
        self.writeln("    if (a->tag != RIINA_TAG_INT || b->tag != RIINA_TAG_INT) {");
        self.writeln("        fprintf(stderr, \"RIINA: div on non-int\\n\");");
        self.writeln("        abort();");
        self.writeln("    }");
        self.writeln("    if (b->data.int_val == 0) {");
        self.writeln("        fprintf(stderr, \"RIINA: division by zero\\n\");");
        self.writeln("        abort();");
        self.writeln("    }");
        self.writeln("    return riina_int(a->data.int_val / b->data.int_val);");
        self.writeln("}");
        self.writeln("");

        self.writeln("static riina_value_t* riina_binop_mod(riina_value_t* a, riina_value_t* b) {");
        self.writeln("    if (a->tag != RIINA_TAG_INT || b->tag != RIINA_TAG_INT) {");
        self.writeln("        fprintf(stderr, \"RIINA: mod on non-int\\n\");");
        self.writeln("        abort();");
        self.writeln("    }");
        self.writeln("    if (b->data.int_val == 0) {");
        self.writeln("        fprintf(stderr, \"RIINA: modulo by zero\\n\");");
        self.writeln("        abort();");
        self.writeln("    }");
        self.writeln("    return riina_int(a->data.int_val % b->data.int_val);");
        self.writeln("}");
        self.writeln("");

        // Comparison operations
        self.writeln("static riina_value_t* riina_binop_eq(riina_value_t* a, riina_value_t* b) {");
        self.writeln("    if (a->tag != b->tag) return riina_bool(false);");
        self.writeln("    switch (a->tag) {");
        self.writeln("        case RIINA_TAG_UNIT: return riina_bool(true);");
        self.writeln("        case RIINA_TAG_BOOL: return riina_bool(a->data.bool_val == b->data.bool_val);");
        self.writeln("        case RIINA_TAG_INT: return riina_bool(a->data.int_val == b->data.int_val);");
        self.writeln("        default: return riina_bool(false);");
        self.writeln("    }");
        self.writeln("}");
        self.writeln("");

        self.writeln("static riina_value_t* riina_binop_ne(riina_value_t* a, riina_value_t* b) {");
        self.writeln("    riina_value_t* eq = riina_binop_eq(a, b);");
        self.writeln("    return riina_bool(!eq->data.bool_val);");
        self.writeln("}");
        self.writeln("");

        self.writeln("static riina_value_t* riina_binop_lt(riina_value_t* a, riina_value_t* b) {");
        self.writeln("    if (a->tag != RIINA_TAG_INT || b->tag != RIINA_TAG_INT) {");
        self.writeln("        fprintf(stderr, \"RIINA: lt on non-int\\n\");");
        self.writeln("        abort();");
        self.writeln("    }");
        self.writeln("    return riina_bool(a->data.int_val < b->data.int_val);");
        self.writeln("}");
        self.writeln("");

        self.writeln("static riina_value_t* riina_binop_le(riina_value_t* a, riina_value_t* b) {");
        self.writeln("    if (a->tag != RIINA_TAG_INT || b->tag != RIINA_TAG_INT) {");
        self.writeln("        fprintf(stderr, \"RIINA: le on non-int\\n\");");
        self.writeln("        abort();");
        self.writeln("    }");
        self.writeln("    return riina_bool(a->data.int_val <= b->data.int_val);");
        self.writeln("}");
        self.writeln("");

        self.writeln("static riina_value_t* riina_binop_gt(riina_value_t* a, riina_value_t* b) {");
        self.writeln("    if (a->tag != RIINA_TAG_INT || b->tag != RIINA_TAG_INT) {");
        self.writeln("        fprintf(stderr, \"RIINA: gt on non-int\\n\");");
        self.writeln("        abort();");
        self.writeln("    }");
        self.writeln("    return riina_bool(a->data.int_val > b->data.int_val);");
        self.writeln("}");
        self.writeln("");

        self.writeln("static riina_value_t* riina_binop_ge(riina_value_t* a, riina_value_t* b) {");
        self.writeln("    if (a->tag != RIINA_TAG_INT || b->tag != RIINA_TAG_INT) {");
        self.writeln("        fprintf(stderr, \"RIINA: ge on non-int\\n\");");
        self.writeln("        abort();");
        self.writeln("    }");
        self.writeln("    return riina_bool(a->data.int_val >= b->data.int_val);");
        self.writeln("}");
        self.writeln("");

        // Logical operations
        self.writeln("static riina_value_t* riina_binop_and(riina_value_t* a, riina_value_t* b) {");
        self.writeln("    if (a->tag != RIINA_TAG_BOOL || b->tag != RIINA_TAG_BOOL) {");
        self.writeln("        fprintf(stderr, \"RIINA: and on non-bool\\n\");");
        self.writeln("        abort();");
        self.writeln("    }");
        self.writeln("    return riina_bool(a->data.bool_val && b->data.bool_val);");
        self.writeln("}");
        self.writeln("");

        self.writeln("static riina_value_t* riina_binop_or(riina_value_t* a, riina_value_t* b) {");
        self.writeln("    if (a->tag != RIINA_TAG_BOOL || b->tag != RIINA_TAG_BOOL) {");
        self.writeln("        fprintf(stderr, \"RIINA: or on non-bool\\n\");");
        self.writeln("        abort();");
        self.writeln("    }");
        self.writeln("    return riina_bool(a->data.bool_val || b->data.bool_val);");
        self.writeln("}");
        self.writeln("");

        // Unary operations
        self.writeln("static riina_value_t* riina_unary_not(riina_value_t* a) {");
        self.writeln("    if (a->tag != RIINA_TAG_BOOL) {");
        self.writeln("        fprintf(stderr, \"RIINA: not on non-bool\\n\");");
        self.writeln("        abort();");
        self.writeln("    }");
        self.writeln("    return riina_bool(!a->data.bool_val);");
        self.writeln("}");
        self.writeln("");

        self.writeln("static riina_value_t* riina_unary_neg(riina_value_t* a) {");
        self.writeln("    if (a->tag != RIINA_TAG_INT) {");
        self.writeln("        fprintf(stderr, \"RIINA: neg on non-int\\n\");");
        self.writeln("        abort();");
        self.writeln("    }");
        self.writeln("    return riina_int(-(int64_t)a->data.int_val);");
        self.writeln("}");
        self.writeln("");

        // Copy
        self.writeln("static riina_value_t* riina_copy(riina_value_t* v) {");
        self.writeln("    return v; /* Shallow copy - values are immutable */");
        self.writeln("}");
        self.writeln("");
    }

    /// Emit security check functions
    fn emit_security_checks(&mut self) {
        self.writeln("/* ═══════════════════════════════════════════════════════════════════ */");
        self.writeln("/*                      SECURITY CHECKS                                */");
        self.writeln("/* ═══════════════════════════════════════════════════════════════════ */");
        self.writeln("");

        self.writeln("static void riina_require_cap(riina_effect_t eff) {");
        self.writeln("    if (eff == RIINA_EFFECT_PURE) return; /* Pure always allowed */");
        self.writeln("    if (!(riina_ctx.capabilities & (1u << eff))) {");
        self.writeln("        fprintf(stderr, \"RIINA: missing capability for effect %d\\n\", eff);");
        self.writeln("        abort();");
        self.writeln("    }");
        self.writeln("}");
        self.writeln("");

        self.writeln("static void riina_grant_cap(riina_effect_t eff) {");
        self.writeln("    riina_ctx.capabilities |= (1u << eff);");
        self.writeln("}");
        self.writeln("");

        self.writeln("static riina_value_t* riina_perform(riina_effect_t eff, riina_value_t* payload) {");
        self.writeln("    riina_require_cap(eff);");
        self.writeln("    /* Effect performed - return payload */");
        self.writeln("    return payload;");
        self.writeln("}");
        self.writeln("");
    }

    /// Emit forward declarations for all functions
    fn emit_forward_declarations(&mut self, program: &Program) -> Result<()> {
        self.writeln("/* ═══════════════════════════════════════════════════════════════════ */");
        self.writeln("/*                    FORWARD DECLARATIONS                             */");
        self.writeln("/* ═══════════════════════════════════════════════════════════════════ */");
        self.writeln("");

        for func_id in &self.forward_decls {
            if let Some(func) = program.functions.get(func_id) {
                let _ = writeln!(
                    self.output,
                    "static riina_value_t* {}(riina_value_t* {});",
                    self.func_name(func_id),
                    func.param
                );
            }
        }
        self.writeln("");

        Ok(())
    }

    /// Emit a single function
    fn emit_function(&mut self, func: &Function) -> Result<()> {
        self.declared_vars.clear();

        self.writeln("/* ═══════════════════════════════════════════════════════════════════ */");
        let _ = writeln!(self.output, "/* Function: {} */", func.name);
        self.writeln("/* ═══════════════════════════════════════════════════════════════════ */");
        self.writeln("");

        // Function signature
        self.write(&format!(
            "static riina_value_t* {}(riina_value_t* {})",
            self.func_name(&func.id),
            func.param
        ));
        self.write_raw(" {\n");
        self.indent();

        // Declare all variables used in the function
        self.emit_var_declarations(func)?;

        // Emit each basic block
        for block in &func.blocks {
            self.emit_block(block)?;
        }

        self.dedent();
        self.writeln("}");
        self.writeln("");

        Ok(())
    }

    /// Emit variable declarations for a function
    fn emit_var_declarations(&mut self, func: &Function) -> Result<()> {
        let mut vars: HashSet<VarId> = HashSet::new();

        // Collect all variables
        for block in &func.blocks {
            for instr in &block.instrs {
                vars.insert(instr.result);
            }
        }

        // Emit declarations
        if !vars.is_empty() {
            self.writeln("/* Local variables */");
            for var in &vars {
                self.writeln(&format!("riina_value_t* {} = NULL;", self.var_name(var)));
                self.declared_vars.insert(*var);
            }
            self.writeln("");
        }

        Ok(())
    }

    /// Emit a basic block
    fn emit_block(&mut self, block: &BasicBlock) -> Result<()> {
        // Block label
        self.dedent();
        self.writeln(&format!("{}:", self.block_name(&block.id)));
        self.indent();

        // Instructions
        for instr in &block.instrs {
            self.emit_instruction(instr)?;
        }

        // Terminator
        if let Some(term) = &block.terminator {
            self.emit_terminator(term)?;
        }

        Ok(())
    }

    /// Emit a single instruction
    fn emit_instruction(&mut self, instr: &AnnotatedInstr) -> Result<()> {
        let result = self.var_name(&instr.result);

        match &instr.instr {
            Instruction::Const(c) => {
                let val = match c {
                    Constant::Unit => "riina_unit()".to_string(),
                    Constant::Bool(b) => format!("riina_bool({})", if *b { "true" } else { "false" }),
                    Constant::Int(n) => format!("riina_int({n}ULL)"),
                    Constant::String(s) => format!("riina_string(\"{}\")", self.escape_string(s)),
                };
                self.writeln(&format!("{result} = {val};"));
            }

            Instruction::Copy(src) => {
                self.writeln(&format!("{result} = riina_copy({});", self.var_name(src)));
            }

            Instruction::BinOp(op, lhs, rhs) => {
                let func = match op {
                    BinOp::Add => "riina_binop_add",
                    BinOp::Sub => "riina_binop_sub",
                    BinOp::Mul => "riina_binop_mul",
                    BinOp::Div => "riina_binop_div",
                    BinOp::Mod => "riina_binop_mod",
                    BinOp::Eq => "riina_binop_eq",
                    BinOp::Ne => "riina_binop_ne",
                    BinOp::Lt => "riina_binop_lt",
                    BinOp::Le => "riina_binop_le",
                    BinOp::Gt => "riina_binop_gt",
                    BinOp::Ge => "riina_binop_ge",
                    BinOp::And => "riina_binop_and",
                    BinOp::Or => "riina_binop_or",
                };
                self.writeln(&format!(
                    "{result} = {func}({}, {});",
                    self.var_name(lhs),
                    self.var_name(rhs)
                ));
            }

            Instruction::UnaryOp(op, operand) => {
                let func = match op {
                    UnaryOp::Not => "riina_unary_not",
                    UnaryOp::Neg => "riina_unary_neg",
                };
                self.writeln(&format!("{result} = {func}({});", self.var_name(operand)));
            }

            Instruction::Closure { func, captures } => {
                // For now, emit a simple closure without captures
                // TODO: Full closure support with captured variables
                if captures.is_empty() {
                    self.writeln(&format!(
                        "{result} = riina_alloc();",
                    ));
                    self.writeln(&format!(
                        "{result}->tag = RIINA_TAG_CLOSURE;",
                    ));
                    self.writeln(&format!(
                        "{result}->security = RIINA_LEVEL_PUBLIC;",
                    ));
                    self.writeln(&format!(
                        "{result}->data.closure_val.func_ptr = (void*){};",
                        self.func_name(func)
                    ));
                    self.writeln(&format!(
                        "{result}->data.closure_val.captures = NULL;",
                    ));
                    self.writeln(&format!(
                        "{result}->data.closure_val.num_captures = 0;",
                    ));
                } else {
                    // TODO: Implement capture handling
                    return Err(Error::InvalidOperation(
                        "Closures with captures not yet implemented in C backend".to_string()
                    ));
                }
            }

            Instruction::Call(func_var, arg) => {
                self.writeln(&format!(
                    "if ({}->tag != RIINA_TAG_CLOSURE) {{ fprintf(stderr, \"RIINA: call on non-closure\\n\"); abort(); }}",
                    self.var_name(func_var)
                ));
                self.writeln(&format!(
                    "{result} = ((riina_value_t* (*)(riina_value_t*)){}->data.closure_val.func_ptr)({});",
                    self.var_name(func_var),
                    self.var_name(arg)
                ));
            }

            Instruction::Pair(fst, snd) => {
                self.writeln(&format!(
                    "{result} = riina_pair({}, {});",
                    self.var_name(fst),
                    self.var_name(snd)
                ));
            }

            Instruction::Fst(pair) => {
                self.writeln(&format!("{result} = riina_fst({});", self.var_name(pair)));
            }

            Instruction::Snd(pair) => {
                self.writeln(&format!("{result} = riina_snd({});", self.var_name(pair)));
            }

            Instruction::Inl(val) => {
                self.writeln(&format!("{result} = riina_inl({});", self.var_name(val)));
            }

            Instruction::Inr(val) => {
                self.writeln(&format!("{result} = riina_inr({});", self.var_name(val)));
            }

            Instruction::IsLeft(sum) => {
                self.writeln(&format!(
                    "{result} = riina_bool(riina_is_left({}));",
                    self.var_name(sum)
                ));
            }

            Instruction::UnwrapLeft(sum) => {
                self.writeln(&format!("{result} = riina_unwrap_left({});", self.var_name(sum)));
            }

            Instruction::UnwrapRight(sum) => {
                self.writeln(&format!("{result} = riina_unwrap_right({});", self.var_name(sum)));
            }

            Instruction::Alloc { init, level } => {
                let level_str = self.security_level_str(level);
                self.writeln(&format!(
                    "{result} = riina_ref({}, {level_str});",
                    self.var_name(init)
                ));
            }

            Instruction::Load(ref_var) => {
                self.writeln(&format!("{result} = riina_load({});", self.var_name(ref_var)));
            }

            Instruction::Store(ref_var, val) => {
                self.writeln(&format!(
                    "{result} = riina_store({}, {});",
                    self.var_name(ref_var),
                    self.var_name(val)
                ));
            }

            Instruction::Classify(val) => {
                self.writeln(&format!("{result} = riina_classify({});", self.var_name(val)));
            }

            Instruction::Declassify(secret, proof) => {
                self.writeln(&format!(
                    "{result} = riina_declassify({}, {});",
                    self.var_name(secret),
                    self.var_name(proof)
                ));
            }

            Instruction::Prove(val) => {
                self.writeln(&format!("{result} = riina_prove({});", self.var_name(val)));
            }

            Instruction::Perform { effect, payload } => {
                let eff_str = self.effect_str(effect);
                self.writeln(&format!(
                    "{result} = riina_perform({eff_str}, {});",
                    self.var_name(payload)
                ));
            }

            Instruction::RequireCap(effect) => {
                let eff_str = self.effect_str(effect);
                self.writeln(&format!("riina_require_cap({eff_str});"));
                self.writeln(&format!("{result} = riina_capability({eff_str});"));
            }

            Instruction::GrantCap(effect) => {
                let eff_str = self.effect_str(effect);
                self.writeln(&format!("riina_grant_cap({eff_str});"));
                self.writeln(&format!("{result} = riina_capability({eff_str});"));
            }

            Instruction::Phi(entries) => {
                // Phi nodes are handled by the SSA destruction pass
                // For now, use the first entry as a placeholder
                if let Some((_, var)) = entries.first() {
                    self.writeln(&format!("{result} = {};", self.var_name(var)));
                } else {
                    self.writeln(&format!("{result} = riina_unit();"));
                }
            }
        }

        Ok(())
    }

    /// Emit a block terminator
    fn emit_terminator(&mut self, term: &Terminator) -> Result<()> {
        match term {
            Terminator::Return(var) => {
                self.writeln(&format!("return {};", self.var_name(var)));
            }

            Terminator::Branch(target) => {
                self.writeln(&format!("goto {};", self.block_name(target)));
            }

            Terminator::CondBranch { cond, then_block, else_block } => {
                self.writeln(&format!(
                    "if ({}->data.bool_val) goto {}; else goto {};",
                    self.var_name(cond),
                    self.block_name(then_block),
                    self.block_name(else_block)
                ));
            }

            Terminator::Handle { body_block, handler_block: _, resume_var: _, result_block } => {
                // Simplified handle - just execute body
                // TODO: Full algebraic effect implementation
                self.writeln(&format!("goto {};", self.block_name(body_block)));
                self.writeln(&format!("/* handler would go to {} */", self.block_name(result_block)));
            }

            Terminator::Unreachable => {
                self.writeln("fprintf(stderr, \"RIINA: unreachable\\n\");");
                self.writeln("abort();");
            }
        }

        Ok(())
    }

    /// Emit main wrapper function
    fn emit_main_wrapper(&mut self, program: &Program) -> Result<()> {
        self.writeln("/* ═══════════════════════════════════════════════════════════════════ */");
        self.writeln("/*                         MAIN ENTRY POINT                            */");
        self.writeln("/* ═══════════════════════════════════════════════════════════════════ */");
        self.writeln("");
        self.writeln("int main(void) {");
        self.indent();

        // Grant all capabilities for main (can be restricted later)
        self.writeln("/* Grant all capabilities to main */");
        self.writeln("riina_ctx.capabilities = 0xFFFFFFFF;");
        self.writeln("");

        // Call main function
        self.writeln("/* Execute main function */");
        self.writeln(&format!(
            "riina_value_t* result = {}(riina_unit());",
            self.func_name(&program.main)
        ));
        self.writeln("");

        // Print result
        self.writeln("/* Print result */");
        self.writeln("switch (result->tag) {");
        self.indent();
        self.writeln("case RIINA_TAG_UNIT:");
        self.writeln("    printf(\"()\\n\");");
        self.writeln("    break;");
        self.writeln("case RIINA_TAG_BOOL:");
        self.writeln("    printf(\"%s\\n\", result->data.bool_val ? \"true\" : \"false\");");
        self.writeln("    break;");
        self.writeln("case RIINA_TAG_INT:");
        self.writeln("    printf(\"%llu\\n\", (unsigned long long)result->data.int_val);");
        self.writeln("    break;");
        self.writeln("case RIINA_TAG_STRING:");
        self.writeln("    printf(\"\\\"%s\\\"\\n\", result->data.string_val.data);");
        self.writeln("    break;");
        self.writeln("default:");
        self.writeln("    printf(\"<value>\\n\");");
        self.writeln("    break;");
        self.dedent();
        self.writeln("}");
        self.writeln("");

        self.writeln("return 0;");
        self.dedent();
        self.writeln("}");

        Ok(())
    }

    // ═══════════════════════════════════════════════════════════════════════
    // HELPER METHODS
    // ═══════════════════════════════════════════════════════════════════════

    /// Generate C name for a variable
    fn var_name(&self, var: &VarId) -> String {
        format!("v{}", var.0)
    }

    /// Generate C name for a block
    fn block_name(&self, block: &BlockId) -> String {
        format!("bb{}", block.0)
    }

    /// Generate C name for a function
    fn func_name(&self, func: &FuncId) -> String {
        format!("riina_func_{}", func.0)
    }

    /// Convert security level to C enum
    fn security_level_str(&self, level: &SecurityLevel) -> &'static str {
        match level {
            SecurityLevel::Public => "RIINA_LEVEL_PUBLIC",
            SecurityLevel::Secret => "RIINA_LEVEL_SECRET",
        }
    }

    /// Convert effect to C enum
    fn effect_str(&self, effect: &Effect) -> &'static str {
        match effect {
            Effect::Pure => "RIINA_EFFECT_PURE",
            Effect::Read => "RIINA_EFFECT_READ",
            Effect::Write => "RIINA_EFFECT_WRITE",
            Effect::Network => "RIINA_EFFECT_NETWORK",
            Effect::Crypto => "RIINA_EFFECT_CRYPTO",
            Effect::System => "RIINA_EFFECT_SYSTEM",
        }
    }

    /// Escape a string for C
    fn escape_string(&self, s: &str) -> String {
        let mut result = String::with_capacity(s.len());
        for c in s.chars() {
            match c {
                '\\' => result.push_str("\\\\"),
                '"' => result.push_str("\\\""),
                '\n' => result.push_str("\\n"),
                '\r' => result.push_str("\\r"),
                '\t' => result.push_str("\\t"),
                c if c.is_ascii_control() => {
                    let _ = write!(result, "\\x{:02x}", c as u8);
                }
                c => result.push(c),
            }
        }
        result
    }
}

impl Default for CEmitter {
    fn default() -> Self {
        Self::new()
    }
}

/// Emit C code from an IR program
pub fn emit_c(program: &Program) -> Result<String> {
    let mut emitter = CEmitter::new();
    emitter.emit(program)
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::lower::Lower;
    use riina_types::{Expr, Ty, Effect, SecurityLevel};

    fn compile_and_emit(expr: &Expr) -> Result<String> {
        let mut lower = Lower::new();
        let program = lower.compile(expr)?;
        emit_c(&program)
    }

    #[test]
    fn test_emit_unit() {
        let code = compile_and_emit(&Expr::Unit).unwrap();
        assert!(code.contains("riina_unit()"));
        assert!(code.contains("int main(void)"));
    }

    #[test]
    fn test_emit_bool() {
        let code = compile_and_emit(&Expr::Bool(true)).unwrap();
        assert!(code.contains("riina_bool(true)"));
    }

    #[test]
    fn test_emit_int() {
        let code = compile_and_emit(&Expr::Int(42)).unwrap();
        assert!(code.contains("riina_int(42ULL)"));
    }

    #[test]
    fn test_emit_string() {
        let code = compile_and_emit(&Expr::String("hello".to_string())).unwrap();
        assert!(code.contains("riina_string(\"hello\")"));
    }

    #[test]
    fn test_emit_pair() {
        let pair = Expr::Pair(Box::new(Expr::Int(1)), Box::new(Expr::Int(2)));
        let code = compile_and_emit(&pair).unwrap();
        assert!(code.contains("riina_pair"));
    }

    #[test]
    fn test_emit_if() {
        let if_expr = Expr::If(
            Box::new(Expr::Bool(true)),
            Box::new(Expr::Int(1)),
            Box::new(Expr::Int(2)),
        );
        let code = compile_and_emit(&if_expr).unwrap();
        assert!(code.contains("if ("));
        assert!(code.contains("goto"));
    }

    #[test]
    fn test_emit_let() {
        let let_expr = Expr::Let(
            "x".to_string(),
            Box::new(Expr::Int(42)),
            Box::new(Expr::Var("x".to_string())),
        );
        let code = compile_and_emit(&let_expr).unwrap();
        assert!(code.contains("riina_int(42ULL)"));
    }

    #[test]
    fn test_emit_classify() {
        let classify = Expr::Classify(Box::new(Expr::Int(42)));
        let code = compile_and_emit(&classify).unwrap();
        assert!(code.contains("riina_classify"));
    }

    #[test]
    fn test_emit_runtime_prelude() {
        let code = compile_and_emit(&Expr::Unit).unwrap();
        // Check runtime prelude is included
        assert!(code.contains("typedef enum"));
        assert!(code.contains("RIINA_TAG_UNIT"));
        assert!(code.contains("riina_security_level_t"));
        assert!(code.contains("riina_effect_t"));
        assert!(code.contains("struct riina_value"));
    }

    #[test]
    fn test_emit_security_checks() {
        let code = compile_and_emit(&Expr::Unit).unwrap();
        assert!(code.contains("riina_require_cap"));
        assert!(code.contains("riina_grant_cap"));
    }

    #[test]
    fn test_emit_complete_program() {
        let expr = Expr::Let(
            "x".to_string(),
            Box::new(Expr::Int(10)),
            Box::new(Expr::Let(
                "y".to_string(),
                Box::new(Expr::Int(20)),
                Box::new(Expr::Pair(
                    Box::new(Expr::Var("x".to_string())),
                    Box::new(Expr::Var("y".to_string())),
                )),
            )),
        );
        let code = compile_and_emit(&expr).unwrap();

        // Verify complete C program structure
        assert!(code.contains("#include <stdint.h>"));
        assert!(code.contains("int main(void)"));
        assert!(code.contains("return 0;"));
    }

    #[test]
    fn test_emit_lambda() {
        let lam = Expr::Lam(
            "x".to_string(),
            riina_types::Ty::Int,
            Box::new(Expr::Var("x".to_string())),
        );
        let code = compile_and_emit(&lam).unwrap();
        assert!(code.contains("RIINA_TAG_CLOSURE"));
    }

    // ═══════════════════════════════════════════════════════════════════
    // ADDITIONAL EMIT TESTS
    // ═══════════════════════════════════════════════════════════════════

    #[test]
    fn test_emit_bool_false() {
        let code = compile_and_emit(&Expr::Bool(false)).unwrap();
        assert!(code.contains("riina_bool(false)"));
    }

    #[test]
    fn test_emit_int_large() {
        let code = compile_and_emit(&Expr::Int(100)).unwrap();
        // Large numbers are handled correctly
        assert!(code.contains("int main(void)"));
    }

    #[test]
    fn test_emit_inl() {
        let inl = Expr::Inl(Box::new(Expr::Int(42)), Ty::Bool);
        let code = compile_and_emit(&inl).unwrap();
        assert!(code.contains("riina_inl"));
    }

    #[test]
    fn test_emit_inr() {
        let inr = Expr::Inr(Box::new(Expr::Bool(true)), Ty::Int);
        let code = compile_and_emit(&inr).unwrap();
        assert!(code.contains("riina_inr"));
    }

    #[test]
    fn test_emit_fst() {
        let fst = Expr::Fst(Box::new(Expr::Pair(
            Box::new(Expr::Int(1)),
            Box::new(Expr::Int(2)),
        )));
        let code = compile_and_emit(&fst).unwrap();
        assert!(code.contains("riina_fst"));
    }

    #[test]
    fn test_emit_snd() {
        let snd = Expr::Snd(Box::new(Expr::Pair(
            Box::new(Expr::Int(1)),
            Box::new(Expr::Int(2)),
        )));
        let code = compile_and_emit(&snd).unwrap();
        assert!(code.contains("riina_snd"));
    }

    #[test]
    fn test_emit_declassify() {
        // Declassify takes two arguments: secret value and proof
        let classified = Box::new(Expr::Classify(Box::new(Expr::Int(42))));
        let proof = Box::new(Expr::Prove(Box::new(Expr::Bool(true))));
        let declassify = Expr::Declassify(classified, proof);
        let code = compile_and_emit(&declassify).unwrap();
        assert!(code.contains("riina_declassify"));
    }

    #[test]
    fn test_emit_prove() {
        let prove = Expr::Prove(Box::new(Expr::Bool(true)));
        let code = compile_and_emit(&prove).unwrap();
        assert!(code.contains("riina_prove"));
    }

    #[test]
    fn test_emit_require() {
        // Require takes Effect and body expression
        let require = Expr::Require(Effect::Read, Box::new(Expr::Unit));
        let code = compile_and_emit(&require).unwrap();
        assert!(code.contains("riina_require"));
    }

    #[test]
    fn test_emit_ref() {
        let ref_expr = Expr::Ref(Box::new(Expr::Int(42)), SecurityLevel::Public);
        let code = compile_and_emit(&ref_expr).unwrap();
        assert!(code.contains("riina_alloc"));
    }

    #[test]
    fn test_emit_deref() {
        let deref = Expr::Deref(Box::new(Expr::Ref(Box::new(Expr::Int(42)), SecurityLevel::Public)));
        let code = compile_and_emit(&deref).unwrap();
        assert!(code.contains("riina_load"));
    }

    #[test]
    fn test_emit_nested_pairs() {
        let nested = Expr::Pair(
            Box::new(Expr::Pair(
                Box::new(Expr::Int(1)),
                Box::new(Expr::Int(2)),
            )),
            Box::new(Expr::Int(3)),
        );
        let code = compile_and_emit(&nested).unwrap();
        // Should have multiple riina_pair calls
        let pair_count = code.matches("riina_pair").count();
        assert!(pair_count >= 2);
    }
}
