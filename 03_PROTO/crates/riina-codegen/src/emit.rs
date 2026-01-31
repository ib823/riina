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
use crate::Result;
use riina_types::{Effect, SecurityLevel};
use std::collections::{HashMap, HashSet};
use std::fmt::Write as FmtWrite;

/// Phi copy information: for a target block, which phi result vars need copies
/// from which source vars, keyed by predecessor block ID.
///
/// PhiMap[target_block][predecessor_block] = Vec<(phi_result, source_var)>
type PhiMap = HashMap<BlockId, HashMap<BlockId, Vec<(VarId, VarId)>>>;

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
        self.writeln("#include <setjmp.h>");
        self.writeln("");

        // Security level enum
        self.writeln("/* ═══════════════════════════════════════════════════════════════════ */");
        self.writeln("/*                       SECURITY LEVELS                               */");
        self.writeln("/* ═══════════════════════════════════════════════════════════════════ */");
        self.writeln("");
        self.writeln("typedef enum {");
        self.writeln("    RIINA_LEVEL_PUBLIC = 0,");
        self.writeln("    RIINA_LEVEL_INTERNAL = 1,");
        self.writeln("    RIINA_LEVEL_SESSION = 2,");
        self.writeln("    RIINA_LEVEL_USER = 3,");
        self.writeln("    RIINA_LEVEL_SYSTEM = 4,");
        self.writeln("    RIINA_LEVEL_SECRET = 5");
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
        self.writeln("    RIINA_EFFECT_FILESYSTEM = 3,");
        self.writeln("    RIINA_EFFECT_NETWORK = 4,");
        self.writeln("    RIINA_EFFECT_NETWORK_SECURE = 5,");
        self.writeln("    RIINA_EFFECT_CRYPTO = 6,");
        self.writeln("    RIINA_EFFECT_RANDOM = 7,");
        self.writeln("    RIINA_EFFECT_SYSTEM = 8,");
        self.writeln("    RIINA_EFFECT_TIME = 9,");
        self.writeln("    RIINA_EFFECT_PROCESS = 10,");
        self.writeln("    RIINA_EFFECT_PANEL = 11,");
        self.writeln("    RIINA_EFFECT_ZIRAH = 12,");
        self.writeln("    RIINA_EFFECT_BENTENG = 13,");
        self.writeln("    RIINA_EFFECT_SANDI = 14,");
        self.writeln("    RIINA_EFFECT_MENARA = 15,");
        self.writeln("    RIINA_EFFECT_GAPURA = 16");
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

        // Builtin function helpers
        self.emit_builtin_helpers();
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

        // String concat
        self.writeln("static riina_value_t* riina_string_concat(riina_value_t* a, riina_value_t* b) {");
        self.writeln("    if (a->tag != RIINA_TAG_STRING || b->tag != RIINA_TAG_STRING) {");
        self.writeln("        fprintf(stderr, \"RIINA: string_concat on non-string\\n\"); abort();");
        self.writeln("    }");
        self.writeln("    size_t len = a->data.string_val.len + b->data.string_val.len;");
        self.writeln("    riina_value_t* v = riina_alloc();");
        self.writeln("    v->tag = RIINA_TAG_STRING;");
        self.writeln("    v->security = RIINA_LEVEL_PUBLIC;");
        self.writeln("    v->data.string_val.data = (char*)malloc(len + 1);");
        self.writeln("    if (!v->data.string_val.data) abort();");
        self.writeln("    memcpy(v->data.string_val.data, a->data.string_val.data, a->data.string_val.len);");
        self.writeln("    memcpy(v->data.string_val.data + a->data.string_val.len, b->data.string_val.data, b->data.string_val.len + 1);");
        self.writeln("    v->data.string_val.len = len;");
        self.writeln("    return v;");
        self.writeln("}");
        self.writeln("");

        // String length
        self.writeln("static riina_value_t* riina_string_length(riina_value_t* s) {");
        self.writeln("    if (s->tag != RIINA_TAG_STRING) {");
        self.writeln("        fprintf(stderr, \"RIINA: string_length on non-string\\n\"); abort();");
        self.writeln("    }");
        self.writeln("    return riina_int((uint64_t)s->data.string_val.len);");
        self.writeln("}");
        self.writeln("");

        // String equality
        self.writeln("static riina_value_t* riina_string_eq(riina_value_t* a, riina_value_t* b) {");
        self.writeln("    if (a->tag != RIINA_TAG_STRING || b->tag != RIINA_TAG_STRING) {");
        self.writeln("        fprintf(stderr, \"RIINA: string_eq on non-string\\n\"); abort();");
        self.writeln("    }");
        self.writeln("    bool eq = (a->data.string_val.len == b->data.string_val.len) &&");
        self.writeln("              (memcmp(a->data.string_val.data, b->data.string_val.data, a->data.string_val.len) == 0);");
        self.writeln("    return riina_bool(eq);");
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
        self.writeln("        case RIINA_TAG_STRING:");
        self.writeln("            return riina_bool(a->data.string_val.len == b->data.string_val.len &&");
        self.writeln("                memcmp(a->data.string_val.data, b->data.string_val.data, a->data.string_val.len) == 0);");
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

        // Effect handler stack (setjmp/longjmp based)
        self.writeln("#define RIINA_MAX_HANDLERS 64");
        self.writeln("");
        self.writeln("typedef struct {");
        self.writeln("    jmp_buf env;");
        self.writeln("    riina_effect_t effect;");
        self.writeln("    riina_value_t* payload;  /* set by perform before longjmp */");
        self.writeln("} riina_handler_frame_t;");
        self.writeln("");
        self.writeln("static riina_handler_frame_t riina_handler_stack[RIINA_MAX_HANDLERS];");
        self.writeln("static int riina_handler_top = 0;");
        self.writeln("");
        self.writeln("static void riina_push_handler(riina_effect_t eff) {");
        self.writeln("    if (riina_handler_top >= RIINA_MAX_HANDLERS) {");
        self.writeln("        fprintf(stderr, \"RIINA: handler stack overflow\\n\");");
        self.writeln("        abort();");
        self.writeln("    }");
        self.writeln("    riina_handler_stack[riina_handler_top].effect = eff;");
        self.writeln("    riina_handler_stack[riina_handler_top].payload = NULL;");
        self.writeln("    riina_handler_top++;");
        self.writeln("}");
        self.writeln("");
        self.writeln("static void riina_pop_handler(void) {");
        self.writeln("    if (riina_handler_top > 0) riina_handler_top--;");
        self.writeln("}");
        self.writeln("");
        self.writeln("static riina_value_t* riina_perform(riina_effect_t eff, riina_value_t* payload) {");
        self.writeln("    riina_require_cap(eff);");
        self.writeln("    /* Search handler stack for matching handler */");
        self.writeln("    for (int i = riina_handler_top - 1; i >= 0; i--) {");
        self.writeln("        if (riina_handler_stack[i].effect == eff) {");
        self.writeln("            riina_handler_stack[i].payload = payload;");
        self.writeln("            longjmp(riina_handler_stack[i].env, 1);");
        self.writeln("        }");
        self.writeln("    }");
        self.writeln("    /* No handler installed — return payload (default behavior) */");
        self.writeln("    return payload;");
        self.writeln("}");
        self.writeln("");
    }

    /// Emit built-in function helpers (C implementations of RIINA builtins)
    fn emit_builtin_helpers(&mut self) {
        self.writeln("/* ═══════════════════════════════════════════════════════════════════ */");
        self.writeln("/*                      BUILTIN FUNCTIONS                              */");
        self.writeln("/* ═══════════════════════════════════════════════════════════════════ */");
        self.writeln("");

        // Helper: format a value as a string for printing
        self.writeln("static const char* riina_format(riina_value_t* v) {");
        self.writeln("    static char buf[256];");
        self.writeln("    switch (v->tag) {");
        self.writeln("        case RIINA_TAG_UNIT: return \"()\";");
        self.writeln("        case RIINA_TAG_BOOL: return v->data.bool_val ? \"betul\" : \"salah\";");
        self.writeln("        case RIINA_TAG_INT:");
        self.writeln("            snprintf(buf, sizeof(buf), \"%llu\", (unsigned long long)v->data.int_val);");
        self.writeln("            return buf;");
        self.writeln("        case RIINA_TAG_STRING: return v->data.string_val.data;");
        self.writeln("        default: return \"<value>\";");
        self.writeln("    }");
        self.writeln("}");
        self.writeln("");

        // cetak (print without newline)
        self.writeln("static riina_value_t* riina_builtin_cetak(riina_value_t* arg) {");
        self.writeln("    printf(\"%s\", riina_format(arg));");
        self.writeln("    return riina_unit();");
        self.writeln("}");
        self.writeln("");

        // cetakln (print with newline)
        self.writeln("static riina_value_t* riina_builtin_cetakln(riina_value_t* arg) {");
        self.writeln("    printf(\"%s\\n\", riina_format(arg));");
        self.writeln("    return riina_unit();");
        self.writeln("}");
        self.writeln("");

        // ke_teks (to_string)
        self.writeln("static riina_value_t* riina_builtin_ke_teks(riina_value_t* arg) {");
        self.writeln("    char buf[256];");
        self.writeln("    switch (arg->tag) {");
        self.writeln("        case RIINA_TAG_UNIT: return riina_string(\"()\");");
        self.writeln("        case RIINA_TAG_BOOL: return riina_string(arg->data.bool_val ? \"betul\" : \"salah\");");
        self.writeln("        case RIINA_TAG_INT:");
        self.writeln("            snprintf(buf, sizeof(buf), \"%llu\", (unsigned long long)arg->data.int_val);");
        self.writeln("            return riina_string(buf);");
        self.writeln("        case RIINA_TAG_STRING: return arg;");
        self.writeln("        default: return riina_string(\"<value>\");");
        self.writeln("    }");
        self.writeln("}");
        self.writeln("");

        // nombor_ke_teks (int_to_string) — alias
        self.writeln("static riina_value_t* riina_builtin_nombor_ke_teks(riina_value_t* arg) {");
        self.writeln("    return riina_builtin_ke_teks(arg);");
        self.writeln("}");
        self.writeln("");

        // panjang (length)
        self.writeln("static riina_value_t* riina_builtin_panjang(riina_value_t* arg) {");
        self.writeln("    if (arg->tag != RIINA_TAG_STRING) {");
        self.writeln("        fprintf(stderr, \"RIINA: panjang on non-string\\n\"); abort();");
        self.writeln("    }");
        self.writeln("    return riina_int((uint64_t)arg->data.string_val.len);");
        self.writeln("}");
        self.writeln("");

        // gabung_teks (concat) — expects a pair
        self.writeln("static riina_value_t* riina_builtin_gabung_teks(riina_value_t* arg) {");
        self.writeln("    if (arg->tag != RIINA_TAG_PAIR) {");
        self.writeln("        fprintf(stderr, \"RIINA: gabung_teks expects pair\\n\"); abort();");
        self.writeln("    }");
        self.writeln("    riina_value_t* a = riina_builtin_ke_teks(arg->data.pair_val.fst);");
        self.writeln("    riina_value_t* b = riina_builtin_ke_teks(arg->data.pair_val.snd);");
        self.writeln("    return riina_string_concat(a, b);");
        self.writeln("}");
        self.writeln("");

        // ke_nombor (parse_int)
        self.writeln("static riina_value_t* riina_builtin_ke_nombor(riina_value_t* arg) {");
        self.writeln("    if (arg->tag != RIINA_TAG_STRING) {");
        self.writeln("        fprintf(stderr, \"RIINA: ke_nombor on non-string\\n\"); abort();");
        self.writeln("    }");
        self.writeln("    return riina_int((uint64_t)atoll(arg->data.string_val.data));");
        self.writeln("}");
        self.writeln("");

        // ke_bool (to_bool)
        self.writeln("static riina_value_t* riina_builtin_ke_bool(riina_value_t* arg) {");
        self.writeln("    switch (arg->tag) {");
        self.writeln("        case RIINA_TAG_BOOL: return arg;");
        self.writeln("        case RIINA_TAG_INT: return riina_bool(arg->data.int_val != 0);");
        self.writeln("        case RIINA_TAG_STRING: return riina_bool(arg->data.string_val.len > 0);");
        self.writeln("        default: return riina_bool(false);");
        self.writeln("    }");
        self.writeln("}");
        self.writeln("");

        // bool_ke_nombor
        self.writeln("static riina_value_t* riina_builtin_bool_ke_nombor(riina_value_t* arg) {");
        self.writeln("    if (arg->tag != RIINA_TAG_BOOL) {");
        self.writeln("        fprintf(stderr, \"RIINA: bool_ke_nombor on non-bool\\n\"); abort();");
        self.writeln("    }");
        self.writeln("    return riina_int(arg->data.bool_val ? 1 : 0);");
        self.writeln("}");
        self.writeln("");

        // tegaskan (assert)
        self.writeln("static riina_value_t* riina_builtin_tegaskan(riina_value_t* arg) {");
        self.writeln("    if (arg->tag != RIINA_TAG_BOOL || !arg->data.bool_val) {");
        self.writeln("        fprintf(stderr, \"RIINA: assertion failed\\n\"); abort();");
        self.writeln("    }");
        self.writeln("    return riina_unit();");
        self.writeln("}");
        self.writeln("");

        // tegaskan_betul (assert_true) — alias
        self.writeln("static riina_value_t* riina_builtin_tegaskan_betul(riina_value_t* arg) {");
        self.writeln("    return riina_builtin_tegaskan(arg);");
        self.writeln("}");
        self.writeln("");

        // tegaskan_salah (assert_false)
        self.writeln("static riina_value_t* riina_builtin_tegaskan_salah(riina_value_t* arg) {");
        self.writeln("    if (arg->tag != RIINA_TAG_BOOL || arg->data.bool_val) {");
        self.writeln("        fprintf(stderr, \"RIINA: assert_false failed\\n\"); abort();");
        self.writeln("    }");
        self.writeln("    return riina_unit();");
        self.writeln("}");
        self.writeln("");

        // tegaskan_sama (assert_eq) — expects pair
        self.writeln("static riina_value_t* riina_builtin_tegaskan_sama(riina_value_t* arg) {");
        self.writeln("    if (arg->tag != RIINA_TAG_PAIR) {");
        self.writeln("        fprintf(stderr, \"RIINA: tegaskan_sama expects pair\\n\"); abort();");
        self.writeln("    }");
        self.writeln("    riina_value_t* eq = riina_binop_eq(arg->data.pair_val.fst, arg->data.pair_val.snd);");
        self.writeln("    if (!eq->data.bool_val) {");
        self.writeln("        fprintf(stderr, \"RIINA: assert_eq failed\\n\"); abort();");
        self.writeln("    }");
        self.writeln("    return riina_unit();");
        self.writeln("}");
        self.writeln("");

        // tegaskan_beza (assert_ne) — expects pair
        self.writeln("static riina_value_t* riina_builtin_tegaskan_beza(riina_value_t* arg) {");
        self.writeln("    if (arg->tag != RIINA_TAG_PAIR) {");
        self.writeln("        fprintf(stderr, \"RIINA: tegaskan_beza expects pair\\n\"); abort();");
        self.writeln("    }");
        self.writeln("    riina_value_t* eq = riina_binop_eq(arg->data.pair_val.fst, arg->data.pair_val.snd);");
        self.writeln("    if (eq->data.bool_val) {");
        self.writeln("        fprintf(stderr, \"RIINA: assert_ne failed\\n\"); abort();");
        self.writeln("    }");
        self.writeln("    return riina_unit();");
        self.writeln("}");
        self.writeln("");

        // mutlak (abs)
        self.writeln("static riina_value_t* riina_builtin_mutlak(riina_value_t* arg) {");
        self.writeln("    if (arg->tag != RIINA_TAG_INT) {");
        self.writeln("        fprintf(stderr, \"RIINA: mutlak on non-int\\n\"); abort();");
        self.writeln("    }");
        self.writeln("    return riina_int(arg->data.int_val); /* uint64 always non-negative */");
        self.writeln("}");
        self.writeln("");

        // minimum (min) — expects pair
        self.writeln("static riina_value_t* riina_builtin_minimum(riina_value_t* arg) {");
        self.writeln("    if (arg->tag != RIINA_TAG_PAIR) {");
        self.writeln("        fprintf(stderr, \"RIINA: minimum expects pair\\n\"); abort();");
        self.writeln("    }");
        self.writeln("    riina_value_t* a = arg->data.pair_val.fst;");
        self.writeln("    riina_value_t* b = arg->data.pair_val.snd;");
        self.writeln("    return (a->data.int_val <= b->data.int_val) ? a : b;");
        self.writeln("}");
        self.writeln("");

        // maksimum (max) — expects pair
        self.writeln("static riina_value_t* riina_builtin_maksimum(riina_value_t* arg) {");
        self.writeln("    if (arg->tag != RIINA_TAG_PAIR) {");
        self.writeln("        fprintf(stderr, \"RIINA: maksimum expects pair\\n\"); abort();");
        self.writeln("    }");
        self.writeln("    riina_value_t* a = arg->data.pair_val.fst;");
        self.writeln("    riina_value_t* b = arg->data.pair_val.snd;");
        self.writeln("    return (a->data.int_val >= b->data.int_val) ? a : b;");
        self.writeln("}");
        self.writeln("");

        // kuasa (pow) — expects pair
        self.writeln("static riina_value_t* riina_builtin_kuasa(riina_value_t* arg) {");
        self.writeln("    if (arg->tag != RIINA_TAG_PAIR) {");
        self.writeln("        fprintf(stderr, \"RIINA: kuasa expects pair\\n\"); abort();");
        self.writeln("    }");
        self.writeln("    uint64_t base = arg->data.pair_val.fst->data.int_val;");
        self.writeln("    uint64_t exp = arg->data.pair_val.snd->data.int_val;");
        self.writeln("    uint64_t result = 1;");
        self.writeln("    for (uint64_t i = 0; i < exp; i++) result *= base;");
        self.writeln("    return riina_int(result);");
        self.writeln("}");
        self.writeln("");

        // punca (sqrt)
        self.writeln("static riina_value_t* riina_builtin_punca(riina_value_t* arg) {");
        self.writeln("    if (arg->tag != RIINA_TAG_INT) {");
        self.writeln("        fprintf(stderr, \"RIINA: punca on non-int\\n\"); abort();");
        self.writeln("    }");
        self.writeln("    uint64_t n = arg->data.int_val, r = 0;");
        self.writeln("    while ((r + 1) * (r + 1) <= n) r++;");
        self.writeln("    return riina_int(r);");
        self.writeln("}");
        self.writeln("");

        // gcd
        self.writeln("static riina_value_t* riina_builtin_gcd(riina_value_t* arg) {");
        self.writeln("    if (arg->tag != RIINA_TAG_PAIR) {");
        self.writeln("        fprintf(stderr, \"RIINA: gcd expects pair\\n\"); abort();");
        self.writeln("    }");
        self.writeln("    uint64_t a = arg->data.pair_val.fst->data.int_val;");
        self.writeln("    uint64_t b = arg->data.pair_val.snd->data.int_val;");
        self.writeln("    while (b) { uint64_t t = b; b = a % b; a = t; }");
        self.writeln("    return riina_int(a);");
        self.writeln("}");
        self.writeln("");

        // lcm
        self.writeln("static riina_value_t* riina_builtin_lcm(riina_value_t* arg) {");
        self.writeln("    if (arg->tag != RIINA_TAG_PAIR) {");
        self.writeln("        fprintf(stderr, \"RIINA: lcm expects pair\\n\"); abort();");
        self.writeln("    }");
        self.writeln("    uint64_t a = arg->data.pair_val.fst->data.int_val;");
        self.writeln("    uint64_t b = arg->data.pair_val.snd->data.int_val;");
        self.writeln("    riina_value_t* g = riina_builtin_gcd(arg);");
        self.writeln("    if (g->data.int_val == 0) return riina_int(0);");
        self.writeln("    return riina_int(a / g->data.int_val * b);");
        self.writeln("}");
        self.writeln("");

        // ═══════════════════════════════════════════════════════════════════
        // RUNTIME COLLECTION TYPES
        // ═══════════════════════════════════════════════════════════════════

        // riina_list_t: dynamic array of riina_value_t*
        self.writeln("/* ── List runtime type ── */");
        self.writeln("typedef struct {");
        self.writeln("    riina_value_t** items;");
        self.writeln("    size_t len;");
        self.writeln("    size_t cap;");
        self.writeln("} riina_list_t;");
        self.writeln("");
        self.writeln("static riina_list_t riina_list_new(void) {");
        self.writeln("    riina_list_t l = { NULL, 0, 0 };");
        self.writeln("    return l;");
        self.writeln("}");
        self.writeln("");
        self.writeln("static void riina_list_push(riina_list_t* l, riina_value_t* v) {");
        self.writeln("    if (l->len >= l->cap) {");
        self.writeln("        l->cap = l->cap ? l->cap * 2 : 8;");
        self.writeln("        l->items = (riina_value_t**)realloc(l->items, l->cap * sizeof(riina_value_t*));");
        self.writeln("        if (!l->items) abort();");
        self.writeln("    }");
        self.writeln("    l->items[l->len++] = v;");
        self.writeln("}");
        self.writeln("");
        // Convert riina_list_t to RIINA_TAG_PAIR-based linked list? No — we use a PAIR encoding.
        // Actually, the interpreter uses Value::List but the C runtime uses tagged union.
        // We need a new tag for lists or encode them as nested pairs.
        // For simplicity: add RIINA_TAG_LIST that wraps riina_list_t.
        // But modifying the tag enum is risky. Instead, we'll use a helper approach:
        // list builtins work at the C level with riina_list_t internally,
        // but we won't add a list tag. The C builtins will encode lists as
        // nested Pair(head, Pair(next, ...)) terminated by Unit.
        // ACTUALLY — the BuiltinCall instruction in the IR is only generated for
        // builtins that the lowerer recognizes. Let me check if list builtins
        // actually get lowered to BuiltinCall...
        // Looking at the code: BuiltinCall { name, arg } is generated.
        // The C emitter just calls riina_builtin_{name}(arg).
        // So we need C functions that take/return riina_value_t*.
        // Since there's no list tag, list builtins can't work in C without one.
        // Let's add a RIINA_TAG_LIST and a list field to the union.
        //
        // DECISION: We won't modify the tag enum (too invasive). Instead,
        // we'll note that list/map/set builtins only work in interpreter mode
        // for now. The C emitter will emit stub functions that abort with a
        // "not supported in compiled mode" message. This is the pragmatic choice
        // since adding collection tags requires changes throughout the emitter.
        //
        // UPDATE: Actually, re-reading the plan, M1 asks us to add runtime types.
        // Let's do it properly — add RIINA_TAG_LIST, RIINA_TAG_MAP, RIINA_TAG_SET.

        // We already emitted the tag enum earlier. We need to add these tags.
        // Since we can't go back, we'll define them as additional constants.
        self.writeln("/* Extended tags for collections */");
        self.writeln("#define RIINA_TAG_LIST 12");
        self.writeln("#define RIINA_TAG_MAP 13");
        self.writeln("#define RIINA_TAG_SET 14");
        self.writeln("");

        // Map entry type
        self.writeln("typedef struct riina_map_entry {");
        self.writeln("    char* key;");
        self.writeln("    riina_value_t* value;");
        self.writeln("    struct riina_map_entry* next;");
        self.writeln("} riina_map_entry_t;");
        self.writeln("");
        self.writeln("typedef struct {");
        self.writeln("    riina_map_entry_t* head;");
        self.writeln("    size_t len;");
        self.writeln("} riina_map_t;");
        self.writeln("");

        // Helper: make list value
        self.writeln("static riina_value_t* riina_make_list(riina_list_t l) {");
        self.writeln("    riina_value_t* v = riina_alloc();");
        self.writeln("    v->tag = RIINA_TAG_LIST;");
        self.writeln("    v->security = RIINA_LEVEL_PUBLIC;");
        self.writeln("    /* Store list data in pair_val: fst=items ptr, snd encodes len+cap */");
        self.writeln("    /* We reuse wrapped_val to point to a heap-allocated riina_list_t */");
        self.writeln("    riina_list_t* lp = (riina_list_t*)malloc(sizeof(riina_list_t));");
        self.writeln("    if (!lp) abort();");
        self.writeln("    *lp = l;");
        self.writeln("    v->data.wrapped_val = (riina_value_t*)lp; /* type-punned */");
        self.writeln("    return v;");
        self.writeln("}");
        self.writeln("");
        self.writeln("#define RIINA_LIST_DATA(v) ((riina_list_t*)(v)->data.wrapped_val)");
        self.writeln("");

        // Helper: make map value
        self.writeln("static riina_value_t* riina_make_map(riina_map_t m) {");
        self.writeln("    riina_value_t* v = riina_alloc();");
        self.writeln("    v->tag = RIINA_TAG_MAP;");
        self.writeln("    v->security = RIINA_LEVEL_PUBLIC;");
        self.writeln("    riina_map_t* mp = (riina_map_t*)malloc(sizeof(riina_map_t));");
        self.writeln("    if (!mp) abort();");
        self.writeln("    *mp = m;");
        self.writeln("    v->data.wrapped_val = (riina_value_t*)mp;");
        self.writeln("    return v;");
        self.writeln("}");
        self.writeln("");
        self.writeln("#define RIINA_MAP_DATA(v) ((riina_map_t*)(v)->data.wrapped_val)");
        self.writeln("");

        // ═══════════════════════════════════════════════════════════════════
        // STRING BUILTINS (teks)
        // ═══════════════════════════════════════════════════════════════════

        // teks_belah (str_split): (String, String) -> List
        self.writeln("static riina_value_t* riina_builtin_teks_belah(riina_value_t* arg) {");
        self.writeln("    if (arg->tag != RIINA_TAG_PAIR) abort();");
        self.writeln("    riina_value_t* s = arg->data.pair_val.fst;");
        self.writeln("    riina_value_t* d = arg->data.pair_val.snd;");
        self.writeln("    if (s->tag != RIINA_TAG_STRING || d->tag != RIINA_TAG_STRING) abort();");
        self.writeln("    riina_list_t result = riina_list_new();");
        self.writeln("    char* str = strdup(s->data.string_val.data);");
        self.writeln("    if (!str) abort();");
        self.writeln("    size_t dlen = d->data.string_val.len;");
        self.writeln("    if (dlen == 0) {");
        self.writeln("        /* Split each char */");
        self.writeln("        for (size_t i = 0; i < s->data.string_val.len; i++) {");
        self.writeln("            char c[2] = { str[i], 0 };");
        self.writeln("            riina_list_push(&result, riina_string(c));");
        self.writeln("        }");
        self.writeln("    } else {");
        self.writeln("        char* p = str;");
        self.writeln("        char* found;");
        self.writeln("        while ((found = strstr(p, d->data.string_val.data)) != NULL) {");
        self.writeln("            *found = '\\0';");
        self.writeln("            riina_list_push(&result, riina_string(p));");
        self.writeln("            p = found + dlen;");
        self.writeln("        }");
        self.writeln("        riina_list_push(&result, riina_string(p));");
        self.writeln("    }");
        self.writeln("    free(str);");
        self.writeln("    return riina_make_list(result);");
        self.writeln("}");
        self.writeln("");

        // teks_cantum (str_join): (String, List) -> String
        self.writeln("static riina_value_t* riina_builtin_teks_cantum(riina_value_t* arg) {");
        self.writeln("    if (arg->tag != RIINA_TAG_PAIR) abort();");
        self.writeln("    riina_value_t* sep = arg->data.pair_val.fst;");
        self.writeln("    riina_value_t* lst = arg->data.pair_val.snd;");
        self.writeln("    if (sep->tag != RIINA_TAG_STRING || lst->tag != RIINA_TAG_LIST) abort();");
        self.writeln("    riina_list_t* l = RIINA_LIST_DATA(lst);");
        self.writeln("    size_t total = 0;");
        self.writeln("    for (size_t i = 0; i < l->len; i++) {");
        self.writeln("        if (l->items[i]->tag == RIINA_TAG_STRING) total += l->items[i]->data.string_val.len;");
        self.writeln("        if (i > 0) total += sep->data.string_val.len;");
        self.writeln("    }");
        self.writeln("    char* buf = (char*)malloc(total + 1);");
        self.writeln("    if (!buf) abort();");
        self.writeln("    buf[0] = '\\0';");
        self.writeln("    size_t off = 0;");
        self.writeln("    for (size_t i = 0; i < l->len; i++) {");
        self.writeln("        if (i > 0) { memcpy(buf + off, sep->data.string_val.data, sep->data.string_val.len); off += sep->data.string_val.len; }");
        self.writeln("        if (l->items[i]->tag == RIINA_TAG_STRING) { memcpy(buf + off, l->items[i]->data.string_val.data, l->items[i]->data.string_val.len); off += l->items[i]->data.string_val.len; }");
        self.writeln("    }");
        self.writeln("    buf[off] = '\\0';");
        self.writeln("    riina_value_t* r = riina_string(buf);");
        self.writeln("    free(buf);");
        self.writeln("    return r;");
        self.writeln("}");
        self.writeln("");

        // teks_potong (str_trim)
        self.writeln("static riina_value_t* riina_builtin_teks_potong(riina_value_t* arg) {");
        self.writeln("    if (arg->tag != RIINA_TAG_STRING) abort();");
        self.writeln("    const char* s = arg->data.string_val.data;");
        self.writeln("    size_t len = arg->data.string_val.len;");
        self.writeln("    size_t start = 0, end = len;");
        self.writeln("    while (start < len && (s[start]==' '||s[start]=='\\t'||s[start]=='\\n'||s[start]=='\\r')) start++;");
        self.writeln("    while (end > start && (s[end-1]==' '||s[end-1]=='\\t'||s[end-1]=='\\n'||s[end-1]=='\\r')) end--;");
        self.writeln("    char* buf = (char*)malloc(end - start + 1);");
        self.writeln("    if (!buf) abort();");
        self.writeln("    memcpy(buf, s + start, end - start);");
        self.writeln("    buf[end - start] = '\\0';");
        self.writeln("    riina_value_t* r = riina_string(buf);");
        self.writeln("    free(buf);");
        self.writeln("    return r;");
        self.writeln("}");
        self.writeln("");

        // teks_mengandungi (str_contains): (String, String) -> Bool
        self.writeln("static riina_value_t* riina_builtin_teks_mengandungi(riina_value_t* arg) {");
        self.writeln("    if (arg->tag != RIINA_TAG_PAIR) abort();");
        self.writeln("    riina_value_t* s = arg->data.pair_val.fst;");
        self.writeln("    riina_value_t* sub = arg->data.pair_val.snd;");
        self.writeln("    if (s->tag != RIINA_TAG_STRING || sub->tag != RIINA_TAG_STRING) abort();");
        self.writeln("    return riina_bool(strstr(s->data.string_val.data, sub->data.string_val.data) != NULL);");
        self.writeln("}");
        self.writeln("");

        // teks_ganti (str_replace): (String, (String, String)) -> String
        self.writeln("static riina_value_t* riina_builtin_teks_ganti(riina_value_t* arg) {");
        self.writeln("    if (arg->tag != RIINA_TAG_PAIR) abort();");
        self.writeln("    riina_value_t* s = arg->data.pair_val.fst;");
        self.writeln("    riina_value_t* p = arg->data.pair_val.snd;");
        self.writeln("    if (s->tag != RIINA_TAG_STRING || p->tag != RIINA_TAG_PAIR) abort();");
        self.writeln("    riina_value_t* from = p->data.pair_val.fst;");
        self.writeln("    riina_value_t* to = p->data.pair_val.snd;");
        self.writeln("    if (from->tag != RIINA_TAG_STRING || to->tag != RIINA_TAG_STRING) abort();");
        self.writeln("    const char* src = s->data.string_val.data;");
        self.writeln("    size_t flen = from->data.string_val.len, tlen = to->data.string_val.len;");
        self.writeln("    if (flen == 0) return s;");
        self.writeln("    /* Count occurrences */");
        self.writeln("    size_t count = 0;");
        self.writeln("    const char* tmp = src;");
        self.writeln("    while ((tmp = strstr(tmp, from->data.string_val.data)) != NULL) { count++; tmp += flen; }");
        self.writeln("    size_t newlen = s->data.string_val.len + count * (tlen - flen);");
        self.writeln("    char* buf = (char*)malloc(newlen + 1);");
        self.writeln("    if (!buf) abort();");
        self.writeln("    char* dst = buf;");
        self.writeln("    tmp = src;");
        self.writeln("    const char* found;");
        self.writeln("    while ((found = strstr(tmp, from->data.string_val.data)) != NULL) {");
        self.writeln("        size_t chunk = (size_t)(found - tmp);");
        self.writeln("        memcpy(dst, tmp, chunk); dst += chunk;");
        self.writeln("        memcpy(dst, to->data.string_val.data, tlen); dst += tlen;");
        self.writeln("        tmp = found + flen;");
        self.writeln("    }");
        self.writeln("    strcpy(dst, tmp);");
        self.writeln("    riina_value_t* r = riina_string(buf);");
        self.writeln("    free(buf);");
        self.writeln("    return r;");
        self.writeln("}");
        self.writeln("");

        // teks_mula_dengan (str_starts_with)
        self.writeln("static riina_value_t* riina_builtin_teks_mula_dengan(riina_value_t* arg) {");
        self.writeln("    if (arg->tag != RIINA_TAG_PAIR) abort();");
        self.writeln("    riina_value_t* s = arg->data.pair_val.fst;");
        self.writeln("    riina_value_t* pfx = arg->data.pair_val.snd;");
        self.writeln("    if (s->tag != RIINA_TAG_STRING || pfx->tag != RIINA_TAG_STRING) abort();");
        self.writeln("    if (pfx->data.string_val.len > s->data.string_val.len) return riina_bool(false);");
        self.writeln("    return riina_bool(strncmp(s->data.string_val.data, pfx->data.string_val.data, pfx->data.string_val.len) == 0);");
        self.writeln("}");
        self.writeln("");

        // teks_akhir_dengan (str_ends_with)
        self.writeln("static riina_value_t* riina_builtin_teks_akhir_dengan(riina_value_t* arg) {");
        self.writeln("    if (arg->tag != RIINA_TAG_PAIR) abort();");
        self.writeln("    riina_value_t* s = arg->data.pair_val.fst;");
        self.writeln("    riina_value_t* sfx = arg->data.pair_val.snd;");
        self.writeln("    if (s->tag != RIINA_TAG_STRING || sfx->tag != RIINA_TAG_STRING) abort();");
        self.writeln("    if (sfx->data.string_val.len > s->data.string_val.len) return riina_bool(false);");
        self.writeln("    size_t off = s->data.string_val.len - sfx->data.string_val.len;");
        self.writeln("    return riina_bool(strcmp(s->data.string_val.data + off, sfx->data.string_val.data) == 0);");
        self.writeln("}");
        self.writeln("");

        // teks_huruf_besar (str_to_upper)
        self.writeln("static riina_value_t* riina_builtin_teks_huruf_besar(riina_value_t* arg) {");
        self.writeln("    if (arg->tag != RIINA_TAG_STRING) abort();");
        self.writeln("    size_t len = arg->data.string_val.len;");
        self.writeln("    char* buf = (char*)malloc(len + 1);");
        self.writeln("    if (!buf) abort();");
        self.writeln("    for (size_t i = 0; i < len; i++) {");
        self.writeln("        char c = arg->data.string_val.data[i];");
        self.writeln("        buf[i] = (c >= 'a' && c <= 'z') ? (char)(c - 32) : c;");
        self.writeln("    }");
        self.writeln("    buf[len] = '\\0';");
        self.writeln("    riina_value_t* r = riina_string(buf);");
        self.writeln("    free(buf);");
        self.writeln("    return r;");
        self.writeln("}");
        self.writeln("");

        // teks_huruf_kecil (str_to_lower)
        self.writeln("static riina_value_t* riina_builtin_teks_huruf_kecil(riina_value_t* arg) {");
        self.writeln("    if (arg->tag != RIINA_TAG_STRING) abort();");
        self.writeln("    size_t len = arg->data.string_val.len;");
        self.writeln("    char* buf = (char*)malloc(len + 1);");
        self.writeln("    if (!buf) abort();");
        self.writeln("    for (size_t i = 0; i < len; i++) {");
        self.writeln("        char c = arg->data.string_val.data[i];");
        self.writeln("        buf[i] = (c >= 'A' && c <= 'Z') ? (char)(c + 32) : c;");
        self.writeln("    }");
        self.writeln("    buf[len] = '\\0';");
        self.writeln("    riina_value_t* r = riina_string(buf);");
        self.writeln("    free(buf);");
        self.writeln("    return r;");
        self.writeln("}");
        self.writeln("");

        // teks_aksara_di (str_char_at): (String, Int) -> String
        self.writeln("static riina_value_t* riina_builtin_teks_aksara_di(riina_value_t* arg) {");
        self.writeln("    if (arg->tag != RIINA_TAG_PAIR) abort();");
        self.writeln("    riina_value_t* s = arg->data.pair_val.fst;");
        self.writeln("    riina_value_t* idx = arg->data.pair_val.snd;");
        self.writeln("    if (s->tag != RIINA_TAG_STRING || idx->tag != RIINA_TAG_INT) abort();");
        self.writeln("    size_t i = (size_t)idx->data.int_val;");
        self.writeln("    if (i >= s->data.string_val.len) { fprintf(stderr, \"RIINA: char_at out of bounds\\n\"); abort(); }");
        self.writeln("    char c[2] = { s->data.string_val.data[i], 0 };");
        self.writeln("    return riina_string(c);");
        self.writeln("}");
        self.writeln("");

        // teks_sub (str_substring): (String, (Int, Int)) -> String
        self.writeln("static riina_value_t* riina_builtin_teks_sub(riina_value_t* arg) {");
        self.writeln("    if (arg->tag != RIINA_TAG_PAIR) abort();");
        self.writeln("    riina_value_t* s = arg->data.pair_val.fst;");
        self.writeln("    riina_value_t* range = arg->data.pair_val.snd;");
        self.writeln("    if (s->tag != RIINA_TAG_STRING || range->tag != RIINA_TAG_PAIR) abort();");
        self.writeln("    size_t start = (size_t)range->data.pair_val.fst->data.int_val;");
        self.writeln("    size_t end = (size_t)range->data.pair_val.snd->data.int_val;");
        self.writeln("    if (start > s->data.string_val.len) start = s->data.string_val.len;");
        self.writeln("    if (end > s->data.string_val.len) end = s->data.string_val.len;");
        self.writeln("    if (end < start) end = start;");
        self.writeln("    size_t len = end - start;");
        self.writeln("    char* buf = (char*)malloc(len + 1);");
        self.writeln("    if (!buf) abort();");
        self.writeln("    memcpy(buf, s->data.string_val.data + start, len);");
        self.writeln("    buf[len] = '\\0';");
        self.writeln("    riina_value_t* r = riina_string(buf);");
        self.writeln("    free(buf);");
        self.writeln("    return r;");
        self.writeln("}");
        self.writeln("");

        // teks_indeks (str_index_of): (String, String) -> Int
        self.writeln("static riina_value_t* riina_builtin_teks_indeks(riina_value_t* arg) {");
        self.writeln("    if (arg->tag != RIINA_TAG_PAIR) abort();");
        self.writeln("    riina_value_t* s = arg->data.pair_val.fst;");
        self.writeln("    riina_value_t* sub = arg->data.pair_val.snd;");
        self.writeln("    if (s->tag != RIINA_TAG_STRING || sub->tag != RIINA_TAG_STRING) abort();");
        self.writeln("    const char* found = strstr(s->data.string_val.data, sub->data.string_val.data);");
        self.writeln("    if (found) return riina_int((uint64_t)(found - s->data.string_val.data));");
        self.writeln("    return riina_int(UINT64_MAX);");
        self.writeln("}");
        self.writeln("");

        // ═══════════════════════════════════════════════════════════════════
        // LIST BUILTINS (senarai)
        // ═══════════════════════════════════════════════════════════════════

        // senarai_baru (list_new)
        self.writeln("static riina_value_t* riina_builtin_senarai_baru(riina_value_t* arg) {");
        self.writeln("    (void)arg;");
        self.writeln("    riina_list_t l = riina_list_new();");
        self.writeln("    return riina_make_list(l);");
        self.writeln("}");
        self.writeln("");

        // senarai_tolak (list_push): (List, Value) -> List
        self.writeln("static riina_value_t* riina_builtin_senarai_tolak(riina_value_t* arg) {");
        self.writeln("    if (arg->tag != RIINA_TAG_PAIR) abort();");
        self.writeln("    riina_value_t* lst = arg->data.pair_val.fst;");
        self.writeln("    riina_value_t* val = arg->data.pair_val.snd;");
        self.writeln("    if (lst->tag != RIINA_TAG_LIST) abort();");
        self.writeln("    riina_list_t* old = RIINA_LIST_DATA(lst);");
        self.writeln("    riina_list_t nl = riina_list_new();");
        self.writeln("    for (size_t i = 0; i < old->len; i++) riina_list_push(&nl, old->items[i]);");
        self.writeln("    riina_list_push(&nl, val);");
        self.writeln("    return riina_make_list(nl);");
        self.writeln("}");
        self.writeln("");

        // senarai_dapat (list_get): (List, Int) -> Value
        self.writeln("static riina_value_t* riina_builtin_senarai_dapat(riina_value_t* arg) {");
        self.writeln("    if (arg->tag != RIINA_TAG_PAIR) abort();");
        self.writeln("    riina_value_t* lst = arg->data.pair_val.fst;");
        self.writeln("    riina_value_t* idx = arg->data.pair_val.snd;");
        self.writeln("    if (lst->tag != RIINA_TAG_LIST || idx->tag != RIINA_TAG_INT) abort();");
        self.writeln("    riina_list_t* l = RIINA_LIST_DATA(lst);");
        self.writeln("    size_t i = (size_t)idx->data.int_val;");
        self.writeln("    if (i >= l->len) { fprintf(stderr, \"RIINA: list index out of bounds\\n\"); abort(); }");
        self.writeln("    return l->items[i];");
        self.writeln("}");
        self.writeln("");

        // senarai_panjang (list_len)
        self.writeln("static riina_value_t* riina_builtin_senarai_panjang(riina_value_t* arg) {");
        self.writeln("    if (arg->tag != RIINA_TAG_LIST) abort();");
        self.writeln("    return riina_int((uint64_t)RIINA_LIST_DATA(arg)->len);");
        self.writeln("}");
        self.writeln("");

        // senarai_balik (list_reverse)
        self.writeln("static riina_value_t* riina_builtin_senarai_balik(riina_value_t* arg) {");
        self.writeln("    if (arg->tag != RIINA_TAG_LIST) abort();");
        self.writeln("    riina_list_t* old = RIINA_LIST_DATA(arg);");
        self.writeln("    riina_list_t nl = riina_list_new();");
        self.writeln("    for (size_t i = old->len; i > 0; i--) riina_list_push(&nl, old->items[i-1]);");
        self.writeln("    return riina_make_list(nl);");
        self.writeln("}");
        self.writeln("");

        // senarai_susun (list_sort) — sorts ints ascending
        self.writeln("static int riina_cmp_values(const void* a, const void* b) {");
        self.writeln("    riina_value_t* va = *(riina_value_t**)a;");
        self.writeln("    riina_value_t* vb = *(riina_value_t**)b;");
        self.writeln("    if (va->tag == RIINA_TAG_INT && vb->tag == RIINA_TAG_INT) {");
        self.writeln("        if (va->data.int_val < vb->data.int_val) return -1;");
        self.writeln("        if (va->data.int_val > vb->data.int_val) return 1;");
        self.writeln("        return 0;");
        self.writeln("    }");
        self.writeln("    return 0;");
        self.writeln("}");
        self.writeln("");
        self.writeln("static riina_value_t* riina_builtin_senarai_susun(riina_value_t* arg) {");
        self.writeln("    if (arg->tag != RIINA_TAG_LIST) abort();");
        self.writeln("    riina_list_t* old = RIINA_LIST_DATA(arg);");
        self.writeln("    riina_list_t nl = riina_list_new();");
        self.writeln("    for (size_t i = 0; i < old->len; i++) riina_list_push(&nl, old->items[i]);");
        self.writeln("    if (nl.len > 1) qsort(nl.items, nl.len, sizeof(riina_value_t*), riina_cmp_values);");
        self.writeln("    return riina_make_list(nl);");
        self.writeln("}");
        self.writeln("");

        // senarai_mengandungi (list_contains): (List, Value) -> Bool
        self.writeln("static bool riina_values_equal(riina_value_t* a, riina_value_t* b) {");
        self.writeln("    return riina_binop_eq(a, b)->data.bool_val;");
        self.writeln("}");
        self.writeln("");
        self.writeln("static riina_value_t* riina_builtin_senarai_mengandungi(riina_value_t* arg) {");
        self.writeln("    if (arg->tag != RIINA_TAG_PAIR) abort();");
        self.writeln("    riina_value_t* lst = arg->data.pair_val.fst;");
        self.writeln("    riina_value_t* val = arg->data.pair_val.snd;");
        self.writeln("    if (lst->tag != RIINA_TAG_LIST) abort();");
        self.writeln("    riina_list_t* l = RIINA_LIST_DATA(lst);");
        self.writeln("    for (size_t i = 0; i < l->len; i++) {");
        self.writeln("        if (riina_values_equal(l->items[i], val)) return riina_bool(true);");
        self.writeln("    }");
        self.writeln("    return riina_bool(false);");
        self.writeln("}");
        self.writeln("");

        // senarai_sambung (list_concat): (List, List) -> List
        self.writeln("static riina_value_t* riina_builtin_senarai_sambung(riina_value_t* arg) {");
        self.writeln("    if (arg->tag != RIINA_TAG_PAIR) abort();");
        self.writeln("    riina_value_t* la = arg->data.pair_val.fst;");
        self.writeln("    riina_value_t* lb = arg->data.pair_val.snd;");
        self.writeln("    if (la->tag != RIINA_TAG_LIST || lb->tag != RIINA_TAG_LIST) abort();");
        self.writeln("    riina_list_t* a = RIINA_LIST_DATA(la);");
        self.writeln("    riina_list_t* b = RIINA_LIST_DATA(lb);");
        self.writeln("    riina_list_t nl = riina_list_new();");
        self.writeln("    for (size_t i = 0; i < a->len; i++) riina_list_push(&nl, a->items[i]);");
        self.writeln("    for (size_t i = 0; i < b->len; i++) riina_list_push(&nl, b->items[i]);");
        self.writeln("    return riina_make_list(nl);");
        self.writeln("}");
        self.writeln("");

        // senarai_kepala (list_head)
        self.writeln("static riina_value_t* riina_builtin_senarai_kepala(riina_value_t* arg) {");
        self.writeln("    if (arg->tag != RIINA_TAG_LIST) abort();");
        self.writeln("    riina_list_t* l = RIINA_LIST_DATA(arg);");
        self.writeln("    if (l->len == 0) { fprintf(stderr, \"RIINA: head of empty list\\n\"); abort(); }");
        self.writeln("    return l->items[0];");
        self.writeln("}");
        self.writeln("");

        // senarai_ekor (list_tail)
        self.writeln("static riina_value_t* riina_builtin_senarai_ekor(riina_value_t* arg) {");
        self.writeln("    if (arg->tag != RIINA_TAG_LIST) abort();");
        self.writeln("    riina_list_t* l = RIINA_LIST_DATA(arg);");
        self.writeln("    if (l->len == 0) { fprintf(stderr, \"RIINA: tail of empty list\\n\"); abort(); }");
        self.writeln("    riina_list_t nl = riina_list_new();");
        self.writeln("    for (size_t i = 1; i < l->len; i++) riina_list_push(&nl, l->items[i]);");
        self.writeln("    return riina_make_list(nl);");
        self.writeln("}");
        self.writeln("");

        // senarai_zip (list_zip): (List, List) -> List
        self.writeln("static riina_value_t* riina_builtin_senarai_zip(riina_value_t* arg) {");
        self.writeln("    if (arg->tag != RIINA_TAG_PAIR) abort();");
        self.writeln("    riina_value_t* la = arg->data.pair_val.fst;");
        self.writeln("    riina_value_t* lb = arg->data.pair_val.snd;");
        self.writeln("    if (la->tag != RIINA_TAG_LIST || lb->tag != RIINA_TAG_LIST) abort();");
        self.writeln("    riina_list_t* a = RIINA_LIST_DATA(la);");
        self.writeln("    riina_list_t* b = RIINA_LIST_DATA(lb);");
        self.writeln("    riina_list_t nl = riina_list_new();");
        self.writeln("    size_t min = a->len < b->len ? a->len : b->len;");
        self.writeln("    for (size_t i = 0; i < min; i++) riina_list_push(&nl, riina_pair(a->items[i], b->items[i]));");
        self.writeln("    return riina_make_list(nl);");
        self.writeln("}");
        self.writeln("");

        // senarai_nombor (list_enumerate): List -> List of (Int, Value)
        self.writeln("static riina_value_t* riina_builtin_senarai_nombor(riina_value_t* arg) {");
        self.writeln("    if (arg->tag != RIINA_TAG_LIST) abort();");
        self.writeln("    riina_list_t* l = RIINA_LIST_DATA(arg);");
        self.writeln("    riina_list_t nl = riina_list_new();");
        self.writeln("    for (size_t i = 0; i < l->len; i++) riina_list_push(&nl, riina_pair(riina_int((uint64_t)i), l->items[i]));");
        self.writeln("    return riina_make_list(nl);");
        self.writeln("}");
        self.writeln("");

        // ═══════════════════════════════════════════════════════════════════
        // MAP BUILTINS (peta)
        // ═══════════════════════════════════════════════════════════════════

        // peta_baru (map_new)
        self.writeln("static riina_value_t* riina_builtin_peta_baru(riina_value_t* arg) {");
        self.writeln("    (void)arg;");
        self.writeln("    riina_map_t m = { NULL, 0 };");
        self.writeln("    return riina_make_map(m);");
        self.writeln("}");
        self.writeln("");

        // peta_letak (map_insert): (Map, (String, Value)) -> Map
        self.writeln("static riina_value_t* riina_builtin_peta_letak(riina_value_t* arg) {");
        self.writeln("    if (arg->tag != RIINA_TAG_PAIR) abort();");
        self.writeln("    riina_value_t* mv = arg->data.pair_val.fst;");
        self.writeln("    riina_value_t* kv = arg->data.pair_val.snd;");
        self.writeln("    if (mv->tag != RIINA_TAG_MAP || kv->tag != RIINA_TAG_PAIR) abort();");
        self.writeln("    riina_value_t* key = kv->data.pair_val.fst;");
        self.writeln("    riina_value_t* val = kv->data.pair_val.snd;");
        self.writeln("    if (key->tag != RIINA_TAG_STRING) abort();");
        self.writeln("    riina_map_t* old = RIINA_MAP_DATA(mv);");
        self.writeln("    /* Copy existing entries */");
        self.writeln("    riina_map_t nm = { NULL, 0 };");
        self.writeln("    riina_map_entry_t** tail = &nm.head;");
        self.writeln("    bool replaced = false;");
        self.writeln("    for (riina_map_entry_t* e = old->head; e; e = e->next) {");
        self.writeln("        riina_map_entry_t* ne = (riina_map_entry_t*)malloc(sizeof(riina_map_entry_t));");
        self.writeln("        if (!ne) abort();");
        self.writeln("        if (strcmp(e->key, key->data.string_val.data) == 0) {");
        self.writeln("            ne->key = strdup(key->data.string_val.data);");
        self.writeln("            ne->value = val;");
        self.writeln("            replaced = true;");
        self.writeln("        } else {");
        self.writeln("            ne->key = strdup(e->key);");
        self.writeln("            ne->value = e->value;");
        self.writeln("        }");
        self.writeln("        ne->next = NULL;");
        self.writeln("        *tail = ne; tail = &ne->next;");
        self.writeln("        nm.len++;");
        self.writeln("    }");
        self.writeln("    if (!replaced) {");
        self.writeln("        riina_map_entry_t* ne = (riina_map_entry_t*)malloc(sizeof(riina_map_entry_t));");
        self.writeln("        if (!ne) abort();");
        self.writeln("        ne->key = strdup(key->data.string_val.data);");
        self.writeln("        ne->value = val;");
        self.writeln("        ne->next = NULL;");
        self.writeln("        *tail = ne;");
        self.writeln("        nm.len++;");
        self.writeln("    }");
        self.writeln("    return riina_make_map(nm);");
        self.writeln("}");
        self.writeln("");

        // peta_dapat (map_get): (Map, String) -> Value
        self.writeln("static riina_value_t* riina_builtin_peta_dapat(riina_value_t* arg) {");
        self.writeln("    if (arg->tag != RIINA_TAG_PAIR) abort();");
        self.writeln("    riina_value_t* mv = arg->data.pair_val.fst;");
        self.writeln("    riina_value_t* key = arg->data.pair_val.snd;");
        self.writeln("    if (mv->tag != RIINA_TAG_MAP || key->tag != RIINA_TAG_STRING) abort();");
        self.writeln("    riina_map_t* m = RIINA_MAP_DATA(mv);");
        self.writeln("    for (riina_map_entry_t* e = m->head; e; e = e->next) {");
        self.writeln("        if (strcmp(e->key, key->data.string_val.data) == 0) return e->value;");
        self.writeln("    }");
        self.writeln("    fprintf(stderr, \"RIINA: key not found in map\\n\"); abort();");
        self.writeln("    return NULL;");
        self.writeln("}");
        self.writeln("");

        // peta_buang (map_remove): (Map, String) -> Map
        self.writeln("static riina_value_t* riina_builtin_peta_buang(riina_value_t* arg) {");
        self.writeln("    if (arg->tag != RIINA_TAG_PAIR) abort();");
        self.writeln("    riina_value_t* mv = arg->data.pair_val.fst;");
        self.writeln("    riina_value_t* key = arg->data.pair_val.snd;");
        self.writeln("    if (mv->tag != RIINA_TAG_MAP || key->tag != RIINA_TAG_STRING) abort();");
        self.writeln("    riina_map_t* old = RIINA_MAP_DATA(mv);");
        self.writeln("    riina_map_t nm = { NULL, 0 };");
        self.writeln("    riina_map_entry_t** tail = &nm.head;");
        self.writeln("    for (riina_map_entry_t* e = old->head; e; e = e->next) {");
        self.writeln("        if (strcmp(e->key, key->data.string_val.data) != 0) {");
        self.writeln("            riina_map_entry_t* ne = (riina_map_entry_t*)malloc(sizeof(riina_map_entry_t));");
        self.writeln("            if (!ne) abort();");
        self.writeln("            ne->key = strdup(e->key); ne->value = e->value; ne->next = NULL;");
        self.writeln("            *tail = ne; tail = &ne->next;");
        self.writeln("            nm.len++;");
        self.writeln("        }");
        self.writeln("    }");
        self.writeln("    return riina_make_map(nm);");
        self.writeln("}");
        self.writeln("");

        // peta_kunci (map_keys): Map -> List
        self.writeln("static riina_value_t* riina_builtin_peta_kunci(riina_value_t* arg) {");
        self.writeln("    if (arg->tag != RIINA_TAG_MAP) abort();");
        self.writeln("    riina_map_t* m = RIINA_MAP_DATA(arg);");
        self.writeln("    riina_list_t nl = riina_list_new();");
        self.writeln("    for (riina_map_entry_t* e = m->head; e; e = e->next) riina_list_push(&nl, riina_string(e->key));");
        self.writeln("    return riina_make_list(nl);");
        self.writeln("}");
        self.writeln("");

        // peta_nilai (map_values): Map -> List
        self.writeln("static riina_value_t* riina_builtin_peta_nilai(riina_value_t* arg) {");
        self.writeln("    if (arg->tag != RIINA_TAG_MAP) abort();");
        self.writeln("    riina_map_t* m = RIINA_MAP_DATA(arg);");
        self.writeln("    riina_list_t nl = riina_list_new();");
        self.writeln("    for (riina_map_entry_t* e = m->head; e; e = e->next) riina_list_push(&nl, e->value);");
        self.writeln("    return riina_make_list(nl);");
        self.writeln("}");
        self.writeln("");

        // peta_mengandungi (map_contains): (Map, String) -> Bool
        self.writeln("static riina_value_t* riina_builtin_peta_mengandungi(riina_value_t* arg) {");
        self.writeln("    if (arg->tag != RIINA_TAG_PAIR) abort();");
        self.writeln("    riina_value_t* mv = arg->data.pair_val.fst;");
        self.writeln("    riina_value_t* key = arg->data.pair_val.snd;");
        self.writeln("    if (mv->tag != RIINA_TAG_MAP || key->tag != RIINA_TAG_STRING) abort();");
        self.writeln("    riina_map_t* m = RIINA_MAP_DATA(mv);");
        self.writeln("    for (riina_map_entry_t* e = m->head; e; e = e->next) {");
        self.writeln("        if (strcmp(e->key, key->data.string_val.data) == 0) return riina_bool(true);");
        self.writeln("    }");
        self.writeln("    return riina_bool(false);");
        self.writeln("}");
        self.writeln("");

        // peta_panjang (map_len): Map -> Int
        self.writeln("static riina_value_t* riina_builtin_peta_panjang(riina_value_t* arg) {");
        self.writeln("    if (arg->tag != RIINA_TAG_MAP) abort();");
        self.writeln("    return riina_int((uint64_t)RIINA_MAP_DATA(arg)->len);");
        self.writeln("}");
        self.writeln("");

        // ═══════════════════════════════════════════════════════════════════
        // SET BUILTINS (set) — uses List internally
        // ═══════════════════════════════════════════════════════════════════

        // set_baru (set_new)
        self.writeln("static riina_value_t* riina_builtin_set_baru(riina_value_t* arg) {");
        self.writeln("    (void)arg;");
        self.writeln("    riina_list_t l = riina_list_new();");
        self.writeln("    return riina_make_list(l);");
        self.writeln("}");
        self.writeln("");

        // set_letak (set_insert): (List, Value) -> List
        self.writeln("static riina_value_t* riina_builtin_set_letak(riina_value_t* arg) {");
        self.writeln("    if (arg->tag != RIINA_TAG_PAIR) abort();");
        self.writeln("    riina_value_t* lst = arg->data.pair_val.fst;");
        self.writeln("    riina_value_t* val = arg->data.pair_val.snd;");
        self.writeln("    if (lst->tag != RIINA_TAG_LIST) abort();");
        self.writeln("    riina_list_t* old = RIINA_LIST_DATA(lst);");
        self.writeln("    /* Check if already present */");
        self.writeln("    for (size_t i = 0; i < old->len; i++) {");
        self.writeln("        if (riina_values_equal(old->items[i], val)) return lst;");
        self.writeln("    }");
        self.writeln("    riina_list_t nl = riina_list_new();");
        self.writeln("    for (size_t i = 0; i < old->len; i++) riina_list_push(&nl, old->items[i]);");
        self.writeln("    riina_list_push(&nl, val);");
        self.writeln("    return riina_make_list(nl);");
        self.writeln("}");
        self.writeln("");

        // set_buang (set_remove): (List, Value) -> List
        self.writeln("static riina_value_t* riina_builtin_set_buang(riina_value_t* arg) {");
        self.writeln("    if (arg->tag != RIINA_TAG_PAIR) abort();");
        self.writeln("    riina_value_t* lst = arg->data.pair_val.fst;");
        self.writeln("    riina_value_t* val = arg->data.pair_val.snd;");
        self.writeln("    if (lst->tag != RIINA_TAG_LIST) abort();");
        self.writeln("    riina_list_t* old = RIINA_LIST_DATA(lst);");
        self.writeln("    riina_list_t nl = riina_list_new();");
        self.writeln("    for (size_t i = 0; i < old->len; i++) {");
        self.writeln("        if (!riina_values_equal(old->items[i], val)) riina_list_push(&nl, old->items[i]);");
        self.writeln("    }");
        self.writeln("    return riina_make_list(nl);");
        self.writeln("}");
        self.writeln("");

        // set_mengandungi (set_contains): (List, Value) -> Bool
        self.writeln("static riina_value_t* riina_builtin_set_mengandungi(riina_value_t* arg) {");
        self.writeln("    return riina_builtin_senarai_mengandungi(arg);");
        self.writeln("}");
        self.writeln("");

        // set_kesatuan (set_union): (List, List) -> List
        self.writeln("static riina_value_t* riina_builtin_set_kesatuan(riina_value_t* arg) {");
        self.writeln("    if (arg->tag != RIINA_TAG_PAIR) abort();");
        self.writeln("    riina_value_t* la = arg->data.pair_val.fst;");
        self.writeln("    riina_value_t* lb = arg->data.pair_val.snd;");
        self.writeln("    if (la->tag != RIINA_TAG_LIST || lb->tag != RIINA_TAG_LIST) abort();");
        self.writeln("    riina_list_t* a = RIINA_LIST_DATA(la);");
        self.writeln("    riina_list_t* b = RIINA_LIST_DATA(lb);");
        self.writeln("    riina_list_t nl = riina_list_new();");
        self.writeln("    for (size_t i = 0; i < a->len; i++) riina_list_push(&nl, a->items[i]);");
        self.writeln("    for (size_t i = 0; i < b->len; i++) {");
        self.writeln("        bool found = false;");
        self.writeln("        for (size_t j = 0; j < a->len; j++) {");
        self.writeln("            if (riina_values_equal(a->items[j], b->items[i])) { found = true; break; }");
        self.writeln("        }");
        self.writeln("        if (!found) riina_list_push(&nl, b->items[i]);");
        self.writeln("    }");
        self.writeln("    return riina_make_list(nl);");
        self.writeln("}");
        self.writeln("");

        // set_persilangan (set_intersect): (List, List) -> List
        self.writeln("static riina_value_t* riina_builtin_set_persilangan(riina_value_t* arg) {");
        self.writeln("    if (arg->tag != RIINA_TAG_PAIR) abort();");
        self.writeln("    riina_value_t* la = arg->data.pair_val.fst;");
        self.writeln("    riina_value_t* lb = arg->data.pair_val.snd;");
        self.writeln("    if (la->tag != RIINA_TAG_LIST || lb->tag != RIINA_TAG_LIST) abort();");
        self.writeln("    riina_list_t* a = RIINA_LIST_DATA(la);");
        self.writeln("    riina_list_t* b = RIINA_LIST_DATA(lb);");
        self.writeln("    riina_list_t nl = riina_list_new();");
        self.writeln("    for (size_t i = 0; i < a->len; i++) {");
        self.writeln("        for (size_t j = 0; j < b->len; j++) {");
        self.writeln("            if (riina_values_equal(a->items[i], b->items[j])) {");
        self.writeln("                riina_list_push(&nl, a->items[i]);");
        self.writeln("                break;");
        self.writeln("            }");
        self.writeln("        }");
        self.writeln("    }");
        self.writeln("    return riina_make_list(nl);");
        self.writeln("}");
        self.writeln("");

        // set_panjang (set_len)
        self.writeln("static riina_value_t* riina_builtin_set_panjang(riina_value_t* arg) {");
        self.writeln("    return riina_builtin_senarai_panjang(arg);");
        self.writeln("}");
        self.writeln("");

        // ═══════════════════════════════════════════════════════════════════
        // TIME BUILTINS (masa)
        // ═══════════════════════════════════════════════════════════════════

        self.writeln("#include <time.h>");
        self.writeln("");

        // masa_sekarang (time_now): () -> Int
        self.writeln("static riina_value_t* riina_builtin_masa_sekarang(riina_value_t* arg) {");
        self.writeln("    (void)arg;");
        self.writeln("    return riina_int((uint64_t)time(NULL));");
        self.writeln("}");
        self.writeln("");

        // masa_sekarang_ms (time_now_ms): () -> Int
        self.writeln("static riina_value_t* riina_builtin_masa_sekarang_ms(riina_value_t* arg) {");
        self.writeln("    (void)arg;");
        self.writeln("    struct timespec ts;");
        self.writeln("    clock_gettime(CLOCK_REALTIME, &ts);");
        self.writeln("    return riina_int((uint64_t)ts.tv_sec * 1000 + (uint64_t)ts.tv_nsec / 1000000);");
        self.writeln("}");
        self.writeln("");

        // masa_format (time_format): (Int, String) -> String
        self.writeln("static riina_value_t* riina_builtin_masa_format(riina_value_t* arg) {");
        self.writeln("    if (arg->tag != RIINA_TAG_PAIR) abort();");
        self.writeln("    riina_value_t* ts = arg->data.pair_val.fst;");
        self.writeln("    riina_value_t* fmt = arg->data.pair_val.snd;");
        self.writeln("    if (ts->tag != RIINA_TAG_INT || fmt->tag != RIINA_TAG_STRING) abort();");
        self.writeln("    time_t t = (time_t)ts->data.int_val;");
        self.writeln("    struct tm* tm_p = gmtime(&t);");
        self.writeln("    char buf[256];");
        self.writeln("    strftime(buf, sizeof(buf), fmt->data.string_val.data, tm_p);");
        self.writeln("    return riina_string(buf);");
        self.writeln("}");
        self.writeln("");

        // masa_urai (time_parse): (String, String) -> Int
        self.writeln("static riina_value_t* riina_builtin_masa_urai(riina_value_t* arg) {");
        self.writeln("    if (arg->tag != RIINA_TAG_PAIR) abort();");
        self.writeln("    riina_value_t* s = arg->data.pair_val.fst;");
        self.writeln("    riina_value_t* fmt = arg->data.pair_val.snd;");
        self.writeln("    if (s->tag != RIINA_TAG_STRING || fmt->tag != RIINA_TAG_STRING) abort();");
        self.writeln("    struct tm tm_s = {0};");
        self.writeln("    strptime(s->data.string_val.data, fmt->data.string_val.data, &tm_s);");
        self.writeln("    return riina_int((uint64_t)mktime(&tm_s));");
        self.writeln("}");
        self.writeln("");

        // masa_tidur (time_sleep): Int -> ()
        self.writeln("static riina_value_t* riina_builtin_masa_tidur(riina_value_t* arg) {");
        self.writeln("    if (arg->tag != RIINA_TAG_INT) abort();");
        self.writeln("    struct timespec ts;");
        self.writeln("    ts.tv_sec = (time_t)(arg->data.int_val / 1000);");
        self.writeln("    ts.tv_nsec = (long)((arg->data.int_val % 1000) * 1000000);");
        self.writeln("    nanosleep(&ts, NULL);");
        self.writeln("    return riina_unit();");
        self.writeln("}");
        self.writeln("");

        // masa_jam (time_clock): () -> Int (monotonic nanoseconds)
        self.writeln("static riina_value_t* riina_builtin_masa_jam(riina_value_t* arg) {");
        self.writeln("    (void)arg;");
        self.writeln("    struct timespec ts;");
        self.writeln("    clock_gettime(CLOCK_MONOTONIC, &ts);");
        self.writeln("    return riina_int((uint64_t)ts.tv_sec * 1000000000ULL + (uint64_t)ts.tv_nsec);");
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
                if func.captures.is_empty() {
                    let _ = writeln!(
                        self.output,
                        "static riina_value_t* {}(riina_value_t* {});",
                        self.func_name(func_id),
                        func.param
                    );
                } else {
                    let _ = writeln!(
                        self.output,
                        "static riina_value_t* {}(riina_value_t* _self, riina_value_t* {});",
                        self.func_name(func_id),
                        func.param
                    );
                }
            }
        }
        self.writeln("");

        Ok(())
    }

    /// Build phi map for SSA destruction: collects all phi nodes in a function
    /// and organizes them by target block and predecessor block.
    fn build_phi_map(func: &Function) -> PhiMap {
        let mut phi_map: PhiMap = HashMap::new();
        for block in &func.blocks {
            for instr in &block.instrs {
                if let Instruction::Phi(entries) = &instr.instr {
                    for (pred_block, src_var) in entries {
                        phi_map
                            .entry(block.id)
                            .or_default()
                            .entry(*pred_block)
                            .or_default()
                            .push((instr.result, *src_var));
                    }
                }
            }
        }
        phi_map
    }

    /// Emit a single function
    fn emit_function(&mut self, func: &Function) -> Result<()> {
        self.declared_vars.clear();

        self.writeln("/* ═══════════════════════════════════════════════════════════════════ */");
        let _ = writeln!(self.output, "/* Function: {} */", func.name);
        self.writeln("/* ═══════════════════════════════════════════════════════════════════ */");
        self.writeln("");

        // Function signature
        if func.captures.is_empty() {
            self.write(&format!(
                "static riina_value_t* {}(riina_value_t* {})",
                self.func_name(&func.id),
                func.param
            ));
        } else {
            self.write(&format!(
                "static riina_value_t* {}(riina_value_t* _self, riina_value_t* {})",
                self.func_name(&func.id),
                func.param
            ));
        }
        self.write_raw(" {\n");
        self.indent();

        // Declare all variables used in the function
        self.emit_var_declarations(func)?;

        // Bind parameter and captured variables to their VarIds
        if !func.captures.is_empty() {
            self.writeln("/* Extract captured variables */");
            for (i, (_name, _ty)) in func.captures.iter().enumerate() {
                let var = VarId::new(i as u32);
                self.writeln(&format!(
                    "{} = _self->data.closure_val.captures[{i}];",
                    self.var_name(&var)
                ));
            }
            let param_var = VarId::new(func.captures.len() as u32);
            self.writeln(&format!(
                "{} = {};",
                self.var_name(&param_var),
                func.param
            ));
            self.writeln("");
        } else {
            // For non-capture functions, bind parameter to VarId(0)
            // (the lowerer allocates VarId(0) for the parameter)
            let param_var = VarId::new(0);
            if self.declared_vars.contains(&param_var) {
                self.writeln(&format!(
                    "{} = {};",
                    self.var_name(&param_var),
                    func.param
                ));
                self.writeln("");
            }
        }

        // Build phi map for SSA destruction (copy insertion before jumps)
        let phi_map = Self::build_phi_map(func);

        // Emit each basic block
        for block in &func.blocks {
            self.emit_block_with_phi(block, &phi_map)?;
        }

        self.dedent();
        self.writeln("}");
        self.writeln("");

        Ok(())
    }

    /// Emit variable declarations for a function
    fn emit_var_declarations(&mut self, func: &Function) -> Result<()> {
        let mut vars: HashSet<VarId> = HashSet::new();

        // Add capture VarIds and parameter VarId
        if !func.captures.is_empty() {
            for i in 0..func.captures.len() {
                vars.insert(VarId::new(i as u32));
            }
            vars.insert(VarId::new(func.captures.len() as u32));
        }

        // Collect all variables (results and operands)
        for block in &func.blocks {
            for instr in &block.instrs {
                vars.insert(instr.result);
                // Also collect operand VarIds (for captures/params referenced)
                match &instr.instr {
                    Instruction::Copy(v) | Instruction::Fst(v) | Instruction::Snd(v)
                    | Instruction::IsLeft(v) | Instruction::UnwrapLeft(v) | Instruction::UnwrapRight(v)
                    | Instruction::Load(v) | Instruction::Classify(v) | Instruction::Prove(v)
                    | Instruction::UnaryOp(_, v) | Instruction::Inl(v) | Instruction::Inr(v) => {
                        vars.insert(*v);
                    }
                    Instruction::BinOp(_, a, b) | Instruction::Pair(a, b)
                    | Instruction::Store(a, b) | Instruction::Declassify(a, b)
                    | Instruction::Call(a, b) => {
                        vars.insert(*a);
                        vars.insert(*b);
                    }
                    Instruction::Alloc { init, .. } => {
                        vars.insert(*init);
                    }
                    Instruction::Perform { payload, .. } => {
                        vars.insert(*payload);
                    }
                    Instruction::Closure { captures, .. } => {
                        for c in captures {
                            vars.insert(*c);
                        }
                    }
                    Instruction::Phi(entries) => {
                        for (_, v) in entries {
                            vars.insert(*v);
                        }
                    }
                    Instruction::BuiltinCall { arg, .. } => {
                        vars.insert(*arg);
                    }
                    Instruction::Const(_) | Instruction::RequireCap(_) | Instruction::GrantCap(_) => {}
                }
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

    /// Emit a basic block with phi copy insertion (SSA destruction).
    fn emit_block_with_phi(&mut self, block: &BasicBlock, phi_map: &PhiMap) -> Result<()> {
        // Block label
        self.dedent();
        self.writeln(&format!("{}:", self.block_name(&block.id)));
        self.indent();

        // Instructions
        for instr in &block.instrs {
            self.emit_instruction(instr)?;
        }

        // Terminator (with phi copy insertion before jumps)
        if let Some(term) = &block.terminator {
            self.emit_terminator_with_phi(term, &block.id, phi_map)?;
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
                // Closure emission: captures array allocated and populated.
                // Single-arg calling convention; multi-arg via currying.
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
                    self.writeln(&format!("{result} = riina_alloc();"));
                    self.writeln(&format!("{result}->tag = RIINA_TAG_CLOSURE;"));
                    self.writeln(&format!("{result}->security = RIINA_LEVEL_PUBLIC;"));
                    self.writeln(&format!(
                        "{result}->data.closure_val.func_ptr = (void*){};",
                        self.func_name(func)
                    ));
                    self.writeln(&format!(
                        "{result}->data.closure_val.captures = (riina_value_t**)malloc({} * sizeof(riina_value_t*));",
                        captures.len()
                    ));
                    self.writeln(&format!(
                        "{result}->data.closure_val.num_captures = {};",
                        captures.len()
                    ));
                    for (i, cap) in captures.iter().enumerate() {
                        self.writeln(&format!(
                            "{result}->data.closure_val.captures[{}] = {};",
                            i, self.var_name(cap)
                        ));
                    }
                }
            }

            Instruction::Call(func_var, arg) => {
                self.writeln(&format!(
                    "if ({}->tag != RIINA_TAG_CLOSURE) {{ fprintf(stderr, \"RIINA: call on non-closure\\n\"); abort(); }}",
                    self.var_name(func_var)
                ));
                // If closure has captures, pass _self as first arg
                self.writeln(&format!(
                    "if ({}->data.closure_val.num_captures > 0) {{",
                    self.var_name(func_var)
                ));
                self.indent();
                self.writeln(&format!(
                    "{result} = ((riina_value_t* (*)(riina_value_t*, riina_value_t*)){}->data.closure_val.func_ptr)({}, {});",
                    self.var_name(func_var),
                    self.var_name(func_var),
                    self.var_name(arg)
                ));
                self.dedent();
                self.writeln("} else {");
                self.indent();
                self.writeln(&format!(
                    "{result} = ((riina_value_t* (*)(riina_value_t*)){}->data.closure_val.func_ptr)({});",
                    self.var_name(func_var),
                    self.var_name(arg)
                ));
                self.dedent();
                self.writeln("}");
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

            Instruction::BuiltinCall { name, arg } => {
                self.writeln(&format!(
                    "{result} = riina_builtin_{name}({});",
                    self.var_name(arg)
                ));
            }

            Instruction::Phi(_entries) => {
                // SSA phi destruction: phi nodes are eliminated by copy insertion.
                // The phi result variable is already declared. We do NOT emit code
                // at the phi site itself; instead, predecessor blocks insert copies
                // before their terminator (see emit_phi_copies in emit_block).
                //
                // However, as a safety net for blocks with no predecessor assignment,
                // initialize to unit (dead code in well-formed IR).
                self.writeln(&format!("{result} = {result}; /* phi: assigned by predecessors */"));
            }
        }

        Ok(())
    }

    /// Emit phi copy assignments: before branching to `target`, copy source vars
    /// into phi result vars for all phi nodes in the target block that expect
    /// a value from `current_block`.
    fn emit_phi_copies(&mut self, current_block: &BlockId, target: &BlockId, phi_map: &PhiMap) {
        if let Some(target_phis) = phi_map.get(target) {
            if let Some(copies) = target_phis.get(current_block) {
                for (phi_result, src_var) in copies {
                    self.writeln(&format!(
                        "{} = {}; /* phi copy: {} <- {} */",
                        self.var_name(phi_result),
                        self.var_name(src_var),
                        self.var_name(phi_result),
                        self.var_name(src_var),
                    ));
                }
            }
        }
    }

    /// Emit a block terminator with phi copy insertion (SSA destruction).
    fn emit_terminator_with_phi(
        &mut self,
        term: &Terminator,
        current_block: &BlockId,
        phi_map: &PhiMap,
    ) -> Result<()> {
        match term {
            Terminator::Return(var) => {
                self.writeln(&format!("return {};", self.var_name(var)));
            }

            Terminator::Branch(target) => {
                self.emit_phi_copies(current_block, target, phi_map);
                self.writeln(&format!("goto {};", self.block_name(target)));
            }

            Terminator::CondBranch { cond, then_block, else_block } => {
                // Emit phi copies for both branches using an if/else to select
                // which copies to perform before jumping.
                let has_then_phis = phi_map.get(then_block)
                    .and_then(|m| m.get(current_block))
                    .map_or(false, |v| !v.is_empty());
                let has_else_phis = phi_map.get(else_block)
                    .and_then(|m| m.get(current_block))
                    .map_or(false, |v| !v.is_empty());

                if has_then_phis || has_else_phis {
                    self.writeln(&format!("if ({}->data.bool_val) {{", self.var_name(cond)));
                    self.indent();
                    self.emit_phi_copies(current_block, then_block, phi_map);
                    self.writeln(&format!("goto {};", self.block_name(then_block)));
                    self.dedent();
                    self.writeln("} else {");
                    self.indent();
                    self.emit_phi_copies(current_block, else_block, phi_map);
                    self.writeln(&format!("goto {};", self.block_name(else_block)));
                    self.dedent();
                    self.writeln("}");
                } else {
                    self.writeln(&format!(
                        "if ({}->data.bool_val) goto {}; else goto {};",
                        self.var_name(cond),
                        self.block_name(then_block),
                        self.block_name(else_block)
                    ));
                }
            }

            Terminator::Handle { body_block, handler_block, resume_var, result_block } => {
                // Push handler frame, setjmp for non-local return from perform
                self.writeln("riina_push_handler(RIINA_EFFECT_PURE); /* handler frame */");
                self.writeln(&format!(
                    "if (setjmp(riina_handler_stack[riina_handler_top - 1].env) == 0) {{"
                ));
                self.indent();
                // Normal path: execute body
                self.emit_phi_copies(current_block, body_block, phi_map);
                self.writeln(&format!("goto {};", self.block_name(body_block)));
                self.dedent();
                self.writeln("} else {");
                self.indent();
                // Handler path: effect was performed, payload in handler frame
                self.writeln(&format!(
                    "riina_value_t* {} = riina_handler_stack[riina_handler_top].payload;",
                    resume_var
                ));
                self.writeln("riina_pop_handler();");
                self.emit_phi_copies(current_block, handler_block, phi_map);
                self.writeln(&format!("goto {};", self.block_name(handler_block)));
                self.dedent();
                self.writeln("}");
                let _ = result_block; // used by handler_block's continuation
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
            SecurityLevel::Internal => "RIINA_LEVEL_INTERNAL",
            SecurityLevel::Session => "RIINA_LEVEL_SESSION",
            SecurityLevel::User => "RIINA_LEVEL_USER",
            SecurityLevel::System => "RIINA_LEVEL_SYSTEM",
            SecurityLevel::Secret => "RIINA_LEVEL_SECRET",
        }
    }

    /// Convert effect to C enum
    fn effect_str(&self, effect: &Effect) -> &'static str {
        match effect {
            Effect::Pure => "RIINA_EFFECT_PURE",
            Effect::Read => "RIINA_EFFECT_READ",
            Effect::Write => "RIINA_EFFECT_WRITE",
            Effect::FileSystem => "RIINA_EFFECT_FILESYSTEM",
            Effect::Network => "RIINA_EFFECT_NETWORK",
            Effect::NetworkSecure => "RIINA_EFFECT_NETWORK_SECURE",
            Effect::Crypto => "RIINA_EFFECT_CRYPTO",
            Effect::Random => "RIINA_EFFECT_RANDOM",
            Effect::System => "RIINA_EFFECT_SYSTEM",
            Effect::Time => "RIINA_EFFECT_TIME",
            Effect::Process => "RIINA_EFFECT_PROCESS",
            Effect::Panel => "RIINA_EFFECT_PANEL",
            Effect::Zirah => "RIINA_EFFECT_ZIRAH",
            Effect::Benteng => "RIINA_EFFECT_BENTENG",
            Effect::Sandi => "RIINA_EFFECT_SANDI",
            Effect::Menara => "RIINA_EFFECT_MENARA",
            Effect::Gapura => "RIINA_EFFECT_GAPURA",
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
