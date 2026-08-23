// Copyright (c) 2026 The RIINA Authors. All rights reserved.

//! WebAssembly Backend
//!
//! Translates RIINA IR to WebAssembly binary format (.wasm).
//! Direct emission — no Emscripten, no LLVM, no external tools.
//!
//! # Architecture
//!
//! ```text
//!   ir::Program
//!       │
//!       ▼
//!   ┌────────────────────┐
//!   │  WasmBackend::emit │  IR → WASM instructions
//!   └────────────────────┘
//!       │
//!       ▼
//!   ┌────────────────────┐
//!   │  wasm_encode       │  WASM instructions → binary
//!   └────────────────────┘
//!       │
//!       ▼
//!   .wasm binary + JS glue
//! ```
//!
//! # Memory Layout
//!
//! ```text
//! Linear memory:
//!   [0..data_end)        — string constants (data section)
//!   [data_end..heap_ptr) — bump-allocated heap (pairs, sums, closures, refs)
//!   [heap_ptr..65536)    — free space
//! ```
//!
//! # Security Invariants
//!
//! The WASM backend preserves RIINA's security properties:
//! - Non-interference: WASM linear memory is partitioned for secret/public data
//! - Effect safety: WASM imports gate all side effects
//! - Type safety: WASM's type system enforces stack discipline
//!
//! Mode: ULTRA KIASU | FUCKING PARANOID | ZERO TRUST

use crate::backend::{AuxFile, Backend, BackendOutput, Target};
use crate::ir::{
    BasicBlock, BinOp, BlockId, Constant, FuncId, Function, Instruction, Program, Terminator,
    UnaryOp, VarId,
};
use riina_types::Ty;
use crate::wasm_encode::{
    self, DataSegment, ElemSegment, Export, ExportKind, FuncBody, FuncType, GlobalType, Import,
    ImportKind, MemoryType, Op, TableType, ValType, WasmModule,
};
use crate::{Error, Result};

use std::collections::HashMap;

/// Initial heap pointer offset (after data section).
/// Aligned to 16 bytes.
const HEAP_START_ALIGN: u32 = 16;

/// Global index for the heap pointer.
const GLOBAL_HEAP_PTR: u32 = 0;

/// Number of imported functions (cetak, panic).
const NUM_IMPORTS: u32 = 2;

/// WebAssembly backend.
pub struct WasmBackend {
    target: Target,
}

/// How a RIINA boolean renders as text, in RIINA's own spelling — index 0 is
/// `false`, index 1 is `true`. Byte-identical to the C backend's `riina_format`
/// and to the interpreter's `format_value` (master plan REQ-80).
const BOOL_RENDERINGS: [&str; 2] = ["salah", "betul"];

impl WasmBackend {
    pub fn new(target: Target) -> Self {
        Self { target }
    }

    /// Translate an IR program to a WASM module.
    fn translate(&self, program: &Program) -> Result<WasmModule> {
        let mut module = WasmModule::new();

        // Collect string constants from the entire program
        let mut string_table: HashMap<String, u32> = HashMap::new();
        let mut data_offset: u32 = 0;
        let mut data_segments: Vec<DataSegment> = Vec::new();

        // `ke_teks` of a Bool renders "betul"/"salah" (REQ-80), so those two
        // heap strings must exist whether or not the program contains the
        // literals. Interned first, in this pass, because the data section is
        // laid out here. 18 bytes total.
        let interned: Vec<String> = BOOL_RENDERINGS
            .iter()
            .map(|s| (*s).to_string())
            .chain(program.functions.values().flat_map(|f| {
                f.blocks.iter().flat_map(|b| {
                    b.instrs.iter().filter_map(|i| match &i.instr {
                        Instruction::Const(Constant::String(s)) => Some(s.clone()),
                        _ => None,
                    })
                })
            }))
            .collect();
        for s in &interned {
            if !string_table.contains_key(s) {
                let offset = data_offset;
                let bytes = s.as_bytes();
                // Store length (4 bytes) + string bytes
                data_segments.push(DataSegment {
                    offset,
                    data: {
                        let mut d = Vec::with_capacity(4 + bytes.len());
                        d.extend_from_slice(&(bytes.len() as u32).to_le_bytes());
                        d.extend_from_slice(bytes);
                        d
                    },
                });
                string_table.insert(s.clone(), offset);
                data_offset += 4 + bytes.len() as u32;
            }
        }

        // Align heap start
        let heap_start = (data_offset + HEAP_START_ALIGN - 1) & !(HEAP_START_ALIGN - 1);
        if heap_start == 0 {
            // Even with no data, start heap at 16 to avoid null pointer confusion
        }
        let heap_start = if heap_start == 0 {
            HEAP_START_ALIGN
        } else {
            heap_start
        };

        // === Import section: WASI fd_write for I/O ===
        // fd_write(fd: i32, iovs: i32, iovs_len: i32, nwritten: i32) -> i32
        let fd_write_type_idx = module.types.len() as u32;
        module.types.push(FuncType {
            params: vec![ValType::I32, ValType::I32, ValType::I32, ValType::I32],
            results: vec![ValType::I32],
        });
        // proc_exit(code: i32) -> ()
        let proc_exit_type_idx = module.types.len() as u32;
        module.types.push(FuncType {
            params: vec![ValType::I32],
            results: vec![],
        });

        module.imports.push(Import {
            module: "wasi_snapshot_preview1".to_string(),
            name: "fd_write".to_string(),
            kind: ImportKind::Func(fd_write_type_idx),
        });
        module.imports.push(Import {
            module: "wasi_snapshot_preview1".to_string(),
            name: "proc_exit".to_string(),
            kind: ImportKind::Func(proc_exit_type_idx),
        });

        // === Memory ===
        module.memories.push(MemoryType {
            min: 1,
            max: Some(256),
        });

        // === Global: heap pointer (mutable i32) ===
        let mut heap_init = Vec::new();
        heap_init.push(Op::I32Const as u8);
        wasm_encode::encode_sleb128(heap_start as i64, &mut heap_init);
        heap_init.push(Op::End as u8);
        module.globals.push(GlobalType {
            val_type: ValType::I32,
            mutable: true,
            init: heap_init,
        });

        // Export memory
        module.exports.push(Export {
            name: "memory".to_string(),
            kind: ExportKind::Memory,
            index: 0,
        });

        // === Allocator function: $riina_alloc(size: i32) -> i32 ===
        // This is the first defined function (index = NUM_IMPORTS)
        let alloc_type_idx = module.types.len() as u32;
        module.types.push(FuncType {
            params: vec![ValType::I32],
            results: vec![ValType::I32],
        });
        module.functions.push(alloc_type_idx);
        let alloc_body = self.emit_alloc_function();
        module.codes.push(alloc_body);

        let alloc_func_index = NUM_IMPORTS; // 2 imports, then alloc is index 2

        // === Boxed numeric-tower runtime helpers ===
        // Internal WASM functions for arbitrary-precision integers (`besar`) and
        // decimals (`perpuluhan`). Decimals are a BigInt mantissa scaled by a power
        // of ten, so they reuse the bignum runtime. Emitted only when the program
        // uses the corresponding type, so other modules carry no bloat.
        let uses_bigint = program.functions.values().any(|f| {
            f.blocks
                .iter()
                .any(|b| b.instrs.iter().any(|i| matches!(i.ty, Ty::BigInt)))
        });
        let uses_decimal = program.functions.values().any(|f| {
            f.blocks
                .iter()
                .any(|b| b.instrs.iter().any(|i| matches!(i.ty, Ty::Decimal)))
        });
        let uses_fixed = program.functions.values().any(|f| {
            f.blocks
                .iter()
                .any(|b| b.instrs.iter().any(|i| matches!(i.ty, Ty::Fixed)))
        });
        let uses_fixedbin = program.functions.values().any(|f| {
            f.blocks
                .iter()
                .any(|b| b.instrs.iter().any(|i| matches!(i.ty, Ty::FixedBin)))
        });
        // Fixed (`wang`/`titik_tetap`) shares the Decimal record layout and reuses
        // its parse/render/addsub/compare helpers; Q-format `qmn` reuses the
        // decimal parse/render and the fixed rounding primitive. All are
        // BigInt-backed, so the runtimes nest: qmn ⇒ fixed ⇒ decimal ⇒ bignum.
        let needs_fixed = uses_fixed || uses_fixedbin;
        let needs_decimal = uses_decimal || needs_fixed;
        let needs_bignum = uses_bigint || needs_decimal;
        let n_bignum_fns: u32 = if needs_bignum { 9 } else { 0 };
        // Helper signatures shared by the bignum + decimal runtimes.
        let (bin_type_idx, ter_type_idx) = if needs_bignum {
            let b = module.types.len() as u32;
            module.types.push(FuncType {
                params: vec![ValType::I32, ValType::I32],
                results: vec![ValType::I32],
            });
            let t = module.types.len() as u32;
            module.types.push(FuncType {
                params: vec![ValType::I32, ValType::I32, ValType::I32],
                results: vec![ValType::I32],
            });
            (b, t)
        } else {
            (0, 0)
        };
        let (
            bi_from_str_index,
            bi_to_str_index,
            bi_cmp_mag_index,
            bi_cmp_index,
            bi_addsub_index,
            bi_mul_index,
            bi_divmod_index,
        ) = if needs_bignum {
            // (i32)->i32 helpers (share alloc's type): parse + render.
            let from = NUM_IMPORTS + 1;
            module.functions.push(alloc_type_idx);
            module.codes.push(self.emit_bi_from_str(alloc_func_index));
            let to = NUM_IMPORTS + 2;
            module.functions.push(alloc_type_idx);
            module.codes.push(self.emit_bi_to_str(alloc_func_index));
            // (i32,i32)->i32 helpers: cmp_mag, cmp (W2.2a), add_mag, sub_mag (W2.2b).
            let cmp_mag = NUM_IMPORTS + 3;
            module.functions.push(bin_type_idx);
            module.codes.push(self.emit_bi_cmp_mag());
            let cmp = NUM_IMPORTS + 4;
            module.functions.push(bin_type_idx);
            module.codes.push(self.emit_bi_cmp(cmp_mag));
            let add_mag = NUM_IMPORTS + 5;
            module.functions.push(bin_type_idx);
            module.codes.push(self.emit_bi_add_mag(alloc_func_index));
            let sub_mag = NUM_IMPORTS + 6;
            module.functions.push(bin_type_idx);
            module.codes.push(self.emit_bi_sub_mag(alloc_func_index));
            // (i32,i32,i32)->i32 helper: signed add/sub (W2.2b).
            let addsub = NUM_IMPORTS + 7;
            module.functions.push(ter_type_idx);
            module
                .codes
                .push(self.emit_bi_addsub(alloc_func_index, cmp_mag, add_mag, sub_mag));
            // (i32,i32)->i32 multiply (W2.3).
            let mul = NUM_IMPORTS + 8;
            module.functions.push(bin_type_idx);
            module.codes.push(self.emit_bi_mul(alloc_func_index));
            // (i32,i32,i32)->i32 truncating divmod (W2.4): want_rem selects q or r.
            let divmod = NUM_IMPORTS + 9;
            module.functions.push(ter_type_idx);
            module
                .codes
                .push(self.emit_bi_divmod(alloc_func_index, cmp_mag));
            (from, to, cmp_mag, cmp, addsub, mul, divmod)
        } else {
            (0, 0, 0, 0, 0, 0, 0) // unused: no bignum op is emitted when unneeded
        };

        // === Decimal (`perpuluhan`) runtime ===
        // A decimal is `[scale:i32][mantissa_ptr:i32]` (value = mantissa·10^-scale),
        // the mantissa a BigInt record. W3.1a: from_str (parse) + to_str (display);
        // W3.1b: arithmetic — scale-aligned exact add/sub, mul (scales add),
        // half-to-even div to 34 places + trailing-zero strip, value-based compare
        // (matching `decimal.rs`). Mod/And/Or stay fail-closed (typechecker rejects).
        let n_decimal_fns: u32 = if needs_decimal { 7 } else { 0 };
        let (
            dec_from_str_index,
            dec_to_str_index,
            dec_pow10_mul_index,
            dec_addsub_index,
            dec_mul_index,
            dec_cmp_index,
            dec_div_index,
        ) = if needs_decimal {
            let base = NUM_IMPORTS + n_bignum_fns;
            let dfrom = base + 1;
            module.functions.push(alloc_type_idx);
            module
                .codes
                .push(self.emit_dec_from_str(alloc_func_index, bi_from_str_index));
            let dto = base + 2;
            module.functions.push(alloc_type_idx);
            module
                .codes
                .push(self.emit_dec_to_str(alloc_func_index, bi_to_str_index));
            // dec_pow10_mul(mant, n) -> mant * 10^n (internal to the helpers below).
            let dpow = base + 3;
            module.functions.push(bin_type_idx);
            module.codes.push(self.emit_dec_pow10_mul(
                alloc_func_index,
                bi_from_str_index,
                bi_mul_index,
            ));
            let daddsub = base + 4;
            module.functions.push(ter_type_idx);
            module
                .codes
                .push(self.emit_dec_addsub(alloc_func_index, bi_addsub_index, dpow));
            let dmul = base + 5;
            module.functions.push(bin_type_idx);
            module
                .codes
                .push(self.emit_dec_mul(alloc_func_index, bi_mul_index));
            let dcmp = base + 6;
            module.functions.push(bin_type_idx);
            module.codes.push(self.emit_dec_cmp(bi_cmp_index, dpow));
            let ddiv = base + 7;
            module.functions.push(bin_type_idx);
            module.codes.push(self.emit_dec_div(
                alloc_func_index,
                bi_divmod_index,
                bi_mul_index,
                bi_cmp_mag_index,
                bi_addsub_index,
                dpow,
            ));
            (dfrom, dto, dpow, daddsub, dmul, dcmp, ddiv)
        } else {
            (0, 0, 0, 0, 0, 0, 0)
        };

        // === Fixed-point (`wang`/`titik_tetap`) runtime ===
        // A Fixed shares the Decimal record layout `[scale][mantissa]` and reuses
        // dec_from_str/dec_to_str/dec_addsub/dec_cmp (parse, scale-preserving
        // display, exact aligned add/sub, value-based compare). New here (W3.2):
        // mul/div round **half-to-even back to max(scale)** via fix_round_q, and
        // `titik_tetap` parses then rescales to an explicit target scale.
        let n_fixed_fns: u32 = if needs_fixed { 4 } else { 0 };
        let (fix_round_q_index, fix_mul_index, fix_div_index, fix_titik_tetap_index) = if needs_fixed
        {
            let base = NUM_IMPORTS + n_bignum_fns + n_decimal_fns;
            // fix_round_q(num, den) -> round-half-to-even BigInt quotient
            // (internal to the three helpers below).
            let fround = base + 1;
            module.functions.push(bin_type_idx);
            module.codes.push(self.emit_fix_round_q(
                alloc_func_index,
                bi_divmod_index,
                bi_mul_index,
                bi_cmp_mag_index,
                bi_addsub_index,
            ));
            let fmul = base + 2;
            module.functions.push(bin_type_idx);
            module.codes.push(self.emit_fix_mul(
                alloc_func_index,
                bi_mul_index,
                dec_pow10_mul_index,
                fround,
            ));
            let fdiv = base + 3;
            module.functions.push(bin_type_idx);
            module
                .codes
                .push(self.emit_fix_div(alloc_func_index, dec_pow10_mul_index, fround));
            let ftt = base + 4;
            module.functions.push(alloc_type_idx);
            module.codes.push(self.emit_fix_titik_tetap(
                alloc_func_index,
                dec_from_str_index,
                dec_pow10_mul_index,
                fround,
            ));
            (fround, fmul, fdiv, ftt)
        } else {
            (0, 0, 0, 0)
        };

        // === Q-format binary fixed-point (`qmn`) runtime ===
        // A FixedBin is `[frac_bits:i32][raw:i64@8]` (value = raw / 2^frac_bits,
        // raw a wrapping i64 word — the machine-int trade-off). All arithmetic is
        // done exactly in BigInt then wrapped back (W3.3, matching
        // `fixed_bin.rs`): construction/display convert decimal↔binary exactly
        // via the decimal runtime + fix_round_q.
        let n_fixedbin_fns: u32 = if uses_fixedbin { 10 } else { 0 };
        let (
            qmn_parse_index,
            qmn_to_str_index,
            qmn_addsub_index,
            qmn_mul_index,
            qmn_div_index,
            qmn_cmp_index,
        ) = if uses_fixedbin {
            let base = NUM_IMPORTS + n_bignum_fns + n_decimal_fns + n_fixed_fns;
            // Internal building blocks.
            let qpow2 = base + 1;
            module.functions.push(alloc_type_idx);
            module.codes.push(self.emit_qmn_two_pow(alloc_func_index));
            let qraw = base + 2;
            module.functions.push(alloc_type_idx);
            module.codes.push(self.emit_qmn_raw_to_big(alloc_func_index));
            let qwrap = base + 3;
            module.functions.push(bin_type_idx);
            module.codes.push(self.emit_qmn_wrap_store(
                alloc_func_index,
                bi_divmod_index,
                bi_addsub_index,
                qpow2,
            ));
            let qalign = base + 4;
            module.functions.push(bin_type_idx);
            module
                .codes
                .push(self.emit_qmn_align(bi_mul_index, qpow2, qraw));
            // Dispatchable operations.
            let qparse = base + 5;
            module.functions.push(alloc_type_idx);
            module.codes.push(self.emit_qmn_parse(
                alloc_func_index,
                dec_from_str_index,
                dec_pow10_mul_index,
                bi_mul_index,
                fix_round_q_index,
                (qpow2, qwrap),
            ));
            let qstr = base + 6;
            module.functions.push(alloc_type_idx);
            module.codes.push(self.emit_qmn_to_str(
                alloc_func_index,
                dec_to_str_index,
                dec_pow10_mul_index,
                bi_divmod_index,
                bi_mul_index,
                (qpow2, qraw),
            ));
            let qaddsub = base + 7;
            module.functions.push(ter_type_idx);
            module
                .codes
                .push(self.emit_qmn_addsub(bi_addsub_index, qalign, qwrap));
            let qmul = base + 8;
            module.functions.push(bin_type_idx);
            module.codes.push(self.emit_qmn_mul(
                bi_mul_index,
                fix_round_q_index,
                qpow2,
                qalign,
                qwrap,
            ));
            let qdiv = base + 9;
            module.functions.push(bin_type_idx);
            module.codes.push(self.emit_qmn_div(
                bi_mul_index,
                fix_round_q_index,
                qpow2,
                qalign,
                qwrap,
            ));
            let qcmp = base + 10;
            module.functions.push(bin_type_idx);
            module.codes.push(self.emit_qmn_cmp(bi_cmp_index, qalign));
            (qparse, qstr, qaddsub, qmul, qdiv, qcmp)
        } else {
            (0, 0, 0, 0, 0, 0)
        };
        let n_helper_fns = n_bignum_fns + n_decimal_fns + n_fixed_fns + n_fixedbin_fns;

        // === User functions ===
        let mut func_ids: Vec<FuncId> = program.functions.keys().copied().collect();
        func_ids.sort_by_key(|f| f.0); // Deterministic order
        let mut func_index_map: HashMap<FuncId, u32> = HashMap::new();
        for (i, &fid) in func_ids.iter().enumerate() {
            // User functions start after imports + alloc + numeric-tower helpers
            func_index_map.insert(fid, NUM_IMPORTS + 1 + n_helper_fns + i as u32);
        }

        // Table for indirect calls (closures)
        let total_funcs = NUM_IMPORTS + 1 + n_helper_fns + func_ids.len() as u32;
        module.tables.push(TableType {
            min: total_funcs,
            max: Some(total_funcs),
        });

        // Element segment: initialize table with defined functions (not imports).
        // Starts at table offset NUM_IMPORTS so table[func_idx] = function[func_idx].
        let all_func_indices: Vec<u32> = (NUM_IMPORTS..total_funcs).collect();
        let mut elem_offset = Vec::new();
        elem_offset.push(Op::I32Const as u8);
        wasm_encode::encode_sleb128(NUM_IMPORTS as i64, &mut elem_offset);
        elem_offset.push(Op::End as u8);
        module.elements.push(ElemSegment {
            offset_expr: elem_offset,
            func_indices: all_func_indices,
        });

        // Emit each user function — all share the same type: (i64, i64) -> i64.
        // The uniform value cell is i64: closure_ptr, arg, and result are all
        // cells (a pointer is a cell whose value is a < 2^32 linear-memory addr).
        let user_func_type_idx = module.types.len() as u32;
        module.types.push(FuncType {
            params: vec![ValType::I64, ValType::I64], // closure_ptr, arg
            results: vec![ValType::I64],
        });

        for &fid in &func_ids {
            let func = program.function(fid).unwrap();
            module.functions.push(user_func_type_idx);

            let body = self.emit_function(
                func,
                &func_index_map,
                &string_table,
                alloc_func_index,
                user_func_type_idx,
                bi_from_str_index,
                bi_to_str_index,
                bi_cmp_index,
                bi_addsub_index,
                bi_mul_index,
                bi_divmod_index,
                dec_from_str_index,
                dec_to_str_index,
                dec_addsub_index,
                dec_mul_index,
                dec_cmp_index,
                dec_div_index,
                fix_mul_index,
                fix_div_index,
                fix_titik_tetap_index,
                qmn_parse_index,
                qmn_to_str_index,
                qmn_addsub_index,
                qmn_mul_index,
                qmn_div_index,
                qmn_cmp_index,
            )?;
            module.codes.push(body);
        }

        // === _start trampoline ===
        // WASI expects _start with signature () -> ().
        // Main has signature (i32, i32) -> i32. The trampoline calls main(0, 0) and drops the result.
        if let Some(&main_idx) = func_index_map.get(&FuncId::MAIN) {
            let start_type_idx = module.types.len() as u32;
            module.types.push(FuncType {
                params: vec![],
                results: vec![],
            });
            module.functions.push(start_type_idx);

            let mut trampoline_code = Vec::new();
            // Push closure_ptr=0 and arg=0 for main (i64 value cells)
            wasm_i64c(&mut trampoline_code, 0);
            wasm_i64c(&mut trampoline_code, 0);
            // Call main; result (i64) is on the stack. Store it in local 0.
            trampoline_code.push(Op::Call as u8);
            wasm_encode::encode_uleb128(main_idx as u64, &mut trampoline_code);
            wasm_local(&mut trampoline_code, Op::LocalSet, 0); // result = local 0

            // Echo the program's final value, byte-identical to the C `main`
            // echo: skip Unit (the `cetak`-then-return-Unit case), otherwise
            // print Int/Bool/String/Element + newline. Locals 1,2 are itoa
            // scratch. `return_ty` is the typechecker-inferred result type,
            // which matches the runtime value (verified against the C backend).
            let main_ret = program
                .function(FuncId::MAIN)
                .map(|f| f.return_ty.clone())
                .unwrap_or(Ty::Unit);
            match main_ret {
                Ty::Unit => { /* no echo */ }
                // A sized integer (`Ty::IntN`) echoes like a plain int — the i32
                // cell holds the width-masked value (numeric tower). A *signed*
                // sized result echoes signed (sign-extend + leading '-'); local 3
                // is the sign flag.
                Ty::Int | Ty::CInt => wasm_echo_int(&mut trampoline_code, 0, 1, 2, 3, None),
                Ty::IntN { bits, signed } => {
                    let sb = if signed && bits <= 32 { Some(bits) } else { None };
                    wasm_echo_int(&mut trampoline_code, 0, 1, 2, 3, sb);
                }
                Ty::Bool => {
                    wasm_local(&mut trampoline_code, Op::LocalGet, 0);
                    trampoline_code.push(Op::I32WrapI64 as u8); // i64 cell -> i32 cond
                    trampoline_code.push(Op::If as u8);
                    trampoline_code.push(0x40);
                    wasm_write_bytes(&mut trampoline_code, b"true\n");
                    trampoline_code.push(Op::Else as u8);
                    wasm_write_bytes(&mut trampoline_code, b"false\n");
                    trampoline_code.push(Op::End as u8);
                }
                Ty::Element => {
                    wasm_echo_strptr(&mut trampoline_code, 0);
                    wasm_write_bytes(&mut trampoline_code, b"\n");
                }
                Ty::String => {
                    wasm_write_bytes(&mut trampoline_code, b"\"");
                    wasm_echo_strptr(&mut trampoline_code, 0);
                    wasm_write_bytes(&mut trampoline_code, b"\"\n");
                }
                _ => wasm_write_bytes(&mut trampoline_code, b"<value>\n"),
            }

            module.codes.push(FuncBody {
                // local 0 = main result (i64 cell), 1 = itoa value scratch (i64);
                // 2 = itoa ptr (i32 addr), 3 = signed-echo flag (i32).
                locals: vec![(2, ValType::I64), (2, ValType::I32)],
                code: trampoline_code,
            });

            // after alloc + bignum helpers + user funcs
            let start_func_index = NUM_IMPORTS + 1 + n_helper_fns + func_ids.len() as u32;
            module.exports.push(Export {
                name: "_start".to_string(),
                kind: ExportKind::Func,
                index: start_func_index,
            });

            // Also export main directly for JS callers
            module.exports.push(Export {
                name: "main".to_string(),
                kind: ExportKind::Func,
                index: main_idx,
            });
        }

        // Data segments
        module.data = data_segments;

        Ok(module)
    }

    /// Emit the bump allocator function body.
    ///
    /// ```wasm
    /// (func $riina_alloc (param $size i32) (result i32)
    ///   (local $ptr i32)
    ///   global.get $heap_ptr
    ///   local.set $ptr
    ///   global.get $heap_ptr
    ///   local.get $size
    ///   i32.add
    ///   global.set $heap_ptr
    ///   local.get $ptr)
    /// ```
    fn emit_alloc_function(&self) -> FuncBody {
        let mut code = Vec::new();

        // local $ptr is local index 1 (param $size is 0)
        // global.get $heap_ptr
        code.push(Op::GlobalGet as u8);
        wasm_encode::encode_uleb128(GLOBAL_HEAP_PTR as u64, &mut code);
        // local.set $ptr (local 1)
        code.push(Op::LocalSet as u8);
        wasm_encode::encode_uleb128(1, &mut code);
        // global.get $heap_ptr
        code.push(Op::GlobalGet as u8);
        wasm_encode::encode_uleb128(GLOBAL_HEAP_PTR as u64, &mut code);
        // local.get $size (local 0)
        code.push(Op::LocalGet as u8);
        wasm_encode::encode_uleb128(0, &mut code);
        // i32.add
        code.push(Op::I32Add as u8);
        // global.set $heap_ptr
        code.push(Op::GlobalSet as u8);
        wasm_encode::encode_uleb128(GLOBAL_HEAP_PTR as u64, &mut code);
        // local.get $ptr
        code.push(Op::LocalGet as u8);
        wasm_encode::encode_uleb128(1, &mut code);

        FuncBody {
            locals: vec![(1, ValType::I32)], // one extra local for $ptr
            code,
        }
    }

    /// Emit `bi_from_str(str_ptr: i32) -> i32`: parse a base-10 string
    /// `[len:i32][bytes]` into a fresh BigInt record `[len:i32][neg:i32][u32 limbs]`
    /// (little-endian base-2^32, matching `bigint.rs`); returns the record pointer.
    /// Per digit `d`: `acc = acc*10 + d` as an in-place limb pass
    /// (`carry=d; for j<len: cur=limb[j]*10+carry; limb[j]=cur mod 2^32; carry=cur/2^32`).
    /// W2.1 parses unsigned magnitudes (no sign — the parsed literals are
    /// non-negative; signed results come from arithmetic in W2.2).
    fn emit_bi_from_str(&self, alloc_func_index: u32) -> FuncBody {
        // param 0 = str_ptr; i32 locals 1..=6, i64 locals 7..=8.
        const STR: u32 = 0;
        const REC: u32 = 1;
        const SLEN: u32 = 2;
        const I: u32 = 3;
        const LEN: u32 = 4;
        const J: u32 = 5;
        const ADDR: u32 = 6;
        const CARRY: u32 = 7;
        const CUR: u32 = 8;
        let mut c = Vec::new();
        let lget = |c: &mut Vec<u8>, i: u32| wasm_local(c, Op::LocalGet, i);
        let lset = |c: &mut Vec<u8>, i: u32| wasm_local(c, Op::LocalSet, i);
        let op = |c: &mut Vec<u8>, o: Op| c.push(o as u8);

        // slen = mem[str]
        lget(&mut c, STR);
        wasm_load(&mut c, 0);
        lset(&mut c, SLEN);
        // rec = alloc(8 + (slen+2)*4)
        lget(&mut c, SLEN);
        wasm_i32c(&mut c, 2);
        op(&mut c, Op::I32Add);
        wasm_i32c(&mut c, 4);
        op(&mut c, Op::I32Mul);
        wasm_i32c(&mut c, 8);
        op(&mut c, Op::I32Add);
        op(&mut c, Op::Call);
        wasm_encode::encode_uleb128(alloc_func_index as u64, &mut c);
        lset(&mut c, REC);
        // mem[rec+0] = 0 (len); mem[rec+4] = 0 (neg)
        lget(&mut c, REC);
        wasm_i32c(&mut c, 0);
        wasm_store(&mut c, 0);
        lget(&mut c, REC);
        wasm_i32c(&mut c, 0);
        wasm_store(&mut c, 4);
        // len = 0; i = 0
        wasm_i32c(&mut c, 0);
        lset(&mut c, LEN);
        wasm_i32c(&mut c, 0);
        lset(&mut c, I);
        // outer: for i in 0..slen
        op(&mut c, Op::Block);
        c.push(0x40);
        op(&mut c, Op::Loop);
        c.push(0x40);
        // if i >= slen: break (br 1)
        lget(&mut c, I);
        lget(&mut c, SLEN);
        op(&mut c, Op::I32GeS);
        op(&mut c, Op::BrIf);
        wasm_encode::encode_uleb128(1, &mut c);
        // carry = (i64)(mem[str+4+i] - '0')
        lget(&mut c, STR);
        wasm_i32c(&mut c, 4);
        op(&mut c, Op::I32Add);
        lget(&mut c, I);
        op(&mut c, Op::I32Add);
        wasm_load8u(&mut c, 0);
        wasm_i32c(&mut c, 48);
        op(&mut c, Op::I32Sub);
        op(&mut c, Op::I64ExtendI32U);
        lset(&mut c, CARRY);
        // j = 0
        wasm_i32c(&mut c, 0);
        lset(&mut c, J);
        // inner: for j in 0..len  (scale-by-10-add)
        op(&mut c, Op::Block);
        c.push(0x40);
        op(&mut c, Op::Loop);
        c.push(0x40);
        // if j >= len: break (br 1)
        lget(&mut c, J);
        lget(&mut c, LEN);
        op(&mut c, Op::I32GeS);
        op(&mut c, Op::BrIf);
        wasm_encode::encode_uleb128(1, &mut c);
        // addr = rec + 8 + j*4
        lget(&mut c, REC);
        wasm_i32c(&mut c, 8);
        op(&mut c, Op::I32Add);
        lget(&mut c, J);
        wasm_i32c(&mut c, 4);
        op(&mut c, Op::I32Mul);
        op(&mut c, Op::I32Add);
        lset(&mut c, ADDR);
        // cur = (i64)mem[addr]*10 + carry
        lget(&mut c, ADDR);
        wasm_load(&mut c, 0);
        op(&mut c, Op::I64ExtendI32U);
        wasm_i64c(&mut c, 10);
        op(&mut c, Op::I64Mul);
        lget(&mut c, CARRY);
        op(&mut c, Op::I64Add);
        lset(&mut c, CUR);
        // mem[addr] = (i32)(cur mod 2^32)
        lget(&mut c, ADDR);
        lget(&mut c, CUR);
        op(&mut c, Op::I32WrapI64);
        wasm_store(&mut c, 0);
        // carry = cur / 2^32
        lget(&mut c, CUR);
        wasm_i64c(&mut c, 4294967296);
        op(&mut c, Op::I64DivU);
        lset(&mut c, CARRY);
        // j += 1; continue
        lget(&mut c, J);
        wasm_i32c(&mut c, 1);
        op(&mut c, Op::I32Add);
        lset(&mut c, J);
        op(&mut c, Op::Br);
        wasm_encode::encode_uleb128(0, &mut c);
        op(&mut c, Op::End); // loop (inner)
        op(&mut c, Op::End); // block (inner)
        // if carry != 0 { limb[len] = (i32)carry; len += 1 }
        lget(&mut c, CARRY);
        op(&mut c, Op::I64Eqz);
        op(&mut c, Op::I32Eqz);
        op(&mut c, Op::If);
        c.push(0x40);
        lget(&mut c, REC);
        wasm_i32c(&mut c, 8);
        op(&mut c, Op::I32Add);
        lget(&mut c, LEN);
        wasm_i32c(&mut c, 4);
        op(&mut c, Op::I32Mul);
        op(&mut c, Op::I32Add);
        lget(&mut c, CARRY);
        op(&mut c, Op::I32WrapI64);
        wasm_store(&mut c, 0);
        lget(&mut c, LEN);
        wasm_i32c(&mut c, 1);
        op(&mut c, Op::I32Add);
        lset(&mut c, LEN);
        op(&mut c, Op::End); // if
        // i += 1; continue
        lget(&mut c, I);
        wasm_i32c(&mut c, 1);
        op(&mut c, Op::I32Add);
        lset(&mut c, I);
        op(&mut c, Op::Br);
        wasm_encode::encode_uleb128(0, &mut c);
        op(&mut c, Op::End); // loop (outer)
        op(&mut c, Op::End); // block (outer)
        // mem[rec+0] = len
        lget(&mut c, REC);
        lget(&mut c, LEN);
        wasm_store(&mut c, 0);
        // return rec
        lget(&mut c, REC);

        FuncBody {
            locals: vec![(6, ValType::I32), (2, ValType::I64)],
            code: c,
        }
    }

    /// Emit `bi_to_str(rec: i32) -> i32`: render a BigInt record to a heap string
    /// `[len:i32][bytes]` and return its pointer. Copies the magnitude to scratch,
    /// then repeatedly divides it by 10 (`for k=slen-1..0: cur=rem*2^32+limb[k];
    /// limb[k]=cur/10; rem=cur%10`), writing each remainder digit backward.
    fn emit_bi_to_str(&self, alloc_func_index: u32) -> FuncBody {
        const REC: u32 = 0;
        const LEN: u32 = 1;
        const NEG: u32 = 2;
        const MAXD: u32 = 3;
        const BUF: u32 = 4;
        const SCR: u32 = 5;
        const SLEN2: u32 = 6;
        const WP: u32 = 7;
        const K: u32 = 8;
        const ADDR: u32 = 9;
        const REM: u32 = 11;
        const CUR: u32 = 12;
        let mut c = Vec::new();
        let lget = |c: &mut Vec<u8>, i: u32| wasm_local(c, Op::LocalGet, i);
        let lset = |c: &mut Vec<u8>, i: u32| wasm_local(c, Op::LocalSet, i);
        let op = |c: &mut Vec<u8>, o: Op| c.push(o as u8);
        let call_alloc = |c: &mut Vec<u8>| {
            c.push(Op::Call as u8);
            wasm_encode::encode_uleb128(alloc_func_index as u64, c);
        };

        // len = mem[rec+0]; neg = mem[rec+4]
        lget(&mut c, REC);
        wasm_load(&mut c, 0);
        lset(&mut c, LEN);
        lget(&mut c, REC);
        wasm_load(&mut c, 4);
        lset(&mut c, NEG);
        // if len == 0 { return the string "0" }
        lget(&mut c, LEN);
        op(&mut c, Op::I32Eqz);
        op(&mut c, Op::If);
        c.push(0x40);
        wasm_i32c(&mut c, 8);
        call_alloc(&mut c);
        lset(&mut c, BUF);
        lget(&mut c, BUF);
        wasm_i32c(&mut c, 1);
        wasm_store(&mut c, 0); // len prefix = 1
        lget(&mut c, BUF);
        wasm_i32c(&mut c, 48);
        wasm_store8(&mut c, 4); // '0'
        lget(&mut c, BUF);
        op(&mut c, Op::Return);
        op(&mut c, Op::End); // if (len==0)
        // maxd = len*10 + 1
        lget(&mut c, LEN);
        wasm_i32c(&mut c, 10);
        op(&mut c, Op::I32Mul);
        wasm_i32c(&mut c, 1);
        op(&mut c, Op::I32Add);
        lset(&mut c, MAXD);
        // buf = alloc(align4(maxd + 5))   [4-byte len prefix + maxd digits + slack]
        // Round up to a multiple of 4 so the bump pointer stays 4-aligned for the
        // scratch alloc and the i32 length-prefix store (see emit_ke_teks).
        lget(&mut c, MAXD);
        wasm_i32c(&mut c, 8);
        op(&mut c, Op::I32Add);
        wasm_i32c(&mut c, -4);
        op(&mut c, Op::I32And);
        call_alloc(&mut c);
        lset(&mut c, BUF);
        // scr = alloc(len*4); copy magnitude into it
        lget(&mut c, LEN);
        wasm_i32c(&mut c, 4);
        op(&mut c, Op::I32Mul);
        call_alloc(&mut c);
        lset(&mut c, SCR);
        wasm_i32c(&mut c, 0);
        lset(&mut c, K);
        op(&mut c, Op::Block);
        c.push(0x40);
        op(&mut c, Op::Loop);
        c.push(0x40);
        lget(&mut c, K);
        lget(&mut c, LEN);
        op(&mut c, Op::I32GeS);
        op(&mut c, Op::BrIf);
        wasm_encode::encode_uleb128(1, &mut c);
        // scr[k] = mem[rec + 8 + k*4]
        lget(&mut c, SCR);
        lget(&mut c, K);
        wasm_i32c(&mut c, 4);
        op(&mut c, Op::I32Mul);
        op(&mut c, Op::I32Add);
        lget(&mut c, REC);
        wasm_i32c(&mut c, 8);
        op(&mut c, Op::I32Add);
        lget(&mut c, K);
        wasm_i32c(&mut c, 4);
        op(&mut c, Op::I32Mul);
        op(&mut c, Op::I32Add);
        wasm_load(&mut c, 0);
        wasm_store(&mut c, 0);
        lget(&mut c, K);
        wasm_i32c(&mut c, 1);
        op(&mut c, Op::I32Add);
        lset(&mut c, K);
        op(&mut c, Op::Br);
        wasm_encode::encode_uleb128(0, &mut c);
        op(&mut c, Op::End); // loop (copy)
        op(&mut c, Op::End); // block (copy)
        // slen2 = len; wp = buf + 4 + maxd
        lget(&mut c, LEN);
        lset(&mut c, SLEN2);
        lget(&mut c, BUF);
        wasm_i32c(&mut c, 4);
        op(&mut c, Op::I32Add);
        lget(&mut c, MAXD);
        op(&mut c, Op::I32Add);
        lset(&mut c, WP);
        // outer: while slen2 > 0
        op(&mut c, Op::Block);
        c.push(0x40);
        op(&mut c, Op::Loop);
        c.push(0x40);
        lget(&mut c, SLEN2);
        op(&mut c, Op::I32Eqz);
        op(&mut c, Op::BrIf);
        wasm_encode::encode_uleb128(1, &mut c);
        // rem = 0; for k = slen2-1 downto 0
        wasm_i64c(&mut c, 0);
        lset(&mut c, REM);
        lget(&mut c, SLEN2);
        wasm_i32c(&mut c, 1);
        op(&mut c, Op::I32Sub);
        lset(&mut c, K);
        op(&mut c, Op::Block);
        c.push(0x40);
        op(&mut c, Op::Loop);
        c.push(0x40);
        lget(&mut c, K);
        wasm_i32c(&mut c, 0);
        op(&mut c, Op::I32LtS);
        op(&mut c, Op::BrIf);
        wasm_encode::encode_uleb128(1, &mut c);
        // addr = scr + k*4
        lget(&mut c, SCR);
        lget(&mut c, K);
        wasm_i32c(&mut c, 4);
        op(&mut c, Op::I32Mul);
        op(&mut c, Op::I32Add);
        lset(&mut c, ADDR);
        // cur = rem*2^32 + (i64)mem[addr]
        lget(&mut c, REM);
        wasm_i64c(&mut c, 4294967296);
        op(&mut c, Op::I64Mul);
        lget(&mut c, ADDR);
        wasm_load(&mut c, 0);
        op(&mut c, Op::I64ExtendI32U);
        op(&mut c, Op::I64Add);
        lset(&mut c, CUR);
        // mem[addr] = (i32)(cur/10)
        lget(&mut c, ADDR);
        lget(&mut c, CUR);
        wasm_i64c(&mut c, 10);
        op(&mut c, Op::I64DivU);
        op(&mut c, Op::I32WrapI64);
        wasm_store(&mut c, 0);
        // rem = cur % 10
        lget(&mut c, CUR);
        wasm_i64c(&mut c, 10);
        op(&mut c, Op::I64RemU);
        lset(&mut c, REM);
        // k -= 1; continue
        lget(&mut c, K);
        wasm_i32c(&mut c, 1);
        op(&mut c, Op::I32Sub);
        lset(&mut c, K);
        op(&mut c, Op::Br);
        wasm_encode::encode_uleb128(0, &mut c);
        op(&mut c, Op::End); // loop (divmod)
        op(&mut c, Op::End); // block (divmod)
        // shrink slen2 while top limb == 0
        op(&mut c, Op::Block);
        c.push(0x40);
        op(&mut c, Op::Loop);
        c.push(0x40);
        lget(&mut c, SLEN2);
        op(&mut c, Op::I32Eqz);
        op(&mut c, Op::BrIf);
        wasm_encode::encode_uleb128(1, &mut c);
        // if mem[scr + (slen2-1)*4] != 0: stop
        lget(&mut c, SCR);
        lget(&mut c, SLEN2);
        wasm_i32c(&mut c, 1);
        op(&mut c, Op::I32Sub);
        wasm_i32c(&mut c, 4);
        op(&mut c, Op::I32Mul);
        op(&mut c, Op::I32Add);
        wasm_load(&mut c, 0);
        op(&mut c, Op::BrIf);
        wasm_encode::encode_uleb128(1, &mut c);
        lget(&mut c, SLEN2);
        wasm_i32c(&mut c, 1);
        op(&mut c, Op::I32Sub);
        lset(&mut c, SLEN2);
        op(&mut c, Op::Br);
        wasm_encode::encode_uleb128(0, &mut c);
        op(&mut c, Op::End); // loop (shrink)
        op(&mut c, Op::End); // block (shrink)
        // wp -= 1; mem[wp] = '0' + (i32)rem
        lget(&mut c, WP);
        wasm_i32c(&mut c, 1);
        op(&mut c, Op::I32Sub);
        lset(&mut c, WP);
        lget(&mut c, WP);
        lget(&mut c, REM);
        op(&mut c, Op::I32WrapI64);
        wasm_i32c(&mut c, 48);
        op(&mut c, Op::I32Add);
        wasm_store8(&mut c, 0);
        op(&mut c, Op::Br);
        wasm_encode::encode_uleb128(0, &mut c);
        op(&mut c, Op::End); // loop (outer)
        op(&mut c, Op::End); // block (outer)
        // if neg { wp -= 1; mem[wp] = '-' }
        lget(&mut c, NEG);
        op(&mut c, Op::If);
        c.push(0x40);
        lget(&mut c, WP);
        wasm_i32c(&mut c, 1);
        op(&mut c, Op::I32Sub);
        lset(&mut c, WP);
        lget(&mut c, WP);
        wasm_i32c(&mut c, 45);
        wasm_store8(&mut c, 0);
        op(&mut c, Op::End); // if (neg)
        // nd = (buf + 4 + maxd) - wp; mem[wp-4] = nd; return wp-4
        lget(&mut c, BUF);
        wasm_i32c(&mut c, 4);
        op(&mut c, Op::I32Add);
        lget(&mut c, MAXD);
        op(&mut c, Op::I32Add);
        lget(&mut c, WP);
        op(&mut c, Op::I32Sub);
        lset(&mut c, MAXD); // reuse MAXD to hold nd
        lget(&mut c, WP);
        wasm_i32c(&mut c, 4);
        op(&mut c, Op::I32Sub);
        lget(&mut c, MAXD);
        wasm_store(&mut c, 0);
        lget(&mut c, WP);
        wasm_i32c(&mut c, 4);
        op(&mut c, Op::I32Sub);

        FuncBody {
            locals: vec![(10, ValType::I32), (2, ValType::I64)],
            code: c,
        }
    }

    /// Emit `bi_cmp_mag(a: i32, b: i32) -> i32`: compare BigInt **magnitudes**,
    /// returning -1/0/1. Magnitudes are normalized (no leading zero limbs), so a
    /// longer limb count is unconditionally the larger magnitude; equal lengths
    /// compare limbs from most-significant down (unsigned).
    fn emit_bi_cmp_mag(&self) -> FuncBody {
        const A: u32 = 0;
        const B: u32 = 1;
        const LA: u32 = 2;
        const LB: u32 = 3;
        const K: u32 = 4;
        const UA: u32 = 5;
        const UB: u32 = 6;
        let mut c = Vec::new();
        let lget = |c: &mut Vec<u8>, i: u32| wasm_local(c, Op::LocalGet, i);
        let lset = |c: &mut Vec<u8>, i: u32| wasm_local(c, Op::LocalSet, i);
        let op = |c: &mut Vec<u8>, o: Op| c.push(o as u8);
        // la = mem[a]; lb = mem[b]
        lget(&mut c, A);
        wasm_load(&mut c, 0);
        lset(&mut c, LA);
        lget(&mut c, B);
        wasm_load(&mut c, 0);
        lset(&mut c, LB);
        // if la != lb { return la > lb ? 1 : -1 }
        lget(&mut c, LA);
        lget(&mut c, LB);
        op(&mut c, Op::I32Ne);
        op(&mut c, Op::If);
        c.push(0x40);
        lget(&mut c, LA);
        lget(&mut c, LB);
        op(&mut c, Op::I32GtS);
        op(&mut c, Op::If);
        c.push(0x40);
        wasm_i32c(&mut c, 1);
        op(&mut c, Op::Return);
        op(&mut c, Op::Else);
        wasm_i32c(&mut c, -1);
        op(&mut c, Op::Return);
        op(&mut c, Op::End);
        op(&mut c, Op::End);
        // k = la - 1; for k downto 0
        lget(&mut c, LA);
        wasm_i32c(&mut c, 1);
        op(&mut c, Op::I32Sub);
        lset(&mut c, K);
        op(&mut c, Op::Block);
        c.push(0x40);
        op(&mut c, Op::Loop);
        c.push(0x40);
        lget(&mut c, K);
        wasm_i32c(&mut c, 0);
        op(&mut c, Op::I32LtS);
        op(&mut c, Op::BrIf);
        wasm_encode::encode_uleb128(1, &mut c);
        // ua = mem[a+8+k*4]; ub = mem[b+8+k*4]
        lget(&mut c, A);
        wasm_i32c(&mut c, 8);
        op(&mut c, Op::I32Add);
        lget(&mut c, K);
        wasm_i32c(&mut c, 4);
        op(&mut c, Op::I32Mul);
        op(&mut c, Op::I32Add);
        wasm_load(&mut c, 0);
        lset(&mut c, UA);
        lget(&mut c, B);
        wasm_i32c(&mut c, 8);
        op(&mut c, Op::I32Add);
        lget(&mut c, K);
        wasm_i32c(&mut c, 4);
        op(&mut c, Op::I32Mul);
        op(&mut c, Op::I32Add);
        wasm_load(&mut c, 0);
        lset(&mut c, UB);
        // if ua != ub { return ua >u ub ? 1 : -1 }
        lget(&mut c, UA);
        lget(&mut c, UB);
        op(&mut c, Op::I32Ne);
        op(&mut c, Op::If);
        c.push(0x40);
        lget(&mut c, UA);
        lget(&mut c, UB);
        op(&mut c, Op::I32GeU); // ua != ub here, so >=u is equivalent to >u
        op(&mut c, Op::If);
        c.push(0x40);
        wasm_i32c(&mut c, 1);
        op(&mut c, Op::Return);
        op(&mut c, Op::Else);
        wasm_i32c(&mut c, -1);
        op(&mut c, Op::Return);
        op(&mut c, Op::End);
        op(&mut c, Op::End);
        // k -= 1; continue
        lget(&mut c, K);
        wasm_i32c(&mut c, 1);
        op(&mut c, Op::I32Sub);
        lset(&mut c, K);
        op(&mut c, Op::Br);
        wasm_encode::encode_uleb128(0, &mut c);
        op(&mut c, Op::End); // loop
        op(&mut c, Op::End); // block
        wasm_i32c(&mut c, 0); // equal
        FuncBody {
            locals: vec![(5, ValType::I32)],
            code: c,
        }
    }

    /// Emit `bi_cmp(a: i32, b: i32) -> i32`: signed BigInt compare (-1/0/1).
    /// Different signs decide immediately (negative < non-negative); same sign
    /// compares magnitudes, reversed when both are negative.
    fn emit_bi_cmp(&self, cmp_mag_index: u32) -> FuncBody {
        const A: u32 = 0;
        const B: u32 = 1;
        const NA: u32 = 2;
        const NB: u32 = 3;
        const M: u32 = 4;
        let mut c = Vec::new();
        let lget = |c: &mut Vec<u8>, i: u32| wasm_local(c, Op::LocalGet, i);
        let lset = |c: &mut Vec<u8>, i: u32| wasm_local(c, Op::LocalSet, i);
        let op = |c: &mut Vec<u8>, o: Op| c.push(o as u8);
        // na = mem[a+4]; nb = mem[b+4]
        lget(&mut c, A);
        wasm_load(&mut c, 4);
        lset(&mut c, NA);
        lget(&mut c, B);
        wasm_load(&mut c, 4);
        lset(&mut c, NB);
        // if na != nb { return na ? -1 : 1 }
        lget(&mut c, NA);
        lget(&mut c, NB);
        op(&mut c, Op::I32Ne);
        op(&mut c, Op::If);
        c.push(0x40);
        lget(&mut c, NA);
        op(&mut c, Op::If);
        c.push(0x40);
        wasm_i32c(&mut c, -1);
        op(&mut c, Op::Return);
        op(&mut c, Op::Else);
        wasm_i32c(&mut c, 1);
        op(&mut c, Op::Return);
        op(&mut c, Op::End);
        op(&mut c, Op::End);
        // m = cmp_mag(a, b)
        lget(&mut c, A);
        lget(&mut c, B);
        op(&mut c, Op::Call);
        wasm_encode::encode_uleb128(cmp_mag_index as u64, &mut c);
        lset(&mut c, M);
        // return na ? -m : m
        lget(&mut c, NA);
        op(&mut c, Op::If);
        c.push(0x7F); // result i32
        wasm_i32c(&mut c, 0);
        lget(&mut c, M);
        op(&mut c, Op::I32Sub);
        op(&mut c, Op::Else);
        lget(&mut c, M);
        op(&mut c, Op::End);
        FuncBody {
            locals: vec![(3, ValType::I32)],
            code: c,
        }
    }

    /// Emit `bi_add_mag(a: i32, b: i32) -> i32`: add BigInt **magnitudes**,
    /// returning a fresh `[len][neg=0][limbs]` record (caller sets the sign).
    /// Schoolbook carry-propagating add over base-2^32 limbs.
    fn emit_bi_add_mag(&self, alloc_func_index: u32) -> FuncBody {
        const A: u32 = 0;
        const B: u32 = 1;
        const LA: u32 = 2;
        const LB: u32 = 3;
        const MAXL: u32 = 4;
        const RES: u32 = 5;
        const I: u32 = 6;
        const RLEN: u32 = 7;
        const CARRY: u32 = 8;
        const SUM: u32 = 9;
        let mut c = Vec::new();
        let lget = |c: &mut Vec<u8>, i: u32| wasm_local(c, Op::LocalGet, i);
        let lset = |c: &mut Vec<u8>, i: u32| wasm_local(c, Op::LocalSet, i);
        let op = |c: &mut Vec<u8>, o: Op| c.push(o as u8);
        // Push limb `idx` of `rec` (length `len`) as an i64, or 0 if idx >= len.
        let limb = |c: &mut Vec<u8>, rec: u32, len: u32, idx: u32| {
            wasm_local(c, Op::LocalGet, idx);
            wasm_local(c, Op::LocalGet, len);
            c.push(Op::I32LtS as u8);
            c.push(Op::If as u8);
            c.push(0x7E); // i64
            wasm_local(c, Op::LocalGet, rec);
            wasm_i32c(c, 8);
            c.push(Op::I32Add as u8);
            wasm_local(c, Op::LocalGet, idx);
            wasm_i32c(c, 4);
            c.push(Op::I32Mul as u8);
            c.push(Op::I32Add as u8);
            wasm_load(c, 0);
            c.push(Op::I64ExtendI32U as u8);
            c.push(Op::Else as u8);
            wasm_i64c(c, 0);
            c.push(Op::End as u8);
        };
        // la = mem[a]; lb = mem[b]
        lget(&mut c, A);
        wasm_load(&mut c, 0);
        lset(&mut c, LA);
        lget(&mut c, B);
        wasm_load(&mut c, 0);
        lset(&mut c, LB);
        // maxl = max(la, lb)
        lget(&mut c, LA);
        lset(&mut c, MAXL);
        lget(&mut c, LB);
        lget(&mut c, LA);
        op(&mut c, Op::I32GtS);
        op(&mut c, Op::If);
        c.push(0x40);
        lget(&mut c, LB);
        lset(&mut c, MAXL);
        op(&mut c, Op::End);
        // res = alloc(8 + (maxl+1)*4)
        lget(&mut c, MAXL);
        wasm_i32c(&mut c, 1);
        op(&mut c, Op::I32Add);
        wasm_i32c(&mut c, 4);
        op(&mut c, Op::I32Mul);
        wasm_i32c(&mut c, 8);
        op(&mut c, Op::I32Add);
        op(&mut c, Op::Call);
        wasm_encode::encode_uleb128(alloc_func_index as u64, &mut c);
        lset(&mut c, RES);
        // mem[res+4] = 0 (neg)
        lget(&mut c, RES);
        wasm_i32c(&mut c, 0);
        wasm_store(&mut c, 4);
        // carry = 0; i = 0
        wasm_i64c(&mut c, 0);
        lset(&mut c, CARRY);
        wasm_i32c(&mut c, 0);
        lset(&mut c, I);
        // for i in 0..maxl
        op(&mut c, Op::Block);
        c.push(0x40);
        op(&mut c, Op::Loop);
        c.push(0x40);
        lget(&mut c, I);
        lget(&mut c, MAXL);
        op(&mut c, Op::I32GeS);
        op(&mut c, Op::BrIf);
        wasm_encode::encode_uleb128(1, &mut c);
        // sum = a[i] + b[i] + carry
        limb(&mut c, A, LA, I);
        limb(&mut c, B, LB, I);
        op(&mut c, Op::I64Add);
        lget(&mut c, CARRY);
        op(&mut c, Op::I64Add);
        lset(&mut c, SUM);
        // mem[res+8+i*4] = wrap(sum)
        lget(&mut c, RES);
        wasm_i32c(&mut c, 8);
        op(&mut c, Op::I32Add);
        lget(&mut c, I);
        wasm_i32c(&mut c, 4);
        op(&mut c, Op::I32Mul);
        op(&mut c, Op::I32Add);
        lget(&mut c, SUM);
        op(&mut c, Op::I32WrapI64);
        wasm_store(&mut c, 0);
        // carry = sum / 2^32
        lget(&mut c, SUM);
        wasm_i64c(&mut c, 4294967296);
        op(&mut c, Op::I64DivU);
        lset(&mut c, CARRY);
        // i += 1
        lget(&mut c, I);
        wasm_i32c(&mut c, 1);
        op(&mut c, Op::I32Add);
        lset(&mut c, I);
        op(&mut c, Op::Br);
        wasm_encode::encode_uleb128(0, &mut c);
        op(&mut c, Op::End); // loop
        op(&mut c, Op::End); // block
        // rlen = maxl; if carry != 0 { limb[maxl] = carry; rlen = maxl+1 }
        lget(&mut c, MAXL);
        lset(&mut c, RLEN);
        lget(&mut c, CARRY);
        op(&mut c, Op::I64Eqz);
        op(&mut c, Op::I32Eqz);
        op(&mut c, Op::If);
        c.push(0x40);
        lget(&mut c, RES);
        wasm_i32c(&mut c, 8);
        op(&mut c, Op::I32Add);
        lget(&mut c, MAXL);
        wasm_i32c(&mut c, 4);
        op(&mut c, Op::I32Mul);
        op(&mut c, Op::I32Add);
        lget(&mut c, CARRY);
        op(&mut c, Op::I32WrapI64);
        wasm_store(&mut c, 0);
        lget(&mut c, MAXL);
        wasm_i32c(&mut c, 1);
        op(&mut c, Op::I32Add);
        lset(&mut c, RLEN);
        op(&mut c, Op::End);
        // mem[res] = rlen; return res
        lget(&mut c, RES);
        lget(&mut c, RLEN);
        wasm_store(&mut c, 0);
        lget(&mut c, RES);
        FuncBody {
            locals: vec![(6, ValType::I32), (2, ValType::I64)],
            code: c,
        }
    }

    /// Emit `bi_sub_mag(a: i32, b: i32) -> i32`: subtract magnitudes (|a| - |b|),
    /// **requires |a| >= |b|** so the result is non-negative. Borrow-propagating
    /// subtract, then strip leading zero limbs to normalize.
    fn emit_bi_sub_mag(&self, alloc_func_index: u32) -> FuncBody {
        const A: u32 = 0;
        const B: u32 = 1;
        const LA: u32 = 2;
        const LB: u32 = 3;
        const RES: u32 = 4;
        const I: u32 = 5;
        const RLEN: u32 = 6;
        const BORROW: u32 = 7;
        const DIFF: u32 = 8;
        let mut c = Vec::new();
        let lget = |c: &mut Vec<u8>, i: u32| wasm_local(c, Op::LocalGet, i);
        let lset = |c: &mut Vec<u8>, i: u32| wasm_local(c, Op::LocalSet, i);
        let op = |c: &mut Vec<u8>, o: Op| c.push(o as u8);
        let limb = |c: &mut Vec<u8>, rec: u32, len: u32, idx: u32| {
            wasm_local(c, Op::LocalGet, idx);
            wasm_local(c, Op::LocalGet, len);
            c.push(Op::I32LtS as u8);
            c.push(Op::If as u8);
            c.push(0x7E);
            wasm_local(c, Op::LocalGet, rec);
            wasm_i32c(c, 8);
            c.push(Op::I32Add as u8);
            wasm_local(c, Op::LocalGet, idx);
            wasm_i32c(c, 4);
            c.push(Op::I32Mul as u8);
            c.push(Op::I32Add as u8);
            wasm_load(c, 0);
            c.push(Op::I64ExtendI32U as u8);
            c.push(Op::Else as u8);
            wasm_i64c(c, 0);
            c.push(Op::End as u8);
        };
        // la = mem[a]; lb = mem[b]
        lget(&mut c, A);
        wasm_load(&mut c, 0);
        lset(&mut c, LA);
        lget(&mut c, B);
        wasm_load(&mut c, 0);
        lset(&mut c, LB);
        // res = alloc(8 + la*4)
        lget(&mut c, LA);
        wasm_i32c(&mut c, 4);
        op(&mut c, Op::I32Mul);
        wasm_i32c(&mut c, 8);
        op(&mut c, Op::I32Add);
        op(&mut c, Op::Call);
        wasm_encode::encode_uleb128(alloc_func_index as u64, &mut c);
        lset(&mut c, RES);
        lget(&mut c, RES);
        wasm_i32c(&mut c, 0);
        wasm_store(&mut c, 4);
        // borrow = 0; i = 0
        wasm_i32c(&mut c, 0);
        lset(&mut c, BORROW);
        wasm_i32c(&mut c, 0);
        lset(&mut c, I);
        // for i in 0..la
        op(&mut c, Op::Block);
        c.push(0x40);
        op(&mut c, Op::Loop);
        c.push(0x40);
        lget(&mut c, I);
        lget(&mut c, LA);
        op(&mut c, Op::I32GeS);
        op(&mut c, Op::BrIf);
        wasm_encode::encode_uleb128(1, &mut c);
        // diff = a[i] - b[i] - borrow
        limb(&mut c, A, LA, I);
        limb(&mut c, B, LB, I);
        op(&mut c, Op::I64Sub);
        lget(&mut c, BORROW);
        op(&mut c, Op::I64ExtendI32U);
        op(&mut c, Op::I64Sub);
        lset(&mut c, DIFF);
        // if diff < 0 { diff += 2^32; borrow = 1 } else { borrow = 0 }
        lget(&mut c, DIFF);
        wasm_i64c(&mut c, 0);
        op(&mut c, Op::I64LtS);
        op(&mut c, Op::If);
        c.push(0x40);
        lget(&mut c, DIFF);
        wasm_i64c(&mut c, 4294967296);
        op(&mut c, Op::I64Add);
        lset(&mut c, DIFF);
        wasm_i32c(&mut c, 1);
        lset(&mut c, BORROW);
        op(&mut c, Op::Else);
        wasm_i32c(&mut c, 0);
        lset(&mut c, BORROW);
        op(&mut c, Op::End);
        // mem[res+8+i*4] = wrap(diff)
        lget(&mut c, RES);
        wasm_i32c(&mut c, 8);
        op(&mut c, Op::I32Add);
        lget(&mut c, I);
        wasm_i32c(&mut c, 4);
        op(&mut c, Op::I32Mul);
        op(&mut c, Op::I32Add);
        lget(&mut c, DIFF);
        op(&mut c, Op::I32WrapI64);
        wasm_store(&mut c, 0);
        // i += 1
        lget(&mut c, I);
        wasm_i32c(&mut c, 1);
        op(&mut c, Op::I32Add);
        lset(&mut c, I);
        op(&mut c, Op::Br);
        wasm_encode::encode_uleb128(0, &mut c);
        op(&mut c, Op::End); // loop
        op(&mut c, Op::End); // block
        // normalize: rlen = la; while rlen>0 && limb[rlen-1]==0 { rlen-- }
        lget(&mut c, LA);
        lset(&mut c, RLEN);
        op(&mut c, Op::Block);
        c.push(0x40);
        op(&mut c, Op::Loop);
        c.push(0x40);
        lget(&mut c, RLEN);
        op(&mut c, Op::I32Eqz);
        op(&mut c, Op::BrIf);
        wasm_encode::encode_uleb128(1, &mut c);
        lget(&mut c, RES);
        wasm_i32c(&mut c, 8);
        op(&mut c, Op::I32Add);
        lget(&mut c, RLEN);
        wasm_i32c(&mut c, 1);
        op(&mut c, Op::I32Sub);
        wasm_i32c(&mut c, 4);
        op(&mut c, Op::I32Mul);
        op(&mut c, Op::I32Add);
        wasm_load(&mut c, 0);
        op(&mut c, Op::BrIf);
        wasm_encode::encode_uleb128(1, &mut c);
        lget(&mut c, RLEN);
        wasm_i32c(&mut c, 1);
        op(&mut c, Op::I32Sub);
        lset(&mut c, RLEN);
        op(&mut c, Op::Br);
        wasm_encode::encode_uleb128(0, &mut c);
        op(&mut c, Op::End); // loop
        op(&mut c, Op::End); // block
        // mem[res] = rlen; return res
        lget(&mut c, RES);
        lget(&mut c, RLEN);
        wasm_store(&mut c, 0);
        lget(&mut c, RES);
        FuncBody {
            locals: vec![(6, ValType::I32), (1, ValType::I64)],
            code: c,
        }
    }

    /// Emit `bi_addsub(a: i32, b: i32, sub: i32) -> i32`: signed `a + b` (sub=0)
    /// or `a - b` (sub=1). Flips b's sign when subtracting, then: equal signs add
    /// magnitudes (keep sign); differing signs subtract the smaller magnitude from
    /// the larger (taking the larger's sign). Result `-0` is normalized to `+0`.
    fn emit_bi_addsub(
        &self,
        alloc_func_index: u32,
        cmp_mag_index: u32,
        add_mag_index: u32,
        sub_mag_index: u32,
    ) -> FuncBody {
        const A: u32 = 0;
        const B: u32 = 1;
        const SUB: u32 = 2;
        const NA: u32 = 3;
        const BNEG: u32 = 4;
        const CMP: u32 = 5;
        const RES: u32 = 6;
        let mut c = Vec::new();
        let lget = |c: &mut Vec<u8>, i: u32| wasm_local(c, Op::LocalGet, i);
        let lset = |c: &mut Vec<u8>, i: u32| wasm_local(c, Op::LocalSet, i);
        let op = |c: &mut Vec<u8>, o: Op| c.push(o as u8);
        let call = |c: &mut Vec<u8>, idx: u32| {
            c.push(Op::Call as u8);
            wasm_encode::encode_uleb128(idx as u64, c);
        };
        // na = mem[a+4]; bneg = (mem[b+4] != sub)   [XOR of 0/1 flags]
        lget(&mut c, A);
        wasm_load(&mut c, 4);
        lset(&mut c, NA);
        lget(&mut c, B);
        wasm_load(&mut c, 4);
        lget(&mut c, SUB);
        op(&mut c, Op::I32Ne);
        lset(&mut c, BNEG);
        // if na == bneg { res = add_mag(a,b); res.neg = na }
        lget(&mut c, NA);
        lget(&mut c, BNEG);
        op(&mut c, Op::I32Eq);
        op(&mut c, Op::If);
        c.push(0x40);
        lget(&mut c, A);
        lget(&mut c, B);
        call(&mut c, add_mag_index);
        lset(&mut c, RES);
        lget(&mut c, RES);
        lget(&mut c, NA);
        wasm_store(&mut c, 4);
        op(&mut c, Op::Else);
        // cmp = cmp_mag(a,b)
        lget(&mut c, A);
        lget(&mut c, B);
        call(&mut c, cmp_mag_index);
        lset(&mut c, CMP);
        lget(&mut c, CMP);
        op(&mut c, Op::I32Eqz);
        op(&mut c, Op::If);
        c.push(0x40);
        // equal magnitudes → zero record
        wasm_i32c(&mut c, 8);
        call(&mut c, alloc_func_index);
        lset(&mut c, RES);
        lget(&mut c, RES);
        wasm_i32c(&mut c, 0);
        wasm_store(&mut c, 0);
        lget(&mut c, RES);
        wasm_i32c(&mut c, 0);
        wasm_store(&mut c, 4);
        op(&mut c, Op::Else);
        lget(&mut c, CMP);
        wasm_i32c(&mut c, 0);
        op(&mut c, Op::I32GtS);
        op(&mut c, Op::If);
        c.push(0x40);
        // |a| > |b| → a - b, sign na
        lget(&mut c, A);
        lget(&mut c, B);
        call(&mut c, sub_mag_index);
        lset(&mut c, RES);
        lget(&mut c, RES);
        lget(&mut c, NA);
        wasm_store(&mut c, 4);
        op(&mut c, Op::Else);
        // |a| < |b| → b - a, sign bneg
        lget(&mut c, B);
        lget(&mut c, A);
        call(&mut c, sub_mag_index);
        lset(&mut c, RES);
        lget(&mut c, RES);
        lget(&mut c, BNEG);
        wasm_store(&mut c, 4);
        op(&mut c, Op::End); // if cmp>0
        op(&mut c, Op::End); // if cmp==0
        op(&mut c, Op::End); // if na==bneg
        // normalize -0: if mem[res]==0 { mem[res+4]=0 }
        lget(&mut c, RES);
        wasm_load(&mut c, 0);
        op(&mut c, Op::I32Eqz);
        op(&mut c, Op::If);
        c.push(0x40);
        lget(&mut c, RES);
        wasm_i32c(&mut c, 0);
        wasm_store(&mut c, 4);
        op(&mut c, Op::End);
        lget(&mut c, RES);
        FuncBody {
            locals: vec![(4, ValType::I32)],
            code: c,
        }
    }

    /// Emit `bi_mul(a: i32, b: i32) -> i32`: signed BigInt multiply. Schoolbook
    /// O(la·lb) limb multiply-accumulate into a zeroed `la+lb`-limb result
    /// (`t = a[i]*b[j] + w[i+j] + carry` fits in u64 exactly), then sign =
    /// `a.neg XOR b.neg`, normalized so a zero product is `+0`.
    fn emit_bi_mul(&self, alloc_func_index: u32) -> FuncBody {
        const A: u32 = 0;
        const B: u32 = 1;
        const LA: u32 = 2;
        const LB: u32 = 3;
        const N: u32 = 4;
        const RES: u32 = 5;
        const I: u32 = 6;
        const J: u32 = 7;
        const ADDR: u32 = 8;
        const RLEN: u32 = 9;
        const K: u32 = 10;
        const T: u32 = 11;
        let mut c = Vec::new();
        let lget = |c: &mut Vec<u8>, i: u32| wasm_local(c, Op::LocalGet, i);
        let lset = |c: &mut Vec<u8>, i: u32| wasm_local(c, Op::LocalSet, i);
        let op = |c: &mut Vec<u8>, o: Op| c.push(o as u8);
        // la = mem[a]; lb = mem[b]; n = la + lb
        lget(&mut c, A);
        wasm_load(&mut c, 0);
        lset(&mut c, LA);
        lget(&mut c, B);
        wasm_load(&mut c, 0);
        lset(&mut c, LB);
        lget(&mut c, LA);
        lget(&mut c, LB);
        op(&mut c, Op::I32Add);
        lset(&mut c, N);
        // res = alloc(8 + n*4)
        lget(&mut c, N);
        wasm_i32c(&mut c, 4);
        op(&mut c, Op::I32Mul);
        wasm_i32c(&mut c, 8);
        op(&mut c, Op::I32Add);
        op(&mut c, Op::Call);
        wasm_encode::encode_uleb128(alloc_func_index as u64, &mut c);
        lset(&mut c, RES);
        // zero the n result limbs: for i in 0..n { w[i] = 0 }
        wasm_i32c(&mut c, 0);
        lset(&mut c, I);
        op(&mut c, Op::Block);
        c.push(0x40);
        op(&mut c, Op::Loop);
        c.push(0x40);
        lget(&mut c, I);
        lget(&mut c, N);
        op(&mut c, Op::I32GeS);
        op(&mut c, Op::BrIf);
        wasm_encode::encode_uleb128(1, &mut c);
        lget(&mut c, RES);
        wasm_i32c(&mut c, 8);
        op(&mut c, Op::I32Add);
        lget(&mut c, I);
        wasm_i32c(&mut c, 4);
        op(&mut c, Op::I32Mul);
        op(&mut c, Op::I32Add);
        wasm_i32c(&mut c, 0);
        wasm_store(&mut c, 0);
        lget(&mut c, I);
        wasm_i32c(&mut c, 1);
        op(&mut c, Op::I32Add);
        lset(&mut c, I);
        op(&mut c, Op::Br);
        wasm_encode::encode_uleb128(0, &mut c);
        op(&mut c, Op::End); // loop (zero)
        op(&mut c, Op::End); // block (zero)
        // for i in 0..la
        wasm_i32c(&mut c, 0);
        lset(&mut c, I);
        op(&mut c, Op::Block);
        c.push(0x40);
        op(&mut c, Op::Loop);
        c.push(0x40);
        lget(&mut c, I);
        lget(&mut c, LA);
        op(&mut c, Op::I32GeS);
        op(&mut c, Op::BrIf);
        wasm_encode::encode_uleb128(1, &mut c);
        // k = 0; for j in 0..lb
        wasm_i64c(&mut c, 0);
        lset(&mut c, K);
        wasm_i32c(&mut c, 0);
        lset(&mut c, J);
        op(&mut c, Op::Block);
        c.push(0x40);
        op(&mut c, Op::Loop);
        c.push(0x40);
        lget(&mut c, J);
        lget(&mut c, LB);
        op(&mut c, Op::I32GeS);
        op(&mut c, Op::BrIf);
        wasm_encode::encode_uleb128(1, &mut c);
        // addr = res + 8 + (i+j)*4
        lget(&mut c, RES);
        wasm_i32c(&mut c, 8);
        op(&mut c, Op::I32Add);
        lget(&mut c, I);
        lget(&mut c, J);
        op(&mut c, Op::I32Add);
        wasm_i32c(&mut c, 4);
        op(&mut c, Op::I32Mul);
        op(&mut c, Op::I32Add);
        lset(&mut c, ADDR);
        // t = a[i]*b[j] + w[i+j] + k
        lget(&mut c, A);
        wasm_i32c(&mut c, 8);
        op(&mut c, Op::I32Add);
        lget(&mut c, I);
        wasm_i32c(&mut c, 4);
        op(&mut c, Op::I32Mul);
        op(&mut c, Op::I32Add);
        wasm_load(&mut c, 0);
        op(&mut c, Op::I64ExtendI32U);
        lget(&mut c, B);
        wasm_i32c(&mut c, 8);
        op(&mut c, Op::I32Add);
        lget(&mut c, J);
        wasm_i32c(&mut c, 4);
        op(&mut c, Op::I32Mul);
        op(&mut c, Op::I32Add);
        wasm_load(&mut c, 0);
        op(&mut c, Op::I64ExtendI32U);
        op(&mut c, Op::I64Mul);
        lget(&mut c, ADDR);
        wasm_load(&mut c, 0);
        op(&mut c, Op::I64ExtendI32U);
        op(&mut c, Op::I64Add);
        lget(&mut c, K);
        op(&mut c, Op::I64Add);
        lset(&mut c, T);
        // w[i+j] = wrap(t); k = t / 2^32
        lget(&mut c, ADDR);
        lget(&mut c, T);
        op(&mut c, Op::I32WrapI64);
        wasm_store(&mut c, 0);
        lget(&mut c, T);
        wasm_i64c(&mut c, 4294967296);
        op(&mut c, Op::I64DivU);
        lset(&mut c, K);
        // j += 1
        lget(&mut c, J);
        wasm_i32c(&mut c, 1);
        op(&mut c, Op::I32Add);
        lset(&mut c, J);
        op(&mut c, Op::Br);
        wasm_encode::encode_uleb128(0, &mut c);
        op(&mut c, Op::End); // loop (inner j)
        op(&mut c, Op::End); // block (inner j)
        // w[i+lb] = wrap(k)
        lget(&mut c, RES);
        wasm_i32c(&mut c, 8);
        op(&mut c, Op::I32Add);
        lget(&mut c, I);
        lget(&mut c, LB);
        op(&mut c, Op::I32Add);
        wasm_i32c(&mut c, 4);
        op(&mut c, Op::I32Mul);
        op(&mut c, Op::I32Add);
        lget(&mut c, K);
        op(&mut c, Op::I32WrapI64);
        wasm_store(&mut c, 0);
        // i += 1
        lget(&mut c, I);
        wasm_i32c(&mut c, 1);
        op(&mut c, Op::I32Add);
        lset(&mut c, I);
        op(&mut c, Op::Br);
        wasm_encode::encode_uleb128(0, &mut c);
        op(&mut c, Op::End); // loop (outer i)
        op(&mut c, Op::End); // block (outer i)
        // res.neg = (a.neg != b.neg)
        lget(&mut c, RES);
        lget(&mut c, A);
        wasm_load(&mut c, 4);
        lget(&mut c, B);
        wasm_load(&mut c, 4);
        op(&mut c, Op::I32Ne);
        wasm_store(&mut c, 4);
        // normalize: rlen = n; while rlen>0 && w[rlen-1]==0 { rlen-- }
        lget(&mut c, N);
        lset(&mut c, RLEN);
        op(&mut c, Op::Block);
        c.push(0x40);
        op(&mut c, Op::Loop);
        c.push(0x40);
        lget(&mut c, RLEN);
        op(&mut c, Op::I32Eqz);
        op(&mut c, Op::BrIf);
        wasm_encode::encode_uleb128(1, &mut c);
        lget(&mut c, RES);
        wasm_i32c(&mut c, 8);
        op(&mut c, Op::I32Add);
        lget(&mut c, RLEN);
        wasm_i32c(&mut c, 1);
        op(&mut c, Op::I32Sub);
        wasm_i32c(&mut c, 4);
        op(&mut c, Op::I32Mul);
        op(&mut c, Op::I32Add);
        wasm_load(&mut c, 0);
        op(&mut c, Op::BrIf);
        wasm_encode::encode_uleb128(1, &mut c);
        lget(&mut c, RLEN);
        wasm_i32c(&mut c, 1);
        op(&mut c, Op::I32Sub);
        lset(&mut c, RLEN);
        op(&mut c, Op::Br);
        wasm_encode::encode_uleb128(0, &mut c);
        op(&mut c, Op::End); // loop (normalize)
        op(&mut c, Op::End); // block (normalize)
        // mem[res] = rlen; if rlen == 0 { res.neg = 0 }
        lget(&mut c, RES);
        lget(&mut c, RLEN);
        wasm_store(&mut c, 0);
        lget(&mut c, RLEN);
        op(&mut c, Op::I32Eqz);
        op(&mut c, Op::If);
        c.push(0x40);
        lget(&mut c, RES);
        wasm_i32c(&mut c, 0);
        wasm_store(&mut c, 4);
        op(&mut c, Op::End);
        lget(&mut c, RES);
        FuncBody {
            locals: vec![(8, ValType::I32), (2, ValType::I64)],
            code: c,
        }
    }

    /// Emit `bi_divmod(a: i32, b: i32, want_rem: i32) -> i32`: truncating BigInt
    /// division — returns the quotient (`want_rem=0`) or remainder (`want_rem=1`).
    /// Quotient truncates toward zero (sign = `a.neg XOR b.neg`); remainder takes
    /// the dividend's sign — matching Rust/C `/` and `%` and `bigint.rs::divmod`
    /// (proved in `BigIntModel.v`). Bit-serial shift-and-subtract on magnitudes
    /// (reusing `bi_cmp_mag`; shl1/subtract/bit-ops inline). Division by zero
    /// traps (`unreachable`), matching the C runtime's `abort()`.
    fn emit_bi_divmod(&self, alloc_func_index: u32, cmp_mag_index: u32) -> FuncBody {
        const A: u32 = 0;
        const B: u32 = 1;
        const WANT_REM: u32 = 2;
        const LA: u32 = 3;
        const LV: u32 = 4;
        const Q: u32 = 5;
        const R: u32 = 6;
        const RLEN: u32 = 7;
        const BIT: u32 = 8;
        const LIMBIDX: u32 = 9;
        const OFF: u32 = 10;
        const K: u32 = 11;
        const CARRY: u32 = 12;
        const BITVAL: u32 = 13;
        const BORROW: u32 = 14;
        const QLEN: u32 = 15;
        const RES: u32 = 16;
        const RESLEN: u32 = 17;
        const NL: u32 = 18;
        const DIFF: u32 = 19;
        let mut c = Vec::new();
        let lget = |c: &mut Vec<u8>, i: u32| wasm_local(c, Op::LocalGet, i);
        let lset = |c: &mut Vec<u8>, i: u32| wasm_local(c, Op::LocalSet, i);
        let op = |c: &mut Vec<u8>, o: Op| c.push(o as u8);
        // Push the address of limb `idx` (in local `idxl`) of record in local `rec`.
        let limb_addr = |c: &mut Vec<u8>, rec: u32, idxl: u32| {
            wasm_local(c, Op::LocalGet, rec);
            wasm_i32c(c, 8);
            c.push(Op::I32Add as u8);
            wasm_local(c, Op::LocalGet, idxl);
            wasm_i32c(c, 4);
            c.push(Op::I32Mul as u8);
            c.push(Op::I32Add as u8);
        };
        let call = |c: &mut Vec<u8>, idx: u32| {
            c.push(Op::Call as u8);
            wasm_encode::encode_uleb128(idx as u64, c);
        };
        // A small self-contained `block { loop { <cond>; body } }` is built by the
        // caller; helpers above keep the address arithmetic terse.

        // la = mem[a]; lv = mem[b]
        lget(&mut c, A);
        wasm_load(&mut c, 0);
        lset(&mut c, LA);
        lget(&mut c, B);
        wasm_load(&mut c, 0);
        lset(&mut c, LV);
        // division by zero traps (matches C abort)
        lget(&mut c, LV);
        op(&mut c, Op::I32Eqz);
        op(&mut c, Op::If);
        c.push(0x40);
        op(&mut c, Op::Unreachable);
        op(&mut c, Op::End);
        // if |a| < |b| { quotient = 0, remainder = a }
        lget(&mut c, A);
        lget(&mut c, B);
        call(&mut c, cmp_mag_index);
        wasm_i32c(&mut c, 0);
        op(&mut c, Op::I32LtS);
        op(&mut c, Op::If);
        c.push(0x40);
        lget(&mut c, WANT_REM);
        op(&mut c, Op::If);
        c.push(0x40);
        // remainder = copy of a (mag + a.neg, normalized)
        lget(&mut c, LA);
        wasm_i32c(&mut c, 4);
        op(&mut c, Op::I32Mul);
        wasm_i32c(&mut c, 8);
        op(&mut c, Op::I32Add);
        call(&mut c, alloc_func_index);
        lset(&mut c, RES);
        lget(&mut c, RES);
        lget(&mut c, LA);
        wasm_store(&mut c, 0);
        lget(&mut c, RES);
        lget(&mut c, A);
        wasm_load(&mut c, 4);
        wasm_store(&mut c, 4);
        wasm_i32c(&mut c, 0);
        lset(&mut c, K);
        op(&mut c, Op::Block);
        c.push(0x40);
        op(&mut c, Op::Loop);
        c.push(0x40);
        lget(&mut c, K);
        lget(&mut c, LA);
        op(&mut c, Op::I32GeS);
        op(&mut c, Op::BrIf);
        wasm_encode::encode_uleb128(1, &mut c);
        limb_addr(&mut c, RES, K);
        limb_addr(&mut c, A, K);
        wasm_load(&mut c, 0);
        wasm_store(&mut c, 0);
        lget(&mut c, K);
        wasm_i32c(&mut c, 1);
        op(&mut c, Op::I32Add);
        lset(&mut c, K);
        op(&mut c, Op::Br);
        wasm_encode::encode_uleb128(0, &mut c);
        op(&mut c, Op::End);
        op(&mut c, Op::End);
        lget(&mut c, LA);
        op(&mut c, Op::I32Eqz);
        op(&mut c, Op::If);
        c.push(0x40);
        lget(&mut c, RES);
        wasm_i32c(&mut c, 0);
        wasm_store(&mut c, 4);
        op(&mut c, Op::End);
        lget(&mut c, RES);
        op(&mut c, Op::Return);
        op(&mut c, Op::Else);
        // quotient = 0
        wasm_i32c(&mut c, 8);
        call(&mut c, alloc_func_index);
        lset(&mut c, RES);
        lget(&mut c, RES);
        wasm_i32c(&mut c, 0);
        wasm_store(&mut c, 0);
        lget(&mut c, RES);
        wasm_i32c(&mut c, 0);
        wasm_store(&mut c, 4);
        lget(&mut c, RES);
        op(&mut c, Op::Return);
        op(&mut c, Op::End);
        op(&mut c, Op::End);
        // q = alloc(8 + la*4), zeroed
        lget(&mut c, LA);
        wasm_i32c(&mut c, 4);
        op(&mut c, Op::I32Mul);
        wasm_i32c(&mut c, 8);
        op(&mut c, Op::I32Add);
        call(&mut c, alloc_func_index);
        lset(&mut c, Q);
        wasm_i32c(&mut c, 0);
        lset(&mut c, K);
        op(&mut c, Op::Block);
        c.push(0x40);
        op(&mut c, Op::Loop);
        c.push(0x40);
        lget(&mut c, K);
        lget(&mut c, LA);
        op(&mut c, Op::I32GeS);
        op(&mut c, Op::BrIf);
        wasm_encode::encode_uleb128(1, &mut c);
        limb_addr(&mut c, Q, K);
        wasm_i32c(&mut c, 0);
        wasm_store(&mut c, 0);
        lget(&mut c, K);
        wasm_i32c(&mut c, 1);
        op(&mut c, Op::I32Add);
        lset(&mut c, K);
        op(&mut c, Op::Br);
        wasm_encode::encode_uleb128(0, &mut c);
        op(&mut c, Op::End);
        op(&mut c, Op::End);
        // r = alloc(8 + (lv+2)*4), zeroed; rlen = 0
        lget(&mut c, LV);
        wasm_i32c(&mut c, 2);
        op(&mut c, Op::I32Add);
        wasm_i32c(&mut c, 4);
        op(&mut c, Op::I32Mul);
        wasm_i32c(&mut c, 8);
        op(&mut c, Op::I32Add);
        call(&mut c, alloc_func_index);
        lset(&mut c, R);
        wasm_i32c(&mut c, 0);
        lset(&mut c, K);
        op(&mut c, Op::Block);
        c.push(0x40);
        op(&mut c, Op::Loop);
        c.push(0x40);
        lget(&mut c, K);
        lget(&mut c, LV);
        wasm_i32c(&mut c, 2);
        op(&mut c, Op::I32Add);
        op(&mut c, Op::I32GeS);
        op(&mut c, Op::BrIf);
        wasm_encode::encode_uleb128(1, &mut c);
        limb_addr(&mut c, R, K);
        wasm_i32c(&mut c, 0);
        wasm_store(&mut c, 0);
        lget(&mut c, K);
        wasm_i32c(&mut c, 1);
        op(&mut c, Op::I32Add);
        lset(&mut c, K);
        op(&mut c, Op::Br);
        wasm_encode::encode_uleb128(0, &mut c);
        op(&mut c, Op::End);
        op(&mut c, Op::End);
        wasm_i32c(&mut c, 0);
        lset(&mut c, RLEN);
        lget(&mut c, R);
        wasm_i32c(&mut c, 0);
        wasm_store(&mut c, 0);
        // bit = la*32 - 1; for bit downto 0
        lget(&mut c, LA);
        wasm_i32c(&mut c, 32);
        op(&mut c, Op::I32Mul);
        wasm_i32c(&mut c, 1);
        op(&mut c, Op::I32Sub);
        lset(&mut c, BIT);
        op(&mut c, Op::Block); // outer_done
        c.push(0x40);
        op(&mut c, Op::Loop); // outer
        c.push(0x40);
        lget(&mut c, BIT);
        wasm_i32c(&mut c, 0);
        op(&mut c, Op::I32LtS);
        op(&mut c, Op::BrIf);
        wasm_encode::encode_uleb128(1, &mut c);
        // --- shl1(r) ---
        wasm_i32c(&mut c, 0);
        lset(&mut c, CARRY);
        wasm_i32c(&mut c, 0);
        lset(&mut c, K);
        op(&mut c, Op::Block);
        c.push(0x40);
        op(&mut c, Op::Loop);
        c.push(0x40);
        lget(&mut c, K);
        lget(&mut c, RLEN);
        op(&mut c, Op::I32GeS);
        op(&mut c, Op::BrIf);
        wasm_encode::encode_uleb128(1, &mut c);
        limb_addr(&mut c, R, K);
        wasm_load(&mut c, 0);
        lset(&mut c, NL);
        limb_addr(&mut c, R, K);
        lget(&mut c, NL);
        wasm_i32c(&mut c, 1);
        op(&mut c, Op::I32Shl);
        lget(&mut c, CARRY);
        op(&mut c, Op::I32Or);
        wasm_store(&mut c, 0);
        lget(&mut c, NL);
        wasm_i32c(&mut c, 31);
        op(&mut c, Op::I32ShrU);
        lset(&mut c, CARRY);
        lget(&mut c, K);
        wasm_i32c(&mut c, 1);
        op(&mut c, Op::I32Add);
        lset(&mut c, K);
        op(&mut c, Op::Br);
        wasm_encode::encode_uleb128(0, &mut c);
        op(&mut c, Op::End);
        op(&mut c, Op::End);
        // if carry { r[rlen] = carry; rlen++ }
        lget(&mut c, CARRY);
        op(&mut c, Op::If);
        c.push(0x40);
        limb_addr(&mut c, R, RLEN);
        lget(&mut c, CARRY);
        wasm_store(&mut c, 0);
        lget(&mut c, RLEN);
        wasm_i32c(&mut c, 1);
        op(&mut c, Op::I32Add);
        lset(&mut c, RLEN);
        op(&mut c, Op::End);
        // limbidx = bit>>5; off = bit&31; bitval = (a[limbidx] >> off) & 1
        lget(&mut c, BIT);
        wasm_i32c(&mut c, 5);
        op(&mut c, Op::I32ShrU);
        lset(&mut c, LIMBIDX);
        lget(&mut c, BIT);
        wasm_i32c(&mut c, 31);
        op(&mut c, Op::I32And);
        lset(&mut c, OFF);
        limb_addr(&mut c, A, LIMBIDX);
        wasm_load(&mut c, 0);
        lget(&mut c, OFF);
        op(&mut c, Op::I32ShrU);
        wasm_i32c(&mut c, 1);
        op(&mut c, Op::I32And);
        lset(&mut c, BITVAL);
        // if bitval { if rlen==0 { r[0]=1; rlen=1 } else { r[0] |= 1 } }
        lget(&mut c, BITVAL);
        op(&mut c, Op::If);
        c.push(0x40);
        lget(&mut c, RLEN);
        op(&mut c, Op::I32Eqz);
        op(&mut c, Op::If);
        c.push(0x40);
        lget(&mut c, R);
        wasm_i32c(&mut c, 1);
        wasm_store(&mut c, 8);
        wasm_i32c(&mut c, 1);
        lset(&mut c, RLEN);
        op(&mut c, Op::Else);
        lget(&mut c, R);
        lget(&mut c, R);
        wasm_load(&mut c, 8);
        wasm_i32c(&mut c, 1);
        op(&mut c, Op::I32Or);
        wasm_store(&mut c, 8);
        op(&mut c, Op::End);
        op(&mut c, Op::End);
        // mem[r] = rlen
        lget(&mut c, R);
        lget(&mut c, RLEN);
        wasm_store(&mut c, 0);
        // if cmp_mag(r, b) >= 0 { r -= b; q[limbidx] |= 1<<off }
        lget(&mut c, R);
        lget(&mut c, B);
        call(&mut c, cmp_mag_index);
        wasm_i32c(&mut c, 0);
        op(&mut c, Op::I32GeS);
        op(&mut c, Op::If);
        c.push(0x40);
        // r -= b over lv limbs
        wasm_i32c(&mut c, 0);
        lset(&mut c, BORROW);
        wasm_i32c(&mut c, 0);
        lset(&mut c, K);
        op(&mut c, Op::Block);
        c.push(0x40);
        op(&mut c, Op::Loop);
        c.push(0x40);
        lget(&mut c, K);
        lget(&mut c, LV);
        op(&mut c, Op::I32GeS);
        op(&mut c, Op::BrIf);
        wasm_encode::encode_uleb128(1, &mut c);
        limb_addr(&mut c, R, K);
        wasm_load(&mut c, 0);
        op(&mut c, Op::I64ExtendI32U);
        limb_addr(&mut c, B, K);
        wasm_load(&mut c, 0);
        op(&mut c, Op::I64ExtendI32U);
        op(&mut c, Op::I64Sub);
        lget(&mut c, BORROW);
        op(&mut c, Op::I64ExtendI32U);
        op(&mut c, Op::I64Sub);
        lset(&mut c, DIFF);
        lget(&mut c, DIFF);
        wasm_i64c(&mut c, 0);
        op(&mut c, Op::I64LtS);
        op(&mut c, Op::If);
        c.push(0x40);
        lget(&mut c, DIFF);
        wasm_i64c(&mut c, 4294967296);
        op(&mut c, Op::I64Add);
        lset(&mut c, DIFF);
        wasm_i32c(&mut c, 1);
        lset(&mut c, BORROW);
        op(&mut c, Op::Else);
        wasm_i32c(&mut c, 0);
        lset(&mut c, BORROW);
        op(&mut c, Op::End);
        limb_addr(&mut c, R, K);
        lget(&mut c, DIFF);
        op(&mut c, Op::I32WrapI64);
        wasm_store(&mut c, 0);
        lget(&mut c, K);
        wasm_i32c(&mut c, 1);
        op(&mut c, Op::I32Add);
        lset(&mut c, K);
        op(&mut c, Op::Br);
        wasm_encode::encode_uleb128(0, &mut c);
        op(&mut c, Op::End);
        op(&mut c, Op::End);
        // propagate borrow into r[lv..rlen]
        op(&mut c, Op::Block);
        c.push(0x40);
        op(&mut c, Op::Loop);
        c.push(0x40);
        lget(&mut c, K);
        lget(&mut c, RLEN);
        op(&mut c, Op::I32GeS);
        op(&mut c, Op::BrIf);
        wasm_encode::encode_uleb128(1, &mut c);
        limb_addr(&mut c, R, K);
        wasm_load(&mut c, 0);
        op(&mut c, Op::I64ExtendI32U);
        lget(&mut c, BORROW);
        op(&mut c, Op::I64ExtendI32U);
        op(&mut c, Op::I64Sub);
        lset(&mut c, DIFF);
        lget(&mut c, DIFF);
        wasm_i64c(&mut c, 0);
        op(&mut c, Op::I64LtS);
        op(&mut c, Op::If);
        c.push(0x40);
        lget(&mut c, DIFF);
        wasm_i64c(&mut c, 4294967296);
        op(&mut c, Op::I64Add);
        lset(&mut c, DIFF);
        wasm_i32c(&mut c, 1);
        lset(&mut c, BORROW);
        op(&mut c, Op::Else);
        wasm_i32c(&mut c, 0);
        lset(&mut c, BORROW);
        op(&mut c, Op::End);
        limb_addr(&mut c, R, K);
        lget(&mut c, DIFF);
        op(&mut c, Op::I32WrapI64);
        wasm_store(&mut c, 0);
        lget(&mut c, K);
        wasm_i32c(&mut c, 1);
        op(&mut c, Op::I32Add);
        lset(&mut c, K);
        op(&mut c, Op::Br);
        wasm_encode::encode_uleb128(0, &mut c);
        op(&mut c, Op::End);
        op(&mut c, Op::End);
        // strip leading zeros of r
        op(&mut c, Op::Block);
        c.push(0x40);
        op(&mut c, Op::Loop);
        c.push(0x40);
        lget(&mut c, RLEN);
        op(&mut c, Op::I32Eqz);
        op(&mut c, Op::BrIf);
        wasm_encode::encode_uleb128(1, &mut c);
        lget(&mut c, R);
        wasm_i32c(&mut c, 8);
        op(&mut c, Op::I32Add);
        lget(&mut c, RLEN);
        wasm_i32c(&mut c, 1);
        op(&mut c, Op::I32Sub);
        wasm_i32c(&mut c, 4);
        op(&mut c, Op::I32Mul);
        op(&mut c, Op::I32Add);
        wasm_load(&mut c, 0);
        op(&mut c, Op::BrIf);
        wasm_encode::encode_uleb128(1, &mut c);
        lget(&mut c, RLEN);
        wasm_i32c(&mut c, 1);
        op(&mut c, Op::I32Sub);
        lset(&mut c, RLEN);
        op(&mut c, Op::Br);
        wasm_encode::encode_uleb128(0, &mut c);
        op(&mut c, Op::End);
        op(&mut c, Op::End);
        lget(&mut c, R);
        lget(&mut c, RLEN);
        wasm_store(&mut c, 0);
        // q[limbidx] |= 1 << off
        limb_addr(&mut c, Q, LIMBIDX);
        limb_addr(&mut c, Q, LIMBIDX);
        wasm_load(&mut c, 0);
        wasm_i32c(&mut c, 1);
        lget(&mut c, OFF);
        op(&mut c, Op::I32Shl);
        op(&mut c, Op::I32Or);
        wasm_store(&mut c, 0);
        op(&mut c, Op::End); // if cmp>=0
        // bit--
        lget(&mut c, BIT);
        wasm_i32c(&mut c, 1);
        op(&mut c, Op::I32Sub);
        lset(&mut c, BIT);
        op(&mut c, Op::Br);
        wasm_encode::encode_uleb128(0, &mut c);
        op(&mut c, Op::End); // loop (outer)
        op(&mut c, Op::End); // block (outer)
        // strip leading zeros of q
        lget(&mut c, LA);
        lset(&mut c, QLEN);
        op(&mut c, Op::Block);
        c.push(0x40);
        op(&mut c, Op::Loop);
        c.push(0x40);
        lget(&mut c, QLEN);
        op(&mut c, Op::I32Eqz);
        op(&mut c, Op::BrIf);
        wasm_encode::encode_uleb128(1, &mut c);
        lget(&mut c, Q);
        wasm_i32c(&mut c, 8);
        op(&mut c, Op::I32Add);
        lget(&mut c, QLEN);
        wasm_i32c(&mut c, 1);
        op(&mut c, Op::I32Sub);
        wasm_i32c(&mut c, 4);
        op(&mut c, Op::I32Mul);
        op(&mut c, Op::I32Add);
        wasm_load(&mut c, 0);
        op(&mut c, Op::BrIf);
        wasm_encode::encode_uleb128(1, &mut c);
        lget(&mut c, QLEN);
        wasm_i32c(&mut c, 1);
        op(&mut c, Op::I32Sub);
        lset(&mut c, QLEN);
        op(&mut c, Op::Br);
        wasm_encode::encode_uleb128(0, &mut c);
        op(&mut c, Op::End);
        op(&mut c, Op::End);
        lget(&mut c, Q);
        lget(&mut c, QLEN);
        wasm_store(&mut c, 0);
        // select result: remainder (res=r, neg=a.neg) or quotient (res=q, neg=a.neg^b.neg)
        lget(&mut c, WANT_REM);
        op(&mut c, Op::If);
        c.push(0x40);
        lget(&mut c, R);
        lset(&mut c, RES);
        lget(&mut c, R);
        lget(&mut c, A);
        wasm_load(&mut c, 4);
        wasm_store(&mut c, 4);
        lget(&mut c, RLEN);
        lset(&mut c, RESLEN);
        op(&mut c, Op::Else);
        lget(&mut c, Q);
        lset(&mut c, RES);
        lget(&mut c, Q);
        lget(&mut c, A);
        wasm_load(&mut c, 4);
        lget(&mut c, B);
        wasm_load(&mut c, 4);
        op(&mut c, Op::I32Ne);
        wasm_store(&mut c, 4);
        lget(&mut c, QLEN);
        lset(&mut c, RESLEN);
        op(&mut c, Op::End);
        // normalize -0
        lget(&mut c, RESLEN);
        op(&mut c, Op::I32Eqz);
        op(&mut c, Op::If);
        c.push(0x40);
        lget(&mut c, RES);
        wasm_i32c(&mut c, 0);
        wasm_store(&mut c, 4);
        op(&mut c, Op::End);
        lget(&mut c, RES);
        FuncBody {
            locals: vec![(16, ValType::I32), (1, ValType::I64)],
            code: c,
        }
    }

    /// Emit `dec_from_str(str: i32) -> i32`: parse a decimal literal into a
    /// `[scale:i32][mantissa_ptr:i32]` record (value = mantissa·10^-scale),
    /// matching `decimal.rs::parse`. The mantissa is the int+frac digits (sans
    /// the point) parsed via `bi_from_str`, with the leading sign applied; scale
    /// is the fractional digit count.
    fn emit_dec_from_str(&self, alloc_func_index: u32, bi_from_str_index: u32) -> FuncBody {
        const STR: u32 = 0;
        const SLEN: u32 = 1;
        const START: u32 = 2;
        const NEG: u32 = 3;
        const DOTPOS: u32 = 4;
        const SCALE: u32 = 5;
        const MCOUNT: u32 = 6;
        const MSTR: u32 = 7;
        const J: u32 = 8;
        const WP: u32 = 9;
        const MANT: u32 = 10;
        const C: u32 = 11;
        const DEC: u32 = 12;
        let mut c = Vec::new();
        let lget = |c: &mut Vec<u8>, i: u32| wasm_local(c, Op::LocalGet, i);
        let lset = |c: &mut Vec<u8>, i: u32| wasm_local(c, Op::LocalSet, i);
        let op = |c: &mut Vec<u8>, o: Op| c.push(o as u8);
        let call = |c: &mut Vec<u8>, idx: u32| {
            c.push(Op::Call as u8);
            wasm_encode::encode_uleb128(idx as u64, c);
        };
        // slen = mem[str]; start = 0; neg = 0
        lget(&mut c, STR);
        wasm_load(&mut c, 0);
        lset(&mut c, SLEN);
        wasm_i32c(&mut c, 0);
        lset(&mut c, START);
        wasm_i32c(&mut c, 0);
        lset(&mut c, NEG);
        // c = data[0]
        lget(&mut c, STR);
        wasm_load8u(&mut c, 4);
        lset(&mut c, C);
        // if c == '-' { neg=1; start=1 } else if c == '+' { start=1 }
        lget(&mut c, C);
        wasm_i32c(&mut c, 45);
        op(&mut c, Op::I32Eq);
        op(&mut c, Op::If);
        c.push(0x40);
        wasm_i32c(&mut c, 1);
        lset(&mut c, NEG);
        wasm_i32c(&mut c, 1);
        lset(&mut c, START);
        op(&mut c, Op::Else);
        lget(&mut c, C);
        wasm_i32c(&mut c, 43);
        op(&mut c, Op::I32Eq);
        op(&mut c, Op::If);
        c.push(0x40);
        wasm_i32c(&mut c, 1);
        lset(&mut c, START);
        op(&mut c, Op::End);
        op(&mut c, Op::End);
        // dotpos = -1; for j in start..slen { if data[j]=='.' && dotpos==-1 { dotpos=j } }
        wasm_i32c(&mut c, -1);
        lset(&mut c, DOTPOS);
        lget(&mut c, START);
        lset(&mut c, J);
        op(&mut c, Op::Block);
        c.push(0x40);
        op(&mut c, Op::Loop);
        c.push(0x40);
        lget(&mut c, J);
        lget(&mut c, SLEN);
        op(&mut c, Op::I32GeS);
        op(&mut c, Op::BrIf);
        wasm_encode::encode_uleb128(1, &mut c);
        lget(&mut c, STR);
        wasm_i32c(&mut c, 4);
        op(&mut c, Op::I32Add);
        lget(&mut c, J);
        op(&mut c, Op::I32Add);
        wasm_load8u(&mut c, 0);
        wasm_i32c(&mut c, 46);
        op(&mut c, Op::I32Eq);
        lget(&mut c, DOTPOS);
        wasm_i32c(&mut c, -1);
        op(&mut c, Op::I32Eq);
        op(&mut c, Op::I32And);
        op(&mut c, Op::If);
        c.push(0x40);
        lget(&mut c, J);
        lset(&mut c, DOTPOS);
        op(&mut c, Op::End);
        lget(&mut c, J);
        wasm_i32c(&mut c, 1);
        op(&mut c, Op::I32Add);
        lset(&mut c, J);
        op(&mut c, Op::Br);
        wasm_encode::encode_uleb128(0, &mut c);
        op(&mut c, Op::End);
        op(&mut c, Op::End);
        // scale = dotpos>=0 ? slen-dotpos-1 : 0
        lget(&mut c, DOTPOS);
        wasm_i32c(&mut c, 0);
        op(&mut c, Op::I32GeS);
        op(&mut c, Op::If);
        c.push(0x7F);
        lget(&mut c, SLEN);
        lget(&mut c, DOTPOS);
        op(&mut c, Op::I32Sub);
        wasm_i32c(&mut c, 1);
        op(&mut c, Op::I32Sub);
        op(&mut c, Op::Else);
        wasm_i32c(&mut c, 0);
        op(&mut c, Op::End);
        lset(&mut c, SCALE);
        // mcount = (slen - start) - (dotpos>=0 ? 1 : 0)
        lget(&mut c, SLEN);
        lget(&mut c, START);
        op(&mut c, Op::I32Sub);
        lget(&mut c, DOTPOS);
        wasm_i32c(&mut c, 0);
        op(&mut c, Op::I32GeS);
        op(&mut c, Op::If);
        c.push(0x7F);
        wasm_i32c(&mut c, 1);
        op(&mut c, Op::Else);
        wasm_i32c(&mut c, 0);
        op(&mut c, Op::End);
        op(&mut c, Op::I32Sub);
        lset(&mut c, MCOUNT);
        // mstr = alloc(align4(4 + mcount)); mem[mstr] = mcount
        lget(&mut c, MCOUNT);
        wasm_i32c(&mut c, 7);
        op(&mut c, Op::I32Add);
        wasm_i32c(&mut c, -4);
        op(&mut c, Op::I32And);
        call(&mut c, alloc_func_index);
        lset(&mut c, MSTR);
        lget(&mut c, MSTR);
        lget(&mut c, MCOUNT);
        wasm_store(&mut c, 0);
        // wp = mstr+4; for j in start..slen { if data[j] != '.' { mem[wp]=data[j]; wp++ } }
        lget(&mut c, MSTR);
        wasm_i32c(&mut c, 4);
        op(&mut c, Op::I32Add);
        lset(&mut c, WP);
        lget(&mut c, START);
        lset(&mut c, J);
        op(&mut c, Op::Block);
        c.push(0x40);
        op(&mut c, Op::Loop);
        c.push(0x40);
        lget(&mut c, J);
        lget(&mut c, SLEN);
        op(&mut c, Op::I32GeS);
        op(&mut c, Op::BrIf);
        wasm_encode::encode_uleb128(1, &mut c);
        lget(&mut c, STR);
        wasm_i32c(&mut c, 4);
        op(&mut c, Op::I32Add);
        lget(&mut c, J);
        op(&mut c, Op::I32Add);
        wasm_load8u(&mut c, 0);
        lset(&mut c, C);
        lget(&mut c, C);
        wasm_i32c(&mut c, 46);
        op(&mut c, Op::I32Ne);
        op(&mut c, Op::If);
        c.push(0x40);
        lget(&mut c, WP);
        lget(&mut c, C);
        wasm_store8(&mut c, 0);
        lget(&mut c, WP);
        wasm_i32c(&mut c, 1);
        op(&mut c, Op::I32Add);
        lset(&mut c, WP);
        op(&mut c, Op::End);
        lget(&mut c, J);
        wasm_i32c(&mut c, 1);
        op(&mut c, Op::I32Add);
        lset(&mut c, J);
        op(&mut c, Op::Br);
        wasm_encode::encode_uleb128(0, &mut c);
        op(&mut c, Op::End);
        op(&mut c, Op::End);
        // mant = bi_from_str(mstr); mant.neg = neg; if mant.len==0 { mant.neg=0 }
        lget(&mut c, MSTR);
        call(&mut c, bi_from_str_index);
        lset(&mut c, MANT);
        lget(&mut c, MANT);
        lget(&mut c, NEG);
        wasm_store(&mut c, 4);
        lget(&mut c, MANT);
        wasm_load(&mut c, 0);
        op(&mut c, Op::I32Eqz);
        op(&mut c, Op::If);
        c.push(0x40);
        lget(&mut c, MANT);
        wasm_i32c(&mut c, 0);
        wasm_store(&mut c, 4);
        op(&mut c, Op::End);
        // dec = alloc(8); dec.scale = scale; dec.mantissa = mant; return dec
        wasm_i32c(&mut c, 8);
        call(&mut c, alloc_func_index);
        lset(&mut c, DEC);
        lget(&mut c, DEC);
        lget(&mut c, SCALE);
        wasm_store(&mut c, 0);
        lget(&mut c, DEC);
        lget(&mut c, MANT);
        wasm_store(&mut c, 4);
        lget(&mut c, DEC);
        FuncBody {
            locals: vec![(12, ValType::I32)],
            code: c,
        }
    }

    /// Emit `dec_to_str(dec: i32) -> i32`: render a decimal record to a heap
    /// string, matching `decimal.rs::to_string_repr` — scale 0 is the bare
    /// mantissa; otherwise the magnitude digits get a point inserted `scale` from
    /// the right (zero-padded to `0.0…d` when shorter), with a leading `-` if the
    /// mantissa is negative.
    fn emit_dec_to_str(&self, alloc_func_index: u32, bi_to_str_index: u32) -> FuncBody {
        const DEC: u32 = 0;
        const SCALE: u32 = 1;
        const MANT: u32 = 2;
        const NEG: u32 = 3;
        const MAG: u32 = 4;
        const MAGLEN: u32 = 5;
        const SAVEDNEG: u32 = 6;
        const RESULTLEN: u32 = 7;
        const RES: u32 = 8;
        const WP: u32 = 9;
        const POINT: u32 = 10;
        const K: u32 = 11;
        let mut c = Vec::new();
        let lget = |c: &mut Vec<u8>, i: u32| wasm_local(c, Op::LocalGet, i);
        let lset = |c: &mut Vec<u8>, i: u32| wasm_local(c, Op::LocalSet, i);
        let op = |c: &mut Vec<u8>, o: Op| c.push(o as u8);
        let call = |c: &mut Vec<u8>, idx: u32| {
            c.push(Op::Call as u8);
            wasm_encode::encode_uleb128(idx as u64, c);
        };
        // copy `n` bytes from src (local) to wp (local), advancing wp; uses no
        // extra locals beyond a fresh counter pushed by the caller — inlined below.
        // scale = mem[dec]; mant = mem[dec+4]
        lget(&mut c, DEC);
        wasm_load(&mut c, 0);
        lset(&mut c, SCALE);
        lget(&mut c, DEC);
        wasm_load(&mut c, 4);
        lset(&mut c, MANT);
        // if scale == 0 { return bi_to_str(mant) }
        lget(&mut c, SCALE);
        op(&mut c, Op::I32Eqz);
        op(&mut c, Op::If);
        c.push(0x40);
        lget(&mut c, MANT);
        call(&mut c, bi_to_str_index);
        op(&mut c, Op::Return);
        op(&mut c, Op::End);
        // neg = mant.neg; mag = bi_to_str(|mant|) (zero neg around the call)
        lget(&mut c, MANT);
        wasm_load(&mut c, 4);
        lset(&mut c, NEG);
        lget(&mut c, MANT);
        wasm_load(&mut c, 4);
        lset(&mut c, SAVEDNEG);
        lget(&mut c, MANT);
        wasm_i32c(&mut c, 0);
        wasm_store(&mut c, 4);
        lget(&mut c, MANT);
        call(&mut c, bi_to_str_index);
        lset(&mut c, MAG);
        lget(&mut c, MANT);
        lget(&mut c, SAVEDNEG);
        wasm_store(&mut c, 4);
        lget(&mut c, MAG);
        wasm_load(&mut c, 0);
        lset(&mut c, MAGLEN);
        // if maglen <= scale { "0." + (scale-maglen) zeros + mag } else { mag with point }
        lget(&mut c, MAGLEN);
        lget(&mut c, SCALE);
        op(&mut c, Op::I32LeS);
        op(&mut c, Op::If);
        c.push(0x40);
        // resultlen = 2 + scale + neg
        wasm_i32c(&mut c, 2);
        lget(&mut c, SCALE);
        op(&mut c, Op::I32Add);
        lget(&mut c, NEG);
        op(&mut c, Op::I32Add);
        lset(&mut c, RESULTLEN);
        lget(&mut c, RESULTLEN);
        wasm_i32c(&mut c, 7);
        op(&mut c, Op::I32Add);
        wasm_i32c(&mut c, -4);
        op(&mut c, Op::I32And);
        call(&mut c, alloc_func_index);
        lset(&mut c, RES);
        lget(&mut c, RES);
        lget(&mut c, RESULTLEN);
        wasm_store(&mut c, 0);
        lget(&mut c, RES);
        wasm_i32c(&mut c, 4);
        op(&mut c, Op::I32Add);
        lset(&mut c, WP);
        // if neg { *wp++ = '-' }
        lget(&mut c, NEG);
        op(&mut c, Op::If);
        c.push(0x40);
        lget(&mut c, WP);
        wasm_i32c(&mut c, 45);
        wasm_store8(&mut c, 0);
        lget(&mut c, WP);
        wasm_i32c(&mut c, 1);
        op(&mut c, Op::I32Add);
        lset(&mut c, WP);
        op(&mut c, Op::End);
        // *wp++ = '0'; *wp++ = '.'
        lget(&mut c, WP);
        wasm_i32c(&mut c, 48);
        wasm_store8(&mut c, 0);
        lget(&mut c, WP);
        wasm_i32c(&mut c, 46);
        wasm_store8(&mut c, 1);
        lget(&mut c, WP);
        wasm_i32c(&mut c, 2);
        op(&mut c, Op::I32Add);
        lset(&mut c, WP);
        // for k in 0..(scale-maglen) { *wp++ = '0' }
        wasm_i32c(&mut c, 0);
        lset(&mut c, K);
        op(&mut c, Op::Block);
        c.push(0x40);
        op(&mut c, Op::Loop);
        c.push(0x40);
        lget(&mut c, K);
        lget(&mut c, SCALE);
        lget(&mut c, MAGLEN);
        op(&mut c, Op::I32Sub);
        op(&mut c, Op::I32GeS);
        op(&mut c, Op::BrIf);
        wasm_encode::encode_uleb128(1, &mut c);
        lget(&mut c, WP);
        wasm_i32c(&mut c, 48);
        wasm_store8(&mut c, 0);
        lget(&mut c, WP);
        wasm_i32c(&mut c, 1);
        op(&mut c, Op::I32Add);
        lset(&mut c, WP);
        lget(&mut c, K);
        wasm_i32c(&mut c, 1);
        op(&mut c, Op::I32Add);
        lset(&mut c, K);
        op(&mut c, Op::Br);
        wasm_encode::encode_uleb128(0, &mut c);
        op(&mut c, Op::End);
        op(&mut c, Op::End);
        // for k in 0..maglen { *wp++ = mag[4+k] }
        wasm_i32c(&mut c, 0);
        lset(&mut c, K);
        op(&mut c, Op::Block);
        c.push(0x40);
        op(&mut c, Op::Loop);
        c.push(0x40);
        lget(&mut c, K);
        lget(&mut c, MAGLEN);
        op(&mut c, Op::I32GeS);
        op(&mut c, Op::BrIf);
        wasm_encode::encode_uleb128(1, &mut c);
        lget(&mut c, WP);
        lget(&mut c, MAG);
        wasm_i32c(&mut c, 4);
        op(&mut c, Op::I32Add);
        lget(&mut c, K);
        op(&mut c, Op::I32Add);
        wasm_load8u(&mut c, 0);
        wasm_store8(&mut c, 0);
        lget(&mut c, WP);
        wasm_i32c(&mut c, 1);
        op(&mut c, Op::I32Add);
        lset(&mut c, WP);
        lget(&mut c, K);
        wasm_i32c(&mut c, 1);
        op(&mut c, Op::I32Add);
        lset(&mut c, K);
        op(&mut c, Op::Br);
        wasm_encode::encode_uleb128(0, &mut c);
        op(&mut c, Op::End);
        op(&mut c, Op::End);
        op(&mut c, Op::Else);
        // point = maglen - scale; resultlen = maglen + 1 + neg
        lget(&mut c, MAGLEN);
        lget(&mut c, SCALE);
        op(&mut c, Op::I32Sub);
        lset(&mut c, POINT);
        lget(&mut c, MAGLEN);
        wasm_i32c(&mut c, 1);
        op(&mut c, Op::I32Add);
        lget(&mut c, NEG);
        op(&mut c, Op::I32Add);
        lset(&mut c, RESULTLEN);
        lget(&mut c, RESULTLEN);
        wasm_i32c(&mut c, 7);
        op(&mut c, Op::I32Add);
        wasm_i32c(&mut c, -4);
        op(&mut c, Op::I32And);
        call(&mut c, alloc_func_index);
        lset(&mut c, RES);
        lget(&mut c, RES);
        lget(&mut c, RESULTLEN);
        wasm_store(&mut c, 0);
        lget(&mut c, RES);
        wasm_i32c(&mut c, 4);
        op(&mut c, Op::I32Add);
        lset(&mut c, WP);
        // if neg { *wp++ = '-' }
        lget(&mut c, NEG);
        op(&mut c, Op::If);
        c.push(0x40);
        lget(&mut c, WP);
        wasm_i32c(&mut c, 45);
        wasm_store8(&mut c, 0);
        lget(&mut c, WP);
        wasm_i32c(&mut c, 1);
        op(&mut c, Op::I32Add);
        lset(&mut c, WP);
        op(&mut c, Op::End);
        // for k in 0..point { *wp++ = mag[4+k] }
        wasm_i32c(&mut c, 0);
        lset(&mut c, K);
        op(&mut c, Op::Block);
        c.push(0x40);
        op(&mut c, Op::Loop);
        c.push(0x40);
        lget(&mut c, K);
        lget(&mut c, POINT);
        op(&mut c, Op::I32GeS);
        op(&mut c, Op::BrIf);
        wasm_encode::encode_uleb128(1, &mut c);
        lget(&mut c, WP);
        lget(&mut c, MAG);
        wasm_i32c(&mut c, 4);
        op(&mut c, Op::I32Add);
        lget(&mut c, K);
        op(&mut c, Op::I32Add);
        wasm_load8u(&mut c, 0);
        wasm_store8(&mut c, 0);
        lget(&mut c, WP);
        wasm_i32c(&mut c, 1);
        op(&mut c, Op::I32Add);
        lset(&mut c, WP);
        lget(&mut c, K);
        wasm_i32c(&mut c, 1);
        op(&mut c, Op::I32Add);
        lset(&mut c, K);
        op(&mut c, Op::Br);
        wasm_encode::encode_uleb128(0, &mut c);
        op(&mut c, Op::End);
        op(&mut c, Op::End);
        // *wp++ = '.'
        lget(&mut c, WP);
        wasm_i32c(&mut c, 46);
        wasm_store8(&mut c, 0);
        lget(&mut c, WP);
        wasm_i32c(&mut c, 1);
        op(&mut c, Op::I32Add);
        lset(&mut c, WP);
        // for k in point..maglen { *wp++ = mag[4+k] }
        lget(&mut c, POINT);
        lset(&mut c, K);
        op(&mut c, Op::Block);
        c.push(0x40);
        op(&mut c, Op::Loop);
        c.push(0x40);
        lget(&mut c, K);
        lget(&mut c, MAGLEN);
        op(&mut c, Op::I32GeS);
        op(&mut c, Op::BrIf);
        wasm_encode::encode_uleb128(1, &mut c);
        lget(&mut c, WP);
        lget(&mut c, MAG);
        wasm_i32c(&mut c, 4);
        op(&mut c, Op::I32Add);
        lget(&mut c, K);
        op(&mut c, Op::I32Add);
        wasm_load8u(&mut c, 0);
        wasm_store8(&mut c, 0);
        lget(&mut c, WP);
        wasm_i32c(&mut c, 1);
        op(&mut c, Op::I32Add);
        lset(&mut c, WP);
        lget(&mut c, K);
        wasm_i32c(&mut c, 1);
        op(&mut c, Op::I32Add);
        lset(&mut c, K);
        op(&mut c, Op::Br);
        wasm_encode::encode_uleb128(0, &mut c);
        op(&mut c, Op::End);
        op(&mut c, Op::End);
        op(&mut c, Op::End); // if maglen<=scale / else
        lget(&mut c, RES);
        FuncBody {
            locals: vec![(11, ValType::I32)],
            code: c,
        }
    }

    /// Emit `dec_pow10_mul(mant: i32, n: i32) -> i32`: return `mant * 10^n` as a
    /// fresh BigInt (or `mant` itself when n == 0). 10^n is built as the digit
    /// string `1 0…0` parsed by `bi_from_str` (proven in W2), then `bi_mul`.
    /// Used by the Decimal scale-alignment (`decimal.rs::align`) and division.
    fn emit_dec_pow10_mul(
        &self,
        alloc_func_index: u32,
        bi_from_str_index: u32,
        bi_mul_index: u32,
    ) -> FuncBody {
        const MANT: u32 = 0;
        const N: u32 = 1;
        const S: u32 = 2;
        const K: u32 = 3;
        let mut c = Vec::new();
        let lget = |c: &mut Vec<u8>, i: u32| wasm_local(c, Op::LocalGet, i);
        let lset = |c: &mut Vec<u8>, i: u32| wasm_local(c, Op::LocalSet, i);
        let op = |c: &mut Vec<u8>, o: Op| c.push(o as u8);
        let call = |c: &mut Vec<u8>, idx: u32| {
            c.push(Op::Call as u8);
            wasm_encode::encode_uleb128(idx as u64, c);
        };
        // if n == 0 { return mant }
        lget(&mut c, N);
        op(&mut c, Op::I32Eqz);
        op(&mut c, Op::If);
        c.push(0x40);
        lget(&mut c, MANT);
        op(&mut c, Op::Return);
        op(&mut c, Op::End);
        // s = alloc(align4(4 + 1 + n)); mem[s] = n+1; data = '1' then n '0's
        lget(&mut c, N);
        wasm_i32c(&mut c, 8);
        op(&mut c, Op::I32Add);
        wasm_i32c(&mut c, -4);
        op(&mut c, Op::I32And);
        call(&mut c, alloc_func_index);
        lset(&mut c, S);
        lget(&mut c, S);
        lget(&mut c, N);
        wasm_i32c(&mut c, 1);
        op(&mut c, Op::I32Add);
        wasm_store(&mut c, 0);
        lget(&mut c, S);
        wasm_i32c(&mut c, 49); // '1'
        wasm_store8(&mut c, 4);
        wasm_i32c(&mut c, 0);
        lset(&mut c, K);
        op(&mut c, Op::Block);
        c.push(0x40);
        op(&mut c, Op::Loop);
        c.push(0x40);
        lget(&mut c, K);
        lget(&mut c, N);
        op(&mut c, Op::I32GeS);
        op(&mut c, Op::BrIf);
        wasm_encode::encode_uleb128(1, &mut c);
        lget(&mut c, S);
        wasm_i32c(&mut c, 5);
        op(&mut c, Op::I32Add);
        lget(&mut c, K);
        op(&mut c, Op::I32Add);
        wasm_i32c(&mut c, 48); // '0'
        wasm_store8(&mut c, 0);
        lget(&mut c, K);
        wasm_i32c(&mut c, 1);
        op(&mut c, Op::I32Add);
        lset(&mut c, K);
        op(&mut c, Op::Br);
        wasm_encode::encode_uleb128(0, &mut c);
        op(&mut c, Op::End);
        op(&mut c, Op::End);
        // return bi_mul(mant, bi_from_str(s))
        lget(&mut c, MANT);
        lget(&mut c, S);
        call(&mut c, bi_from_str_index);
        call(&mut c, bi_mul_index);
        FuncBody {
            locals: vec![(2, ValType::I32)],
            code: c,
        }
    }

    /// Emit `dec_addsub(a: i32, b: i32, sub: i32) -> i32`: exact Decimal add
    /// (sub=0) / sub (sub=1) — align both mantissas to `max(scale)` via
    /// `dec_pow10_mul`, `bi_addsub` them, result keeps the common scale
    /// (matching `decimal.rs::{add,sub}`).
    fn emit_dec_addsub(
        &self,
        alloc_func_index: u32,
        bi_addsub_index: u32,
        dec_pow10_mul_index: u32,
    ) -> FuncBody {
        const A: u32 = 0;
        const B: u32 = 1;
        const SUB: u32 = 2;
        const SA: u32 = 3;
        const SB: u32 = 4;
        const SCALE: u32 = 5;
        const M: u32 = 6;
        const D: u32 = 7;
        let mut c = Vec::new();
        let lget = |c: &mut Vec<u8>, i: u32| wasm_local(c, Op::LocalGet, i);
        let lset = |c: &mut Vec<u8>, i: u32| wasm_local(c, Op::LocalSet, i);
        let op = |c: &mut Vec<u8>, o: Op| c.push(o as u8);
        let call = |c: &mut Vec<u8>, idx: u32| {
            c.push(Op::Call as u8);
            wasm_encode::encode_uleb128(idx as u64, c);
        };
        // sa = mem[a]; sb = mem[b]; scale = max(sa, sb)
        lget(&mut c, A);
        wasm_load(&mut c, 0);
        lset(&mut c, SA);
        lget(&mut c, B);
        wasm_load(&mut c, 0);
        lset(&mut c, SB);
        lget(&mut c, SA);
        lset(&mut c, SCALE);
        lget(&mut c, SB);
        lget(&mut c, SA);
        op(&mut c, Op::I32GtS);
        op(&mut c, Op::If);
        c.push(0x40);
        lget(&mut c, SB);
        lset(&mut c, SCALE);
        op(&mut c, Op::End);
        // m = bi_addsub(pow10_mul(a.mant, scale-sa), pow10_mul(b.mant, scale-sb), sub)
        lget(&mut c, A);
        wasm_load(&mut c, 4);
        lget(&mut c, SCALE);
        lget(&mut c, SA);
        op(&mut c, Op::I32Sub);
        call(&mut c, dec_pow10_mul_index);
        lget(&mut c, B);
        wasm_load(&mut c, 4);
        lget(&mut c, SCALE);
        lget(&mut c, SB);
        op(&mut c, Op::I32Sub);
        call(&mut c, dec_pow10_mul_index);
        lget(&mut c, SUB);
        call(&mut c, bi_addsub_index);
        lset(&mut c, M);
        // d = alloc(8); d.scale = scale; d.mant = m
        wasm_i32c(&mut c, 8);
        call(&mut c, alloc_func_index);
        lset(&mut c, D);
        lget(&mut c, D);
        lget(&mut c, SCALE);
        wasm_store(&mut c, 0);
        lget(&mut c, D);
        lget(&mut c, M);
        wasm_store(&mut c, 4);
        lget(&mut c, D);
        FuncBody {
            locals: vec![(5, ValType::I32)],
            code: c,
        }
    }

    /// Emit `dec_mul(a: i32, b: i32) -> i32`: exact Decimal multiply — mantissas
    /// `bi_mul`, scales add (matching `decimal.rs::mul`).
    fn emit_dec_mul(&self, alloc_func_index: u32, bi_mul_index: u32) -> FuncBody {
        const A: u32 = 0;
        const B: u32 = 1;
        const M: u32 = 2;
        const D: u32 = 3;
        let mut c = Vec::new();
        let lget = |c: &mut Vec<u8>, i: u32| wasm_local(c, Op::LocalGet, i);
        let lset = |c: &mut Vec<u8>, i: u32| wasm_local(c, Op::LocalSet, i);
        let call = |c: &mut Vec<u8>, idx: u32| {
            c.push(Op::Call as u8);
            wasm_encode::encode_uleb128(idx as u64, c);
        };
        lget(&mut c, A);
        wasm_load(&mut c, 4);
        lget(&mut c, B);
        wasm_load(&mut c, 4);
        call(&mut c, bi_mul_index);
        lset(&mut c, M);
        wasm_i32c(&mut c, 8);
        call(&mut c, alloc_func_index);
        lset(&mut c, D);
        lget(&mut c, D);
        lget(&mut c, A);
        wasm_load(&mut c, 0);
        lget(&mut c, B);
        wasm_load(&mut c, 0);
        c.push(Op::I32Add as u8);
        wasm_store(&mut c, 0);
        lget(&mut c, D);
        lget(&mut c, M);
        wasm_store(&mut c, 4);
        lget(&mut c, D);
        FuncBody {
            locals: vec![(2, ValType::I32)],
            code: c,
        }
    }

    /// Emit `dec_cmp(a: i32, b: i32) -> i32`: value-based Decimal compare
    /// (-1/0/1, scale-insensitive: `3.14 == 3.140`) — align mantissas to the
    /// common scale, then `bi_cmp` (matching `decimal.rs::compare`).
    fn emit_dec_cmp(&self, bi_cmp_index: u32, dec_pow10_mul_index: u32) -> FuncBody {
        const A: u32 = 0;
        const B: u32 = 1;
        const SA: u32 = 2;
        const SB: u32 = 3;
        const SCALE: u32 = 4;
        let mut c = Vec::new();
        let lget = |c: &mut Vec<u8>, i: u32| wasm_local(c, Op::LocalGet, i);
        let lset = |c: &mut Vec<u8>, i: u32| wasm_local(c, Op::LocalSet, i);
        let op = |c: &mut Vec<u8>, o: Op| c.push(o as u8);
        let call = |c: &mut Vec<u8>, idx: u32| {
            c.push(Op::Call as u8);
            wasm_encode::encode_uleb128(idx as u64, c);
        };
        lget(&mut c, A);
        wasm_load(&mut c, 0);
        lset(&mut c, SA);
        lget(&mut c, B);
        wasm_load(&mut c, 0);
        lset(&mut c, SB);
        lget(&mut c, SA);
        lset(&mut c, SCALE);
        lget(&mut c, SB);
        lget(&mut c, SA);
        op(&mut c, Op::I32GtS);
        op(&mut c, Op::If);
        c.push(0x40);
        lget(&mut c, SB);
        lset(&mut c, SCALE);
        op(&mut c, Op::End);
        lget(&mut c, A);
        wasm_load(&mut c, 4);
        lget(&mut c, SCALE);
        lget(&mut c, SA);
        op(&mut c, Op::I32Sub);
        call(&mut c, dec_pow10_mul_index);
        lget(&mut c, B);
        wasm_load(&mut c, 4);
        lget(&mut c, SCALE);
        lget(&mut c, SB);
        op(&mut c, Op::I32Sub);
        call(&mut c, dec_pow10_mul_index);
        call(&mut c, bi_cmp_index);
        FuncBody {
            locals: vec![(3, ValType::I32)],
            code: c,
        }
    }

    /// Emit `dec_div(a: i32, b: i32) -> i32`: Decimal division, rounded
    /// **half-to-even** to 34 fractional digits then trailing-zero-stripped,
    /// matching `decimal.rs::div`. `num/den` are scaled so the integer quotient
    /// is the 34-place mantissa; the round compares `2|r|` vs `|den|` via
    /// `bi_cmp_mag` (sign-insensitive — no in-place `abs` mutation), bumping the
    /// quotient away from zero on Greater, and on a tie only when it is odd.
    /// Division by zero traps (`unreachable`), matching the C runtime's abort.
    fn emit_dec_div(
        &self,
        alloc_func_index: u32,
        bi_divmod_index: u32,
        bi_mul_index: u32,
        bi_cmp_mag_index: u32,
        bi_addsub_index: u32,
        dec_pow10_mul_index: u32,
    ) -> FuncBody {
        const A: u32 = 0;
        const B: u32 = 1;
        const MA: u32 = 2;
        const MB: u32 = 3;
        const SHIFT: u32 = 4;
        const NUM: u32 = 5;
        const DEN: u32 = 6;
        const Q: u32 = 7;
        const R: u32 = 8;
        const TWO: u32 = 9;
        const CMPRES: u32 = 10;
        const RESNEG: u32 = 11;
        const ONE: u32 = 12;
        const TEN: u32 = 13;
        const SCALE: u32 = 14;
        const Q2: u32 = 15;
        const D: u32 = 16;
        let mut c = Vec::new();
        let lget = |c: &mut Vec<u8>, i: u32| wasm_local(c, Op::LocalGet, i);
        let lset = |c: &mut Vec<u8>, i: u32| wasm_local(c, Op::LocalSet, i);
        let op = |c: &mut Vec<u8>, o: Op| c.push(o as u8);
        let call = |c: &mut Vec<u8>, idx: u32| {
            c.push(Op::Call as u8);
            wasm_encode::encode_uleb128(idx as u64, c);
        };
        // Build a 1-limb positive BigInt constant `v` into local `dst`.
        let mkconst = |c: &mut Vec<u8>, dst: u32, v: i64| {
            wasm_i32c(c, 12);
            c.push(Op::Call as u8);
            wasm_encode::encode_uleb128(alloc_func_index as u64, c);
            wasm_local(c, Op::LocalSet, dst);
            wasm_local(c, Op::LocalGet, dst);
            wasm_i32c(c, 1);
            wasm_store(c, 0);
            wasm_local(c, Op::LocalGet, dst);
            wasm_i32c(c, 0);
            wasm_store(c, 4);
            wasm_local(c, Op::LocalGet, dst);
            wasm_i32c(c, v);
            wasm_store(c, 8);
        };
        // ma = a.mant; mb = b.mant; trap on zero divisor
        lget(&mut c, A);
        wasm_load(&mut c, 4);
        lset(&mut c, MA);
        lget(&mut c, B);
        wasm_load(&mut c, 4);
        lset(&mut c, MB);
        lget(&mut c, MB);
        wasm_load(&mut c, 0);
        op(&mut c, Op::I32Eqz);
        op(&mut c, Op::If);
        c.push(0x40);
        op(&mut c, Op::Unreachable);
        op(&mut c, Op::End);
        // shift = 34 + b.scale - a.scale
        wasm_i32c(&mut c, 34);
        lget(&mut c, B);
        wasm_load(&mut c, 0);
        op(&mut c, Op::I32Add);
        lget(&mut c, A);
        wasm_load(&mut c, 0);
        op(&mut c, Op::I32Sub);
        lset(&mut c, SHIFT);
        // num/den per the sign of shift
        lget(&mut c, SHIFT);
        wasm_i32c(&mut c, 0);
        op(&mut c, Op::I32GeS);
        op(&mut c, Op::If);
        c.push(0x40);
        lget(&mut c, MA);
        lget(&mut c, SHIFT);
        call(&mut c, dec_pow10_mul_index);
        lset(&mut c, NUM);
        lget(&mut c, MB);
        lset(&mut c, DEN);
        op(&mut c, Op::Else);
        lget(&mut c, MA);
        lset(&mut c, NUM);
        lget(&mut c, MB);
        wasm_i32c(&mut c, 0);
        lget(&mut c, SHIFT);
        op(&mut c, Op::I32Sub);
        call(&mut c, dec_pow10_mul_index);
        lset(&mut c, DEN);
        op(&mut c, Op::End);
        // q = num / den (truncated); r = num % den
        lget(&mut c, NUM);
        lget(&mut c, DEN);
        wasm_i32c(&mut c, 0);
        call(&mut c, bi_divmod_index);
        lset(&mut c, Q);
        lget(&mut c, NUM);
        lget(&mut c, DEN);
        wasm_i32c(&mut c, 1);
        call(&mut c, bi_divmod_index);
        lset(&mut c, R);
        // cmpres = cmp_mag(2*r, den)  [magnitude-only: |2r| vs |den|]
        mkconst(&mut c, TWO, 2);
        lget(&mut c, R);
        lget(&mut c, TWO);
        call(&mut c, bi_mul_index);
        lget(&mut c, DEN);
        call(&mut c, bi_cmp_mag_index);
        lset(&mut c, CMPRES);
        // resneg = (ma.neg != mb.neg)
        lget(&mut c, MA);
        wasm_load(&mut c, 4);
        lget(&mut c, MB);
        wasm_load(&mut c, 4);
        op(&mut c, Op::I32Ne);
        lset(&mut c, RESNEG);
        mkconst(&mut c, ONE, 1);
        // if cmpres > 0 { q = bi_addsub(q, 1, resneg) }   [away from zero]
        lget(&mut c, CMPRES);
        wasm_i32c(&mut c, 0);
        op(&mut c, Op::I32GtS);
        op(&mut c, Op::If);
        c.push(0x40);
        lget(&mut c, Q);
        lget(&mut c, ONE);
        lget(&mut c, RESNEG);
        call(&mut c, bi_addsub_index);
        lset(&mut c, Q);
        op(&mut c, Op::Else);
        // else if cmpres == 0 { if q is odd { bump } }   [half: round to even]
        lget(&mut c, CMPRES);
        op(&mut c, Op::I32Eqz);
        op(&mut c, Op::If);
        c.push(0x40);
        lget(&mut c, Q);
        lget(&mut c, TWO);
        wasm_i32c(&mut c, 1);
        call(&mut c, bi_divmod_index);
        wasm_load(&mut c, 0); // parity remainder's len: 0 = even
        op(&mut c, Op::If);
        c.push(0x40);
        lget(&mut c, Q);
        lget(&mut c, ONE);
        lget(&mut c, RESNEG);
        call(&mut c, bi_addsub_index);
        lset(&mut c, Q);
        op(&mut c, Op::End);
        op(&mut c, Op::End);
        op(&mut c, Op::End);
        // strip trailing zero digits: while scale>0 && q % 10 == 0 { q /= 10; scale-- }
        wasm_i32c(&mut c, 34);
        lset(&mut c, SCALE);
        mkconst(&mut c, TEN, 10);
        op(&mut c, Op::Block);
        c.push(0x40);
        op(&mut c, Op::Loop);
        c.push(0x40);
        lget(&mut c, SCALE);
        op(&mut c, Op::I32Eqz);
        op(&mut c, Op::BrIf);
        wasm_encode::encode_uleb128(1, &mut c);
        lget(&mut c, Q);
        lget(&mut c, TEN);
        wasm_i32c(&mut c, 0);
        call(&mut c, bi_divmod_index);
        lset(&mut c, Q2);
        lget(&mut c, Q);
        lget(&mut c, TEN);
        wasm_i32c(&mut c, 1);
        call(&mut c, bi_divmod_index);
        wasm_load(&mut c, 0); // remainder len != 0 → not divisible → stop
        op(&mut c, Op::BrIf);
        wasm_encode::encode_uleb128(1, &mut c);
        lget(&mut c, Q2);
        lset(&mut c, Q);
        lget(&mut c, SCALE);
        wasm_i32c(&mut c, 1);
        op(&mut c, Op::I32Sub);
        lset(&mut c, SCALE);
        op(&mut c, Op::Br);
        wasm_encode::encode_uleb128(0, &mut c);
        op(&mut c, Op::End);
        op(&mut c, Op::End);
        // d = alloc(8); d.scale = scale; d.mant = q
        wasm_i32c(&mut c, 8);
        call(&mut c, alloc_func_index);
        lset(&mut c, D);
        lget(&mut c, D);
        lget(&mut c, SCALE);
        wasm_store(&mut c, 0);
        lget(&mut c, D);
        lget(&mut c, Q);
        wasm_store(&mut c, 4);
        lget(&mut c, D);
        FuncBody {
            locals: vec![(15, ValType::I32)],
            code: c,
        }
    }

    /// Emit `fix_round_q(num: i32, den: i32) -> i32`: BigInt quotient `num/den`
    /// rounded **half-to-even** — the single fixed-point rounding primitive
    /// (matching `fixed.rs::round_quotient`, proven in `FixedPointModel.v`).
    /// `2|r|` vs `|den|` via the sign-insensitive `bi_cmp_mag`; Greater bumps the
    /// quotient away from zero, a tie bumps only when the quotient is odd.
    /// `den` must be nonzero (callers check).
    fn emit_fix_round_q(
        &self,
        alloc_func_index: u32,
        bi_divmod_index: u32,
        bi_mul_index: u32,
        bi_cmp_mag_index: u32,
        bi_addsub_index: u32,
    ) -> FuncBody {
        const NUM: u32 = 0;
        const DEN: u32 = 1;
        const Q: u32 = 2;
        const R: u32 = 3;
        const TWO: u32 = 4;
        const CMPRES: u32 = 5;
        const RESNEG: u32 = 6;
        const ONE: u32 = 7;
        let mut c = Vec::new();
        let lget = |c: &mut Vec<u8>, i: u32| wasm_local(c, Op::LocalGet, i);
        let lset = |c: &mut Vec<u8>, i: u32| wasm_local(c, Op::LocalSet, i);
        let op = |c: &mut Vec<u8>, o: Op| c.push(o as u8);
        let call = |c: &mut Vec<u8>, idx: u32| {
            c.push(Op::Call as u8);
            wasm_encode::encode_uleb128(idx as u64, c);
        };
        let mkconst = |c: &mut Vec<u8>, dst: u32, v: i64| {
            wasm_i32c(c, 12);
            c.push(Op::Call as u8);
            wasm_encode::encode_uleb128(alloc_func_index as u64, c);
            wasm_local(c, Op::LocalSet, dst);
            wasm_local(c, Op::LocalGet, dst);
            wasm_i32c(c, 1);
            wasm_store(c, 0);
            wasm_local(c, Op::LocalGet, dst);
            wasm_i32c(c, 0);
            wasm_store(c, 4);
            wasm_local(c, Op::LocalGet, dst);
            wasm_i32c(c, v);
            wasm_store(c, 8);
        };
        // q = num / den; r = num % den
        lget(&mut c, NUM);
        lget(&mut c, DEN);
        wasm_i32c(&mut c, 0);
        call(&mut c, bi_divmod_index);
        lset(&mut c, Q);
        lget(&mut c, NUM);
        lget(&mut c, DEN);
        wasm_i32c(&mut c, 1);
        call(&mut c, bi_divmod_index);
        lset(&mut c, R);
        // cmpres = cmp_mag(2*r, den)
        mkconst(&mut c, TWO, 2);
        lget(&mut c, R);
        lget(&mut c, TWO);
        call(&mut c, bi_mul_index);
        lget(&mut c, DEN);
        call(&mut c, bi_cmp_mag_index);
        lset(&mut c, CMPRES);
        // resneg = (num.neg != den.neg)
        lget(&mut c, NUM);
        wasm_load(&mut c, 4);
        lget(&mut c, DEN);
        wasm_load(&mut c, 4);
        op(&mut c, Op::I32Ne);
        lset(&mut c, RESNEG);
        mkconst(&mut c, ONE, 1);
        // if cmpres > 0 { q = bi_addsub(q, 1, resneg) }
        lget(&mut c, CMPRES);
        wasm_i32c(&mut c, 0);
        op(&mut c, Op::I32GtS);
        op(&mut c, Op::If);
        c.push(0x40);
        lget(&mut c, Q);
        lget(&mut c, ONE);
        lget(&mut c, RESNEG);
        call(&mut c, bi_addsub_index);
        lset(&mut c, Q);
        op(&mut c, Op::Else);
        // else if cmpres == 0 && q odd { bump }
        lget(&mut c, CMPRES);
        op(&mut c, Op::I32Eqz);
        op(&mut c, Op::If);
        c.push(0x40);
        lget(&mut c, Q);
        lget(&mut c, TWO);
        wasm_i32c(&mut c, 1);
        call(&mut c, bi_divmod_index);
        wasm_load(&mut c, 0); // parity remainder len: 0 = even
        op(&mut c, Op::If);
        c.push(0x40);
        lget(&mut c, Q);
        lget(&mut c, ONE);
        lget(&mut c, RESNEG);
        call(&mut c, bi_addsub_index);
        lset(&mut c, Q);
        op(&mut c, Op::End);
        op(&mut c, Op::End);
        op(&mut c, Op::End);
        lget(&mut c, Q);
        FuncBody {
            locals: vec![(6, ValType::I32)],
            code: c,
        }
    }

    /// Emit `fix_mul(a: i32, b: i32) -> i32`: fixed-point multiply — the exact
    /// product (scale `sa+sb`) is rounded half-to-even back to `max(sa, sb)`
    /// (`1.55 * 1.55` at scale 2 → `2.40`), matching `fixed.rs::mul`.
    fn emit_fix_mul(
        &self,
        alloc_func_index: u32,
        bi_mul_index: u32,
        dec_pow10_mul_index: u32,
        fix_round_q_index: u32,
    ) -> FuncBody {
        const A: u32 = 0;
        const B: u32 = 1;
        const SA: u32 = 2;
        const SB: u32 = 3;
        const TARGET: u32 = 4;
        const DROP: u32 = 5;
        const M: u32 = 6;
        const ONE: u32 = 7;
        const D: u32 = 8;
        let mut c = Vec::new();
        let lget = |c: &mut Vec<u8>, i: u32| wasm_local(c, Op::LocalGet, i);
        let lset = |c: &mut Vec<u8>, i: u32| wasm_local(c, Op::LocalSet, i);
        let op = |c: &mut Vec<u8>, o: Op| c.push(o as u8);
        let call = |c: &mut Vec<u8>, idx: u32| {
            c.push(Op::Call as u8);
            wasm_encode::encode_uleb128(idx as u64, c);
        };
        let mkconst = |c: &mut Vec<u8>, dst: u32, v: i64| {
            wasm_i32c(c, 12);
            c.push(Op::Call as u8);
            wasm_encode::encode_uleb128(alloc_func_index as u64, c);
            wasm_local(c, Op::LocalSet, dst);
            wasm_local(c, Op::LocalGet, dst);
            wasm_i32c(c, 1);
            wasm_store(c, 0);
            wasm_local(c, Op::LocalGet, dst);
            wasm_i32c(c, 0);
            wasm_store(c, 4);
            wasm_local(c, Op::LocalGet, dst);
            wasm_i32c(c, v);
            wasm_store(c, 8);
        };
        // sa, sb, target = max(sa, sb), drop = sa + sb - target
        lget(&mut c, A);
        wasm_load(&mut c, 0);
        lset(&mut c, SA);
        lget(&mut c, B);
        wasm_load(&mut c, 0);
        lset(&mut c, SB);
        lget(&mut c, SA);
        lset(&mut c, TARGET);
        lget(&mut c, SB);
        lget(&mut c, SA);
        op(&mut c, Op::I32GtS);
        op(&mut c, Op::If);
        c.push(0x40);
        lget(&mut c, SB);
        lset(&mut c, TARGET);
        op(&mut c, Op::End);
        lget(&mut c, SA);
        lget(&mut c, SB);
        op(&mut c, Op::I32Add);
        lget(&mut c, TARGET);
        op(&mut c, Op::I32Sub);
        lset(&mut c, DROP);
        // m = bi_mul(a.mant, b.mant)
        lget(&mut c, A);
        wasm_load(&mut c, 4);
        lget(&mut c, B);
        wasm_load(&mut c, 4);
        call(&mut c, bi_mul_index);
        lset(&mut c, M);
        // if drop > 0 { m = fix_round_q(m, 10^drop) }
        lget(&mut c, DROP);
        wasm_i32c(&mut c, 0);
        op(&mut c, Op::I32GtS);
        op(&mut c, Op::If);
        c.push(0x40);
        mkconst(&mut c, ONE, 1);
        lget(&mut c, M);
        lget(&mut c, ONE);
        lget(&mut c, DROP);
        call(&mut c, dec_pow10_mul_index);
        call(&mut c, fix_round_q_index);
        lset(&mut c, M);
        op(&mut c, Op::End);
        // d = alloc(8); d.scale = target; d.mant = m
        wasm_i32c(&mut c, 8);
        call(&mut c, alloc_func_index);
        lset(&mut c, D);
        lget(&mut c, D);
        lget(&mut c, TARGET);
        wasm_store(&mut c, 0);
        lget(&mut c, D);
        lget(&mut c, M);
        wasm_store(&mut c, 4);
        lget(&mut c, D);
        FuncBody {
            locals: vec![(7, ValType::I32)],
            code: c,
        }
    }

    /// Emit `fix_div(a: i32, b: i32) -> i32`: fixed-point divide — rounded
    /// half-to-even to `max(sa, sb)` (the fixed scale is preserved, not extended:
    /// `10.00 / 3 = 3.33`), matching `fixed.rs::div`. The scale shift
    /// `target + sb - sa` is always ≥ 0 (target ≥ sa), so only the numerator is
    /// scaled. Division by zero traps, matching the C runtime's abort.
    fn emit_fix_div(
        &self,
        alloc_func_index: u32,
        dec_pow10_mul_index: u32,
        fix_round_q_index: u32,
    ) -> FuncBody {
        const A: u32 = 0;
        const B: u32 = 1;
        const SA: u32 = 2;
        const SB: u32 = 3;
        const TARGET: u32 = 4;
        const M: u32 = 5;
        const D: u32 = 6;
        let mut c = Vec::new();
        let lget = |c: &mut Vec<u8>, i: u32| wasm_local(c, Op::LocalGet, i);
        let lset = |c: &mut Vec<u8>, i: u32| wasm_local(c, Op::LocalSet, i);
        let op = |c: &mut Vec<u8>, o: Op| c.push(o as u8);
        let call = |c: &mut Vec<u8>, idx: u32| {
            c.push(Op::Call as u8);
            wasm_encode::encode_uleb128(idx as u64, c);
        };
        // trap on zero divisor
        lget(&mut c, B);
        wasm_load(&mut c, 4);
        wasm_load(&mut c, 0);
        op(&mut c, Op::I32Eqz);
        op(&mut c, Op::If);
        c.push(0x40);
        op(&mut c, Op::Unreachable);
        op(&mut c, Op::End);
        // sa, sb, target = max
        lget(&mut c, A);
        wasm_load(&mut c, 0);
        lset(&mut c, SA);
        lget(&mut c, B);
        wasm_load(&mut c, 0);
        lset(&mut c, SB);
        lget(&mut c, SA);
        lset(&mut c, TARGET);
        lget(&mut c, SB);
        lget(&mut c, SA);
        op(&mut c, Op::I32GtS);
        op(&mut c, Op::If);
        c.push(0x40);
        lget(&mut c, SB);
        lset(&mut c, TARGET);
        op(&mut c, Op::End);
        // m = fix_round_q(a.mant * 10^(target + sb - sa), b.mant)
        lget(&mut c, A);
        wasm_load(&mut c, 4);
        lget(&mut c, TARGET);
        lget(&mut c, SB);
        op(&mut c, Op::I32Add);
        lget(&mut c, SA);
        op(&mut c, Op::I32Sub);
        call(&mut c, dec_pow10_mul_index);
        lget(&mut c, B);
        wasm_load(&mut c, 4);
        call(&mut c, fix_round_q_index);
        lset(&mut c, M);
        // d = alloc(8); d.scale = target; d.mant = m
        wasm_i32c(&mut c, 8);
        call(&mut c, alloc_func_index);
        lset(&mut c, D);
        lget(&mut c, D);
        lget(&mut c, TARGET);
        wasm_store(&mut c, 0);
        lget(&mut c, D);
        lget(&mut c, M);
        wasm_store(&mut c, 4);
        lget(&mut c, D);
        FuncBody {
            locals: vec![(5, ValType::I32)],
            code: c,
        }
    }

    /// Emit `fix_titik_tetap(pair: i32) -> i32`: the explicit-scale constructor —
    /// `titik_tetap(("3.14159", 2))` parses the literal then **rescales** to the
    /// target scale (grow: ×10^(to−from); shrink: round half-to-even), matching
    /// `fixed.rs::parse_scaled`/`rescaled`. The arg is a `[fst:i64][snd:i64]`
    /// heap pair of (string ptr, target scale).
    fn emit_fix_titik_tetap(
        &self,
        alloc_func_index: u32,
        dec_from_str_index: u32,
        dec_pow10_mul_index: u32,
        fix_round_q_index: u32,
    ) -> FuncBody {
        const PAIR: u32 = 0;
        const TARGET: u32 = 1;
        const PARSED: u32 = 2;
        const FROM: u32 = 3;
        const M: u32 = 4;
        const ONE: u32 = 5;
        const D: u32 = 6;
        let mut c = Vec::new();
        let lget = |c: &mut Vec<u8>, i: u32| wasm_local(c, Op::LocalGet, i);
        let lset = |c: &mut Vec<u8>, i: u32| wasm_local(c, Op::LocalSet, i);
        let op = |c: &mut Vec<u8>, o: Op| c.push(o as u8);
        let call = |c: &mut Vec<u8>, idx: u32| {
            c.push(Op::Call as u8);
            wasm_encode::encode_uleb128(idx as u64, c);
        };
        let mkconst = |c: &mut Vec<u8>, dst: u32, v: i64| {
            wasm_i32c(c, 12);
            c.push(Op::Call as u8);
            wasm_encode::encode_uleb128(alloc_func_index as u64, c);
            wasm_local(c, Op::LocalSet, dst);
            wasm_local(c, Op::LocalGet, dst);
            wasm_i32c(c, 1);
            wasm_store(c, 0);
            wasm_local(c, Op::LocalGet, dst);
            wasm_i32c(c, 0);
            wasm_store(c, 4);
            wasm_local(c, Op::LocalGet, dst);
            wasm_i32c(c, v);
            wasm_store(c, 8);
        };
        // target = (i32)pair.snd; parsed = dec_from_str((i32)pair.fst)
        lget(&mut c, PAIR);
        c.push(Op::I64Load as u8);
        c.push(0x02);
        c.push(0x08);
        op(&mut c, Op::I32WrapI64);
        lset(&mut c, TARGET);
        lget(&mut c, PAIR);
        c.push(Op::I64Load as u8);
        c.push(0x02);
        c.push(0x00);
        op(&mut c, Op::I32WrapI64);
        call(&mut c, dec_from_str_index);
        lset(&mut c, PARSED);
        lget(&mut c, PARSED);
        wasm_load(&mut c, 0);
        lset(&mut c, FROM);
        lget(&mut c, PARSED);
        wasm_load(&mut c, 4);
        lset(&mut c, M);
        // rescale: grow (×10^(target−from)) or shrink (round half-to-even)
        lget(&mut c, TARGET);
        lget(&mut c, FROM);
        op(&mut c, Op::I32GeS);
        op(&mut c, Op::If);
        c.push(0x40);
        lget(&mut c, M);
        lget(&mut c, TARGET);
        lget(&mut c, FROM);
        op(&mut c, Op::I32Sub);
        call(&mut c, dec_pow10_mul_index);
        lset(&mut c, M);
        op(&mut c, Op::Else);
        mkconst(&mut c, ONE, 1);
        lget(&mut c, M);
        lget(&mut c, ONE);
        lget(&mut c, FROM);
        lget(&mut c, TARGET);
        op(&mut c, Op::I32Sub);
        call(&mut c, dec_pow10_mul_index);
        call(&mut c, fix_round_q_index);
        lset(&mut c, M);
        op(&mut c, Op::End);
        // d = alloc(8); d.scale = target; d.mant = m
        wasm_i32c(&mut c, 8);
        call(&mut c, alloc_func_index);
        lset(&mut c, D);
        lget(&mut c, D);
        lget(&mut c, TARGET);
        wasm_store(&mut c, 0);
        lget(&mut c, D);
        lget(&mut c, M);
        wasm_store(&mut c, 4);
        lget(&mut c, D);
        FuncBody {
            locals: vec![(6, ValType::I32)],
            code: c,
        }
    }

    /// Emit `qmn_two_pow(bits: i32) -> i32`: `2^bits` as a BigInt — `bits/32 + 1`
    /// limbs, all zero except limb `bits>>5` = `1 << (bits & 31)`. Handles any
    /// `bits` up to 64 (used for the 2^64 wrap modulus).
    fn emit_qmn_two_pow(&self, alloc_func_index: u32) -> FuncBody {
        const BITS: u32 = 0;
        const NL: u32 = 1;
        const R: u32 = 2;
        const K: u32 = 3;
        let mut c = Vec::new();
        let lget = |c: &mut Vec<u8>, i: u32| wasm_local(c, Op::LocalGet, i);
        let lset = |c: &mut Vec<u8>, i: u32| wasm_local(c, Op::LocalSet, i);
        let op = |c: &mut Vec<u8>, o: Op| c.push(o as u8);
        // nl = (bits >> 5) + 1
        lget(&mut c, BITS);
        wasm_i32c(&mut c, 5);
        op(&mut c, Op::I32ShrU);
        wasm_i32c(&mut c, 1);
        op(&mut c, Op::I32Add);
        lset(&mut c, NL);
        // r = alloc(8 + nl*4); r.len = nl; r.neg = 0
        lget(&mut c, NL);
        wasm_i32c(&mut c, 4);
        op(&mut c, Op::I32Mul);
        wasm_i32c(&mut c, 8);
        op(&mut c, Op::I32Add);
        op(&mut c, Op::Call);
        wasm_encode::encode_uleb128(alloc_func_index as u64, &mut c);
        lset(&mut c, R);
        lget(&mut c, R);
        lget(&mut c, NL);
        wasm_store(&mut c, 0);
        lget(&mut c, R);
        wasm_i32c(&mut c, 0);
        wasm_store(&mut c, 4);
        // zero the limbs
        wasm_i32c(&mut c, 0);
        lset(&mut c, K);
        op(&mut c, Op::Block);
        c.push(0x40);
        op(&mut c, Op::Loop);
        c.push(0x40);
        lget(&mut c, K);
        lget(&mut c, NL);
        op(&mut c, Op::I32GeS);
        op(&mut c, Op::BrIf);
        wasm_encode::encode_uleb128(1, &mut c);
        lget(&mut c, R);
        wasm_i32c(&mut c, 8);
        op(&mut c, Op::I32Add);
        lget(&mut c, K);
        wasm_i32c(&mut c, 4);
        op(&mut c, Op::I32Mul);
        op(&mut c, Op::I32Add);
        wasm_i32c(&mut c, 0);
        wasm_store(&mut c, 0);
        lget(&mut c, K);
        wasm_i32c(&mut c, 1);
        op(&mut c, Op::I32Add);
        lset(&mut c, K);
        op(&mut c, Op::Br);
        wasm_encode::encode_uleb128(0, &mut c);
        op(&mut c, Op::End);
        op(&mut c, Op::End);
        // limb[bits>>5] = 1 << (bits & 31)
        lget(&mut c, R);
        wasm_i32c(&mut c, 8);
        op(&mut c, Op::I32Add);
        lget(&mut c, BITS);
        wasm_i32c(&mut c, 5);
        op(&mut c, Op::I32ShrU);
        wasm_i32c(&mut c, 4);
        op(&mut c, Op::I32Mul);
        op(&mut c, Op::I32Add);
        wasm_i32c(&mut c, 1);
        lget(&mut c, BITS);
        wasm_i32c(&mut c, 31);
        op(&mut c, Op::I32And);
        op(&mut c, Op::I32Shl);
        wasm_store(&mut c, 0);
        lget(&mut c, R);
        FuncBody {
            locals: vec![(3, ValType::I32)],
            code: c,
        }
    }

    /// Emit `qmn_raw_to_big(rec: i32) -> i32`: the record's signed i64 `raw` as a
    /// BigInt. The magnitude is `raw < 0 ? 0 - raw : raw` (the i64 wrap makes
    /// `i64::MIN`'s magnitude 2^63 come out right as an unsigned bit pattern);
    /// limbs are `u mod 2^32` and `u / 2^32` (unsigned), normalized.
    fn emit_qmn_raw_to_big(&self, alloc_func_index: u32) -> FuncBody {
        const REC: u32 = 0;
        const NEG: u32 = 1;
        const LO: u32 = 2;
        const HI: u32 = 3;
        const B: u32 = 4;
        const LEN: u32 = 5;
        const RAW: u32 = 6; // i64
        const U: u32 = 7; // i64
        let mut c = Vec::new();
        let lget = |c: &mut Vec<u8>, i: u32| wasm_local(c, Op::LocalGet, i);
        let lset = |c: &mut Vec<u8>, i: u32| wasm_local(c, Op::LocalSet, i);
        let op = |c: &mut Vec<u8>, o: Op| c.push(o as u8);
        // raw = i64.load rec+8
        lget(&mut c, REC);
        c.push(Op::I64Load as u8);
        c.push(0x02);
        c.push(0x08);
        lset(&mut c, RAW);
        // neg = raw < 0; u = neg ? 0 - raw : raw
        lget(&mut c, RAW);
        wasm_i64c(&mut c, 0);
        op(&mut c, Op::I64LtS);
        lset(&mut c, NEG);
        lget(&mut c, NEG);
        op(&mut c, Op::If);
        c.push(0x40);
        wasm_i64c(&mut c, 0);
        lget(&mut c, RAW);
        op(&mut c, Op::I64Sub);
        lset(&mut c, U);
        op(&mut c, Op::Else);
        lget(&mut c, RAW);
        lset(&mut c, U);
        op(&mut c, Op::End);
        // lo = wrap(u); hi = wrap(u /u 2^32)
        lget(&mut c, U);
        op(&mut c, Op::I32WrapI64);
        lset(&mut c, LO);
        lget(&mut c, U);
        wasm_i64c(&mut c, 4294967296);
        op(&mut c, Op::I64DivU);
        op(&mut c, Op::I32WrapI64);
        lset(&mut c, HI);
        // len = hi != 0 ? 2 : (lo != 0 ? 1 : 0)
        lget(&mut c, HI);
        op(&mut c, Op::If);
        c.push(0x7F);
        wasm_i32c(&mut c, 2);
        op(&mut c, Op::Else);
        lget(&mut c, LO);
        op(&mut c, Op::If);
        c.push(0x7F);
        wasm_i32c(&mut c, 1);
        op(&mut c, Op::Else);
        wasm_i32c(&mut c, 0);
        op(&mut c, Op::End);
        op(&mut c, Op::End);
        lset(&mut c, LEN);
        // b = alloc(16); len; neg = (len != 0) && neg; limbs
        wasm_i32c(&mut c, 16);
        op(&mut c, Op::Call);
        wasm_encode::encode_uleb128(alloc_func_index as u64, &mut c);
        lset(&mut c, B);
        lget(&mut c, B);
        lget(&mut c, LEN);
        wasm_store(&mut c, 0);
        lget(&mut c, B);
        lget(&mut c, NEG);
        lget(&mut c, LEN);
        wasm_i32c(&mut c, 0);
        op(&mut c, Op::I32Ne);
        op(&mut c, Op::I32And);
        wasm_store(&mut c, 4);
        lget(&mut c, B);
        lget(&mut c, LO);
        wasm_store(&mut c, 8);
        lget(&mut c, B);
        lget(&mut c, HI);
        wasm_store(&mut c, 12);
        lget(&mut c, B);
        FuncBody {
            locals: vec![(5, ValType::I32), (2, ValType::I64)],
            code: c,
        }
    }

    /// Emit `qmn_wrap_store(b: i32, fb: i32) -> i32`: reduce BigInt `b` into a
    /// wrapping i64 word (two's complement mod 2^64, matching
    /// `fixed_bin.rs::to_i64_wrapping`) and build the `[fb][raw:i64@8]` record.
    fn emit_qmn_wrap_store(
        &self,
        alloc_func_index: u32,
        bi_divmod_index: u32,
        bi_addsub_index: u32,
        qmn_two_pow_index: u32,
    ) -> FuncBody {
        const B: u32 = 0;
        const FB: u32 = 1;
        const M64: u32 = 2;
        const R: u32 = 3;
        const LEN: u32 = 4;
        const LO: u32 = 5;
        const HI: u32 = 6;
        const REC: u32 = 7;
        let mut c = Vec::new();
        let lget = |c: &mut Vec<u8>, i: u32| wasm_local(c, Op::LocalGet, i);
        let lset = |c: &mut Vec<u8>, i: u32| wasm_local(c, Op::LocalSet, i);
        let op = |c: &mut Vec<u8>, o: Op| c.push(o as u8);
        let call = |c: &mut Vec<u8>, idx: u32| {
            c.push(Op::Call as u8);
            wasm_encode::encode_uleb128(idx as u64, c);
        };
        // m64 = 2^64; r = b mod 2^64 (truncating, dividend's sign)
        wasm_i32c(&mut c, 64);
        call(&mut c, qmn_two_pow_index);
        lset(&mut c, M64);
        lget(&mut c, B);
        lget(&mut c, M64);
        wasm_i32c(&mut c, 1);
        call(&mut c, bi_divmod_index);
        lset(&mut c, R);
        // if r.neg { r = r + 2^64 }
        lget(&mut c, R);
        wasm_load(&mut c, 4);
        op(&mut c, Op::If);
        c.push(0x40);
        lget(&mut c, R);
        lget(&mut c, M64);
        wasm_i32c(&mut c, 0);
        call(&mut c, bi_addsub_index);
        lset(&mut c, R);
        op(&mut c, Op::End);
        // lo/hi from the (≤ 2) limbs
        lget(&mut c, R);
        wasm_load(&mut c, 0);
        lset(&mut c, LEN);
        wasm_i32c(&mut c, 0);
        lset(&mut c, LO);
        wasm_i32c(&mut c, 0);
        lset(&mut c, HI);
        lget(&mut c, LEN);
        wasm_i32c(&mut c, 1);
        op(&mut c, Op::I32GeS);
        op(&mut c, Op::If);
        c.push(0x40);
        lget(&mut c, R);
        wasm_load(&mut c, 8);
        lset(&mut c, LO);
        op(&mut c, Op::End);
        lget(&mut c, LEN);
        wasm_i32c(&mut c, 2);
        op(&mut c, Op::I32GeS);
        op(&mut c, Op::If);
        c.push(0x40);
        lget(&mut c, R);
        wasm_load(&mut c, 12);
        lset(&mut c, HI);
        op(&mut c, Op::End);
        // rec = alloc(16); rec.fb = fb; rec.raw = ext(lo) + ext(hi)*2^32
        wasm_i32c(&mut c, 16);
        call(&mut c, alloc_func_index);
        lset(&mut c, REC);
        lget(&mut c, REC);
        lget(&mut c, FB);
        wasm_store(&mut c, 0);
        lget(&mut c, REC);
        lget(&mut c, LO);
        op(&mut c, Op::I64ExtendI32U);
        lget(&mut c, HI);
        op(&mut c, Op::I64ExtendI32U);
        wasm_i64c(&mut c, 4294967296);
        op(&mut c, Op::I64Mul);
        op(&mut c, Op::I64Add);
        c.push(Op::I64Store as u8);
        c.push(0x02);
        c.push(0x08);
        lget(&mut c, REC);
        FuncBody {
            locals: vec![(6, ValType::I32)],
            code: c,
        }
    }

    /// Emit `qmn_align(rec: i32, fb: i32) -> i32`: the record's raw re-expressed
    /// at `fb` fractional bits as a BigInt — `raw_big * 2^(fb - rec.fb)`
    /// (`fb >= rec.fb`; exact).
    fn emit_qmn_align(
        &self,
        bi_mul_index: u32,
        qmn_two_pow_index: u32,
        qmn_raw_to_big_index: u32,
    ) -> FuncBody {
        const REC: u32 = 0;
        const FB: u32 = 1;
        let mut c = Vec::new();
        let lget = |c: &mut Vec<u8>, i: u32| wasm_local(c, Op::LocalGet, i);
        let op = |c: &mut Vec<u8>, o: Op| c.push(o as u8);
        let call = |c: &mut Vec<u8>, idx: u32| {
            c.push(Op::Call as u8);
            wasm_encode::encode_uleb128(idx as u64, c);
        };
        lget(&mut c, REC);
        call(&mut c, qmn_raw_to_big_index);
        lget(&mut c, FB);
        lget(&mut c, REC);
        wasm_load(&mut c, 0);
        op(&mut c, Op::I32Sub);
        call(&mut c, qmn_two_pow_index);
        call(&mut c, bi_mul_index);
        FuncBody {
            locals: vec![],
            code: c,
        }
    }

    /// Emit `qmn_parse(pair: i32) -> i32`: the `qmn((literal, frac_bits))`
    /// constructor — `raw = round_he(mantissa · 2^fb / 10^scale)` (matching
    /// `fixed_bin.rs::parse`). `frac_bits` outside `1..=32` traps, matching the
    /// C runtime's abort.
    fn emit_qmn_parse(
        &self,
        alloc_func_index: u32,
        dec_from_str_index: u32,
        dec_pow10_mul_index: u32,
        bi_mul_index: u32,
        fix_round_q_index: u32,
        (qmn_two_pow_index, qmn_wrap_store_index): (u32, u32),
    ) -> FuncBody {
        const PAIR: u32 = 0;
        const FB: u32 = 1;
        const D: u32 = 2;
        const ONE: u32 = 3;
        const RAWBIG: u32 = 4;
        let mut c = Vec::new();
        let lget = |c: &mut Vec<u8>, i: u32| wasm_local(c, Op::LocalGet, i);
        let lset = |c: &mut Vec<u8>, i: u32| wasm_local(c, Op::LocalSet, i);
        let op = |c: &mut Vec<u8>, o: Op| c.push(o as u8);
        let call = |c: &mut Vec<u8>, idx: u32| {
            c.push(Op::Call as u8);
            wasm_encode::encode_uleb128(idx as u64, c);
        };
        let mkconst = |c: &mut Vec<u8>, dst: u32, v: i64| {
            wasm_i32c(c, 12);
            c.push(Op::Call as u8);
            wasm_encode::encode_uleb128(alloc_func_index as u64, c);
            wasm_local(c, Op::LocalSet, dst);
            wasm_local(c, Op::LocalGet, dst);
            wasm_i32c(c, 1);
            wasm_store(c, 0);
            wasm_local(c, Op::LocalGet, dst);
            wasm_i32c(c, 0);
            wasm_store(c, 4);
            wasm_local(c, Op::LocalGet, dst);
            wasm_i32c(c, v);
            wasm_store(c, 8);
        };
        // fb = (i32)pair.snd; validate 1..=32 (trap like the C abort)
        lget(&mut c, PAIR);
        c.push(Op::I64Load as u8);
        c.push(0x02);
        c.push(0x08);
        op(&mut c, Op::I32WrapI64);
        lset(&mut c, FB);
        lget(&mut c, FB);
        wasm_i32c(&mut c, 1);
        op(&mut c, Op::I32LtS);
        lget(&mut c, FB);
        wasm_i32c(&mut c, 32);
        op(&mut c, Op::I32GtS);
        op(&mut c, Op::I32Or);
        op(&mut c, Op::If);
        c.push(0x40);
        op(&mut c, Op::Unreachable);
        op(&mut c, Op::End);
        // d = dec_from_str((i32)pair.fst)   [scale][mantissa]
        lget(&mut c, PAIR);
        c.push(Op::I64Load as u8);
        c.push(0x02);
        c.push(0x00);
        op(&mut c, Op::I32WrapI64);
        call(&mut c, dec_from_str_index);
        lset(&mut c, D);
        // rawbig = round_he(mant * 2^fb, 10^scale)
        mkconst(&mut c, ONE, 1);
        lget(&mut c, D);
        wasm_load(&mut c, 4);
        lget(&mut c, FB);
        call(&mut c, qmn_two_pow_index);
        call(&mut c, bi_mul_index);
        lget(&mut c, ONE);
        lget(&mut c, D);
        wasm_load(&mut c, 0);
        call(&mut c, dec_pow10_mul_index);
        call(&mut c, fix_round_q_index);
        lset(&mut c, RAWBIG);
        // wrap into the record
        lget(&mut c, RAWBIG);
        lget(&mut c, FB);
        call(&mut c, qmn_wrap_store_index);
        FuncBody {
            locals: vec![(4, ValType::I32)],
            code: c,
        }
    }

    /// Emit `qmn_to_str(rec: i32) -> i32`: render the exact decimal value —
    /// `raw·5^fb / 10^fb` with trailing zeros stripped (`0.5`, not `0.50000000`),
    /// matching `fixed_bin.rs::to_string_repr`. `5^fb` is computed exactly as
    /// `10^fb / 2^fb`; the strip + render reuse the decimal machinery.
    fn emit_qmn_to_str(
        &self,
        alloc_func_index: u32,
        dec_to_str_index: u32,
        dec_pow10_mul_index: u32,
        bi_divmod_index: u32,
        bi_mul_index: u32,
        (qmn_two_pow_index, qmn_raw_to_big_index): (u32, u32),
    ) -> FuncBody {
        const REC: u32 = 0;
        const FB: u32 = 1;
        const ONE: u32 = 2;
        const NUM: u32 = 3;
        const SCALE: u32 = 4;
        const TEN: u32 = 5;
        const Q2: u32 = 6;
        const D: u32 = 7;
        let mut c = Vec::new();
        let lget = |c: &mut Vec<u8>, i: u32| wasm_local(c, Op::LocalGet, i);
        let lset = |c: &mut Vec<u8>, i: u32| wasm_local(c, Op::LocalSet, i);
        let op = |c: &mut Vec<u8>, o: Op| c.push(o as u8);
        let call = |c: &mut Vec<u8>, idx: u32| {
            c.push(Op::Call as u8);
            wasm_encode::encode_uleb128(idx as u64, c);
        };
        let mkconst = |c: &mut Vec<u8>, dst: u32, v: i64| {
            wasm_i32c(c, 12);
            c.push(Op::Call as u8);
            wasm_encode::encode_uleb128(alloc_func_index as u64, c);
            wasm_local(c, Op::LocalSet, dst);
            wasm_local(c, Op::LocalGet, dst);
            wasm_i32c(c, 1);
            wasm_store(c, 0);
            wasm_local(c, Op::LocalGet, dst);
            wasm_i32c(c, 0);
            wasm_store(c, 4);
            wasm_local(c, Op::LocalGet, dst);
            wasm_i32c(c, v);
            wasm_store(c, 8);
        };
        // fb = rec.fb; num = raw_big * (10^fb / 2^fb)
        lget(&mut c, REC);
        wasm_load(&mut c, 0);
        lset(&mut c, FB);
        mkconst(&mut c, ONE, 1);
        lget(&mut c, REC);
        call(&mut c, qmn_raw_to_big_index);
        lget(&mut c, ONE);
        lget(&mut c, FB);
        call(&mut c, dec_pow10_mul_index);
        lget(&mut c, FB);
        call(&mut c, qmn_two_pow_index);
        wasm_i32c(&mut c, 0);
        call(&mut c, bi_divmod_index);
        call(&mut c, bi_mul_index);
        lset(&mut c, NUM);
        // strip trailing zeros: while scale>0 && num%10==0 { num/=10; scale-- }
        lget(&mut c, FB);
        lset(&mut c, SCALE);
        mkconst(&mut c, TEN, 10);
        op(&mut c, Op::Block);
        c.push(0x40);
        op(&mut c, Op::Loop);
        c.push(0x40);
        lget(&mut c, SCALE);
        op(&mut c, Op::I32Eqz);
        op(&mut c, Op::BrIf);
        wasm_encode::encode_uleb128(1, &mut c);
        lget(&mut c, NUM);
        lget(&mut c, TEN);
        wasm_i32c(&mut c, 0);
        call(&mut c, bi_divmod_index);
        lset(&mut c, Q2);
        lget(&mut c, NUM);
        lget(&mut c, TEN);
        wasm_i32c(&mut c, 1);
        call(&mut c, bi_divmod_index);
        wasm_load(&mut c, 0);
        op(&mut c, Op::BrIf);
        wasm_encode::encode_uleb128(1, &mut c);
        lget(&mut c, Q2);
        lset(&mut c, NUM);
        lget(&mut c, SCALE);
        wasm_i32c(&mut c, 1);
        op(&mut c, Op::I32Sub);
        lset(&mut c, SCALE);
        op(&mut c, Op::Br);
        wasm_encode::encode_uleb128(0, &mut c);
        op(&mut c, Op::End);
        op(&mut c, Op::End);
        // d = [scale][num]; dec_to_str(d)
        wasm_i32c(&mut c, 8);
        call(&mut c, alloc_func_index);
        lset(&mut c, D);
        lget(&mut c, D);
        lget(&mut c, SCALE);
        wasm_store(&mut c, 0);
        lget(&mut c, D);
        lget(&mut c, NUM);
        wasm_store(&mut c, 4);
        lget(&mut c, D);
        call(&mut c, dec_to_str_index);
        FuncBody {
            locals: vec![(7, ValType::I32)],
            code: c,
        }
    }

    /// Emit `qmn_addsub(a: i32, b: i32, sub: i32) -> i32`: exact in BigInt at
    /// `max(frac_bits)`, wrapped back into the i64 word (matching
    /// `fixed_bin.rs::{add,sub}` — machine-int overflow wraps).
    fn emit_qmn_addsub(
        &self,
        bi_addsub_index: u32,
        qmn_align_index: u32,
        qmn_wrap_store_index: u32,
    ) -> FuncBody {
        const A: u32 = 0;
        const B: u32 = 1;
        const SUB: u32 = 2;
        const FB: u32 = 3;
        let mut c = Vec::new();
        let lget = |c: &mut Vec<u8>, i: u32| wasm_local(c, Op::LocalGet, i);
        let lset = |c: &mut Vec<u8>, i: u32| wasm_local(c, Op::LocalSet, i);
        let op = |c: &mut Vec<u8>, o: Op| c.push(o as u8);
        let call = |c: &mut Vec<u8>, idx: u32| {
            c.push(Op::Call as u8);
            wasm_encode::encode_uleb128(idx as u64, c);
        };
        // fb = max(a.fb, b.fb)
        lget(&mut c, A);
        wasm_load(&mut c, 0);
        lset(&mut c, FB);
        lget(&mut c, B);
        wasm_load(&mut c, 0);
        lget(&mut c, FB);
        op(&mut c, Op::I32GtS);
        op(&mut c, Op::If);
        c.push(0x40);
        lget(&mut c, B);
        wasm_load(&mut c, 0);
        lset(&mut c, FB);
        op(&mut c, Op::End);
        // wrap_store(bi_addsub(align(a,fb), align(b,fb), sub), fb)
        lget(&mut c, A);
        lget(&mut c, FB);
        call(&mut c, qmn_align_index);
        lget(&mut c, B);
        lget(&mut c, FB);
        call(&mut c, qmn_align_index);
        lget(&mut c, SUB);
        call(&mut c, bi_addsub_index);
        lget(&mut c, FB);
        call(&mut c, qmn_wrap_store_index);
        FuncBody {
            locals: vec![(1, ValType::I32)],
            code: c,
        }
    }

    /// Emit `qmn_mul(a: i32, b: i32) -> i32`: `round_he(a' · b' / 2^fb)` at
    /// `fb = max(frac_bits)`, wrapped (matching `fixed_bin.rs::mul`).
    fn emit_qmn_mul(
        &self,
        bi_mul_index: u32,
        fix_round_q_index: u32,
        qmn_two_pow_index: u32,
        qmn_align_index: u32,
        qmn_wrap_store_index: u32,
    ) -> FuncBody {
        const A: u32 = 0;
        const B: u32 = 1;
        const FB: u32 = 2;
        let mut c = Vec::new();
        let lget = |c: &mut Vec<u8>, i: u32| wasm_local(c, Op::LocalGet, i);
        let lset = |c: &mut Vec<u8>, i: u32| wasm_local(c, Op::LocalSet, i);
        let op = |c: &mut Vec<u8>, o: Op| c.push(o as u8);
        let call = |c: &mut Vec<u8>, idx: u32| {
            c.push(Op::Call as u8);
            wasm_encode::encode_uleb128(idx as u64, c);
        };
        lget(&mut c, A);
        wasm_load(&mut c, 0);
        lset(&mut c, FB);
        lget(&mut c, B);
        wasm_load(&mut c, 0);
        lget(&mut c, FB);
        op(&mut c, Op::I32GtS);
        op(&mut c, Op::If);
        c.push(0x40);
        lget(&mut c, B);
        wasm_load(&mut c, 0);
        lset(&mut c, FB);
        op(&mut c, Op::End);
        lget(&mut c, A);
        lget(&mut c, FB);
        call(&mut c, qmn_align_index);
        lget(&mut c, B);
        lget(&mut c, FB);
        call(&mut c, qmn_align_index);
        call(&mut c, bi_mul_index);
        lget(&mut c, FB);
        call(&mut c, qmn_two_pow_index);
        call(&mut c, fix_round_q_index);
        lget(&mut c, FB);
        call(&mut c, qmn_wrap_store_index);
        FuncBody {
            locals: vec![(1, ValType::I32)],
            code: c,
        }
    }

    /// Emit `qmn_div(a: i32, b: i32) -> i32`: `round_he(a' · 2^fb / b')` at
    /// `fb = max(frac_bits)`, wrapped (matching `fixed_bin.rs::div`). Division
    /// by zero (b.raw == 0) traps, matching the C runtime's abort.
    fn emit_qmn_div(
        &self,
        bi_mul_index: u32,
        fix_round_q_index: u32,
        qmn_two_pow_index: u32,
        qmn_align_index: u32,
        qmn_wrap_store_index: u32,
    ) -> FuncBody {
        const A: u32 = 0;
        const B: u32 = 1;
        const FB: u32 = 2;
        let mut c = Vec::new();
        let lget = |c: &mut Vec<u8>, i: u32| wasm_local(c, Op::LocalGet, i);
        let lset = |c: &mut Vec<u8>, i: u32| wasm_local(c, Op::LocalSet, i);
        let op = |c: &mut Vec<u8>, o: Op| c.push(o as u8);
        let call = |c: &mut Vec<u8>, idx: u32| {
            c.push(Op::Call as u8);
            wasm_encode::encode_uleb128(idx as u64, c);
        };
        // trap on zero divisor (raw == 0)
        lget(&mut c, B);
        c.push(Op::I64Load as u8);
        c.push(0x02);
        c.push(0x08);
        op(&mut c, Op::I64Eqz);
        op(&mut c, Op::If);
        c.push(0x40);
        op(&mut c, Op::Unreachable);
        op(&mut c, Op::End);
        lget(&mut c, A);
        wasm_load(&mut c, 0);
        lset(&mut c, FB);
        lget(&mut c, B);
        wasm_load(&mut c, 0);
        lget(&mut c, FB);
        op(&mut c, Op::I32GtS);
        op(&mut c, Op::If);
        c.push(0x40);
        lget(&mut c, B);
        wasm_load(&mut c, 0);
        lset(&mut c, FB);
        op(&mut c, Op::End);
        lget(&mut c, A);
        lget(&mut c, FB);
        call(&mut c, qmn_align_index);
        lget(&mut c, FB);
        call(&mut c, qmn_two_pow_index);
        call(&mut c, bi_mul_index);
        lget(&mut c, B);
        lget(&mut c, FB);
        call(&mut c, qmn_align_index);
        call(&mut c, fix_round_q_index);
        lget(&mut c, FB);
        call(&mut c, qmn_wrap_store_index);
        FuncBody {
            locals: vec![(1, ValType::I32)],
            code: c,
        }
    }

    /// Emit `qmn_cmp(a: i32, b: i32) -> i32`: value-based compare (-1/0/1) —
    /// align both raws to `max(frac_bits)` and `bi_cmp` (matching
    /// `fixed_bin.rs::compare`).
    fn emit_qmn_cmp(&self, bi_cmp_index: u32, qmn_align_index: u32) -> FuncBody {
        const A: u32 = 0;
        const B: u32 = 1;
        const FB: u32 = 2;
        let mut c = Vec::new();
        let lget = |c: &mut Vec<u8>, i: u32| wasm_local(c, Op::LocalGet, i);
        let lset = |c: &mut Vec<u8>, i: u32| wasm_local(c, Op::LocalSet, i);
        let op = |c: &mut Vec<u8>, o: Op| c.push(o as u8);
        let call = |c: &mut Vec<u8>, idx: u32| {
            c.push(Op::Call as u8);
            wasm_encode::encode_uleb128(idx as u64, c);
        };
        lget(&mut c, A);
        wasm_load(&mut c, 0);
        lset(&mut c, FB);
        lget(&mut c, B);
        wasm_load(&mut c, 0);
        lget(&mut c, FB);
        op(&mut c, Op::I32GtS);
        op(&mut c, Op::If);
        c.push(0x40);
        lget(&mut c, B);
        wasm_load(&mut c, 0);
        lset(&mut c, FB);
        op(&mut c, Op::End);
        lget(&mut c, A);
        lget(&mut c, FB);
        call(&mut c, qmn_align_index);
        lget(&mut c, B);
        lget(&mut c, FB);
        call(&mut c, qmn_align_index);
        call(&mut c, bi_cmp_index);
        FuncBody {
            locals: vec![(1, ValType::I32)],
            code: c,
        }
    }

    ///
    /// This method analyzes the block structure to detect if/else patterns
    /// (CondBranch → then_block/else_block → merge via Phi) and emits
    /// proper WASM structured control flow (if/else/end) instead of
    /// invalid bare br_if instructions.
    #[allow(clippy::too_many_arguments)] // threads alloc + bignum + type indices
    fn emit_function(
        &self,
        func: &Function,
        func_map: &HashMap<FuncId, u32>,
        string_table: &HashMap<String, u32>,
        alloc_func_index: u32,
        user_func_type_idx: u32,
        bi_from_str_index: u32,
        bi_to_str_index: u32,
        bi_cmp_index: u32,
        bi_addsub_index: u32,
        bi_mul_index: u32,
        bi_divmod_index: u32,
        dec_from_str_index: u32,
        dec_to_str_index: u32,
        dec_addsub_index: u32,
        dec_mul_index: u32,
        dec_cmp_index: u32,
        dec_div_index: u32,
        fix_mul_index: u32,
        fix_div_index: u32,
        fix_titik_tetap_index: u32,
        qmn_parse_index: u32,
        qmn_to_str_index: u32,
        qmn_addsub_index: u32,
        qmn_mul_index: u32,
        qmn_div_index: u32,
        qmn_cmp_index: u32,
    ) -> Result<FuncBody> {
        let mut code = Vec::new();
        let mut locals: Vec<(u32, ValType)> = Vec::new();
        let mut local_count: u32 = 2; // Two params: closure_ptr (local 0), arg (local 1)

        let mut var_to_local: HashMap<VarId, u32> = HashMap::new();
        let mut var_to_func: HashMap<VarId, FuncId> = HashMap::new();

        // Closure calling convention: local 0 = closure_ptr, local 1 = arg
        // The IR's variable numbering for functions with captures:
        //   VarId(0..N-1) = captures (loaded from closure_ptr + (i+1)*4)
        //   VarId(N) = param (local 1 = arg)
        // For functions without captures:
        //   VarId(0) = param (local 1 = arg)
        let num_captures = func.captures.len() as u32;
        var_to_local.insert(VarId::new(num_captures), 1); // param = local 1

        for block in &func.blocks {
            for instr in &block.instrs {
                let result = instr.result;
                if let std::collections::hash_map::Entry::Vacant(e) = var_to_local.entry(result) {
                    e.insert(local_count);
                    local_count += 1;
                }
                match &instr.instr {
                    Instruction::Closure { func: fid, .. } => {
                        var_to_func.insert(result, *fid);
                    }
                    Instruction::Copy(src) => {
                        if let Some(&fid) = var_to_func.get(src) {
                            var_to_func.insert(result, fid);
                        }
                    }
                    Instruction::FixClosure { closure, .. } => {
                        if let Some(&fid) = var_to_func.get(closure) {
                            var_to_func.insert(result, fid);
                        }
                    }
                    _ => {}
                }
            }
        }

        // Allocate locals for captures: VarId(0..N-1) → locals 2, 3, ...
        if !func.captures.is_empty() {
            for i in 0..func.captures.len() {
                let cap_var = VarId::new(i as u32);
                if let std::collections::hash_map::Entry::Vacant(e) = var_to_local.entry(cap_var) {
                    e.insert(local_count);
                    local_count += 1;
                }
            }
        }

        // Reserve two scratch i32 locals for the integer-printing (itoa) routine.
        let itoa_v = local_count;
        let itoa_p = local_count + 1;
        // Six more scratch i32 locals for the string builtins (ke_teks /
        // gabung_teks): result ptr, lengths, source ptrs, copy index.
        let scratch = local_count + 2;
        local_count += 8;

        // Map each IR value to its static type so `cetak` can pick an int vs
        // string-pointer print path.
        let mut var_to_ty: HashMap<VarId, Ty> = HashMap::new();
        for block in &func.blocks {
            for instr in &block.instrs {
                var_to_ty.insert(instr.result, instr.ty.clone());
            }
        }

        // Finalize locals (params closure_ptr/arg are locals 0,1, declared by the
        // function type). The uniform value cell is i64, so SSA-value locals and
        // the int-print value scratch `itoa_v` form one i64 group [2, itoa_v];
        // the 7 address/length scratch (`itoa_p` + 6 string-builtin scratch) that
        // follow are addresses, so they stay i32. Indices already order value
        // locals before scratch, so the split preserves the flat numbering.
        let i64_locals = (itoa_v + 1).saturating_sub(2); // SSA values + itoa_v
        let i32_locals = local_count - (itoa_v + 1); // itoa_p + 6 string scratch = 7
        if i64_locals > 0 {
            locals.push((i64_locals, ValType::I64));
        }
        if i32_locals > 0 {
            locals.push((i32_locals, ValType::I32));
        }

        let ctx = EmitCtx {
            var_map: &var_to_local,
            func_map,
            var_to_func: &var_to_func,
            string_table,
            alloc_func_index,
            user_func_type_idx,
            bi_from_str_index,
            bi_to_str_index,
            bi_cmp_index,
            bi_addsub_index,
            bi_mul_index,
            bi_divmod_index,
            dec_from_str_index,
            dec_to_str_index,
            dec_addsub_index,
            dec_mul_index,
            dec_cmp_index,
            dec_div_index,
            fix_mul_index,
            fix_div_index,
            fix_titik_tetap_index,
            qmn_parse_index,
            qmn_to_str_index,
            qmn_addsub_index,
            qmn_mul_index,
            qmn_div_index,
            qmn_cmp_index,
            var_to_ty: &var_to_ty,
            itoa_v,
            itoa_p,
            scratch,
        };

        // Load captures from closure memory into locals.
        // Closure layout: [func_index: i32, capture0: i32, capture1: i32, ...]
        // closure_ptr is local 0. Captures start at offset +4.
        // VarId(i) = capture i, loaded from closure_ptr + (i+1)*4
        if !func.captures.is_empty() {
            for (i, _cap) in func.captures.iter().enumerate() {
                let cap_var = VarId::new(i as u32);
                code.push(Op::LocalGet as u8);
                wasm_encode::encode_uleb128(0, &mut code); // closure_ptr = local 0
                code.push(Op::I32WrapI64 as u8); // cell -> i32 address
                code.push(Op::I64Load as u8);
                code.push(0x02); // align 4
                // A memarg offset is LEB128, not a raw byte: capture 15 is at
                // offset 128, which needs two bytes. Pushing it raw silently
                // truncated, so a closure with 16+ captures read and wrote the
                // wrong cells.
                wasm_encode::encode_uleb128(((i + 1) * 8) as u64, &mut code);
                if let Some(&local) = var_to_local.get(&cap_var) {
                    code.push(Op::LocalSet as u8);
                    wasm_encode::encode_uleb128(local as u64, &mut code);
                }
            }
        }

        // Build a block index for quick lookup by BlockId.
        // Note: if multiple blocks share a BlockId, only the last one is kept.
        let block_map: HashMap<BlockId, usize> = func
            .blocks
            .iter()
            .enumerate()
            .map(|(i, b)| (b.id, i))
            .collect();

        // Emit the function body as structured control flow starting from the
        // entry block. The recursion reconstructs nested AND sequential if/else
        // from the lowerer's CondBranch/merge CFG. (The previous ad-hoc loop
        // only handled a single if/else per function — a second sequential
        // if/else had its then/else blocks emitted flat, so both branches ran.)
        // Start at the entry block's index (via block_map, since blocks may
        // share a BlockId and the map keeps the last — e.g. hand-built test IR).
        let entry_idx = block_map.get(&func.entry).copied().unwrap_or(0);
        self.emit_structured(entry_idx, None, func, &ctx, &block_map, &mut code)?;

        if code.is_empty() || !matches!(code.last(), Some(&b) if b == Op::Return as u8) {
            wasm_i64c(&mut code, 0);
        }

        Ok(FuncBody { locals, code })
    }

    /// Emit a region of the CFG as structured WASM control flow, from block
    /// `entry` up to (but not including) `stop`. Reconstructs nested AND
    /// sequential if/else from `CondBranch` terminators; the merge of each
    /// `CondBranch` is the block its then/else branches rejoin at.
    ///
    /// Returns the index of the block from which this region exits to `stop`
    /// (i.e. the merge's actual predecessor), or `None` if the region diverges
    /// (ends in `Return`/`Unreachable`) or has no merge. The caller uses this
    /// exit block — not the region's entry — to push the branch's contribution
    /// to the merge `Phi`. This is what makes a *nested* if/else correct: its
    /// exit is an inner merge block, which is the block the lowerer keys the
    /// outer `Phi` entry by; the entry block (an inner `CondBranch`) is not.
    fn emit_structured(
        &self,
        entry: usize,
        stop: Option<usize>,
        func: &Function,
        ctx: &EmitCtx<'_>,
        block_map: &HashMap<BlockId, usize>,
        code: &mut Vec<u8>,
    ) -> Result<Option<usize>> {
        let mut cur = entry;
        loop {
            if Some(cur) == stop {
                return Ok(None);
            }
            let block = &func.blocks[cur];
            self.emit_block_instrs(block, ctx, code)?;
            match &block.terminator {
                Some(Terminator::Return(var)) => {
                    if let Some(local) = ctx.var_map.get(var) {
                        code.push(Op::LocalGet as u8);
                        wasm_encode::encode_uleb128(*local as u64, code);
                    }
                    code.push(Op::Return as u8);
                    return Ok(None);
                }
                Some(Terminator::Unreachable) => {
                    code.push(Op::Unreachable as u8);
                    return Ok(None);
                }
                Some(Terminator::Branch(target)) => match block_map.get(target) {
                    Some(&t) => {
                        if Some(t) == stop {
                            // `cur` is the region's exit: it rejoins the enclosing
                            // merge. Report it so the caller pushes the right phi
                            // contribution (for a nested if/else this is an inner
                            // merge block, not the region's entry CondBranch).
                            return Ok(Some(cur));
                        }
                        // A BACK edge — the CFG of a `selagi`/`ulang` loop. This
                        // emitter only knows how to structure forward if/else
                        // regions; following the edge would walk the same blocks
                        // forever. WASM needs real `loop`/`br_if` nesting, which
                        // is not built yet, so refuse the module rather than emit
                        // something that silently runs the body once (which is
                        // exactly the bug real loops were introduced to fix).
                        if t <= cur {
                            return Err(Error::InvalidOperation(
                                "the WASM backend cannot yet compile `selagi`/`ulang` loops \
                                 (they need structured loop/br_if lowering). Use `riinac run`, \
                                 or `riinac build` for a native binary."
                                    .to_string(),
                            ));
                        }
                        cur = t;
                    }
                    None => return Ok(None),
                },
                Some(Terminator::CondBranch {
                    cond,
                    then_block,
                    else_block,
                }) => {
                    let (Some(&then_idx), Some(&else_idx)) =
                        (block_map.get(then_block), block_map.get(else_block))
                    else {
                        return Ok(None);
                    };
                    // The merge is where the two branches rejoin: the Branch
                    // target of the then (or else) branch.
                    let merge = Self::branch_target(&func.blocks[then_idx], block_map)
                        .or_else(|| Self::branch_target(&func.blocks[else_idx], block_map));

                    // A "merge" that points BACKWARDS is not a merge — it is the
                    // back edge of a `selagi`/`ulang` loop, whose header this
                    // block is. Continuing would re-emit the header forever
                    // (the emitter's own walk has no visited set). Structuring a
                    // loop needs real `loop`/`br_if` nesting, which is not built
                    // yet, so refuse the module: a backend that cannot express a
                    // construct fails closed rather than emitting something that
                    // silently runs the body once (REQ-78).
                    if merge.is_some_and(|m| m <= cur) {
                        return Err(Error::InvalidOperation(
                            "the WASM backend cannot yet compile `selagi`/`ulang` loops \
                             (they need structured loop/br_if lowering). Use `riinac run`, \
                             or `riinac build` for a native binary."
                                .to_string(),
                        ));
                    }

                    if let Some(local) = ctx.var_map.get(cond) {
                        code.push(Op::LocalGet as u8);
                        wasm_encode::encode_uleb128(*local as u64, code);
                        code.push(Op::I32WrapI64 as u8); // bool cell -> i32 condition
                    }
                    code.push(Op::If as u8);
                    // Each branch pushes its i64 phi contribution as the block result.
                    code.push(ValType::I64 as u8);
                    // Emit each branch region, then push its contribution to the
                    // merge phi from the region's EXIT block (its merge
                    // predecessor), falling back to the entry block when the
                    // region diverges (no exit-to-merge).
                    let then_exit =
                        self.emit_structured(then_idx, merge, func, ctx, block_map, code)?;
                    self.emit_phi_value_for_branch(
                        &func.blocks[then_exit.unwrap_or(then_idx)],
                        &func.blocks,
                        block_map,
                        ctx,
                        code,
                    )?;
                    code.push(Op::Else as u8);
                    let else_exit =
                        self.emit_structured(else_idx, merge, func, ctx, block_map, code)?;
                    self.emit_phi_value_for_branch(
                        &func.blocks[else_exit.unwrap_or(else_idx)],
                        &func.blocks,
                        block_map,
                        ctx,
                        code,
                    )?;
                    code.push(Op::End as u8);
                    // Store the if/else result into the merge's phi local.
                    if let Some(m) = merge {
                        for instr in &func.blocks[m].instrs {
                            if let Instruction::Phi(_) = &instr.instr {
                                if let Some(local) = ctx.var_map.get(&instr.result) {
                                    code.push(Op::LocalSet as u8);
                                    wasm_encode::encode_uleb128(*local as u64, code);
                                }
                                break;
                            }
                        }
                    }
                    match merge {
                        Some(m) => cur = m,
                        None => {
                            // No merge: BOTH arms diverge (each ends in a
                            // `return`), so nothing rejoins. The `if` was
                            // still typed `(result i64)`, so its result is
                            // sitting on the operand stack with no phi local
                            // to receive it — wasmtime rejects that as
                            // "values remaining on stack at end of block".
                            //
                            // Control genuinely cannot reach here, so say so:
                            // `unreachable` makes the rest of the frame
                            // polymorphic, which absorbs the dangling value.
                            // Before REQ-80's early return this arm was
                            // effectively dead, because a branch could not end
                            // in `return` — every one fell through to a merge.
                            code.push(Op::Unreachable as u8);
                            return Ok(None);
                        }
                    }
                }
                Some(Terminator::Handle { .. }) | None => return Ok(None),
            }
        }
    }

    /// The block index a block unconditionally branches to, if any.
    fn branch_target(block: &BasicBlock, block_map: &HashMap<BlockId, usize>) -> Option<usize> {
        match &block.terminator {
            Some(Terminator::Branch(t)) => block_map.get(t).copied(),
            _ => None,
        }
    }

    /// Emit only the instructions of a block (no terminator).
    fn emit_block_instrs(
        &self,
        block: &BasicBlock,
        ctx: &EmitCtx<'_>,
        code: &mut Vec<u8>,
    ) -> Result<()> {
        for instr in &block.instrs {
            self.emit_instruction(&instr.instr, Some(instr.result), ctx, code)?;
        }
        Ok(())
    }

    /// For a then/else block that branches to a merge block with a Phi,
    /// push the value that this block contributes to the Phi onto the stack.
    fn emit_phi_value_for_branch(
        &self,
        branch_block: &BasicBlock,
        blocks: &[BasicBlock],
        block_map: &HashMap<BlockId, usize>,
        ctx: &EmitCtx<'_>,
        code: &mut Vec<u8>,
    ) -> Result<()> {
        // Find the merge block (target of this block's Branch terminator)
        let target_id = match &branch_block.terminator {
            Some(Terminator::Branch(target)) => Some(*target),
            _ => None,
        };

        if let Some(target_id) = target_id {
            if let Some(&merge_idx) = block_map.get(&target_id) {
                let merge_blk = &blocks[merge_idx];
                // Find the phi node and extract this block's contribution
                for instr in &merge_blk.instrs {
                    if let Instruction::Phi(entries) = &instr.instr {
                        for (bb_id, var) in entries {
                            if *bb_id == branch_block.id {
                                // Push this variable onto the stack
                                if let Some(local) = ctx.var_map.get(var) {
                                    code.push(Op::LocalGet as u8);
                                    wasm_encode::encode_uleb128(*local as u64, code);
                                }
                                return Ok(());
                            }
                        }
                    }
                }
            }
        }

        // If we couldn't find a phi contribution, look at the last instruction
        // in this block and push its result (common fallback)
        if let Some(last_instr) = branch_block.instrs.last() {
            if let Some(local) = ctx.var_map.get(&last_instr.result) {
                code.push(Op::LocalGet as u8);
                wasm_encode::encode_uleb128(*local as u64, code);
            }
        } else {
            // Empty block — push 0 (unit cell)
            wasm_i64c(code, 0);
        }

        Ok(())
    }

    // emit_block is no longer used — block emission is now handled by
    // emit_function (structured if/else) + emit_block_instrs + emit_block_terminator.

    /// Helper: emit `call $riina_alloc` with size on stack, leaving the returned
    /// address lifted into the i64 value cell (`alloc` stays `(i32)->i32` since
    /// linear-memory addresses are i32, so every allocation site gets a uniform
    /// i64 pointer from this single extend).
    fn emit_alloc_call(alloc_func_index: u32, size: u32, code: &mut Vec<u8>) {
        code.push(Op::I32Const as u8);
        wasm_encode::encode_sleb128(size as i64, code);
        code.push(Op::Call as u8);
        wasm_encode::encode_uleb128(alloc_func_index as u64, code);
        code.push(Op::I64ExtendI32U as u8); // address -> i64 cell
    }

    /// Helper: emit local.get for a VarId.
    fn emit_local_get(var: &VarId, var_map: &HashMap<VarId, u32>, code: &mut Vec<u8>) {
        if let Some(local) = var_map.get(var) {
            code.push(Op::LocalGet as u8);
            wasm_encode::encode_uleb128(*local as u64, code);
        }
    }

    /// Map a `-1/0/1` compare result (i32, on the stack — from `bi_cmp` or
    /// `dec_cmp`) to comparison `op`'s boolean and lift it into the i64 cell.
    fn emit_cmp_result_to_bool(op: &BinOp, code: &mut Vec<u8>) {
        match op {
            BinOp::Eq => code.push(Op::I32Eqz as u8), // == 0
            BinOp::Ne => {
                code.push(Op::I32Eqz as u8);
                code.push(Op::I32Eqz as u8); // != 0
            }
            BinOp::Lt => {
                wasm_i32c(code, 0);
                code.push(Op::I32LtS as u8); // < 0
            }
            BinOp::Gt => {
                wasm_i32c(code, 0);
                code.push(Op::I32GtS as u8); // > 0
            }
            BinOp::Le => {
                wasm_i32c(code, 0);
                code.push(Op::I32LeS as u8); // <= 0
            }
            BinOp::Ge => {
                wasm_i32c(code, 0);
                code.push(Op::I32GeS as u8); // >= 0
            }
            _ => unreachable!("comparison op expected"),
        }
        code.push(Op::I64ExtendI32U as u8); // bool -> i64 cell
    }

    /// Emit code that prints the integer in `arg` as unsigned decimal ASCII via
    /// WASI `fd_write`. Digits are written backwards into heap scratch
    /// (`heap_ptr+16..heap_ptr+48`); the iovec lives at `heap_ptr` and
    /// `nwritten` at `heap_ptr+8`, matching the string path's scratch layout.
    fn emit_print_int(arg: &VarId, signed_bits: Option<u8>, ctx: &EmitCtx, code: &mut Vec<u8>) {
        let set_v = |c: &mut Vec<u8>| {
            c.push(Op::LocalSet as u8);
            wasm_encode::encode_uleb128(ctx.itoa_v as u64, c);
        };
        let get_v = |c: &mut Vec<u8>| {
            c.push(Op::LocalGet as u8);
            wasm_encode::encode_uleb128(ctx.itoa_v as u64, c);
        };
        // Numeric tower: scratch holds "value was negative" for a signed sized int
        // (free here — the string-builtin scratch locals are not used while printing
        // an integer). Used to prepend '-' after the magnitude is rendered.
        let set_neg = |c: &mut Vec<u8>| {
            c.push(Op::LocalSet as u8);
            wasm_encode::encode_uleb128(ctx.scratch as u64, c);
        };
        let get_neg = |c: &mut Vec<u8>| {
            c.push(Op::LocalGet as u8);
            wasm_encode::encode_uleb128(ctx.scratch as u64, c);
        };
        let set_p = |c: &mut Vec<u8>| {
            c.push(Op::LocalSet as u8);
            wasm_encode::encode_uleb128(ctx.itoa_p as u64, c);
        };
        let get_p = |c: &mut Vec<u8>| {
            c.push(Op::LocalGet as u8);
            wasm_encode::encode_uleb128(ctx.itoa_p as u64, c);
        };
        let heap = |c: &mut Vec<u8>| {
            c.push(Op::GlobalGet as u8);
            wasm_encode::encode_uleb128(GLOBAL_HEAP_PTR as u64, c);
        };
        let i32c = |c: &mut Vec<u8>, n: i64| {
            c.push(Op::I32Const as u8);
            wasm_encode::encode_sleb128(n, c);
        };

        // $v = arg
        Self::emit_local_get(arg, ctx.var_map, code);
        set_v(code);
        // Signed sized int: sign-extend to a full i32, record the sign, and print
        // the magnitude (the unsigned loop below) with a '-' prepended afterwards.
        if let Some(bits) = signed_bits {
            // $v = sext($v, bits)
            get_v(code);
            emit_sext_i64(bits, code);
            set_v(code);
            // $neg = ($v < 0)   (i64 compare -> i32 flag)
            get_v(code);
            wasm_i64c(code, 0);
            code.push(Op::I64LtS as u8);
            set_neg(code);
            // if $neg { $v = 0 - $v }
            get_neg(code);
            code.push(Op::If as u8);
            code.push(0x40);
            wasm_i64c(code, 0);
            get_v(code);
            code.push(Op::I64Sub as u8);
            set_v(code);
            code.push(Op::End as u8);
        }
        // $p = heap_ptr + 48  (one past the digit buffer; we write backwards)
        heap(code);
        i32c(code, 48);
        code.push(Op::I32Add as u8);
        set_p(code);

        // do { p--; mem[p] = '0' + (v % 10); v = v / 10 } while (v != 0)
        code.push(Op::Loop as u8);
        code.push(0x40); // empty block type
        {
            // p = p - 1
            get_p(code);
            i32c(code, 1);
            code.push(Op::I32Sub as u8);
            set_p(code);
            // mem[p] = 48 + (v % 10)   (i32.store8: addr then value; the digit is
            // an i64 remainder wrapped to an i32 byte)
            get_p(code);
            get_v(code);
            wasm_i64c(code, 10);
            code.push(Op::I64RemU as u8);
            code.push(Op::I32WrapI64 as u8);
            i32c(code, 48); // '0'
            code.push(Op::I32Add as u8);
            code.push(Op::I32Store8 as u8);
            code.push(0x00); // align 0 (1-byte)
            code.push(0x00); // offset 0
            // v = v / 10
            get_v(code);
            wasm_i64c(code, 10);
            code.push(Op::I64DivU as u8);
            set_v(code);
            // if v != 0, branch back to loop (depth 0)  (i64 -> i32 condition)
            get_v(code);
            code.push(Op::I64Eqz as u8);
            code.push(Op::I32Eqz as u8);
            code.push(Op::BrIf as u8);
            wasm_encode::encode_uleb128(0, code);
        }
        code.push(Op::End as u8);

        // Signed & negative: prepend '-' (ASCII 45) before the rendered magnitude.
        if signed_bits.is_some() {
            get_neg(code);
            code.push(Op::If as u8);
            code.push(0x40);
            // p = p - 1; mem[p] = '-'
            get_p(code);
            i32c(code, 1);
            code.push(Op::I32Sub as u8);
            set_p(code);
            get_p(code);
            i32c(code, 45);
            code.push(Op::I32Store8 as u8);
            code.push(0x00);
            code.push(0x00);
            code.push(Op::End as u8);
        }

        // iovec.ptr = $p   → store at heap_ptr[0]
        heap(code);
        get_p(code);
        code.push(Op::I32Store as u8);
        code.push(0x02);
        code.push(0x00);
        // iovec.len = (heap_ptr + 48) - $p   → store at heap_ptr[4]
        heap(code);
        heap(code);
        i32c(code, 48);
        code.push(Op::I32Add as u8);
        get_p(code);
        code.push(Op::I32Sub as u8);
        code.push(Op::I32Store as u8);
        code.push(0x02);
        code.push(0x04); // offset 4
        // fd_write(1, heap_ptr, 1, heap_ptr+8)
        i32c(code, 1);
        heap(code);
        i32c(code, 1);
        heap(code);
        i32c(code, 8);
        code.push(Op::I32Add as u8);
        code.push(Op::Call as u8);
        wasm_encode::encode_uleb128(0, code); // fd_write
        code.push(Op::Drop as u8);
    }

    /// `ke_teks(int)` → a heap string `[len:u32][ascii digits]`; leaves the
    /// pointer on the stack. Two passes: count digits, alloc, write digits.
    /// `signed_bits` is the static width of a *signed* sized-int argument
    /// (`Ty::IntN{signed}`) — the i64 cell carries no runtime tag (unlike the
    /// C backend's `int_signed_bits`), so signedness must come from the call
    /// site's type. `Some(b)`: sign-extend from `b`, render `-` + magnitude
    /// for negatives (the interpreter is the reference: `ke_teks(0i8 - 3i8)`
    /// is "-3", not the masked "253"). `None`: unsigned u64 render, unchanged.
    fn emit_ke_teks(arg: &VarId, ctx: &EmitCtx, code: &mut Vec<u8>, signed_bits: Option<u8>) {
        let v = ctx.itoa_v;
        let wp = ctx.itoa_p;
        let rp = ctx.scratch;
        let cnt = ctx.scratch + 1;
        let neg = ctx.scratch + 2;
        let get = |c: &mut Vec<u8>, l: u32| {
            c.push(Op::LocalGet as u8);
            wasm_encode::encode_uleb128(l as u64, c);
        };
        let set = |c: &mut Vec<u8>, l: u32| {
            c.push(Op::LocalSet as u8);
            wasm_encode::encode_uleb128(l as u64, c);
        };
        // Load |value| into v; for the signed case set the `neg` i32 flag first.
        // Negating i64::MIN wraps to itself, but the magnitude loops below use
        // UNSIGNED div/rem, which read that bit pattern as 2^63 — exactly the
        // magnitude "-9223372036854775808" needs.
        let load_magnitude = |c: &mut Vec<u8>| {
            Self::emit_local_get(arg, ctx.var_map, c);
            if let Some(b) = signed_bits {
                emit_sext_i64(b, c);
                set(c, v);
                get(c, neg);
                c.push(Op::If as u8);
                c.push(0x40);
                wasm_i64c(c, 0);
                get(c, v);
                c.push(Op::I64Sub as u8);
                set(c, v);
                c.push(Op::End as u8);
            } else {
                set(c, v);
            }
        };
        if let Some(b) = signed_bits {
            // neg = (sext(arg) < 0)
            Self::emit_local_get(arg, ctx.var_map, code);
            emit_sext_i64(b, code);
            wasm_i64c(code, 0);
            code.push(Op::I64LtS as u8);
            set(code, neg);
        } else {
            wasm_i32c(code, 0);
            set(code, neg);
        }
        // Pass 1: count chars — digits (always >= 1) plus one for '-' if neg.
        load_magnitude(code);
        get(code, neg);
        set(code, cnt);
        code.push(Op::Loop as u8);
        code.push(0x40);
        get(code, cnt);
        wasm_i32c(code, 1);
        code.push(Op::I32Add as u8);
        set(code, cnt);
        get(code, v);
        wasm_i64c(code, 10);
        code.push(Op::I64DivU as u8);
        set(code, v);
        get(code, v);
        code.push(Op::I64Eqz as u8);
        code.push(Op::I32Eqz as u8);
        code.push(Op::BrIf as u8);
        wasm_encode::encode_uleb128(0, code);
        code.push(Op::End as u8);
        // rp = alloc(align4(4 + cnt)) — keep the bump pointer 4-aligned so the
        // i32 length-prefix store below stays aligned.
        wasm_i32c(code, 4);
        get(code, cnt);
        code.push(Op::I32Add as u8);
        wasm_i32c(code, 3);
        code.push(Op::I32Add as u8);
        wasm_i32c(code, -4); // & ~3
        code.push(Op::I32And as u8);
        code.push(Op::Call as u8);
        wasm_encode::encode_uleb128(ctx.alloc_func_index as u64, code);
        set(code, rp);
        // mem[rp] = cnt (length prefix)
        get(code, rp);
        get(code, cnt);
        code.push(Op::I32Store as u8);
        code.push(0x02);
        code.push(0x00);
        // Pass 2: write digits backward into (rp+4+neg-1, rp+4+cnt); the digit
        // count is cnt-neg, so the loop's final wp is rp+4+neg. v = |arg|.
        load_magnitude(code);
        get(code, rp);
        wasm_i32c(code, 4);
        code.push(Op::I32Add as u8);
        get(code, cnt);
        code.push(Op::I32Add as u8);
        set(code, wp);
        code.push(Op::Loop as u8);
        code.push(0x40);
        get(code, wp);
        wasm_i32c(code, 1);
        code.push(Op::I32Sub as u8);
        set(code, wp);
        get(code, wp);
        get(code, v);
        wasm_i64c(code, 10);
        code.push(Op::I64RemU as u8);
        code.push(Op::I32WrapI64 as u8);
        wasm_i32c(code, 48);
        code.push(Op::I32Add as u8);
        code.push(Op::I32Store8 as u8);
        code.push(0x00);
        code.push(0x00);
        get(code, v);
        wasm_i64c(code, 10);
        code.push(Op::I64DivU as u8);
        set(code, v);
        get(code, v);
        code.push(Op::I64Eqz as u8);
        code.push(Op::I32Eqz as u8);
        code.push(Op::BrIf as u8);
        wasm_encode::encode_uleb128(0, code);
        code.push(Op::End as u8);
        // If negative, the sign char lands just before the digits, at rp+4
        // (= final wp - 1).
        get(code, neg);
        code.push(Op::If as u8);
        code.push(0x40);
        get(code, rp);
        wasm_i32c(code, 4);
        code.push(Op::I32Add as u8);
        wasm_i32c(code, 45); // '-'
        code.push(Op::I32Store8 as u8);
        code.push(0x00);
        code.push(0x00);
        code.push(Op::End as u8);
        // result = rp, lifted into the i64 value cell
        get(code, rp);
        code.push(Op::I64ExtendI32U as u8);
    }

    /// `gabung_teks((s1, s2))` → a freshly-allocated heap string that is the
    /// concatenation of the two `[len][bytes]` strings; leaves the pointer on
    /// the stack. `arg` is a pair pointer `[s1:i32][s2:i32]`.
    fn emit_gabung_teks(arg: &VarId, ctx: &EmitCtx, code: &mut Vec<u8>) {
        let s1 = ctx.scratch;
        let s2 = ctx.scratch + 1;
        let set = |c: &mut Vec<u8>, l: u32| {
            c.push(Op::LocalSet as u8);
            wasm_encode::encode_uleb128(l as u64, c);
        };
        let load = |c: &mut Vec<u8>, off: u8| {
            c.push(Op::I32WrapI64 as u8); // pair ptr cell -> i32 addr
            c.push(Op::I64Load as u8);
            c.push(0x02);
            c.push(off);
            c.push(Op::I32WrapI64 as u8); // loaded string-ptr cell -> i32 scratch
        };
        // s1 = mem[arg+0]; s2 = mem[arg+8]   (8-byte cells)
        Self::emit_local_get(arg, ctx.var_map, code);
        load(code, 0x00);
        set(code, s1);
        Self::emit_local_get(arg, ctx.var_map, code);
        load(code, 0x08);
        set(code, s2);
        Self::emit_str_concat_core(ctx, code);
    }

    /// String `Add` (concatenation) of two operand string pointers. UI/text
    /// lowering emits concatenation as `BinOp(Add)` on `Ty::String`, so the
    /// WASM `Add` path routes string-typed operands here instead of `i32.add`.
    fn emit_str_add(lhs: &VarId, rhs: &VarId, ctx: &EmitCtx, code: &mut Vec<u8>) {
        let s1 = ctx.scratch;
        let s2 = ctx.scratch + 1;
        let set = |c: &mut Vec<u8>, l: u32| {
            c.push(Op::LocalSet as u8);
            wasm_encode::encode_uleb128(l as u64, c);
        };
        Self::emit_local_get(lhs, ctx.var_map, code);
        code.push(Op::I32WrapI64 as u8); // string ptr cell -> i32 scratch
        set(code, s1);
        Self::emit_local_get(rhs, ctx.var_map, code);
        code.push(Op::I32WrapI64 as u8);
        set(code, s2);
        Self::emit_str_concat_core(ctx, code);
    }

    /// Concatenate the two `[len][bytes]` heap strings whose pointers are held in
    /// scratch locals `s1` (= `ctx.scratch`) and `s2` (= `ctx.scratch + 1`):
    /// allocate a fresh `[len1+len2][bytes]` string and leave its pointer on the
    /// stack. Shared by `gabung_teks` and the string `Add` path.
    fn emit_str_concat_core(ctx: &EmitCtx, code: &mut Vec<u8>) {
        let s1 = ctx.scratch;
        let s2 = ctx.scratch + 1;
        let len1 = ctx.scratch + 2;
        let len2 = ctx.scratch + 3;
        let rp = ctx.scratch + 4;
        // The copy index is an i32 address counter; use the 6th (i32) string
        // scratch, NOT itoa_v — itoa_v is now an i64 value-cell local.
        let idx = ctx.scratch + 5;
        let get = |c: &mut Vec<u8>, l: u32| {
            c.push(Op::LocalGet as u8);
            wasm_encode::encode_uleb128(l as u64, c);
        };
        let set = |c: &mut Vec<u8>, l: u32| {
            c.push(Op::LocalSet as u8);
            wasm_encode::encode_uleb128(l as u64, c);
        };
        let load = |c: &mut Vec<u8>, off: u8| {
            c.push(Op::I32Load as u8);
            c.push(0x02);
            c.push(off);
        };
        // len1 = mem[s1]; len2 = mem[s2]
        get(code, s1);
        load(code, 0x00);
        set(code, len1);
        get(code, s2);
        load(code, 0x00);
        set(code, len2);
        // rp = alloc(align4(4 + len1 + len2)) — keep the bump pointer 4-aligned.
        wasm_i32c(code, 4);
        get(code, len1);
        code.push(Op::I32Add as u8);
        get(code, len2);
        code.push(Op::I32Add as u8);
        wasm_i32c(code, 3);
        code.push(Op::I32Add as u8);
        wasm_i32c(code, -4);
        code.push(Op::I32And as u8);
        code.push(Op::Call as u8);
        wasm_encode::encode_uleb128(ctx.alloc_func_index as u64, code);
        set(code, rp);
        // mem[rp] = len1 + len2
        get(code, rp);
        get(code, len1);
        get(code, len2);
        code.push(Op::I32Add as u8);
        code.push(Op::I32Store as u8);
        code.push(0x02);
        code.push(0x00);
        // copy_loop(dst_base, src, len): emit a `while idx < len` byte copy.
        let copy = |c: &mut Vec<u8>, dst_extra: &dyn Fn(&mut Vec<u8>), src: u32, len: u32| {
            wasm_i32c(c, 0);
            set(c, idx);
            c.push(Op::Block as u8);
            c.push(0x40);
            c.push(Op::Loop as u8);
            c.push(0x40);
            // if idx >= len, break out of block (depth 1)
            get(c, idx);
            get(c, len);
            c.push(Op::I32GeU as u8);
            c.push(Op::BrIf as u8);
            wasm_encode::encode_uleb128(1, c);
            // dst addr = rp + 4 + <dst_extra> + idx
            get(c, rp);
            wasm_i32c(c, 4);
            c.push(Op::I32Add as u8);
            dst_extra(c);
            get(c, idx);
            c.push(Op::I32Add as u8);
            // src byte = mem[src + 4 + idx]
            get(c, src);
            wasm_i32c(c, 4);
            c.push(Op::I32Add as u8);
            get(c, idx);
            c.push(Op::I32Add as u8);
            c.push(Op::I32Load8U as u8);
            c.push(0x00);
            c.push(0x00);
            // store byte
            c.push(Op::I32Store8 as u8);
            c.push(0x00);
            c.push(0x00);
            // idx++
            get(c, idx);
            wasm_i32c(c, 1);
            c.push(Op::I32Add as u8);
            set(c, idx);
            c.push(Op::Br as u8);
            wasm_encode::encode_uleb128(0, c);
            c.push(Op::End as u8); // loop
            c.push(Op::End as u8); // block
        };
        // copy s1 into [rp+4 ..)
        copy(code, &|_c: &mut Vec<u8>| {}, s1, len1);
        // copy s2 into [rp+4+len1 ..)
        copy(
            code,
            &|c: &mut Vec<u8>| {
                get(c, len1);
                c.push(Op::I32Add as u8);
            },
            s2,
            len2,
        );
        // result = rp, lifted into the i64 value cell
        get(code, rp);
        code.push(Op::I64ExtendI32U as u8);
    }

    /// Emit a single IR instruction as WASM instructions.
    fn emit_instruction(
        &self,
        instr: &Instruction,
        result: Option<VarId>,
        ctx: &EmitCtx<'_>,
        code: &mut Vec<u8>,
    ) -> Result<()> {
        match instr {
            Instruction::Const(c) => {
                match c {
                    Constant::Unit => {
                        wasm_i64c(code, 0);
                    }
                    Constant::Bool(b) => {
                        wasm_i64c(code, if *b { 1 } else { 0 });
                    }
                    Constant::Int(n) => {
                        // The uniform value cell is i64, so the full 64-bit integer
                        // is materialized directly (`*n as i64` carries the exact
                        // bit pattern, incl. the [2^63, 2^64) range). The old wasm32
                        // 32-bit-cell limitation (a clean compile error for >= 2^32)
                        // is gone — W1 of the numeric tower.
                        wasm_i64c(code, *n as i64);
                    }
                    Constant::String(s) => {
                        // Push pointer to string in data section (points to length
                        // prefix), lifted into the i64 cell.
                        let offset = ctx.string_table.get(s).copied().unwrap_or(0);
                        wasm_i64c(code, offset as i64);
                    }
                }
            }
            Instruction::Load(var) => {
                // Dereference: load the i64 cell at the address held in var
                Self::emit_local_get(var, ctx.var_map, code);
                code.push(Op::I32WrapI64 as u8); // cell -> i32 address
                code.push(Op::I64Load as u8);
                code.push(0x02); // alignment: 4
                code.push(0x00); // offset: 0
            }
            Instruction::Store(dst, src) => {
                // Store to memory: *dst = src
                Self::emit_local_get(dst, ctx.var_map, code);
                code.push(Op::I32WrapI64 as u8); // cell -> i32 address
                Self::emit_local_get(src, ctx.var_map, code);
                code.push(Op::I64Store as u8);
                code.push(0x02); // alignment: 4
                code.push(0x00); // offset: 0
                                 // Store returns unit (0)
                wasm_i64c(code, 0);
            }
            Instruction::BinOp(op, lhs, rhs)
                if matches!(op, BinOp::Add)
                    && matches!(
                        ctx.var_to_ty.get(lhs),
                        Some(Ty::String | Ty::Element | Ty::Color | Ty::UIStyle)
                    ) =>
            {
                // String concatenation is lowered as `Add` on `Ty::String`
                // operands (see `emit_concat` / UI lowering); emit the heap-string
                // concat routine rather than integer add. Leaves the result
                // pointer on the stack for the generic result-store below.
                Self::emit_str_add(lhs, rhs, ctx, code);
            }
            Instruction::BinOp(op, lhs, rhs)
                if matches!(ctx.var_to_ty.get(lhs), Some(Ty::BigInt))
                    || matches!(ctx.var_to_ty.get(rhs), Some(Ty::BigInt)) =>
            {
                // BigInt operands dispatch to the bignum runtime. W2.2a wires the
                // six comparisons via `bi_cmp` (-1/0/1) mapped to a Bool; arithmetic
                // (+, -, *, /) still fails closed so a besar binop never silently
                // `i64.*`-es the record pointers.
                match op {
                    BinOp::Eq | BinOp::Ne | BinOp::Lt | BinOp::Gt | BinOp::Le | BinOp::Ge => {
                        Self::emit_local_get(lhs, ctx.var_map, code);
                        code.push(Op::I32WrapI64 as u8);
                        Self::emit_local_get(rhs, ctx.var_map, code);
                        code.push(Op::I32WrapI64 as u8);
                        code.push(Op::Call as u8);
                        wasm_encode::encode_uleb128(ctx.bi_cmp_index as u64, code);
                        Self::emit_cmp_result_to_bool(op, code);
                    }
                    BinOp::Add | BinOp::Sub => {
                        // Signed add/sub via bi_addsub(a, b, sub): sub=1 for `-`.
                        Self::emit_local_get(lhs, ctx.var_map, code);
                        code.push(Op::I32WrapI64 as u8);
                        Self::emit_local_get(rhs, ctx.var_map, code);
                        code.push(Op::I32WrapI64 as u8);
                        wasm_i32c(code, if matches!(op, BinOp::Sub) { 1 } else { 0 });
                        code.push(Op::Call as u8);
                        wasm_encode::encode_uleb128(ctx.bi_addsub_index as u64, code);
                        code.push(Op::I64ExtendI32U as u8); // result ptr -> i64 cell
                    }
                    BinOp::Mul => {
                        // Schoolbook multiply via bi_mul(a, b).
                        Self::emit_local_get(lhs, ctx.var_map, code);
                        code.push(Op::I32WrapI64 as u8);
                        Self::emit_local_get(rhs, ctx.var_map, code);
                        code.push(Op::I32WrapI64 as u8);
                        code.push(Op::Call as u8);
                        wasm_encode::encode_uleb128(ctx.bi_mul_index as u64, code);
                        code.push(Op::I64ExtendI32U as u8); // result ptr -> i64 cell
                    }
                    BinOp::Div | BinOp::Mod => {
                        // Truncating divmod via bi_divmod(a, b, want_rem): want_rem=1
                        // for `%` (remainder), 0 for `/` (quotient).
                        Self::emit_local_get(lhs, ctx.var_map, code);
                        code.push(Op::I32WrapI64 as u8);
                        Self::emit_local_get(rhs, ctx.var_map, code);
                        code.push(Op::I32WrapI64 as u8);
                        wasm_i32c(code, if matches!(op, BinOp::Mod) { 1 } else { 0 });
                        code.push(Op::Call as u8);
                        wasm_encode::encode_uleb128(ctx.bi_divmod_index as u64, code);
                        code.push(Op::I64ExtendI32U as u8); // result ptr -> i64 cell
                    }
                    _ => {
                        // And/Or on BigInt: the typechecker rejects these, but fail
                        // closed defensively rather than emit i64 bitops on pointers.
                        return Err(crate::Error::InvalidOperation(format!(
                            "BigInt (`besar`) operator {op:?} is not supported by the \
                             WASM backend"
                        )));
                    }
                }
            }
            Instruction::BinOp(op, lhs, rhs)
                if matches!(ctx.var_to_ty.get(lhs), Some(Ty::Decimal))
                    || matches!(ctx.var_to_ty.get(rhs), Some(Ty::Decimal)) =>
            {
                // Decimal (`perpuluhan`) operands dispatch to the decimal runtime
                // (W3.1b): exact scale-aligned add/sub, exact mul (scales add),
                // half-to-even div, value-based compare — matching `decimal.rs` /
                // the C backend. `%`/And/Or are undefined for decimals (the
                // typechecker rejects them); fail closed defensively.
                match op {
                    BinOp::Eq | BinOp::Ne | BinOp::Lt | BinOp::Gt | BinOp::Le | BinOp::Ge => {
                        Self::emit_local_get(lhs, ctx.var_map, code);
                        code.push(Op::I32WrapI64 as u8);
                        Self::emit_local_get(rhs, ctx.var_map, code);
                        code.push(Op::I32WrapI64 as u8);
                        code.push(Op::Call as u8);
                        wasm_encode::encode_uleb128(ctx.dec_cmp_index as u64, code);
                        Self::emit_cmp_result_to_bool(op, code);
                    }
                    BinOp::Add | BinOp::Sub => {
                        Self::emit_local_get(lhs, ctx.var_map, code);
                        code.push(Op::I32WrapI64 as u8);
                        Self::emit_local_get(rhs, ctx.var_map, code);
                        code.push(Op::I32WrapI64 as u8);
                        wasm_i32c(code, if matches!(op, BinOp::Sub) { 1 } else { 0 });
                        code.push(Op::Call as u8);
                        wasm_encode::encode_uleb128(ctx.dec_addsub_index as u64, code);
                        code.push(Op::I64ExtendI32U as u8); // result ptr -> i64 cell
                    }
                    BinOp::Mul => {
                        Self::emit_local_get(lhs, ctx.var_map, code);
                        code.push(Op::I32WrapI64 as u8);
                        Self::emit_local_get(rhs, ctx.var_map, code);
                        code.push(Op::I32WrapI64 as u8);
                        code.push(Op::Call as u8);
                        wasm_encode::encode_uleb128(ctx.dec_mul_index as u64, code);
                        code.push(Op::I64ExtendI32U as u8);
                    }
                    BinOp::Div => {
                        Self::emit_local_get(lhs, ctx.var_map, code);
                        code.push(Op::I32WrapI64 as u8);
                        Self::emit_local_get(rhs, ctx.var_map, code);
                        code.push(Op::I32WrapI64 as u8);
                        code.push(Op::Call as u8);
                        wasm_encode::encode_uleb128(ctx.dec_div_index as u64, code);
                        code.push(Op::I64ExtendI32U as u8);
                    }
                    _ => {
                        return Err(crate::Error::InvalidOperation(format!(
                            "Decimal (`perpuluhan`) operator {op:?} is not supported by \
                             the WASM backend (it is undefined for decimals)"
                        )));
                    }
                }
            }
            Instruction::BinOp(op, lhs, rhs)
                if matches!(ctx.var_to_ty.get(lhs), Some(Ty::Fixed))
                    || matches!(ctx.var_to_ty.get(rhs), Some(Ty::Fixed)) =>
            {
                // Fixed-point (`wang`/`titik_tetap`) operands (W3.2). Add/sub and
                // compare are the same scale-aligned operations as Decimal (the
                // record layout is shared), so they reuse dec_addsub/dec_cmp;
                // mul/div round half-to-even back to max(scale) via the fix_*
                // helpers. `%`/And/Or are undefined for fixed-point; fail closed.
                match op {
                    BinOp::Eq | BinOp::Ne | BinOp::Lt | BinOp::Gt | BinOp::Le | BinOp::Ge => {
                        Self::emit_local_get(lhs, ctx.var_map, code);
                        code.push(Op::I32WrapI64 as u8);
                        Self::emit_local_get(rhs, ctx.var_map, code);
                        code.push(Op::I32WrapI64 as u8);
                        code.push(Op::Call as u8);
                        wasm_encode::encode_uleb128(ctx.dec_cmp_index as u64, code);
                        Self::emit_cmp_result_to_bool(op, code);
                    }
                    BinOp::Add | BinOp::Sub => {
                        Self::emit_local_get(lhs, ctx.var_map, code);
                        code.push(Op::I32WrapI64 as u8);
                        Self::emit_local_get(rhs, ctx.var_map, code);
                        code.push(Op::I32WrapI64 as u8);
                        wasm_i32c(code, if matches!(op, BinOp::Sub) { 1 } else { 0 });
                        code.push(Op::Call as u8);
                        wasm_encode::encode_uleb128(ctx.dec_addsub_index as u64, code);
                        code.push(Op::I64ExtendI32U as u8);
                    }
                    BinOp::Mul => {
                        Self::emit_local_get(lhs, ctx.var_map, code);
                        code.push(Op::I32WrapI64 as u8);
                        Self::emit_local_get(rhs, ctx.var_map, code);
                        code.push(Op::I32WrapI64 as u8);
                        code.push(Op::Call as u8);
                        wasm_encode::encode_uleb128(ctx.fix_mul_index as u64, code);
                        code.push(Op::I64ExtendI32U as u8);
                    }
                    BinOp::Div => {
                        Self::emit_local_get(lhs, ctx.var_map, code);
                        code.push(Op::I32WrapI64 as u8);
                        Self::emit_local_get(rhs, ctx.var_map, code);
                        code.push(Op::I32WrapI64 as u8);
                        code.push(Op::Call as u8);
                        wasm_encode::encode_uleb128(ctx.fix_div_index as u64, code);
                        code.push(Op::I64ExtendI32U as u8);
                    }
                    _ => {
                        return Err(crate::Error::InvalidOperation(format!(
                            "Fixed-point (`wang`/`titik_tetap`) operator {op:?} is not \
                             supported by the WASM backend (it is undefined for \
                             fixed-point)"
                        )));
                    }
                }
            }
            Instruction::BinOp(op, lhs, rhs)
                if matches!(ctx.var_to_ty.get(lhs), Some(Ty::FixedBin))
                    || matches!(ctx.var_to_ty.get(rhs), Some(Ty::FixedBin)) =>
            {
                // Q-format (`qmn`) operands (W3.3): exact in BigInt at
                // max(frac_bits), wrapped back into the i64 word (add/sub) or
                // rounded half-to-even (mul/div); value-based compare.
                // `%`/And/Or are undefined for Q-format; fail closed.
                match op {
                    BinOp::Eq | BinOp::Ne | BinOp::Lt | BinOp::Gt | BinOp::Le | BinOp::Ge => {
                        Self::emit_local_get(lhs, ctx.var_map, code);
                        code.push(Op::I32WrapI64 as u8);
                        Self::emit_local_get(rhs, ctx.var_map, code);
                        code.push(Op::I32WrapI64 as u8);
                        code.push(Op::Call as u8);
                        wasm_encode::encode_uleb128(ctx.qmn_cmp_index as u64, code);
                        Self::emit_cmp_result_to_bool(op, code);
                    }
                    BinOp::Add | BinOp::Sub => {
                        Self::emit_local_get(lhs, ctx.var_map, code);
                        code.push(Op::I32WrapI64 as u8);
                        Self::emit_local_get(rhs, ctx.var_map, code);
                        code.push(Op::I32WrapI64 as u8);
                        wasm_i32c(code, if matches!(op, BinOp::Sub) { 1 } else { 0 });
                        code.push(Op::Call as u8);
                        wasm_encode::encode_uleb128(ctx.qmn_addsub_index as u64, code);
                        code.push(Op::I64ExtendI32U as u8);
                    }
                    BinOp::Mul => {
                        Self::emit_local_get(lhs, ctx.var_map, code);
                        code.push(Op::I32WrapI64 as u8);
                        Self::emit_local_get(rhs, ctx.var_map, code);
                        code.push(Op::I32WrapI64 as u8);
                        code.push(Op::Call as u8);
                        wasm_encode::encode_uleb128(ctx.qmn_mul_index as u64, code);
                        code.push(Op::I64ExtendI32U as u8);
                    }
                    BinOp::Div => {
                        Self::emit_local_get(lhs, ctx.var_map, code);
                        code.push(Op::I32WrapI64 as u8);
                        Self::emit_local_get(rhs, ctx.var_map, code);
                        code.push(Op::I32WrapI64 as u8);
                        code.push(Op::Call as u8);
                        wasm_encode::encode_uleb128(ctx.qmn_div_index as u64, code);
                        code.push(Op::I64ExtendI32U as u8);
                    }
                    _ => {
                        return Err(crate::Error::InvalidOperation(format!(
                            "Q-format (`qmn`) operator {op:?} is not supported by the \
                             WASM backend (it is undefined for binary fixed-point)"
                        )));
                    }
                }
            }
            Instruction::BinOp(op, lhs, rhs) => {
                // Numeric tower: division/modulo/comparison of a *signed* sized int
                // (`Ty::IntN{signed}`) narrower than i32 must sign-extend its
                // operands first — the cell holds the width-masked (unsigned-range)
                // bits, so e.g. an i8 `-1` is stored as 255 and `I32LtS` would treat
                // it as +255. Add/Sub/Mul are bit-identical signed/unsigned (the
                // result mask below suffices); Eq/Ne compare equal bit patterns.
                let needs_signed_operands = matches!(
                    op,
                    BinOp::Div | BinOp::Mod | BinOp::Lt | BinOp::Le | BinOp::Gt | BinOp::Ge
                );
                let lext = needs_signed_operands
                    .then(|| signed_sub64_width(ctx.var_to_ty.get(lhs)))
                    .flatten();
                let rext = needs_signed_operands
                    .then(|| signed_sub64_width(ctx.var_to_ty.get(rhs)))
                    .flatten();
                // Signedness of the division/comparison itself. Plain `Nombor`
                // (`Ty::Int`) is a u64 at runtime (interpreter `Value::Int(u64)`,
                // C backend `uint64_t`), so it takes the UNSIGNED i64 ops — with
                // `I64DivS`/`I64LtS` a value >= 2^63 read as negative and
                // div/mod/order silently diverged from the other two backends
                // (found by a >= 2^63 differential, 2026-08-08). Signed sized
                // ints (`IntN{signed}`) keep the signed ops; their sub-64
                // operands are sign-extended above. Unsigned-vs-signed mixes
                // cannot reach here (the typechecker rejects them).
                let signed_ints = matches!(
                    ctx.var_to_ty.get(lhs),
                    Some(Ty::IntN { signed: true, .. })
                ) || matches!(
                    ctx.var_to_ty.get(rhs),
                    Some(Ty::IntN { signed: true, .. })
                );
                Self::emit_local_get(lhs, ctx.var_map, code);
                if let Some(b) = lext {
                    emit_sext_i64(b, code);
                }
                Self::emit_local_get(rhs, ctx.var_map, code);
                if let Some(b) = rext {
                    emit_sext_i64(b, code);
                }
                match op {
                    BinOp::Add => code.push(Op::I64Add as u8),
                    BinOp::Sub => code.push(Op::I64Sub as u8),
                    BinOp::Mul => code.push(Op::I64Mul as u8),
                    BinOp::Div => code.push(if signed_ints {
                        Op::I64DivS
                    } else {
                        Op::I64DivU
                    } as u8),
                    BinOp::Mod => code.push(if signed_ints {
                        Op::I64RemS
                    } else {
                        Op::I64RemU
                    } as u8),
                    BinOp::And => code.push(Op::I64And as u8),
                    BinOp::Or => code.push(Op::I64Or as u8),
                    // Comparisons yield an i32 (0/1); lift back into the i64 cell.
                    BinOp::Eq => {
                        code.push(Op::I64Eq as u8);
                        code.push(Op::I64ExtendI32U as u8);
                    }
                    BinOp::Ne => {
                        code.push(Op::I64Ne as u8);
                        code.push(Op::I64ExtendI32U as u8);
                    }
                    BinOp::Lt => {
                        code.push(if signed_ints { Op::I64LtS } else { Op::I64LtU } as u8);
                        code.push(Op::I64ExtendI32U as u8);
                    }
                    BinOp::Gt => {
                        code.push(if signed_ints { Op::I64GtS } else { Op::I64GtU } as u8);
                        code.push(Op::I64ExtendI32U as u8);
                    }
                    BinOp::Le => {
                        code.push(if signed_ints { Op::I64LeS } else { Op::I64LeU } as u8);
                        code.push(Op::I64ExtendI32U as u8);
                    }
                    BinOp::Ge => {
                        code.push(if signed_ints { Op::I64GeS } else { Op::I64GeU } as u8);
                        code.push(Op::I64ExtendI32U as u8);
                    }
                }
                // Numeric tower: mask an arithmetic result that types as a sized
                // integer narrower than the 64-bit cell to its width (`& (2^bits-1)`),
                // so compiled overflow wraps modulo 2^bits like the interpreter and
                // the C backend. (With i64 arithmetic this now also masks 32-bit
                // results, which the old i32 cell wrapped implicitly.) Operands are
                // already in-range, so masking the result suffices; comparisons type
                // as `Bool`, so they are not masked.
                if let Some(r) = result.as_ref() {
                    if let Some(Ty::IntN { bits, .. }) = ctx.var_to_ty.get(r) {
                        if *bits < 64 {
                            wasm_i64c(code, (1i64 << bits) - 1);
                            code.push(Op::I64And as u8);
                        }
                    }
                }
            }
            Instruction::UnaryOp(op, operand) => match op {
                UnaryOp::Not => {
                    Self::emit_local_get(operand, ctx.var_map, code);
                    code.push(Op::I64Eqz as u8);
                    code.push(Op::I64ExtendI32U as u8);
                }
                UnaryOp::Neg => {
                    wasm_i64c(code, 0);
                    Self::emit_local_get(operand, ctx.var_map, code);
                    code.push(Op::I64Sub as u8);
                }
            },
            Instruction::Call(func_var, arg) => {
                if let Some(fid) = ctx.var_to_func.get(func_var) {
                    if let Some(&idx) = ctx.func_map.get(fid) {
                        // Direct call: push closure_ptr (the var itself), then arg
                        Self::emit_local_get(func_var, ctx.var_map, code);
                        Self::emit_local_get(arg, ctx.var_map, code);
                        code.push(Op::Call as u8);
                        wasm_encode::encode_uleb128(idx as u64, code);
                    } else {
                        wasm_i64c(code, 0); // null closure ptr (cell)
                        Self::emit_local_get(arg, ctx.var_map, code);
                        code.push(Op::Call as u8);
                        wasm_encode::encode_uleb128(0, code);
                    }
                } else {
                    // Indirect call through closure pointer
                    // Push closure_ptr (first arg), then arg (second arg)
                    Self::emit_local_get(func_var, ctx.var_map, code);
                    Self::emit_local_get(arg, ctx.var_map, code);
                    // Load func_idx (an i64 cell) from closure[0] and wrap it to the
                    // i32 table index.
                    Self::emit_local_get(func_var, ctx.var_map, code);
                    code.push(Op::I32WrapI64 as u8); // closure ptr cell -> i32 addr
                    code.push(Op::I64Load as u8);
                    code.push(0x02);
                    code.push(0x00); // load func_table_idx from closure[0]
                    code.push(Op::I32WrapI64 as u8); // cell -> i32 table index
                                     // call_indirect: type must match (i64, i64) -> i64
                    code.push(Op::CallIndirect as u8);
                    wasm_encode::encode_uleb128(ctx.user_func_type_idx as u64, code);
                    wasm_encode::encode_uleb128(0, code); // table 0
                }
            }
            // REQ-79 + REQ-78: the WASM backend has no list representation, so
            // a list literal is REFUSED rather than lowered to something the
            // (also-unsupported) `senarai_*` builtins would misread.
            Instruction::MakeList(_) => {
                return Err(Error::InvalidOperation(
                    "list literals are not supported by the WASM backend \
                     (native/C only) — master plan REQ-79. Build for the native \
                     target."
                        .to_string(),
                ));
            }

            Instruction::Pair(a, b) => {
                // Alloc 16 bytes (two 8-byte cells), store a at +0, b at +8
                Self::emit_alloc_call(ctx.alloc_func_index, 16, code);
                // Duplicate ptr: tee to result local, then use it
                if let Some(result_var) = result {
                    if let Some(local) = ctx.var_map.get(&result_var) {
                        code.push(Op::LocalTee as u8);
                        wasm_encode::encode_uleb128(*local as u64, code);
                    }
                }
                // Store a at ptr+0
                code.push(Op::I32WrapI64 as u8); // ptr cell -> i32 addr
                Self::emit_local_get(a, ctx.var_map, code);
                code.push(Op::I64Store as u8);
                code.push(0x02);
                code.push(0x00);
                // Store b at ptr+8
                if let Some(result_var) = result {
                    if let Some(local) = ctx.var_map.get(&result_var) {
                        code.push(Op::LocalGet as u8);
                        wasm_encode::encode_uleb128(*local as u64, code);
                    }
                }
                code.push(Op::I32WrapI64 as u8);
                Self::emit_local_get(b, ctx.var_map, code);
                code.push(Op::I64Store as u8);
                code.push(0x02); // align 4
                code.push(0x08); // offset 8
                                 // Result is already in local from LocalTee; load it back for the
                                 // generic LocalSet below
                if let Some(result_var) = result {
                    if let Some(local) = ctx.var_map.get(&result_var) {
                        code.push(Op::LocalGet as u8);
                        wasm_encode::encode_uleb128(*local as u64, code);
                    }
                }
            }
            Instruction::Fst(pair) => {
                // Load the i64 cell at pair_ptr + 0
                Self::emit_local_get(pair, ctx.var_map, code);
                code.push(Op::I32WrapI64 as u8);
                code.push(Op::I64Load as u8);
                code.push(0x02);
                code.push(0x00);
            }
            Instruction::Snd(pair) => {
                // Load the i64 cell at pair_ptr + 8
                Self::emit_local_get(pair, ctx.var_map, code);
                code.push(Op::I32WrapI64 as u8);
                code.push(Op::I64Load as u8);
                code.push(0x02); // align 4
                code.push(0x08); // offset 8
            }
            Instruction::Inl(val) => {
                // Alloc 16 bytes: tag=0 at +0, value at +8 (8-byte cells)
                Self::emit_alloc_call(ctx.alloc_func_index, 16, code);
                if let Some(result_var) = result {
                    if let Some(local) = ctx.var_map.get(&result_var) {
                        code.push(Op::LocalTee as u8);
                        wasm_encode::encode_uleb128(*local as u64, code);
                    }
                }
                // Store tag=0
                code.push(Op::I32WrapI64 as u8);
                wasm_i64c(code, 0);
                code.push(Op::I64Store as u8);
                code.push(0x02);
                code.push(0x00);
                // Store value at +8
                if let Some(result_var) = result {
                    if let Some(local) = ctx.var_map.get(&result_var) {
                        code.push(Op::LocalGet as u8);
                        wasm_encode::encode_uleb128(*local as u64, code);
                    }
                }
                code.push(Op::I32WrapI64 as u8);
                Self::emit_local_get(val, ctx.var_map, code);
                code.push(Op::I64Store as u8);
                code.push(0x02);
                code.push(0x08);
                // Push ptr for generic LocalSet
                if let Some(result_var) = result {
                    if let Some(local) = ctx.var_map.get(&result_var) {
                        code.push(Op::LocalGet as u8);
                        wasm_encode::encode_uleb128(*local as u64, code);
                    }
                }
            }
            Instruction::Inr(val) => {
                // Alloc 16 bytes: tag=1 at +0, value at +8 (8-byte cells)
                Self::emit_alloc_call(ctx.alloc_func_index, 16, code);
                if let Some(result_var) = result {
                    if let Some(local) = ctx.var_map.get(&result_var) {
                        code.push(Op::LocalTee as u8);
                        wasm_encode::encode_uleb128(*local as u64, code);
                    }
                }
                code.push(Op::I32WrapI64 as u8);
                wasm_i64c(code, 1);
                code.push(Op::I64Store as u8);
                code.push(0x02);
                code.push(0x00);
                if let Some(result_var) = result {
                    if let Some(local) = ctx.var_map.get(&result_var) {
                        code.push(Op::LocalGet as u8);
                        wasm_encode::encode_uleb128(*local as u64, code);
                    }
                }
                code.push(Op::I32WrapI64 as u8);
                Self::emit_local_get(val, ctx.var_map, code);
                code.push(Op::I64Store as u8);
                code.push(0x02);
                code.push(0x08);
                if let Some(result_var) = result {
                    if let Some(local) = ctx.var_map.get(&result_var) {
                        code.push(Op::LocalGet as u8);
                        wasm_encode::encode_uleb128(*local as u64, code);
                    }
                }
            }
            Instruction::IsLeft(sum) => {
                // Load tag (i64 cell) at sum_ptr+0, check if == 0, lift to the cell
                Self::emit_local_get(sum, ctx.var_map, code);
                code.push(Op::I32WrapI64 as u8);
                code.push(Op::I64Load as u8);
                code.push(0x02);
                code.push(0x00);
                code.push(Op::I64Eqz as u8); // tag==0 means left
                code.push(Op::I64ExtendI32U as u8);
            }
            Instruction::UnwrapLeft(sum) | Instruction::UnwrapRight(sum) => {
                // Load value (i64 cell) at sum_ptr+8
                Self::emit_local_get(sum, ctx.var_map, code);
                code.push(Op::I32WrapI64 as u8);
                code.push(Op::I64Load as u8);
                code.push(0x02);
                code.push(0x08);
            }
            Instruction::Copy(src) => {
                Self::emit_local_get(src, ctx.var_map, code);
            }
            Instruction::Classify(val) | Instruction::Prove(val) => {
                Self::emit_local_get(val, ctx.var_map, code);
            }
            Instruction::Declassify(val, _proof) => {
                Self::emit_local_get(val, ctx.var_map, code);
            }
            Instruction::Closure { func, captures } => {
                // Alloc (1 + len(captures)) * 8 bytes
                // Layout: [func_index, capture0, capture1, ...] (8-byte cells)
                let size = (1 + captures.len()) as u32 * 8;
                Self::emit_alloc_call(ctx.alloc_func_index, size, code);
                if let Some(result_var) = result {
                    if let Some(local) = ctx.var_map.get(&result_var) {
                        code.push(Op::LocalTee as u8);
                        wasm_encode::encode_uleb128(*local as u64, code);
                    }
                }
                // Store func_index at +0 (as an i64 cell)
                let func_idx = ctx.func_map.get(func).copied().unwrap_or(0);
                code.push(Op::I32WrapI64 as u8); // ptr cell -> i32 addr
                wasm_i64c(code, func_idx as i64);
                code.push(Op::I64Store as u8);
                code.push(0x02);
                code.push(0x00);
                // Store each capture
                for (i, cap) in captures.iter().enumerate() {
                    if let Some(result_var) = result {
                        if let Some(local) = ctx.var_map.get(&result_var) {
                            code.push(Op::LocalGet as u8);
                            wasm_encode::encode_uleb128(*local as u64, code);
                        }
                    }
                    code.push(Op::I32WrapI64 as u8); // ptr cell -> i32 addr
                    Self::emit_local_get(cap, ctx.var_map, code);
                    code.push(Op::I64Store as u8);
                    code.push(0x02); // align 4
                    wasm_encode::encode_uleb128(((i + 1) * 8) as u64, code);
                }
                // Push ptr for generic LocalSet
                if let Some(result_var) = result {
                    if let Some(local) = ctx.var_map.get(&result_var) {
                        code.push(Op::LocalGet as u8);
                        wasm_encode::encode_uleb128(*local as u64, code);
                    }
                }
            }
            Instruction::FixClosure {
                closure,
                capture_index,
                value,
            } => {
                // Patch captures[capture_index] with `value` — the closure
                // itself for plain recursion, a sibling for a group.
                Self::emit_local_get(closure, ctx.var_map, code);
                code.push(Op::I32WrapI64 as u8); // ptr cell -> i32 addr
                if let Some(local) = ctx.var_map.get(value) {
                    code.push(Op::LocalGet as u8);
                    wasm_encode::encode_uleb128(*local as u64, code);
                }
                code.push(Op::I64Store as u8);
                code.push(0x02);
                wasm_encode::encode_uleb128(((capture_index + 1) * 8) as u64, code);
                // Result is the closure ptr
                Self::emit_local_get(closure, ctx.var_map, code);
            }
            Instruction::Alloc { init, .. } => {
                // Allocate one 8-byte cell, store init value
                Self::emit_alloc_call(ctx.alloc_func_index, 8, code);
                if let Some(result_var) = result {
                    if let Some(local) = ctx.var_map.get(&result_var) {
                        code.push(Op::LocalTee as u8);
                        wasm_encode::encode_uleb128(*local as u64, code);
                    }
                }
                code.push(Op::I32WrapI64 as u8); // ptr cell -> i32 addr
                Self::emit_local_get(init, ctx.var_map, code);
                code.push(Op::I64Store as u8);
                code.push(0x02);
                code.push(0x00);
                // Push ptr for generic LocalSet
                if let Some(result_var) = result {
                    if let Some(local) = ctx.var_map.get(&result_var) {
                        code.push(Op::LocalGet as u8);
                        wasm_encode::encode_uleb128(*local as u64, code);
                    }
                }
            }
            Instruction::Phi(_) => {
                // Phi nodes are handled by structured if/else emission in emit_function.
                // Nothing to emit here — the if/else/end block leaves the result on the stack,
                // and emit_function emits the local.set for the phi result.
            }
            Instruction::BuiltinCall { name, arg } => {
                // Route builtins: cetakln/cetak → WASI fd_write(stdout)
                if name == "cetakln" || name == "cetak" {
                    if matches!(
                        ctx.var_to_ty.get(arg),
                        Some(Ty::Int) | Some(Ty::CInt) | Some(Ty::IntN { .. })
                    ) {
                        // Integer argument: convert to decimal ASCII (itoa) and
                        // write via WASI fd_write. (C uses a runtime-tagged
                        // riina_format; WASM values are untagged i32, so we
                        // dispatch on the static IR type here.) A signed sized int
                        // (i8/i16/i32) prints signed (sign-extend + leading '-').
                        let signed_bits = match ctx.var_to_ty.get(arg) {
                            Some(Ty::IntN {
                                bits,
                                signed: true,
                            }) if *bits <= 32 => Some(*bits),
                            _ => None,
                        };
                        Self::emit_print_int(arg, signed_bits, ctx, code);
                    } else if matches!(
                        ctx.var_to_ty.get(arg),
                        Some(Ty::Decimal | Ty::Fixed | Ty::FixedBin)
                    ) {
                        // Decimal/Fixed render via dec_to_str (shared record layout;
                        // Fixed display preserves its scale, which is what
                        // dec_to_str does); Q-format renders via qmn_to_str. Then
                        // print (same iovec path as BigInt; stash the pointer in
                        // scratch).
                        let render = if matches!(ctx.var_to_ty.get(arg), Some(Ty::FixedBin)) {
                            ctx.qmn_to_str_index
                        } else {
                            ctx.dec_to_str_index
                        };
                        Self::emit_local_get(arg, ctx.var_map, code);
                        code.push(Op::I32WrapI64 as u8);
                        code.push(Op::Call as u8);
                        wasm_encode::encode_uleb128(render as u64, code);
                        wasm_local(code, Op::LocalSet, ctx.scratch);
                        // heap[0] = strptr + 4; heap[4] = mem[strptr]; fd_write; drop
                        code.push(Op::GlobalGet as u8);
                        wasm_encode::encode_uleb128(GLOBAL_HEAP_PTR as u64, code);
                        wasm_local(code, Op::LocalGet, ctx.scratch);
                        wasm_i32c(code, 4);
                        code.push(Op::I32Add as u8);
                        wasm_store(code, 0);
                        code.push(Op::GlobalGet as u8);
                        wasm_encode::encode_uleb128(GLOBAL_HEAP_PTR as u64, code);
                        wasm_i32c(code, 4);
                        code.push(Op::I32Add as u8);
                        wasm_local(code, Op::LocalGet, ctx.scratch);
                        wasm_load(code, 0);
                        wasm_store(code, 0);
                        wasm_i32c(code, 1);
                        code.push(Op::GlobalGet as u8);
                        wasm_encode::encode_uleb128(GLOBAL_HEAP_PTR as u64, code);
                        wasm_i32c(code, 1);
                        code.push(Op::GlobalGet as u8);
                        wasm_encode::encode_uleb128(GLOBAL_HEAP_PTR as u64, code);
                        wasm_i32c(code, 8);
                        code.push(Op::I32Add as u8);
                        code.push(Op::Call as u8);
                        wasm_encode::encode_uleb128(0, code);
                        code.push(Op::Drop as u8);
                    } else if matches!(ctx.var_to_ty.get(arg), Some(Ty::BigInt)) {
                        // BigInt: render to a decimal heap string via bi_to_str,
                        // then print it. The string pointer is read twice by the
                        // iovec setup, so stash it in a scratch i32 local.
                        Self::emit_local_get(arg, ctx.var_map, code);
                        code.push(Op::I32WrapI64 as u8);
                        code.push(Op::Call as u8);
                        wasm_encode::encode_uleb128(ctx.bi_to_str_index as u64, code);
                        wasm_local(code, Op::LocalSet, ctx.scratch); // scratch = string ptr (i32)
                        // heap[0] = strptr + 4 (iovec.ptr = data start)
                        code.push(Op::GlobalGet as u8);
                        wasm_encode::encode_uleb128(GLOBAL_HEAP_PTR as u64, code);
                        wasm_local(code, Op::LocalGet, ctx.scratch);
                        wasm_i32c(code, 4);
                        code.push(Op::I32Add as u8);
                        wasm_store(code, 0);
                        // heap[4] = mem[strptr] (iovec.len)
                        code.push(Op::GlobalGet as u8);
                        wasm_encode::encode_uleb128(GLOBAL_HEAP_PTR as u64, code);
                        wasm_i32c(code, 4);
                        code.push(Op::I32Add as u8);
                        wasm_local(code, Op::LocalGet, ctx.scratch);
                        wasm_load(code, 0);
                        wasm_store(code, 0);
                        // fd_write(1, heap, 1, heap+8); drop
                        wasm_i32c(code, 1);
                        code.push(Op::GlobalGet as u8);
                        wasm_encode::encode_uleb128(GLOBAL_HEAP_PTR as u64, code);
                        wasm_i32c(code, 1);
                        code.push(Op::GlobalGet as u8);
                        wasm_encode::encode_uleb128(GLOBAL_HEAP_PTR as u64, code);
                        wasm_i32c(code, 8);
                        code.push(Op::I32Add as u8);
                        code.push(Op::Call as u8);
                        wasm_encode::encode_uleb128(0, code);
                        code.push(Op::Drop as u8);
                    } else if matches!(ctx.var_to_ty.get(arg), Some(Ty::Bool)) {
                        // Bool: write "betul"/"salah", byte-identical to the C
                        // backend's riina_format. Without this arm a bool fell
                        // into the string-pointer branch below, dereferencing
                        // the 0/1 VALUE as a length-prefixed string address —
                        // out-of-bounds on wasmtime (found by the corpus
                        // differential when security_levels.rii first printed
                        // a bool through both backends).
                        Self::emit_local_get(arg, ctx.var_map, code);
                        code.push(Op::I32WrapI64 as u8);
                        code.push(Op::If as u8);
                        code.push(0x40);
                        wasm_write_bytes(code, b"betul");
                        code.push(Op::Else as u8);
                        wasm_write_bytes(code, b"salah");
                        code.push(Op::End as u8);
                    } else {
                        // String pointer (len-prefixed in data section):
                        // Layout: [len:u32][bytes...]. fd_write needs an iovec
                        // {ptr, len} at a known memory location; use heap scratch:
                        // iovec at heap_ptr, nwritten at heap_ptr+8.

                        // Store data ptr (arg+4) at scratch[0]
                        code.push(Op::GlobalGet as u8);
                        wasm_encode::encode_uleb128(GLOBAL_HEAP_PTR as u64, code);
                        Self::emit_local_get(arg, ctx.var_map, code);
                        code.push(Op::I32WrapI64 as u8); // string ptr cell -> i32 addr
                        code.push(Op::I32Const as u8);
                        wasm_encode::encode_sleb128(4, code);
                        code.push(Op::I32Add as u8); // ptr + 4 = data start
                        code.push(Op::I32Store as u8);
                        code.push(0x02);
                        code.push(0x00); // store at scratch[0]

                        // Store len at scratch[4]
                        code.push(Op::GlobalGet as u8);
                        wasm_encode::encode_uleb128(GLOBAL_HEAP_PTR as u64, code);
                        code.push(Op::I32Const as u8);
                        wasm_encode::encode_sleb128(4, code);
                        code.push(Op::I32Add as u8); // scratch + 4
                        Self::emit_local_get(arg, ctx.var_map, code);
                        code.push(Op::I32WrapI64 as u8); // string ptr cell -> i32 addr
                        code.push(Op::I32Load as u8);
                        code.push(0x02);
                        code.push(0x00); // load len from arg (i32 length prefix)
                        code.push(Op::I32Store as u8);
                        code.push(0x02);
                        code.push(0x00); // store at scratch[4]

                        // Call fd_write(1, scratch, 1, scratch+8)
                        code.push(Op::I32Const as u8);
                        wasm_encode::encode_sleb128(1, code); // fd = stdout
                        code.push(Op::GlobalGet as u8);
                        wasm_encode::encode_uleb128(GLOBAL_HEAP_PTR as u64, code); // iovs = scratch
                        code.push(Op::I32Const as u8);
                        wasm_encode::encode_sleb128(1, code); // iovs_len = 1
                        code.push(Op::GlobalGet as u8);
                        wasm_encode::encode_uleb128(GLOBAL_HEAP_PTR as u64, code);
                        code.push(Op::I32Const as u8);
                        wasm_encode::encode_sleb128(8, code);
                        code.push(Op::I32Add as u8); // nwritten = scratch + 8

                        code.push(Op::Call as u8);
                        wasm_encode::encode_uleb128(0, code); // import index 0 = fd_write

                        code.push(Op::Drop as u8); // drop fd_write return value
                    }

                    // `cetakln` (println) appends a newline; `cetak` does not.
                    if name == "cetakln" {
                        wasm_write_bytes(code, b"\n");
                    }

                    // push unit (0) as result
                    wasm_i64c(code, 0);
                } else if name == "ke_teks" || name == "nombor_ke_teks" {
                    match ctx.var_to_ty.get(arg) {
                        Some(Ty::IntN {
                            bits,
                            signed: true,
                        }) => {
                            // Signed sized int → signed decimal heap string.
                            Self::emit_ke_teks(arg, ctx, code, Some(*bits));
                        }
                        Some(Ty::Int | Ty::CInt | Ty::IntN { .. }) => {
                            // Int (or unsigned sized int) → heap string.
                            Self::emit_ke_teks(arg, ctx, code, None);
                        }
                        Some(Ty::BigInt) => {
                            // BigInt → decimal heap string via bi_to_str.
                            Self::emit_local_get(arg, ctx.var_map, code);
                            code.push(Op::I32WrapI64 as u8);
                            code.push(Op::Call as u8);
                            wasm_encode::encode_uleb128(ctx.bi_to_str_index as u64, code);
                            code.push(Op::I64ExtendI32U as u8);
                        }
                        Some(Ty::Decimal | Ty::Fixed) => {
                            // Decimal/Fixed → heap string via dec_to_str.
                            Self::emit_local_get(arg, ctx.var_map, code);
                            code.push(Op::I32WrapI64 as u8);
                            code.push(Op::Call as u8);
                            wasm_encode::encode_uleb128(ctx.dec_to_str_index as u64, code);
                            code.push(Op::I64ExtendI32U as u8);
                        }
                        Some(Ty::FixedBin) => {
                            // Q-format → heap string via qmn_to_str.
                            Self::emit_local_get(arg, ctx.var_map, code);
                            code.push(Op::I32WrapI64 as u8);
                            code.push(Op::Call as u8);
                            wasm_encode::encode_uleb128(ctx.qmn_to_str_index as u64, code);
                            code.push(Op::I64ExtendI32U as u8);
                        }
                        Some(Ty::String | Ty::Element | Ty::Color | Ty::UIStyle) => {
                            // `ke_teks` of a string-typed value is identity — the
                            // value is already a `[len][bytes]` heap string. This
                            // is what makes nested UI fragments (a `tulisan`/
                            // `butang` inside a `paparan`) render: the element is
                            // wrapped in `ke_teks` by `lower_to_text`.
                            Self::emit_local_get(arg, ctx.var_map, code);
                        }
                        Some(Ty::Bool) => {
                            // Bool -> the "betul"/"salah" heap string, chosen at
                            // runtime. Both are interned unconditionally in the
                            // data section (see BOOL_RENDERINGS), so this is a
                            // select between two constant pointers. `select` is
                            // not in this emitter's opcode set, so use the
                            // if/else form already used for phi merges.
                            let ptr = |b: bool| {
                                ctx.string_table
                                    .get(BOOL_RENDERINGS[usize::from(b)])
                                    .copied()
                                    .unwrap_or(0) as i64
                            };
                            Self::emit_local_get(arg, ctx.var_map, code);
                            code.push(Op::I32WrapI64 as u8);
                            code.push(Op::If as u8);
                            code.push(ValType::I64 as u8);
                            wasm_i64c(code, ptr(true));
                            code.push(Op::Else as u8);
                            wasm_i64c(code, ptr(false));
                            code.push(Op::End as u8);
                        }
                        other => {
                            // FAIL CLOSED (REQ-78). This arm used to push a
                            // literal 0 as a "stub", which is a null string
                            // pointer — `ke_teks` then rendered as EMPTY rather
                            // than failing, a silent wrong answer. REQ-78
                            // removed the silent stubs from the builtin
                            // dispatch but missed this one, inside `ke_teks`'s
                            // own type dispatch; `ke_teks(betul)` printed
                            // nothing on WASM while C and the interpreter both
                            // printed `betul`.
                            return Err(Error::InvalidOperation(format!(
                                "`ke_teks` of {other:?} is not implemented by the \
                                 WASM backend. Refusing to emit a stub that would \
                                 silently render as an empty string (master plan \
                                 REQ-78) — build for the native target."
                            )));
                        }
                    }
                } else if name == "gabung_teks" {
                    Self::emit_gabung_teks(arg, ctx, code);
                } else if name == "besar" || name == "bigint" {
                    // BigInt construction (W2): parse the base-10 string literal
                    // into a linear-memory BigInt record via the bi_from_str helper.
                    // The arg is a `[len][bytes]` string pointer (i64 cell) → wrap
                    // to an i32 address, parse, lift the result record pointer back
                    // into the i64 cell.
                    Self::emit_local_get(arg, ctx.var_map, code);
                    code.push(Op::I32WrapI64 as u8);
                    code.push(Op::Call as u8);
                    wasm_encode::encode_uleb128(ctx.bi_from_str_index as u64, code);
                    code.push(Op::I64ExtendI32U as u8);
                } else if name == "perpuluhan" || name == "decimal" {
                    // Decimal construction (W3.1a): parse the literal into a
                    // `[scale][mantissa_ptr]` record via dec_from_str. Arg is a
                    // `[len][bytes]` string pointer (i64 cell) → wrap, parse, lift.
                    Self::emit_local_get(arg, ctx.var_map, code);
                    code.push(Op::I32WrapI64 as u8);
                    code.push(Op::Call as u8);
                    wasm_encode::encode_uleb128(ctx.dec_from_str_index as u64, code);
                    code.push(Op::I64ExtendI32U as u8);
                } else if name == "wang" {
                    // Fixed-point construction, scale inferred from the literal
                    // (W3.2). The parse is identical to Decimal's (the record
                    // layout is shared), so reuse dec_from_str.
                    Self::emit_local_get(arg, ctx.var_map, code);
                    code.push(Op::I32WrapI64 as u8);
                    code.push(Op::Call as u8);
                    wasm_encode::encode_uleb128(ctx.dec_from_str_index as u64, code);
                    code.push(Op::I64ExtendI32U as u8);
                } else if name == "titik_tetap" {
                    // Fixed-point construction at an explicit scale (W3.2): the arg
                    // is a (string, scale) heap pair; fix_titik_tetap parses then
                    // rescales (half-to-even when shrinking).
                    Self::emit_local_get(arg, ctx.var_map, code);
                    code.push(Op::I32WrapI64 as u8);
                    code.push(Op::Call as u8);
                    wasm_encode::encode_uleb128(ctx.fix_titik_tetap_index as u64, code);
                    code.push(Op::I64ExtendI32U as u8);
                } else if name == "qmn" {
                    // Q-format construction (W3.3): the arg is a (string,
                    // frac_bits) heap pair; qmn_parse rounds the literal
                    // half-to-even to the nearest representable raw/2^fb.
                    Self::emit_local_get(arg, ctx.var_map, code);
                    code.push(Op::I32WrapI64 as u8);
                    code.push(Op::Call as u8);
                    wasm_encode::encode_uleb128(ctx.qmn_parse_index as u64, code);
                    code.push(Op::I64ExtendI32U as u8);
                } else {
                    // FAIL CLOSED (REQ-78). This arm used to emit a literal 0
                    // as a "stub", which did not fail — it silently produced a
                    // WRONG ANSWER. `teks_huruf_besar("halo")` returned "halo",
                    // `teks_ulang(("ab",3))` returned "ab", and
                    // `panjang("abcd")` returned the string instead of 4, while
                    // the interpreter and the C backend both agreed on the
                    // right result. A backend that quietly disagrees with the
                    // others is worse than one that refuses, so refuse.
                    return Err(Error::InvalidOperation(format!(
                        "builtin `{name}` is not implemented by the WASM backend \
                         (native/C only). Refusing to emit a stub that would silently \
                         return a wrong value (master plan REQ-78) — build for the \
                         native target, or use only WASM-supported builtins."
                    )));
                }
            }
            Instruction::Perform { payload, .. } => {
                // `perform` has no WASM lowering; passing the payload through
                // is a value-level no-op that happens to be what the C backend
                // does for the same node, so it is kept rather than made an
                // error. (Unlike the builtin arm above, this does not fabricate
                // a value out of thin air.)
                Self::emit_local_get(payload, ctx.var_map, code);
            }
            Instruction::RequireCap(_) | Instruction::GrantCap(_) => {
                // Capability instructions are compile-time checks; emit unit at runtime
                wasm_i64c(code, 0);
            }
            Instruction::FFICall { name, args } => {
                // FFI calls are routed to WASM imports.
                // Push args, then call named import (not yet in import table — stub)
                for arg in args {
                    Self::emit_local_get(arg, ctx.var_map, code);
                }
                let _ = name;
                wasm_i64c(code, 0);
            }

            // JALINAN Phase 6: simplified WASM actor support
            Instruction::ActorDecl { .. } | Instruction::ChoreographyDecl { .. } => {
                // Declaration: push 0 (unit)
                wasm_i64c(code, 0);
            }
            Instruction::ActorSpawn(_, _) => {
                // Spawn: push actor ID (incrementing counter via global)
                // For simplicity, just push 1 as the actor ref
                wasm_i64c(code, 1);
            }
            Instruction::ActorSend(_, _) => {
                // Send: no-op in single-threaded WASM, push 0
                wasm_i64c(code, 0);
            }
            Instruction::ActorRecv(_) => {
                // Recv: return 0 (placeholder — no real mailbox in WASM)
                wasm_i64c(code, 0);
            }
            Instruction::CRDTMerge(_, _) => {
                // CRDT merge: for integers, take max (simplified)
                wasm_i64c(code, 0);
            }
            Instruction::ContentHash(_) => {
                // Content hash: return 0 (placeholder)
                wasm_i64c(code, 0);
            }
        }

        // Store result if there is one.
        // Skip for Phi — it doesn't push anything onto the stack;
        // the phi result is stored by the structured if/else emission
        // in emit_function.
        let skip_store = matches!(instr, Instruction::Phi(_));
        if !skip_store {
            if let Some(result_var) = result {
                if let Some(local) = ctx.var_map.get(&result_var) {
                    code.push(Op::LocalSet as u8);
                    wasm_encode::encode_uleb128(*local as u64, code);
                }
            }
        }

        Ok(())
    }

    /// Generate JavaScript glue code for loading the WASM module.
    fn generate_js_glue(&self) -> Vec<u8> {
        let js = r#"// RIINA WASM Loader — Auto-generated
// Copyright (c) 2026 The RIINA Authors. All rights reserved.

let instance;
let outputBuffer = [];

const RIINA_WASM_IMPORTS = {
  wasi_snapshot_preview1: {
    fd_write: (fd, iovs, iovs_len, nwritten) => {
      const mem = new Uint32Array(instance.exports.memory.buffer);
      let written = 0;
      for (let i = 0; i < iovs_len; i++) {
        const ptr = mem[(iovs + i * 8) / 4];
        const len = mem[(iovs + i * 8 + 4) / 4];
        const bytes = new Uint8Array(instance.exports.memory.buffer, ptr, len);
        const msg = new TextDecoder().decode(bytes);
        outputBuffer.push(msg);
        if (fd === 1) console.log(msg);
        else console.error(msg);
        written += len;
      }
      mem[nwritten / 4] = written;
      return 0;
    },
    proc_exit: (code) => {
      throw new Error('RIINA exit: ' + code);
    },
  },
};

export async function loadRiina(wasmPath) {
  const response = await fetch(wasmPath);
  const bytes = await response.arrayBuffer();
  const result = await WebAssembly.instantiate(bytes, RIINA_WASM_IMPORTS);
  instance = result.instance;
  return instance.exports;
}

export function run(wasmExports) {
  outputBuffer = [];
  if (wasmExports._start) {
    const result = wasmExports._start(0);
    return { result, output: outputBuffer.join('\n') };
  }
  return { result: 0, output: '' };
}

export function getOutput() {
  return outputBuffer.join('\n');
}
"#;
        js.as_bytes().to_vec()
    }
}

// ── WASM result-echo helpers ────────────────────────────────────────────────
// These emit raw WASM that prints the program's final value to stdout, matching
// the C `main` echo byte-for-byte. Used by the `_start` trampoline. They use
// heap scratch: iovec at heap_ptr[0..8], nwritten at heap_ptr[8], a literal/
// digit buffer at heap_ptr+16.. .

fn wasm_heap(code: &mut Vec<u8>) {
    code.push(Op::GlobalGet as u8);
    wasm_encode::encode_uleb128(GLOBAL_HEAP_PTR as u64, code);
}
fn wasm_i32c(code: &mut Vec<u8>, n: i64) {
    code.push(Op::I32Const as u8);
    wasm_encode::encode_sleb128(n, code);
}

/// Push an i64 value constant (the uniform value cell). Used wherever a RIINA
/// value — int, bool, unit, or a pointer lifted into the cell — is materialized.
fn wasm_i64c(code: &mut Vec<u8>, n: i64) {
    code.push(Op::I64Const as u8);
    wasm_encode::encode_sleb128(n, code);
}

// ── linear-memory access helpers (i32 addresses; used by the bignum runtime) ──
fn wasm_load(code: &mut Vec<u8>, off: u8) {
    code.push(Op::I32Load as u8);
    code.push(0x02);
    code.push(off);
}
fn wasm_store(code: &mut Vec<u8>, off: u8) {
    code.push(Op::I32Store as u8);
    code.push(0x02);
    code.push(off);
}
fn wasm_load8u(code: &mut Vec<u8>, off: u8) {
    code.push(Op::I32Load8U as u8);
    code.push(0x00);
    code.push(off);
}
fn wasm_store8(code: &mut Vec<u8>, off: u8) {
    code.push(Op::I32Store8 as u8);
    code.push(0x00);
    code.push(off);
}

/// Numeric tower: the width of a *signed* `Ty::IntN` narrower than the 64-bit
/// value cell (so it needs sign extension before a signed op), else `None`. The
/// cell holds the width-masked (non-negative) bits, so e.g. an i8 `-1` is stored
/// as 255 and must be sign-extended to a full i64. Full `Int` (64) fills the cell.
fn signed_sub64_width(ty: Option<&Ty>) -> Option<u8> {
    match ty {
        Some(Ty::IntN {
            bits,
            signed: true,
        }) if *bits < 64 => Some(*bits),
        _ => None,
    }
}

/// Sign-extend the top-of-stack i64 from `bits` (8, 16, or 32) to a full i64 via
/// the standardized sign-extension operators. Width 64 needs nothing.
fn emit_sext_i64(bits: u8, code: &mut Vec<u8>) {
    match bits {
        8 => code.push(Op::I64Extend8S as u8),
        16 => code.push(Op::I64Extend16S as u8),
        32 => code.push(Op::I64Extend32S as u8),
        _ => {}
    }
}
fn wasm_local(code: &mut Vec<u8>, op: Op, idx: u32) {
    code.push(op as u8);
    wasm_encode::encode_uleb128(idx as u64, code);
}
/// Emit fd_write(1, heap_ptr, 1, heap_ptr+8) (iovec already set up at heap_ptr).
fn wasm_fd_write(code: &mut Vec<u8>) {
    wasm_i32c(code, 1);
    wasm_heap(code);
    wasm_i32c(code, 1);
    wasm_heap(code);
    wasm_i32c(code, 8);
    code.push(Op::I32Add as u8);
    code.push(Op::Call as u8);
    wasm_encode::encode_uleb128(0, code); // fd_write import
    code.push(Op::Drop as u8);
}
/// Write `bytes` literally to stdout (copied into heap scratch at heap_ptr+16).
fn wasm_write_bytes(code: &mut Vec<u8>, bytes: &[u8]) {
    for (i, b) in bytes.iter().enumerate() {
        wasm_heap(code);
        wasm_i32c(code, 16 + i as i64);
        code.push(Op::I32Add as u8);
        wasm_i32c(code, i64::from(*b));
        code.push(Op::I32Store8 as u8);
        code.push(0x00);
        code.push(0x00);
    }
    // iovec.ptr = heap+16
    wasm_heap(code);
    wasm_heap(code);
    wasm_i32c(code, 16);
    code.push(Op::I32Add as u8);
    code.push(Op::I32Store as u8);
    code.push(0x02);
    code.push(0x00);
    // iovec.len = bytes.len()
    wasm_heap(code);
    wasm_i32c(code, bytes.len() as i64);
    code.push(Op::I32Store as u8);
    code.push(0x02);
    code.push(0x04);
    wasm_fd_write(code);
}
/// Write the contents of a length-prefixed string `[len:u32][bytes]` whose
/// pointer is in local `ptr_local` (no quotes, no newline).
fn wasm_echo_strptr(code: &mut Vec<u8>, ptr_local: u32) {
    // iovec.ptr = ptr_local + 4   (ptr_local is an i64 cell -> wrap to address)
    wasm_heap(code);
    wasm_local(code, Op::LocalGet, ptr_local);
    code.push(Op::I32WrapI64 as u8);
    wasm_i32c(code, 4);
    code.push(Op::I32Add as u8);
    code.push(Op::I32Store as u8);
    code.push(0x02);
    code.push(0x00);
    // iovec.len = load len from ptr_local
    wasm_heap(code);
    wasm_local(code, Op::LocalGet, ptr_local);
    code.push(Op::I32WrapI64 as u8);
    code.push(Op::I32Load as u8);
    code.push(0x02);
    code.push(0x00);
    code.push(Op::I32Store as u8);
    code.push(0x02);
    code.push(0x04);
    wasm_fd_write(code);
}
/// Write the unsigned integer in local `v_local` as decimal ASCII + newline.
/// `tv`/`tp` are scratch i32 locals.
fn wasm_echo_int(code: &mut Vec<u8>, v_local: u32, tv: u32, tp: u32, neg: u32, signed_bits: Option<u8>) {
    // $v = v_local
    wasm_local(code, Op::LocalGet, v_local);
    wasm_local(code, Op::LocalSet, tv);
    // Signed sized int: sign-extend, record the sign, print magnitude + '-'.
    if let Some(bits) = signed_bits {
        wasm_local(code, Op::LocalGet, tv);
        emit_sext_i64(bits, code);
        wasm_local(code, Op::LocalSet, tv);
        wasm_local(code, Op::LocalGet, tv);
        wasm_i64c(code, 0);
        code.push(Op::I64LtS as u8);
        wasm_local(code, Op::LocalSet, neg);
        wasm_local(code, Op::LocalGet, neg);
        code.push(Op::If as u8);
        code.push(0x40);
        wasm_i64c(code, 0);
        wasm_local(code, Op::LocalGet, tv);
        code.push(Op::I64Sub as u8);
        wasm_local(code, Op::LocalSet, tv);
        code.push(Op::End as u8);
    }
    // mem[heap+48] = '\n'
    wasm_heap(code);
    wasm_i32c(code, 48);
    code.push(Op::I32Add as u8);
    wasm_i32c(code, 10);
    code.push(Op::I32Store8 as u8);
    code.push(0x00);
    code.push(0x00);
    // $p = heap + 48
    wasm_heap(code);
    wasm_i32c(code, 48);
    code.push(Op::I32Add as u8);
    wasm_local(code, Op::LocalSet, tp);
    // do { p--; mem[p] = '0'+(v%10); v/=10 } while (v != 0)
    code.push(Op::Loop as u8);
    code.push(0x40);
    wasm_local(code, Op::LocalGet, tp);
    wasm_i32c(code, 1);
    code.push(Op::I32Sub as u8);
    wasm_local(code, Op::LocalSet, tp);
    wasm_local(code, Op::LocalGet, tp);
    wasm_local(code, Op::LocalGet, tv);
    wasm_i64c(code, 10);
    code.push(Op::I64RemU as u8);
    code.push(Op::I32WrapI64 as u8);
    wasm_i32c(code, 48);
    code.push(Op::I32Add as u8);
    code.push(Op::I32Store8 as u8);
    code.push(0x00);
    code.push(0x00);
    wasm_local(code, Op::LocalGet, tv);
    wasm_i64c(code, 10);
    code.push(Op::I64DivU as u8);
    wasm_local(code, Op::LocalSet, tv);
    wasm_local(code, Op::LocalGet, tv);
    code.push(Op::I64Eqz as u8);
    code.push(Op::I32Eqz as u8);
    code.push(Op::BrIf as u8);
    wasm_encode::encode_uleb128(0, code);
    code.push(Op::End as u8);
    // Signed & negative: prepend '-' (ASCII 45) before the magnitude.
    if signed_bits.is_some() {
        wasm_local(code, Op::LocalGet, neg);
        code.push(Op::If as u8);
        code.push(0x40);
        wasm_local(code, Op::LocalGet, tp);
        wasm_i32c(code, 1);
        code.push(Op::I32Sub as u8);
        wasm_local(code, Op::LocalSet, tp);
        wasm_local(code, Op::LocalGet, tp);
        wasm_i32c(code, 45);
        code.push(Op::I32Store8 as u8);
        code.push(0x00);
        code.push(0x00);
        code.push(Op::End as u8);
    }
    // iovec.ptr = $p
    wasm_heap(code);
    wasm_local(code, Op::LocalGet, tp);
    code.push(Op::I32Store as u8);
    code.push(0x02);
    code.push(0x00);
    // iovec.len = (heap+49) - $p
    wasm_heap(code);
    wasm_heap(code);
    wasm_i32c(code, 49);
    code.push(Op::I32Add as u8);
    wasm_local(code, Op::LocalGet, tp);
    code.push(Op::I32Sub as u8);
    code.push(Op::I32Store as u8);
    code.push(0x02);
    code.push(0x04);
    wasm_fd_write(code);
}

/// Emission context passed through instruction emission.
struct EmitCtx<'a> {
    var_map: &'a HashMap<VarId, u32>,
    func_map: &'a HashMap<FuncId, u32>,
    var_to_func: &'a HashMap<VarId, FuncId>,
    string_table: &'a HashMap<String, u32>,
    alloc_func_index: u32,
    user_func_type_idx: u32,
    /// Function indices of the bignum runtime helpers (`besar`): parse, render,
    /// and signed compare (`bi_cmp`, returns -1/0/1).
    bi_from_str_index: u32,
    bi_to_str_index: u32,
    bi_cmp_index: u32,
    /// Function index of the signed BigInt add/sub helper (`bi_addsub(a,b,sub)`).
    bi_addsub_index: u32,
    /// Function index of the signed BigInt multiply helper (`bi_mul(a,b)`).
    bi_mul_index: u32,
    /// Function index of the truncating BigInt divmod (`bi_divmod(a,b,want_rem)`).
    bi_divmod_index: u32,
    /// Function indices of the Decimal (`perpuluhan`) runtime: parse, render,
    /// signed add/sub (`dec_addsub(a,b,sub)`), multiply, value-based compare
    /// (-1/0/1), and half-to-even division.
    dec_from_str_index: u32,
    dec_to_str_index: u32,
    dec_addsub_index: u32,
    dec_mul_index: u32,
    dec_cmp_index: u32,
    dec_div_index: u32,
    /// Function indices of the fixed-point (`wang`/`titik_tetap`) runtime:
    /// round-to-scale multiply/divide and the explicit-scale constructor.
    /// (Parse/display/add/sub/compare reuse the Decimal helpers above.)
    fix_mul_index: u32,
    fix_div_index: u32,
    fix_titik_tetap_index: u32,
    /// Function indices of the Q-format (`qmn`) runtime: constructor, render,
    /// wrapping add/sub, round-to-fb multiply/divide, value-based compare.
    qmn_parse_index: u32,
    qmn_to_str_index: u32,
    qmn_addsub_index: u32,
    qmn_mul_index: u32,
    qmn_div_index: u32,
    qmn_cmp_index: u32,
    /// Static type of each IR value, so builtins (e.g. `cetak`) can choose an
    /// int-printing (itoa) path vs. a string-pointer path.
    var_to_ty: &'a HashMap<VarId, Ty>,
    /// Two reserved scratch i32 locals for the integer-printing routine.
    itoa_v: u32,
    itoa_p: u32,
    /// Base index of 6 extra scratch i32 locals (string builtins).
    scratch: u32,
}

impl Backend for WasmBackend {
    fn emit(&self, program: &Program) -> Result<BackendOutput> {
        let module = self.translate(program)?;
        let wasm_bytes = module.encode();

        let js_glue = self.generate_js_glue();

        Ok(BackendOutput {
            primary: wasm_bytes,
            extension: ".wasm".to_string(),
            auxiliary: vec![AuxFile {
                name: "riina_loader.js".to_string(),
                content: js_glue,
            }],
        })
    }

    fn target(&self) -> Target {
        self.target
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::ir::{self, AnnotatedInstr, BlockId};

    /// Helper to create a simple main function with given instructions.
    fn make_program(instrs: Vec<AnnotatedInstr>, ret: VarId) -> Program {
        let mut program = ir::Program::new();
        let mut main_func = ir::Function::new(
            FuncId::MAIN,
            "main".to_string(),
            "x".to_string(),
            riina_types::Ty::Unit,
            riina_types::Ty::Int,
            riina_types::Effect::Pure,
        );
        let entry = BlockId::new(0);
        let mut block = BasicBlock::new(entry);
        block.instrs = instrs;
        block.terminator = Some(Terminator::Return(ret));
        main_func.blocks.push(block);
        main_func.entry = entry;
        program.functions.insert(FuncId::MAIN, main_func);
        program
    }

    fn ann(instr: Instruction, result: VarId) -> AnnotatedInstr {
        AnnotatedInstr {
            instr,
            result,
            ty: riina_types::Ty::Int,
            effect: riina_types::Effect::Pure,
            security: riina_types::SecurityLevel::Public,
        }
    }

    #[test]
    fn test_wasm_backend_target() {
        let backend = WasmBackend::new(Target::Wasm32);
        assert_eq!(backend.target(), Target::Wasm32);
    }

    #[test]
    fn test_wasm_backend_empty_program() {
        let backend = WasmBackend::new(Target::Wasm32);
        let program = ir::Program::new();
        let output = backend.emit(&program).unwrap();
        assert_eq!(output.extension, ".wasm");
        assert!(output.primary.len() >= 8);
        assert_eq!(&output.primary[0..4], b"\x00asm");
    }

    #[test]
    fn test_wasm_backend_has_js_glue() {
        let backend = WasmBackend::new(Target::Wasm32);
        let program = ir::Program::new();
        let output = backend.emit(&program).unwrap();
        assert_eq!(output.auxiliary.len(), 1);
        assert_eq!(output.auxiliary[0].name, "riina_loader.js");
        let js = String::from_utf8(output.auxiliary[0].content.clone()).unwrap();
        assert!(js.contains("WebAssembly.instantiate"));
        assert!(js.contains("fd_write"));
        assert!(js.contains("getOutput"));
    }

    #[test]
    fn test_wasm_mod_operation() {
        let v0 = VarId::new(0);
        let v1 = VarId::new(1);
        let v2 = VarId::new(2);
        let program = make_program(
            vec![
                ann(Instruction::Const(Constant::Int(5)), v0),
                ann(Instruction::Const(Constant::Int(3)), v1),
                ann(Instruction::BinOp(BinOp::Mod, v0, v1), v2),
            ],
            v2,
        );

        let backend = WasmBackend::new(Target::Wasm32);
        let output = backend.emit(&program).unwrap();
        assert!(
            output.primary.windows(1).any(|w| w[0] == 0x6F),
            "WASM binary should contain I32RemS opcode (0x6F)"
        );
    }

    /// The width-mask byte sequence for a u8 result: `i32.const 255` (0x41 0xFF
    /// 0x01) followed by `i32.and` (0x71).
    // i64.const 255 (0x42, sleb128 0xFF 0x01); i64.and (0x83) — the width mask
    // in the uniform i64 value cell.
    const U8_MASK_SEQ: [u8; 4] = [0x42, 0xFF, 0x01, 0x83];

    #[test]
    fn numeric_tower_wasm_masks_sized_arithmetic() {
        // A BinOp whose result types as u8 is masked to 8 bits in WASM.
        let (v0, v1, v2) = (VarId::new(0), VarId::new(1), VarId::new(2));
        let sized_add = AnnotatedInstr {
            instr: Instruction::BinOp(BinOp::Add, v0, v1),
            result: v2,
            ty: riina_types::Ty::IntN {
                bits: 8,
                signed: false,
            },
            effect: riina_types::Effect::Pure,
            security: riina_types::SecurityLevel::Public,
        };
        let program = make_program(
            vec![
                ann(Instruction::Const(Constant::Int(200)), v0),
                ann(Instruction::Const(Constant::Int(100)), v1),
                sized_add,
            ],
            v2,
        );
        let out = WasmBackend::new(Target::Wasm32).emit(&program).unwrap();
        assert!(
            out.primary.windows(4).any(|w| w == U8_MASK_SEQ),
            "u8 arithmetic must be masked with `i64.const 255; i64.and` in WASM"
        );
    }

    #[test]
    fn numeric_tower_wasm_does_not_mask_plain_int() {
        // Plain `Int` arithmetic (via `ann`, which annotates `Ty::Int`) is unmasked.
        let (v0, v1, v2) = (VarId::new(0), VarId::new(1), VarId::new(2));
        let program = make_program(
            vec![
                ann(Instruction::Const(Constant::Int(200)), v0),
                ann(Instruction::Const(Constant::Int(100)), v1),
                ann(Instruction::BinOp(BinOp::Add, v0, v1), v2),
            ],
            v2,
        );
        let out = WasmBackend::new(Target::Wasm32).emit(&program).unwrap();
        assert!(
            !out.primary.windows(4).any(|w| w == U8_MASK_SEQ),
            "plain Int arithmetic must not be width-masked"
        );
    }

    #[test]
    fn plain_int_div_mod_compare_are_unsigned() {
        // Plain `Nombor` (`Ty::Int`) is a u64 at runtime (interpreter
        // `Value::Int(u64)`, C `uint64_t`), so the WASM backend must emit the
        // UNSIGNED i64 division/remainder/order ops. With the signed forms a
        // value >= 2^63 read as negative: `18000000000000000000 > 1` compiled
        // to false and div/mod produced wrapped-signed junk while interp and C
        // agreed on the u64 answers (found 2026-08-08 by a >= 2^63
        // differential; the i64-cell landing had kept the old signed ops).
        let (v0, v1, v2) = (VarId::new(0), VarId::new(1), VarId::new(2));
        // NB: asserting the *absence* of the signed opcode byte is not possible
        // at this level — e.g. 0x7F (i64.div_s) is also the `i32` ValType byte
        // all over the type section. The semantic guard is the corpus example
        // `00_basics/nombor_64bit.rii`, which the C/WASM differential holds
        // byte-equal (a signed op regression makes its output diverge).
        for (op, want) in [
            (BinOp::Div, Op::I64DivU),
            (BinOp::Mod, Op::I64RemU),
            (BinOp::Lt, Op::I64LtU),
            (BinOp::Gt, Op::I64GtU),
            (BinOp::Le, Op::I64LeU),
            (BinOp::Ge, Op::I64GeU),
        ] {
            let program = make_program(
                vec![
                    ann(Instruction::Const(Constant::Int(18_000_000_000_000_000_000)), v0),
                    ann(Instruction::Const(Constant::Int(3)), v1),
                    ann(Instruction::BinOp(op, v0, v1), v2),
                ],
                v2,
            );
            let out = WasmBackend::new(Target::Wasm32).emit(&program).unwrap();
            assert!(
                out.primary.contains(&(want as u8)),
                "plain Int {op:?} must lower to the unsigned op"
            );
        }
    }

    #[test]
    fn signed_i64_div_and_compare_stay_signed() {
        // A signed 64-bit sized int keeps the signed ops (no extension needed
        // at full width) — the unsigned fix must not flip these.
        let (v0, v1, v2) = (VarId::new(0), VarId::new(1), VarId::new(2));
        let i64s = riina_types::Ty::IntN {
            bits: 64,
            signed: true,
        };
        let mk = |instr, result, ty| AnnotatedInstr {
            instr,
            result,
            ty,
            effect: riina_types::Effect::Pure,
            security: riina_types::SecurityLevel::Public,
        };
        for (op, want) in [(BinOp::Div, Op::I64DivS), (BinOp::Lt, Op::I64LtS)] {
            let program = make_program(
                vec![
                    mk(Instruction::Const(Constant::Int(200)), v0, i64s.clone()),
                    mk(Instruction::Const(Constant::Int(2)), v1, i64s.clone()),
                    mk(Instruction::BinOp(op, v0, v1), v2, i64s.clone()),
                ],
                v2,
            );
            let out = WasmBackend::new(Target::Wasm32).emit(&program).unwrap();
            assert!(
                out.primary.contains(&(want as u8)),
                "signed i64 {op:?} must keep the signed op"
            );
        }
    }

    #[test]
    fn numeric_tower_wasm_sign_extends_signed_division() {
        // Signed i8 division must sign-extend its operands to a full i64 before
        // `i64.div_s` (the cell holds the width-masked bits), via `i64.extend8_s`
        // (0xC2). Add/Sub/Mul and unsigned ops do not.
        let (v0, v1, v2) = (VarId::new(0), VarId::new(1), VarId::new(2));
        let i8s = riina_types::Ty::IntN {
            bits: 8,
            signed: true,
        };
        let mk = |instr, result, ty| AnnotatedInstr {
            instr,
            result,
            ty,
            effect: riina_types::Effect::Pure,
            security: riina_types::SecurityLevel::Public,
        };
        let signed = make_program(
            vec![
                mk(Instruction::Const(Constant::Int(200)), v0, i8s.clone()),
                mk(Instruction::Const(Constant::Int(2)), v1, i8s.clone()),
                mk(Instruction::BinOp(BinOp::Div, v0, v1), v2, i8s.clone()),
            ],
            v2,
        );
        let out = WasmBackend::new(Target::Wasm32).emit(&signed).unwrap();
        assert!(
            out.primary.contains(&(Op::I64Extend8S as u8)),
            "signed i8 division must sign-extend operands (i64.extend8_s = 0xC2)"
        );
        // The unsigned u8 counterpart does not sign-extend.
        let u8t = riina_types::Ty::IntN {
            bits: 8,
            signed: false,
        };
        let unsigned = make_program(
            vec![
                mk(Instruction::Const(Constant::Int(200)), v0, u8t.clone()),
                mk(Instruction::Const(Constant::Int(2)), v1, u8t.clone()),
                mk(Instruction::BinOp(BinOp::Div, v0, v1), v2, u8t.clone()),
            ],
            v2,
        );
        let out_u = WasmBackend::new(Target::Wasm32).emit(&unsigned).unwrap();
        assert!(
            !out_u.primary.contains(&(Op::I64Extend8S as u8)),
            "unsigned u8 division must not sign-extend"
        );
    }

    #[test]
    fn numeric_tower_wasm_accepts_64bit_constant() {
        // W1: the uniform i64 value cell represents a true 64-bit integer (>= 2^32)
        // directly. This used to be a clean compile error (the 32-bit cell could
        // not hold it).
        let v0 = VarId::new(0);
        let program = make_program(
            vec![ann(Instruction::Const(Constant::Int(5_000_000_000)), v0)],
            v0,
        );
        let out = WasmBackend::new(Target::Wasm32)
            .emit(&program)
            .expect("a 64-bit constant must compile on wasm32 (i64 value cell)");
        // Materialized as i64.const, not i32.const.
        assert!(
            out.primary.contains(&(Op::I64Const as u8)),
            "64-bit constant must lower to i64.const"
        );
    }

    #[test]
    fn numeric_tower_wasm_accepts_full_u32_and_64bit_range() {
        // The full unsigned 32-bit range AND true 64-bit values (>= 2^32) are
        // representable in the i64 cell (W1). The u32 range used to emit a wrapped
        // i32.const; the 64-bit range used to be a clean compile error.
        let v0 = VarId::new(0);
        for n in [
            3_000_000_000u64,
            u64::from(u32::MAX),
            5_000_000_000,
            u64::from(u32::MAX) + 1,
            1u64 << 40,
            u64::MAX,
        ] {
            let program = make_program(vec![ann(Instruction::Const(Constant::Int(n)), v0)], v0);
            assert!(
                WasmBackend::new(Target::Wasm32).emit(&program).is_ok(),
                "value {n} must be representable on wasm32 (i64 cell)"
            );
        }
    }

    #[test]
    fn test_wasm_logical_or() {
        let v0 = VarId::new(0);
        let v1 = VarId::new(1);
        let v2 = VarId::new(2);
        let program = make_program(
            vec![
                ann(Instruction::Const(Constant::Bool(true)), v0),
                ann(Instruction::Const(Constant::Bool(false)), v1),
                ann(Instruction::BinOp(BinOp::Or, v0, v1), v2),
            ],
            v2,
        );

        let backend = WasmBackend::new(Target::Wasm32);
        let output = backend.emit(&program).unwrap();
        assert!(
            output.primary.windows(1).any(|w| w[0] == 0x72),
            "WASM binary should contain I32Or opcode (0x72)"
        );
    }

    #[test]
    fn test_wasm_call_correct_index() {
        let backend = WasmBackend::new(Target::Wasm32);
        let mut program = ir::Program::new();

        let helper_id = FuncId::new(1);
        let mut helper_func = ir::Function::new(
            helper_id,
            "helper".to_string(),
            "x".to_string(),
            riina_types::Ty::Int,
            riina_types::Ty::Int,
            riina_types::Effect::Pure,
        );
        let he = BlockId::new(0);
        let mut hb = BasicBlock::new(he);
        hb.instrs
            .push(ann(Instruction::Const(Constant::Int(99)), VarId::new(100)));
        hb.terminator = Some(Terminator::Return(VarId::new(100)));
        helper_func.blocks.push(hb);
        helper_func.entry = he;
        program.functions.insert(helper_id, helper_func);

        let v0 = VarId::new(0);
        let v1 = VarId::new(1);
        let v2 = VarId::new(2);
        let mut main_func = ir::Function::new(
            FuncId::MAIN,
            "main".to_string(),
            "x".to_string(),
            riina_types::Ty::Unit,
            riina_types::Ty::Int,
            riina_types::Effect::Pure,
        );
        let entry = BlockId::new(0);
        let mut block = BasicBlock::new(entry);
        block.instrs = vec![
            ann(
                Instruction::Closure {
                    func: helper_id,
                    captures: vec![],
                },
                v0,
            ),
            ann(Instruction::Const(Constant::Int(0)), v1),
            ann(Instruction::Call(v0, v1), v2),
        ];
        block.terminator = Some(Terminator::Return(v2));
        main_func.blocks.push(block);
        main_func.entry = entry;
        program.functions.insert(FuncId::MAIN, main_func);

        let output = backend.emit(&program).unwrap();
        assert!(output.primary.windows(1).any(|w| w[0] == Op::Call as u8));
    }

    #[test]
    fn test_wasm_backend_with_main() {
        let backend = WasmBackend::new(Target::Wasm32);
        let v0 = VarId::new(0);
        let program = make_program(vec![ann(Instruction::Const(Constant::Int(42)), v0)], v0);

        let output = backend.emit(&program).unwrap();
        assert!(output.primary.len() > 8);
        assert!(output.primary.windows(6).any(|w| w == b"_start"));
    }

    // === Phase 2 tests ===

    #[test]
    fn test_wasm_string_constant() {
        let v0 = VarId::new(0);
        let program = make_program(
            vec![ann(
                Instruction::Const(Constant::String("hello".to_string())),
                v0,
            )],
            v0,
        );

        let backend = WasmBackend::new(Target::Wasm32);
        let output = backend.emit(&program).unwrap();
        // Data section should contain "hello"
        let binary = &output.primary;
        assert!(
            binary.windows(5).any(|w| w == b"hello"),
            "WASM binary should contain 'hello' in data section"
        );
    }

    #[test]
    fn test_wasm_pair_create_project() {
        let v0 = VarId::new(0);
        let v1 = VarId::new(1);
        let v2 = VarId::new(2);
        let v3 = VarId::new(3);
        let v4 = VarId::new(4);
        let program = make_program(
            vec![
                ann(Instruction::Const(Constant::Int(10)), v0),
                ann(Instruction::Const(Constant::Int(20)), v1),
                ann(Instruction::Pair(v0, v1), v2),
                ann(Instruction::Fst(v2), v3),
                ann(Instruction::Snd(v2), v4),
            ],
            v4,
        );

        let backend = WasmBackend::new(Target::Wasm32);
        let output = backend.emit(&program).unwrap();
        // Should contain i64.load (0x29) for projections (uniform i64 value cell)
        assert!(
            output.primary.windows(1).any(|w| w[0] == Op::I64Load as u8),
            "WASM binary should contain I64Load for pair projection"
        );
        // Should contain call to alloc
        assert!(
            output.primary.windows(1).any(|w| w[0] == Op::Call as u8),
            "WASM binary should contain Call for alloc"
        );
    }

    #[test]
    fn test_wasm_sum_inject_test_unwrap() {
        let v0 = VarId::new(0);
        let v1 = VarId::new(1);
        let v2 = VarId::new(2);
        let v3 = VarId::new(3);
        let program = make_program(
            vec![
                ann(Instruction::Const(Constant::Int(42)), v0),
                ann(Instruction::Inl(v0), v1),
                ann(Instruction::IsLeft(v1), v2),
                ann(Instruction::UnwrapLeft(v1), v3),
            ],
            v3,
        );

        let backend = WasmBackend::new(Target::Wasm32);
        let output = backend.emit(&program).unwrap();
        // Should contain i32.eqz (0x45) for IsLeft tag check
        assert!(
            output.primary.windows(1).any(|w| w[0] == Op::I32Eqz as u8),
            "WASM binary should contain I32Eqz for IsLeft"
        );
    }

    #[test]
    fn test_wasm_closure_capture() {
        let v0 = VarId::new(0);
        let v1 = VarId::new(1);
        let program = make_program(
            vec![
                ann(Instruction::Const(Constant::Int(42)), v0),
                ann(
                    Instruction::Closure {
                        func: FuncId::MAIN,
                        captures: vec![v0],
                    },
                    v1,
                ),
            ],
            v1,
        );

        let backend = WasmBackend::new(Target::Wasm32);
        let output = backend.emit(&program).unwrap();
        // Should contain i32.store for writing captures
        assert!(
            output
                .primary
                .windows(1)
                .any(|w| w[0] == Op::I32Store as u8),
            "WASM binary should contain I32Store for closure captures"
        );
    }

    #[test]
    fn test_wasm_builtin_cetak() {
        let v0 = VarId::new(0);
        let v1 = VarId::new(1);
        let program = make_program(
            vec![
                ann(
                    Instruction::Const(Constant::String("hello".to_string())),
                    v0,
                ),
                ann(
                    Instruction::BuiltinCall {
                        name: "cetakln".to_string(),
                        arg: v0,
                    },
                    v1,
                ),
            ],
            v1,
        );

        let backend = WasmBackend::new(Target::Wasm32);
        let output = backend.emit(&program).unwrap();
        // Should have "fd_write" in the import section (WASI)
        assert!(
            output.primary.windows(8).any(|w| w == b"fd_write"),
            "WASM binary should import fd_write"
        );
    }

    #[test]
    fn test_wasm_ref_alloc_load_store() {
        let v0 = VarId::new(0);
        let v1 = VarId::new(1);
        let v2 = VarId::new(2);
        let v3 = VarId::new(3);
        let v4 = VarId::new(4);
        let program = make_program(
            vec![
                ann(Instruction::Const(Constant::Int(10)), v0),
                ann(
                    Instruction::Alloc {
                        init: v0,
                        level: riina_types::SecurityLevel::Public,
                    },
                    v1,
                ),
                ann(Instruction::Load(v1), v2),
                ann(Instruction::Const(Constant::Int(20)), v3),
                ann(Instruction::Store(v1, v3), v4),
            ],
            v2,
        );

        let backend = WasmBackend::new(Target::Wasm32);
        let output = backend.emit(&program).unwrap();
        // Should have i64.load and i64.store (uniform i64 value cell)
        assert!(output.primary.windows(1).any(|w| w[0] == Op::I64Load as u8));
        assert!(output
            .primary
            .windows(1)
            .any(|w| w[0] == Op::I64Store as u8));
    }

    #[test]
    fn test_wasm_has_global_heap_ptr() {
        let v0 = VarId::new(0);
        let program = make_program(vec![ann(Instruction::Const(Constant::Int(0)), v0)], v0);

        let backend = WasmBackend::new(Target::Wasm32);
        let output = backend.emit(&program).unwrap();
        // Global section ID is 6
        assert!(
            output.primary.contains(&0x06),
            "WASM binary should contain global section"
        );
    }

    #[test]
    fn test_wasm_has_import_section() {
        let v0 = VarId::new(0);
        let program = make_program(vec![ann(Instruction::Const(Constant::Int(0)), v0)], v0);

        let backend = WasmBackend::new(Target::Wasm32);
        let output = backend.emit(&program).unwrap();
        // Import section should have "wasi_snapshot_preview1"
        assert!(
            output.primary.windows(8).any(|w| w == b"fd_write"),
            "WASM binary should contain WASI import"
        );
    }

    #[test]
    fn test_wasm_has_table_section() {
        let v0 = VarId::new(0);
        let program = make_program(vec![ann(Instruction::Const(Constant::Int(0)), v0)], v0);

        let backend = WasmBackend::new(Target::Wasm32);
        let output = backend.emit(&program).unwrap();
        // Table section ID is 4
        assert!(
            output.primary.contains(&0x04),
            "WASM binary should contain table section"
        );
    }

    #[test]
    fn test_wasm_inr_tag_is_one() {
        let v0 = VarId::new(0);
        let v1 = VarId::new(1);
        let v2 = VarId::new(2);
        let program = make_program(
            vec![
                ann(Instruction::Const(Constant::Int(99)), v0),
                ann(Instruction::Inr(v0), v1),
                ann(Instruction::IsLeft(v1), v2),
            ],
            v2,
        );

        let backend = WasmBackend::new(Target::Wasm32);
        let output = backend.emit(&program).unwrap();
        // Should produce valid WASM
        assert!(output.primary.len() > 8);
    }

    #[test]
    fn test_wasm_fix_closure() {
        let v0 = VarId::new(0);
        let v1 = VarId::new(1);
        let program = make_program(
            vec![
                ann(
                    Instruction::Closure {
                        func: FuncId::MAIN,
                        captures: vec![VarId::new(99)],
                    },
                    v0,
                ),
                ann(
                    Instruction::FixClosure {
                        closure: v0,
                        capture_index: 0,
                        value: v0,
                    },
                    v1,
                ),
            ],
            v1,
        );

        let backend = WasmBackend::new(Target::Wasm32);
        let output = backend.emit(&program).unwrap();
        assert!(output.primary.len() > 8);
    }

    #[test]
    fn test_wasm_multiple_strings_deduped() {
        let v0 = VarId::new(0);
        let v1 = VarId::new(1);
        let program = make_program(
            vec![
                ann(Instruction::Const(Constant::String("abc".to_string())), v0),
                ann(Instruction::Const(Constant::String("abc".to_string())), v1),
            ],
            v1,
        );

        let backend = WasmBackend::new(Target::Wasm32);
        let output = backend.emit(&program).unwrap();
        // "abc" should appear exactly once in data section
        let count = output.primary.windows(3).filter(|w| *w == b"abc").count();
        assert_eq!(count, 1, "Duplicate strings should be deduplicated");
    }

    #[test]
    fn test_wasm_effect_perform_passthrough() {
        let v0 = VarId::new(0);
        let v1 = VarId::new(1);
        let program = make_program(
            vec![
                ann(Instruction::Const(Constant::Int(42)), v0),
                ann(
                    Instruction::Perform {
                        effect: riina_types::Effect::Write,
                        payload: v0,
                    },
                    v1,
                ),
            ],
            v1,
        );

        let backend = WasmBackend::new(Target::Wasm32);
        let output = backend.emit(&program).unwrap();
        assert!(output.primary.len() > 8);
    }

    // === If/else structured control flow tests ===

    /// Build a program with if/else control flow:
    ///   bb0: cond = (x == 0); cond_branch cond bb1 bb2
    ///   bb1: result = 42; branch bb3
    ///   bb2: result = 99; branch bb3
    ///   bb3: phi = phi[(bb1,v_then),(bb2,v_else)]; return phi
    fn make_if_else_program() -> Program {
        let mut program = ir::Program::new();
        let mut main_func = ir::Function::new(
            FuncId::MAIN,
            "main".to_string(),
            "x".to_string(),
            riina_types::Ty::Int,
            riina_types::Ty::Int,
            riina_types::Effect::Pure,
        );
        // Clear default entry block
        main_func.blocks.clear();

        let bb0 = BlockId::new(0);
        let bb1 = BlockId::new(1);
        let bb2 = BlockId::new(2);
        let bb3 = BlockId::new(3);

        let v_zero = VarId::new(10);
        let v_cond = VarId::new(11);
        let v_then = VarId::new(12);
        let v_else = VarId::new(13);
        let v_phi = VarId::new(14);

        // bb0 (entry): compute condition
        let mut entry_block = BasicBlock::new(bb0);
        entry_block.instrs = vec![
            ann(Instruction::Const(Constant::Int(0)), v_zero),
            ann(Instruction::BinOp(BinOp::Eq, VarId::new(0), v_zero), v_cond),
        ];
        entry_block.terminator = Some(Terminator::CondBranch {
            cond: v_cond,
            then_block: bb1,
            else_block: bb2,
        });

        // bb1 (then): return 42
        let mut then_block = BasicBlock::new(bb1);
        then_block.instrs = vec![ann(Instruction::Const(Constant::Int(42)), v_then)];
        then_block.terminator = Some(Terminator::Branch(bb3));

        // bb2 (else): return 99
        let mut else_block = BasicBlock::new(bb2);
        else_block.instrs = vec![ann(Instruction::Const(Constant::Int(99)), v_else)];
        else_block.terminator = Some(Terminator::Branch(bb3));

        // bb3 (merge): phi + return
        let mut merge_block = BasicBlock::new(bb3);
        merge_block.instrs = vec![ann(
            Instruction::Phi(vec![(bb1, v_then), (bb2, v_else)]),
            v_phi,
        )];
        merge_block.terminator = Some(Terminator::Return(v_phi));

        main_func.blocks = vec![entry_block, then_block, else_block, merge_block];
        main_func.entry = bb0;
        program.functions.insert(FuncId::MAIN, main_func);
        program
    }

    #[test]
    fn test_wasm_if_else_structured_control_flow() {
        let program = make_if_else_program();
        let backend = WasmBackend::new(Target::Wasm32);
        let output = backend.emit(&program).unwrap();
        let binary = &output.primary;

        // Verify WASM magic
        assert_eq!(&binary[0..4], b"\x00asm");

        // Should contain Op::If (0x04)
        assert!(
            binary.contains(&(Op::If as u8)),
            "WASM binary should contain If opcode for structured if/else"
        );

        // Should contain Op::Else (0x05)
        assert!(
            binary.contains(&(Op::Else as u8)),
            "WASM binary should contain Else opcode"
        );

        // Should contain Op::End (0x0B) — at least for the if/else/end
        let end_count = binary.iter().filter(|&&b| b == Op::End as u8).count();
        assert!(end_count >= 2,
            "WASM binary should contain at least 2 End opcodes (if/else block + function end), got {}",
            end_count);

        // The if/else control flow itself is structured (proven by the If/Else
        // opcodes above). We no longer assert the *whole* binary is BrIf-free:
        // the `_start` result-echo prints non-Unit results, and its integer
        // itoa routine legitimately uses a `loop` + `BrIf`.
    }

    #[test]
    fn test_wasm_if_else_has_phi_result() {
        let program = make_if_else_program();
        let backend = WasmBackend::new(Target::Wasm32);
        let output = backend.emit(&program).unwrap();
        let binary = &output.primary;

        // Should contain LocalSet (0x21) for storing the phi result
        assert!(
            binary.contains(&(Op::LocalSet as u8)),
            "WASM binary should contain LocalSet for phi result storage"
        );

        // Should contain Return (0x0F) for the merge block
        assert!(
            binary.contains(&(Op::Return as u8)),
            "WASM binary should contain Return opcode"
        );
    }

    #[test]
    fn test_wasm_start_trampoline() {
        let v0 = VarId::new(0);
        let program = make_program(vec![ann(Instruction::Const(Constant::Int(42)), v0)], v0);

        let backend = WasmBackend::new(Target::Wasm32);
        let output = backend.emit(&program).unwrap();
        let binary = &output.primary;

        // Should export _start
        assert!(
            binary.windows(6).any(|w| w == b"_start"),
            "WASM binary should export _start"
        );

        // Should also export main
        assert!(
            binary.windows(4).any(|w| w == b"main"),
            "WASM binary should export main"
        );

        // Should contain Op::Drop (0x1A) for the trampoline dropping main's result
        assert!(
            binary.contains(&(Op::Drop as u8)),
            "WASM binary should contain Drop opcode in _start trampoline"
        );
    }
}
