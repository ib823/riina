// SPDX-License-Identifier: MPL-2.0
// Copyright (c) 2026 The RIINA Authors. See AUTHORS file.

//! AST to IR Lowering
//!
//! Translates RIINA AST expressions to SSA-form IR.
//! Each AST construct is lowered according to the rules in Coq.
//!
//! # Correspondence with Coq
//!
//! ```coq
//! (* 02_FORMAL/coq/properties/Compilation.v *)
//!
//! (* Lowering preserves types *)
//! Theorem lower_preserves_type : forall Γ e T ε ir,
//!   typing Γ e T ε ->
//!   lower e = Some ir ->
//!   ir_typing Γ ir T ε.
//!
//! (* Lowering preserves semantics *)
//! Theorem lower_preserves_eval : forall e v ir,
//!   eval e v ->
//!   lower e = Some ir ->
//!   ir_eval ir v.
//! ```
//!
//! # Translation Rules
//!
//! Each `Expr` variant is translated to a sequence of IR instructions:
//!
//! | Expr | IR Translation |
//! |------|----------------|
//! | `Unit` | `Const(Unit)` |
//! | `Bool(b)` | `Const(Bool(b))` |
//! | `Int(n)` | `Const(Int(n))` |
//! | `String(s)` | `Const(String(s))` |
//! | `Var(x)` | `Copy(lookup(x))` |
//! | `Lam(x, T, e)` | `Closure(f, captures)` where f is a new function |
//! | `App(e1, e2)` | `v1 = lower(e1); v2 = lower(e2); Call(v1, v2)` |
//! | `Pair(e1, e2)` | `v1 = lower(e1); v2 = lower(e2); Pair(v1, v2)` |
//! | `Fst(e)` | `v = lower(e); Fst(v)` |
//! | `Snd(e)` | `v = lower(e); Snd(v)` |
//! | `Inl(e, T)` | `v = lower(e); Inl(v)` |
//! | `Inr(e, T)` | `v = lower(e); Inr(v)` |
//! | `Case(e, x, e1, y, e2)` | Branch on `IsLeft`, then `UnwrapLeft/Right` |
//! | `If(c, t, f)` | `CondBranch` with phi node for result |
//! | `Let(x, e1, e2)` | `v1 = lower(e1); extend env; lower(e2)` |
//! | `Perform(eff, e)` | `v = lower(e); Perform(eff, v)` |
//! | `Handle(e, x, h)` | `Handle` terminator with handler block |
//! | `Ref(e, l)` | `v = lower(e); Alloc(v, l)` |
//! | `Deref(e)` | `v = lower(e); Load(v)` |
//! | `Assign(e1, e2)` | `v1 = lower(e1); v2 = lower(e2); Store(v1, v2)` |
//! | `Classify(e)` | `v = lower(e); Classify(v)` |
//! | `Declassify(e, p)` | `ve = lower(e); vp = lower(p); Declassify(ve, vp)` |
//! | `Prove(e)` | `v = lower(e); Prove(v)` |
//! | `Require(eff, e)` | `RequireCap(eff); lower(e)` |
//! | `Grant(eff, e)` | `GrantCap(eff); lower(e)` |
//!
//! # Mode: ULTRA KIASU | FUCKING PARANOID | ZERO TRUST

use crate::ir::{
    AnnotatedInstr, BlockId, Constant, Function, FuncId,
    Instruction, Program, Terminator, VarId,
};
use crate::{Error, Result};
use crate::ir::BinOp as IrBinOp;
use riina_types::{BinOp, Effect, Expr, Ident, SecurityLevel, Ty};
use crate::builtins;
use std::collections::{HashMap, HashSet};

/// Map a source name to its canonical builtin name, if it is a known builtin.
fn builtin_canonical(name: &str) -> Option<&'static str> {
    // I/O
    match name {
        "cetak" | "print" => return Some("cetak"),
        "cetakln" | "println" => return Some("cetakln"),
        // String
        "gabung_teks" | "concat" => return Some("gabung_teks"),
        "panjang" | "length" => return Some("panjang"),
        // Conversion
        "ke_teks" | "to_string" => return Some("ke_teks"),
        "ke_nombor" | "parse_int" => return Some("ke_nombor"),
        "ke_bool" | "to_bool" => return Some("ke_bool"),
        "bool_ke_nombor" | "bool_to_int" => return Some("bool_ke_nombor"),
        "nombor_ke_teks" | "int_to_string" => return Some("nombor_ke_teks"),
        // Math
        "mutlak" | "abs" => return Some("mutlak"),
        "minimum" | "min" => return Some("minimum"),
        "maksimum" | "max" => return Some("maksimum"),
        "kuasa" | "pow" => return Some("kuasa"),
        "punca" | "sqrt" => return Some("punca"),
        "gcd" => return Some("gcd"),
        "lcm" => return Some("lcm"),
        // Test
        "tegaskan" | "assert" => return Some("tegaskan"),
        "tegaskan_sama" | "assert_eq" => return Some("tegaskan_sama"),
        "tegaskan_beza" | "assert_ne" => return Some("tegaskan_beza"),
        "tegaskan_betul" | "assert_true" => return Some("tegaskan_betul"),
        "tegaskan_salah" | "assert_false" => return Some("tegaskan_salah"),
        _ => {}
    }
    // String (teks) builtins
    for &(bm, en, canonical) in builtins::teks::BUILTINS {
        if name == bm || name == en { return Some(canonical); }
    }
    // List (senarai) builtins
    for &(bm, en, canonical) in builtins::senarai::BUILTINS {
        if name == bm || name == en { return Some(canonical); }
    }
    // Map (peta) builtins
    for &(bm, en, canonical) in builtins::peta::BUILTINS {
        if name == bm || name == en { return Some(canonical); }
    }
    // Set builtins
    for &(bm, en, canonical) in builtins::set::BUILTINS {
        if name == bm || name == en { return Some(canonical); }
    }
    None
}

/// Variable environment during lowering
#[derive(Debug, Clone, Default)]
struct VarEnv {
    /// Map from source names to IR variable IDs
    bindings: HashMap<Ident, VarId>,
    /// Security levels for each variable
    levels: HashMap<VarId, SecurityLevel>,
    /// Types for each variable
    types: HashMap<VarId, Ty>,
}

impl VarEnv {
    fn new() -> Self {
        Self {
            bindings: HashMap::new(),
            levels: HashMap::new(),
            types: HashMap::new(),
        }
    }

    fn bind(&mut self, name: Ident, var: VarId, ty: Ty, level: SecurityLevel) {
        self.bindings.insert(name, var);
        self.levels.insert(var, level);
        self.types.insert(var, ty);
    }

    fn lookup(&self, name: &str) -> Option<VarId> {
        self.bindings.get(name).copied()
    }

}

/// Compute the set of free variables in an expression.
/// A variable is free if it is referenced but not bound within the expression.
fn free_vars(expr: &Expr) -> HashSet<Ident> {
    match expr {
        Expr::Unit | Expr::Bool(_) | Expr::Int(_) | Expr::String(_) | Expr::Loc(_) => {
            HashSet::new()
        }
        Expr::Var(name) => {
            let mut s = HashSet::new();
            s.insert(name.clone());
            s
        }
        Expr::Lam(param, _, body) => {
            let mut fv = free_vars(body);
            fv.remove(param);
            fv
        }
        Expr::App(e1, e2)
        | Expr::Pair(e1, e2)
        | Expr::Assign(e1, e2)
        | Expr::Declassify(e1, e2)
        | Expr::BinOp(_, e1, e2) => {
            let mut fv = free_vars(e1);
            fv.extend(free_vars(e2));
            fv
        }
        Expr::Let(name, e1, e2) => {
            let mut fv = free_vars(e1);
            let mut fv2 = free_vars(e2);
            fv2.remove(name);
            fv.extend(fv2);
            fv
        }
        Expr::LetRec(name, _, e1, e2) => {
            let mut fv1 = free_vars(e1);
            fv1.remove(name); // name is in scope in its own binding
            let mut fv2 = free_vars(e2);
            fv2.remove(name);
            fv1.extend(fv2);
            fv1
        }
        Expr::If(c, t, f) => {
            let mut fv = free_vars(c);
            fv.extend(free_vars(t));
            fv.extend(free_vars(f));
            fv
        }
        Expr::Case(e, x, e1, y, e2) => {
            let mut fv = free_vars(e);
            let mut fv1 = free_vars(e1);
            fv1.remove(x);
            let mut fv2 = free_vars(e2);
            fv2.remove(y);
            fv.extend(fv1);
            fv.extend(fv2);
            fv
        }
        Expr::Fst(e) | Expr::Snd(e) | Expr::Inl(e, _) | Expr::Inr(e, _)
        | Expr::Deref(e) | Expr::Classify(e) | Expr::Prove(e)
        | Expr::Ref(e, _) => free_vars(e),
        Expr::Perform(_, e) | Expr::Require(_, e) | Expr::Grant(_, e) => free_vars(e),
        Expr::Handle(e, x, h) => {
            let mut fv = free_vars(e);
            let mut fvh = free_vars(h);
            fvh.remove(x);
            fv.extend(fvh);
            fv
        }
        Expr::FFICall { args, .. } => {
            let mut fv = HashSet::new();
            for arg in args {
                fv.extend(free_vars(arg));
            }
            fv
        }
    }
}

/// AST to IR lowering pass
///
/// Translates typed RIINA AST to SSA-form IR.
pub struct Lower {
    /// The program being built
    program: Program,
    /// Current function being compiled
    current_func: Option<FuncId>,
    /// Current basic block
    current_block: BlockId,
    /// Next variable ID
    next_var: u32,
    /// Variable environment
    env: VarEnv,
}

impl Lower {
    /// Create a new lowering pass
    #[must_use]
    pub fn new() -> Self {
        Self {
            program: Program::new(),
            current_func: None,
            current_block: BlockId::ENTRY,
            next_var: 0,
            env: VarEnv::new(),
        }
    }

    /// Compile an expression to IR
    ///
    /// Creates a main function that evaluates the expression.
    pub fn compile(&mut self, expr: &Expr) -> Result<Program> {
        // Create main function
        let main_func = Function::new(
            FuncId::MAIN,
            "main".to_string(),
            "_unit".to_string(),
            Ty::Unit,
            self.infer_type(expr),
            self.infer_effect(expr),
        );
        self.program.add_function(main_func);
        self.current_func = Some(FuncId::MAIN);
        self.current_block = BlockId::ENTRY;

        // Lower the expression
        let result = self.lower_expr(expr)?;

        // Add return terminator
        if let Some(func) = self.program.function_mut(FuncId::MAIN) {
            if let Some(block) = func.block_mut(self.current_block) {
                block.terminate(Terminator::Return(result));
            }
        }

        Ok(self.program.clone())
    }

    /// Allocate a fresh variable ID
    fn fresh_var(&mut self) -> VarId {
        let id = VarId::new(self.next_var);
        self.next_var += 1;
        id
    }

    /// Emit an instruction to the current block
    fn emit(&mut self, instr: Instruction, ty: Ty, level: SecurityLevel, effect: Effect) -> VarId {
        let result = self.fresh_var();
        let annotated = AnnotatedInstr {
            instr,
            result,
            ty,
            security: level,
            effect,
        };

        if let Some(func) = self.current_func {
            if let Some(func) = self.program.function_mut(func) {
                if let Some(block) = func.block_mut(self.current_block) {
                    block.push(annotated);
                }
            }
        }

        result
    }

    /// Infer the type of an expression (simplified)
    fn infer_type(&self, expr: &Expr) -> Ty {
        match expr {
            Expr::Unit => Ty::Unit,
            Expr::Bool(_) => Ty::Bool,
            Expr::Int(_) => Ty::Int,
            Expr::String(_) => Ty::String,
            Expr::Pair(e1, e2) => {
                Ty::Prod(Box::new(self.infer_type(e1)), Box::new(self.infer_type(e2)))
            }
            Expr::Fst(e) => {
                if let Ty::Prod(t1, _) = self.infer_type(e) {
                    *t1
                } else {
                    Ty::Unit // Error case
                }
            }
            Expr::Snd(e) => {
                if let Ty::Prod(_, t2) = self.infer_type(e) {
                    *t2
                } else {
                    Ty::Unit // Error case
                }
            }
            Expr::Inl(_, ty) | Expr::Inr(_, ty) => ty.clone(),
            Expr::Lam(_, param_ty, body) => {
                Ty::Fn(
                    Box::new(param_ty.clone()),
                    Box::new(self.infer_type(body)),
                    self.infer_effect(body),
                )
            }
            Expr::Classify(e) => Ty::Secret(Box::new(self.infer_type(e))),
            Expr::Declassify(e, _) => {
                if let Ty::Secret(t) = self.infer_type(e) {
                    *t
                } else {
                    self.infer_type(e)
                }
            }
            Expr::Prove(e) => Ty::Proof(Box::new(self.infer_type(e))),
            Expr::Ref(e, level) => Ty::Ref(Box::new(self.infer_type(e)), *level),
            Expr::Deref(e) => {
                if let Ty::Ref(t, _) = self.infer_type(e) {
                    *t
                } else {
                    Ty::Unit
                }
            }
            Expr::Assign(_, _) => Ty::Unit,
            Expr::If(_, t, _) | Expr::Let(_, _, t) | Expr::LetRec(_, _, _, t) | Expr::Case(_, _, t, _, _) => self.infer_type(t),
            Expr::App(e1, _) => {
                if let Ty::Fn(_, ret, _) = self.infer_type(e1) {
                    *ret
                } else {
                    Ty::Unit
                }
            }
            Expr::Perform(_, e) | Expr::Handle(e, _, _) => self.infer_type(e),
            Expr::Require(eff, _) => Ty::Capability(eff.to_capability_kind()),
            Expr::Grant(_, e) => self.infer_type(e),
            Expr::Var(_) => Ty::Unit, // Would need type environment
            Expr::Loc(_) => Ty::Unit, // Runtime-only; actual type from store
            Expr::BinOp(op, _, _) => match op {
                BinOp::Add | BinOp::Sub | BinOp::Mul | BinOp::Div | BinOp::Mod => Ty::Int,
                BinOp::Eq | BinOp::Ne | BinOp::Lt | BinOp::Le | BinOp::Gt | BinOp::Ge
                | BinOp::And | BinOp::Or => Ty::Bool,
            },
            Expr::FFICall { ret_ty, .. } => ret_ty.clone(),
        }
    }

    /// Infer the effect of an expression
    fn infer_effect(&self, expr: &Expr) -> Effect {
        match expr {
            Expr::Unit | Expr::Bool(_) | Expr::Int(_) | Expr::String(_) | Expr::Var(_) => {
                Effect::Pure
            }
            Expr::Lam(_, _, _) => Effect::Pure,
            Expr::LetRec(_, _, e1, e2) => self.infer_effect(e1).join(self.infer_effect(e2)),
            Expr::Pair(e1, e2) => self.infer_effect(e1).join(self.infer_effect(e2)),
            Expr::Fst(e) | Expr::Snd(e) => self.infer_effect(e),
            Expr::Inl(e, _) | Expr::Inr(e, _) => self.infer_effect(e),
            Expr::Case(e, _, e1, _, e2) => {
                self.infer_effect(e)
                    .join(self.infer_effect(e1))
                    .join(self.infer_effect(e2))
            }
            Expr::If(c, t, f) => {
                self.infer_effect(c)
                    .join(self.infer_effect(t))
                    .join(self.infer_effect(f))
            }
            Expr::Let(_, e1, e2) => self.infer_effect(e1).join(self.infer_effect(e2)),
            Expr::App(e1, e2) => {
                let base = self.infer_effect(e1).join(self.infer_effect(e2));
                if let Ty::Fn(_, _, eff) = self.infer_type(e1) {
                    base.join(eff)
                } else {
                    base
                }
            }
            Expr::Perform(eff, e) => self.infer_effect(e).join(*eff),
            Expr::Handle(e, _, h) => self.infer_effect(e).join(self.infer_effect(h)),
            Expr::Ref(e, _) => self.infer_effect(e).join(Effect::Write),
            Expr::Deref(e) => self.infer_effect(e).join(Effect::Read),
            Expr::Assign(e1, e2) => {
                self.infer_effect(e1)
                    .join(self.infer_effect(e2))
                    .join(Effect::Write)
            }
            Expr::Classify(e) | Expr::Declassify(e, _) | Expr::Prove(e) => self.infer_effect(e),
            Expr::Require(eff, e) => self.infer_effect(e).join(*eff),
            Expr::Grant(_, e) => self.infer_effect(e),
            Expr::BinOp(_, e1, e2) => self.infer_effect(e1).join(self.infer_effect(e2)),
            Expr::Loc(_) => Effect::Pure,
            Expr::FFICall { args, .. } => {
                let mut eff = Effect::System;
                for arg in args {
                    eff = eff.join(self.infer_effect(arg));
                }
                eff
            }
        }
    }

    /// Lower an expression to IR
    ///
    /// Returns the variable ID holding the result.
    fn lower_expr(&mut self, expr: &Expr) -> Result<VarId> {
        match expr {
            // ═══════════════════════════════════════════════════════════════
            // CONSTANTS (Expr::Unit, Expr::Bool, Expr::Int, Expr::String)
            // ═══════════════════════════════════════════════════════════════
            Expr::Unit => {
                Ok(self.emit(
                    Instruction::Const(Constant::Unit),
                    Ty::Unit,
                    SecurityLevel::Public,
                    Effect::Pure,
                ))
            }

            Expr::Bool(b) => {
                Ok(self.emit(
                    Instruction::Const(Constant::Bool(*b)),
                    Ty::Bool,
                    SecurityLevel::Public,
                    Effect::Pure,
                ))
            }

            Expr::Int(n) => {
                Ok(self.emit(
                    Instruction::Const(Constant::Int(*n)),
                    Ty::Int,
                    SecurityLevel::Public,
                    Effect::Pure,
                ))
            }

            Expr::String(s) => {
                Ok(self.emit(
                    Instruction::Const(Constant::String(s.clone())),
                    Ty::String,
                    SecurityLevel::Public,
                    Effect::Pure,
                ))
            }

            // ═══════════════════════════════════════════════════════════════
            // VARIABLES (Expr::Var)
            // ═══════════════════════════════════════════════════════════════
            Expr::Var(name) => {
                // If it's a known builtin used as a bare value (not in App position),
                // emit a string constant placeholder so we don't crash with UnboundVariable.
                if self.env.lookup(name).is_none() {
                    if let Some(canonical) = builtin_canonical(name) {
                        return Ok(self.emit(
                            Instruction::Const(Constant::String(canonical.to_string())),
                            Ty::String,
                            SecurityLevel::Public,
                            Effect::Pure,
                        ));
                    }
                }
                let var = self.env.lookup(name)
                    .ok_or_else(|| Error::UnboundVariable(name.clone()))?;
                let ty = self.env.types.get(&var).cloned().unwrap_or(Ty::Unit);
                let level = self.env.levels.get(&var).copied().unwrap_or(SecurityLevel::Public);
                Ok(self.emit(Instruction::Copy(var), ty, level, Effect::Pure))
            }

            // ═══════════════════════════════════════════════════════════════
            // FUNCTIONS (Expr::Lam, Expr::App)
            // ═══════════════════════════════════════════════════════════════
            Expr::Lam(param, param_ty, body) => {
                // Create a new function for the lambda body
                let func_id = self.program.fresh_func_id();
                let body_effect = self.infer_effect(body);
                let return_ty = self.infer_type(body);

                let mut func = Function::new(
                    func_id,
                    format!("lambda_{}", func_id.0),
                    param.clone(),
                    param_ty.clone(),
                    return_ty.clone(),
                    body_effect,
                );

                // Compute free variables that need to be captured
                let body_fv = free_vars(body);
                let mut capture_names: Vec<Ident> = body_fv.into_iter()
                    .filter(|name| name != param && self.env.lookup(name).is_some())
                    .collect();
                capture_names.sort(); // deterministic order

                // Resolve captures to VarIds in the *current* environment
                let capture_vars: Vec<VarId> = capture_names.iter()
                    .filter_map(|name| self.env.lookup(name))
                    .collect();

                // Record capture metadata on the function for C emission
                func.captures = capture_names.iter()
                    .map(|name| {
                        let var = self.env.lookup(name).unwrap();
                        let ty = self.env.types.get(&var).cloned().unwrap_or(Ty::Unit);
                        (name.clone(), ty)
                    })
                    .collect();

                // Save current state
                let saved_func = self.current_func;
                let saved_block = self.current_block;
                let saved_env = self.env.clone();
                let saved_next_var = self.next_var;

                // Reset for new function
                self.current_func = Some(func_id);
                self.current_block = BlockId::ENTRY;
                self.next_var = 0;
                self.env = VarEnv::new();

                // Bind captured variables in the new environment
                for name in &capture_names {
                    let old_var = saved_env.lookup(name).unwrap();
                    let new_var = self.fresh_var();
                    let ty = saved_env.types.get(&old_var).cloned().unwrap_or(Ty::Unit);
                    let level = saved_env.levels.get(&old_var).copied().unwrap_or(SecurityLevel::Public);
                    self.env.bind(name.clone(), new_var, ty, level);
                }

                // Bind parameter
                let param_var = self.fresh_var();
                self.env.bind(
                    param.clone(),
                    param_var,
                    param_ty.clone(),
                    SecurityLevel::Public,
                );

                // Add function to program so we can add blocks to it
                self.program.add_function(func);

                // Lower the body
                let result = self.lower_expr(body)?;

                // Terminate with return
                if let Some(func) = self.program.function_mut(func_id) {
                    if let Some(block) = func.block_mut(self.current_block) {
                        block.terminate(Terminator::Return(result));
                    }
                }

                // Restore state
                self.current_func = saved_func;
                self.current_block = saved_block;
                self.env = saved_env;
                self.next_var = saved_next_var;

                // Emit closure creation with captured variables
                let fn_ty = Ty::Fn(
                    Box::new(param_ty.clone()),
                    Box::new(return_ty),
                    body_effect,
                );
                Ok(self.emit(
                    Instruction::Closure {
                        func: func_id,
                        captures: capture_vars,
                    },
                    fn_ty,
                    SecurityLevel::Public,
                    Effect::Pure,
                ))
            }

            Expr::App(func_expr, arg_expr) => {
                // Intercept builtin calls: if func is Var(name) and name is a known builtin,
                // emit BuiltinCall instead of Call.
                if let Expr::Var(name) = func_expr.as_ref() {
                    if let Some(canonical) = builtin_canonical(name) {
                        let arg_var = self.lower_expr(arg_expr)?;
                        let effect = self.infer_effect(expr);
                        return Ok(self.emit(
                            Instruction::BuiltinCall {
                                name: canonical.to_string(),
                                arg: arg_var,
                            },
                            Ty::Unit, // builtins mostly return Unit or String; C emitter handles
                            SecurityLevel::Public,
                            effect,
                        ));
                    }
                }
                let func_var = self.lower_expr(func_expr)?;
                let arg_var = self.lower_expr(arg_expr)?;
                let return_ty = if let Ty::Fn(_, ret, _) = self.infer_type(func_expr) {
                    *ret
                } else {
                    Ty::Unit
                };
                let effect = self.infer_effect(expr);
                Ok(self.emit(
                    Instruction::Call(func_var, arg_var),
                    return_ty,
                    SecurityLevel::Public,
                    effect,
                ))
            }

            // ═══════════════════════════════════════════════════════════════
            // PRODUCTS (Expr::Pair, Expr::Fst, Expr::Snd)
            // ═══════════════════════════════════════════════════════════════
            Expr::Pair(e1, e2) => {
                let v1 = self.lower_expr(e1)?;
                let v2 = self.lower_expr(e2)?;
                let ty = Ty::Prod(
                    Box::new(self.infer_type(e1)),
                    Box::new(self.infer_type(e2)),
                );
                let effect = self.infer_effect(e1).join(self.infer_effect(e2));
                Ok(self.emit(
                    Instruction::Pair(v1, v2),
                    ty,
                    SecurityLevel::Public,
                    effect,
                ))
            }

            Expr::Fst(e) => {
                let v = self.lower_expr(e)?;
                let ty = if let Ty::Prod(t1, _) = self.infer_type(e) {
                    *t1
                } else {
                    Ty::Unit
                };
                Ok(self.emit(
                    Instruction::Fst(v),
                    ty,
                    SecurityLevel::Public,
                    self.infer_effect(e),
                ))
            }

            Expr::Snd(e) => {
                let v = self.lower_expr(e)?;
                let ty = if let Ty::Prod(_, t2) = self.infer_type(e) {
                    *t2
                } else {
                    Ty::Unit
                };
                Ok(self.emit(
                    Instruction::Snd(v),
                    ty,
                    SecurityLevel::Public,
                    self.infer_effect(e),
                ))
            }

            // ═══════════════════════════════════════════════════════════════
            // SUMS (Expr::Inl, Expr::Inr, Expr::Case)
            // ═══════════════════════════════════════════════════════════════
            Expr::Inl(e, ty) => {
                let v = self.lower_expr(e)?;
                Ok(self.emit(
                    Instruction::Inl(v),
                    ty.clone(),
                    SecurityLevel::Public,
                    self.infer_effect(e),
                ))
            }

            Expr::Inr(e, ty) => {
                let v = self.lower_expr(e)?;
                Ok(self.emit(
                    Instruction::Inr(v),
                    ty.clone(),
                    SecurityLevel::Public,
                    self.infer_effect(e),
                ))
            }

            Expr::Case(scrutinee, left_name, left_branch, right_name, right_branch) => {
                // Lower scrutinee
                let scrut_var = self.lower_expr(scrutinee)?;

                // Check if left or right
                let is_left = self.emit(
                    Instruction::IsLeft(scrut_var),
                    Ty::Bool,
                    SecurityLevel::Public,
                    Effect::Pure,
                );

                // Create blocks for branches and merge
                let then_block = if let Some(func) = self.current_func {
                    if let Some(func) = self.program.function_mut(func) {
                        func.new_block()
                    } else {
                        return Err(Error::InvalidOperation("No current function".to_string()));
                    }
                } else {
                    return Err(Error::InvalidOperation("No current function".to_string()));
                };

                let else_block = if let Some(func) = self.current_func {
                    if let Some(func) = self.program.function_mut(func) {
                        func.new_block()
                    } else {
                        return Err(Error::InvalidOperation("No current function".to_string()));
                    }
                } else {
                    return Err(Error::InvalidOperation("No current function".to_string()));
                };

                let merge_block = if let Some(func) = self.current_func {
                    if let Some(func) = self.program.function_mut(func) {
                        func.new_block()
                    } else {
                        return Err(Error::InvalidOperation("No current function".to_string()));
                    }
                } else {
                    return Err(Error::InvalidOperation("No current function".to_string()));
                };

                // Terminate current block with conditional branch
                if let Some(func) = self.current_func {
                    if let Some(func) = self.program.function_mut(func) {
                        if let Some(block) = func.block_mut(self.current_block) {
                            block.terminate(Terminator::CondBranch {
                                cond: is_left,
                                then_block,
                                else_block,
                            });
                        }
                    }
                }

                // Left branch (then block)
                self.current_block = then_block;
                let left_val = self.emit(
                    Instruction::UnwrapLeft(scrut_var),
                    Ty::Unit, // TODO: proper type
                    SecurityLevel::Public,
                    Effect::Pure,
                );

                let saved_env = self.env.clone();
                self.env.bind(left_name.clone(), left_val, Ty::Unit, SecurityLevel::Public);
                let left_result = self.lower_expr(left_branch)?;
                self.env = saved_env;

                let then_end_block = self.current_block;

                // Branch to merge
                if let Some(func) = self.current_func {
                    if let Some(func) = self.program.function_mut(func) {
                        if let Some(block) = func.block_mut(then_end_block) {
                            block.terminate(Terminator::Branch(merge_block));
                        }
                    }
                }

                // Right branch (else block)
                self.current_block = else_block;
                let right_val = self.emit(
                    Instruction::UnwrapRight(scrut_var),
                    Ty::Unit, // TODO: proper type
                    SecurityLevel::Public,
                    Effect::Pure,
                );

                let saved_env = self.env.clone();
                self.env.bind(right_name.clone(), right_val, Ty::Unit, SecurityLevel::Public);
                let right_result = self.lower_expr(right_branch)?;
                self.env = saved_env;

                let else_end_block = self.current_block;

                // Branch to merge
                if let Some(func) = self.current_func {
                    if let Some(func) = self.program.function_mut(func) {
                        if let Some(block) = func.block_mut(else_end_block) {
                            block.terminate(Terminator::Branch(merge_block));
                        }
                    }
                }

                // Merge block with phi
                self.current_block = merge_block;
                let result_ty = self.infer_type(left_branch);
                let phi = self.emit(
                    Instruction::Phi(vec![
                        (then_end_block, left_result),
                        (else_end_block, right_result),
                    ]),
                    result_ty,
                    SecurityLevel::Public,
                    self.infer_effect(expr),
                );

                Ok(phi)
            }

            // ═══════════════════════════════════════════════════════════════
            // CONTROL FLOW (Expr::If, Expr::Let)
            // ═══════════════════════════════════════════════════════════════
            Expr::If(cond, then_expr, else_expr) => {
                let cond_var = self.lower_expr(cond)?;

                // Create blocks
                let then_block = if let Some(func) = self.current_func {
                    if let Some(func) = self.program.function_mut(func) {
                        func.new_block()
                    } else {
                        return Err(Error::InvalidOperation("No current function".to_string()));
                    }
                } else {
                    return Err(Error::InvalidOperation("No current function".to_string()));
                };

                let else_block = if let Some(func) = self.current_func {
                    if let Some(func) = self.program.function_mut(func) {
                        func.new_block()
                    } else {
                        return Err(Error::InvalidOperation("No current function".to_string()));
                    }
                } else {
                    return Err(Error::InvalidOperation("No current function".to_string()));
                };

                let merge_block = if let Some(func) = self.current_func {
                    if let Some(func) = self.program.function_mut(func) {
                        func.new_block()
                    } else {
                        return Err(Error::InvalidOperation("No current function".to_string()));
                    }
                } else {
                    return Err(Error::InvalidOperation("No current function".to_string()));
                };

                // Conditional branch
                if let Some(func) = self.current_func {
                    if let Some(func) = self.program.function_mut(func) {
                        if let Some(block) = func.block_mut(self.current_block) {
                            block.terminate(Terminator::CondBranch {
                                cond: cond_var,
                                then_block,
                                else_block,
                            });
                        }
                    }
                }

                // Then branch
                self.current_block = then_block;
                let then_result = self.lower_expr(then_expr)?;
                let then_end_block = self.current_block;

                if let Some(func) = self.current_func {
                    if let Some(func) = self.program.function_mut(func) {
                        if let Some(block) = func.block_mut(then_end_block) {
                            block.terminate(Terminator::Branch(merge_block));
                        }
                    }
                }

                // Else branch
                self.current_block = else_block;
                let else_result = self.lower_expr(else_expr)?;
                let else_end_block = self.current_block;

                if let Some(func) = self.current_func {
                    if let Some(func) = self.program.function_mut(func) {
                        if let Some(block) = func.block_mut(else_end_block) {
                            block.terminate(Terminator::Branch(merge_block));
                        }
                    }
                }

                // Merge with phi
                self.current_block = merge_block;
                let result_ty = self.infer_type(then_expr);
                Ok(self.emit(
                    Instruction::Phi(vec![
                        (then_end_block, then_result),
                        (else_end_block, else_result),
                    ]),
                    result_ty,
                    SecurityLevel::Public,
                    self.infer_effect(expr),
                ))
            }

            Expr::Let(name, binding, body) => {
                let bind_var = self.lower_expr(binding)?;
                let bind_ty = self.infer_type(binding);

                let saved_env = self.env.clone();
                self.env.bind(name.clone(), bind_var, bind_ty, SecurityLevel::Public);
                let result = self.lower_expr(body)?;
                self.env = saved_env;

                Ok(result)
            }

            Expr::LetRec(name, ty_ann, binding, body) => {
                // For LetRec, we pre-bind name so the lambda body can reference it.
                // The lambda captures the placeholder VarId. After the closure is
                // created, we emit FixClosure to patch the self-capture.
                let bind_ty = ty_ann.clone();
                let placeholder = self.fresh_var();

                let saved_env = self.env.clone();
                self.env.bind(name.clone(), placeholder, bind_ty.clone(), SecurityLevel::Public);

                // Lower the binding (lambda). This creates a closure that captures
                // placeholder as the self-reference.
                let bind_var = self.lower_expr(binding)?;

                // Find which capture index corresponds to placeholder
                // and emit FixClosure to patch it to point to itself.
                // The placeholder was captured by the lambda's free_vars analysis.
                self.emit(
                    Instruction::FixClosure {
                        closure: bind_var,
                        capture_index: 0, // placeholder is first free var (sorted)
                    },
                    Ty::Unit,
                    SecurityLevel::Public,
                    Effect::Pure,
                );

                // For the body, use bind_var as the resolved name
                self.env.bind(name.clone(), bind_var, bind_ty, SecurityLevel::Public);
                let result = self.lower_expr(body)?;
                self.env = saved_env;

                Ok(result)
            }

            // ═══════════════════════════════════════════════════════════════
            // EFFECTS (Expr::Perform, Expr::Handle)
            // ═══════════════════════════════════════════════════════════════
            Expr::Perform(effect, payload) => {
                let payload_var = self.lower_expr(payload)?;
                let payload_ty = self.infer_type(payload);
                Ok(self.emit(
                    Instruction::Perform {
                        effect: *effect,
                        payload: payload_var,
                    },
                    payload_ty,
                    SecurityLevel::Public,
                    *effect,
                ))
            }

            Expr::Handle(body, handler_var, handler) => {
                // Create blocks for body and handler
                let body_block = if let Some(func) = self.current_func {
                    if let Some(func) = self.program.function_mut(func) {
                        func.new_block()
                    } else {
                        return Err(Error::InvalidOperation("No current function".to_string()));
                    }
                } else {
                    return Err(Error::InvalidOperation("No current function".to_string()));
                };

                let handler_block = if let Some(func) = self.current_func {
                    if let Some(func) = self.program.function_mut(func) {
                        func.new_block()
                    } else {
                        return Err(Error::InvalidOperation("No current function".to_string()));
                    }
                } else {
                    return Err(Error::InvalidOperation("No current function".to_string()));
                };

                let result_block = if let Some(func) = self.current_func {
                    if let Some(func) = self.program.function_mut(func) {
                        func.new_block()
                    } else {
                        return Err(Error::InvalidOperation("No current function".to_string()));
                    }
                } else {
                    return Err(Error::InvalidOperation("No current function".to_string()));
                };

                // Terminate with handle
                if let Some(func) = self.current_func {
                    if let Some(func) = self.program.function_mut(func) {
                        if let Some(block) = func.block_mut(self.current_block) {
                            block.terminate(Terminator::Handle {
                                body_block,
                                handler_block,
                                resume_var: handler_var.clone(),
                                result_block,
                            });
                        }
                    }
                }

                // Lower body
                self.current_block = body_block;
                let body_result = self.lower_expr(body)?;

                if let Some(func) = self.current_func {
                    if let Some(func) = self.program.function_mut(func) {
                        if let Some(block) = func.block_mut(self.current_block) {
                            block.terminate(Terminator::Branch(result_block));
                        }
                    }
                }

                // Lower handler
                self.current_block = handler_block;
                let handler_param = self.fresh_var();
                self.env.bind(handler_var.clone(), handler_param, Ty::Unit, SecurityLevel::Public);
                let _handler_result = self.lower_expr(handler)?;

                if let Some(func) = self.current_func {
                    if let Some(func) = self.program.function_mut(func) {
                        if let Some(block) = func.block_mut(self.current_block) {
                            block.terminate(Terminator::Branch(result_block));
                        }
                    }
                }

                // Result block
                self.current_block = result_block;
                Ok(body_result)
            }

            // ═══════════════════════════════════════════════════════════════
            // REFERENCES (Expr::Ref, Expr::Deref, Expr::Assign)
            // ═══════════════════════════════════════════════════════════════
            Expr::Ref(init, level) => {
                let init_var = self.lower_expr(init)?;
                let inner_ty = self.infer_type(init);
                Ok(self.emit(
                    Instruction::Alloc {
                        init: init_var,
                        level: *level,
                    },
                    Ty::Ref(Box::new(inner_ty), *level),
                    *level,
                    Effect::Write,
                ))
            }

            Expr::Deref(ref_expr) => {
                let ref_var = self.lower_expr(ref_expr)?;
                let inner_ty = if let Ty::Ref(t, _) = self.infer_type(ref_expr) {
                    *t
                } else {
                    Ty::Unit
                };
                Ok(self.emit(
                    Instruction::Load(ref_var),
                    inner_ty,
                    SecurityLevel::Public,
                    Effect::Read,
                ))
            }

            Expr::Assign(ref_expr, val_expr) => {
                let ref_var = self.lower_expr(ref_expr)?;
                let val_var = self.lower_expr(val_expr)?;
                Ok(self.emit(
                    Instruction::Store(ref_var, val_var),
                    Ty::Unit,
                    SecurityLevel::Public,
                    Effect::Write,
                ))
            }

            // ═══════════════════════════════════════════════════════════════
            // SECURITY (Expr::Classify, Expr::Declassify, Expr::Prove)
            // ═══════════════════════════════════════════════════════════════
            Expr::Classify(inner) => {
                let inner_var = self.lower_expr(inner)?;
                let inner_ty = self.infer_type(inner);
                Ok(self.emit(
                    Instruction::Classify(inner_var),
                    Ty::Secret(Box::new(inner_ty)),
                    SecurityLevel::Secret,
                    self.infer_effect(inner),
                ))
            }

            Expr::Declassify(secret, proof) => {
                let secret_var = self.lower_expr(secret)?;
                let proof_var = self.lower_expr(proof)?;
                let inner_ty = if let Ty::Secret(t) = self.infer_type(secret) {
                    *t
                } else {
                    self.infer_type(secret)
                };
                Ok(self.emit(
                    Instruction::Declassify(secret_var, proof_var),
                    inner_ty,
                    SecurityLevel::Public,
                    self.infer_effect(expr),
                ))
            }

            Expr::Prove(inner) => {
                let inner_var = self.lower_expr(inner)?;
                let inner_ty = self.infer_type(inner);
                Ok(self.emit(
                    Instruction::Prove(inner_var),
                    Ty::Proof(Box::new(inner_ty)),
                    SecurityLevel::Public,
                    self.infer_effect(inner),
                ))
            }

            // ═══════════════════════════════════════════════════════════════
            // CAPABILITIES (Expr::Require, Expr::Grant)
            // ═══════════════════════════════════════════════════════════════
            Expr::Require(effect, body) => {
                let _cap = self.emit(
                    Instruction::RequireCap(*effect),
                    Ty::Capability(effect.to_capability_kind()),
                    SecurityLevel::Public,
                    *effect,
                );
                self.lower_expr(body)
            }

            Expr::Grant(effect, body) => {
                let _cap = self.emit(
                    Instruction::GrantCap(*effect),
                    Ty::Capability(effect.to_capability_kind()),
                    SecurityLevel::Public,
                    Effect::Pure,
                );
                self.lower_expr(body)
            }

            Expr::Loc(l) => {
                // ELoc is a runtime-only value (store location).
                // Encode as integer constant; the runtime interprets it as a location.
                let result_ty = Ty::Unit;
                Ok(self.emit(
                    Instruction::Const(Constant::Int(*l)),
                    result_ty,
                    SecurityLevel::Public,
                    Effect::Pure,
                ))
            }

            Expr::FFICall { name, args, ret_ty } => {
                let mut arg_vars = Vec::new();
                for arg in args {
                    arg_vars.push(self.lower_expr(arg)?);
                }
                Ok(self.emit(
                    Instruction::FFICall { name: name.clone(), args: arg_vars },
                    ret_ty.clone(),
                    SecurityLevel::Public,
                    Effect::System,
                ))
            }

            Expr::BinOp(op, lhs, rhs) => {
                let l = self.lower_expr(lhs)?;
                let r = self.lower_expr(rhs)?;
                let ir_op = match op {
                    BinOp::Add => IrBinOp::Add,
                    BinOp::Sub => IrBinOp::Sub,
                    BinOp::Mul => IrBinOp::Mul,
                    BinOp::Div => IrBinOp::Div,
                    BinOp::Mod => IrBinOp::Mod,
                    BinOp::Eq => IrBinOp::Eq,
                    BinOp::Ne => IrBinOp::Ne,
                    BinOp::Lt => IrBinOp::Lt,
                    BinOp::Le => IrBinOp::Le,
                    BinOp::Gt => IrBinOp::Gt,
                    BinOp::Ge => IrBinOp::Ge,
                    BinOp::And => IrBinOp::And,
                    BinOp::Or => IrBinOp::Or,
                };
                let result_ty = self.infer_type(expr);
                let effect = self.infer_effect(expr);
                Ok(self.emit(
                    Instruction::BinOp(ir_op, l, r),
                    result_ty,
                    SecurityLevel::Public,
                    effect,
                ))
            }
        }
    }
}

impl Default for Lower {
    fn default() -> Self {
        Self::new()
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_lower_unit() {
        let mut lower = Lower::new();
        let prog = lower.compile(&Expr::Unit).unwrap();
        assert!(prog.function(FuncId::MAIN).is_some());
    }

    #[test]
    fn test_lower_bool() {
        let mut lower = Lower::new();
        let prog = lower.compile(&Expr::Bool(true)).unwrap();
        let main = prog.function(FuncId::MAIN).unwrap();
        assert!(!main.blocks.is_empty());
    }

    #[test]
    fn test_lower_int() {
        let mut lower = Lower::new();
        let prog = lower.compile(&Expr::Int(42)).unwrap();
        let main = prog.function(FuncId::MAIN).unwrap();
        assert!(!main.blocks.is_empty());
    }

    #[test]
    fn test_lower_pair() {
        let mut lower = Lower::new();
        let pair = Expr::Pair(
            Box::new(Expr::Int(1)),
            Box::new(Expr::Int(2)),
        );
        let prog = lower.compile(&pair).unwrap();
        let main = prog.function(FuncId::MAIN).unwrap();
        // Should have 3 instructions: const 1, const 2, pair
        assert!(main.blocks[0].instrs.len() >= 3);
    }

    #[test]
    fn test_lower_fst() {
        let mut lower = Lower::new();
        let pair = Expr::Pair(
            Box::new(Expr::Int(1)),
            Box::new(Expr::Int(2)),
        );
        let fst = Expr::Fst(Box::new(pair));
        let prog = lower.compile(&fst).unwrap();
        assert!(prog.function(FuncId::MAIN).is_some());
    }

    #[test]
    fn test_lower_let() {
        let mut lower = Lower::new();
        let let_expr = Expr::Let(
            "x".to_string(),
            Box::new(Expr::Int(42)),
            Box::new(Expr::Var("x".to_string())),
        );
        let prog = lower.compile(&let_expr).unwrap();
        assert!(prog.function(FuncId::MAIN).is_some());
    }

    #[test]
    fn test_lower_if() {
        let mut lower = Lower::new();
        let if_expr = Expr::If(
            Box::new(Expr::Bool(true)),
            Box::new(Expr::Int(1)),
            Box::new(Expr::Int(2)),
        );
        let prog = lower.compile(&if_expr).unwrap();
        let main = prog.function(FuncId::MAIN).unwrap();
        // Should have multiple blocks: entry, then, else, merge
        assert!(main.blocks.len() >= 4);
    }

    #[test]
    fn test_lower_lambda() {
        let mut lower = Lower::new();
        let lam = Expr::Lam(
            "x".to_string(),
            Ty::Int,
            Box::new(Expr::Var("x".to_string())),
        );
        let prog = lower.compile(&lam).unwrap();
        // Should have main function and lambda function
        assert!(prog.functions.len() >= 2);
    }

    #[test]
    fn test_lower_classify() {
        let mut lower = Lower::new();
        let classify = Expr::Classify(Box::new(Expr::Int(42)));
        let prog = lower.compile(&classify).unwrap();
        let main = prog.function(FuncId::MAIN).unwrap();
        // Check that classify instruction was emitted
        let has_classify = main.blocks[0].instrs.iter().any(|i| {
            matches!(i.instr, Instruction::Classify(_))
        });
        assert!(has_classify);
    }

    // ═══════════════════════════════════════════════════════════════════
    // ADDITIONAL LITERAL TESTS
    // ═══════════════════════════════════════════════════════════════════

    #[test]
    fn test_lower_bool_false() {
        let mut lower = Lower::new();
        let prog = lower.compile(&Expr::Bool(false)).unwrap();
        let main = prog.function(FuncId::MAIN).unwrap();
        let has_false = main.blocks[0].instrs.iter().any(|i| {
            matches!(i.instr, Instruction::Const(Constant::Bool(false)))
        });
        assert!(has_false);
    }

    #[test]
    fn test_lower_string() {
        let mut lower = Lower::new();
        let prog = lower.compile(&Expr::String("hello".to_string())).unwrap();
        let main = prog.function(FuncId::MAIN).unwrap();
        let has_string = main.blocks[0].instrs.iter().any(|i| {
            matches!(&i.instr, Instruction::Const(Constant::String(s)) if s == "hello")
        });
        assert!(has_string);
    }

    // ═══════════════════════════════════════════════════════════════════
    // ADDITIONAL PAIR/SUM TESTS
    // ═══════════════════════════════════════════════════════════════════

    #[test]
    fn test_lower_snd() {
        let mut lower = Lower::new();
        let pair = Expr::Pair(
            Box::new(Expr::Int(1)),
            Box::new(Expr::Int(2)),
        );
        let snd = Expr::Snd(Box::new(pair));
        let prog = lower.compile(&snd).unwrap();
        let main = prog.function(FuncId::MAIN).unwrap();
        let has_snd = main.blocks[0].instrs.iter().any(|i| {
            matches!(i.instr, Instruction::Snd(_))
        });
        assert!(has_snd);
    }

    #[test]
    fn test_lower_inl() {
        let mut lower = Lower::new();
        let inl = Expr::Inl(Box::new(Expr::Int(42)), Ty::Bool);
        let prog = lower.compile(&inl).unwrap();
        let main = prog.function(FuncId::MAIN).unwrap();
        let has_inl = main.blocks[0].instrs.iter().any(|i| {
            matches!(i.instr, Instruction::Inl(_))
        });
        assert!(has_inl);
    }

    #[test]
    fn test_lower_inr() {
        let mut lower = Lower::new();
        let inr = Expr::Inr(Box::new(Expr::Bool(true)), Ty::Int);
        let prog = lower.compile(&inr).unwrap();
        let main = prog.function(FuncId::MAIN).unwrap();
        let has_inr = main.blocks[0].instrs.iter().any(|i| {
            matches!(i.instr, Instruction::Inr(_))
        });
        assert!(has_inr);
    }

    #[test]
    fn test_lower_case() {
        let mut lower = Lower::new();
        let case = Expr::Case(
            Box::new(Expr::Inl(Box::new(Expr::Int(1)), Ty::Bool)),
            "x".to_string(),
            Box::new(Expr::Var("x".to_string())),
            "y".to_string(),
            Box::new(Expr::Int(0)),
        );
        let prog = lower.compile(&case).unwrap();
        let main = prog.function(FuncId::MAIN).unwrap();
        // Case creates multiple blocks
        assert!(main.blocks.len() >= 3);
    }

    // ═══════════════════════════════════════════════════════════════════
    // ADDITIONAL SECURITY TESTS
    // ═══════════════════════════════════════════════════════════════════

    #[test]
    fn test_lower_declassify() {
        let mut lower = Lower::new();
        // Declassify takes a secret value and a proof
        let classified = Box::new(Expr::Classify(Box::new(Expr::Int(42))));
        let proof = Box::new(Expr::Prove(Box::new(Expr::Bool(true))));
        let declassify = Expr::Declassify(classified, proof);
        let prog = lower.compile(&declassify).unwrap();
        let main = prog.function(FuncId::MAIN).unwrap();
        let has_declassify = main.blocks[0].instrs.iter().any(|i| {
            matches!(i.instr, Instruction::Declassify(_, _))
        });
        assert!(has_declassify);
    }

    #[test]
    fn test_lower_prove() {
        let mut lower = Lower::new();
        let prove = Expr::Prove(Box::new(Expr::Bool(true)));
        let prog = lower.compile(&prove).unwrap();
        let main = prog.function(FuncId::MAIN).unwrap();
        let has_prove = main.blocks[0].instrs.iter().any(|i| {
            matches!(i.instr, Instruction::Prove(_))
        });
        assert!(has_prove);
    }

    #[test]
    fn test_lower_require() {
        let mut lower = Lower::new();
        // Require takes an Effect and a body expression
        let require = Expr::Require(Effect::Read, Box::new(Expr::Unit));
        let prog = lower.compile(&require).unwrap();
        let main = prog.function(FuncId::MAIN).unwrap();
        let has_require = main.blocks[0].instrs.iter().any(|i| {
            matches!(i.instr, Instruction::RequireCap(_))
        });
        assert!(has_require);
    }

    // ═══════════════════════════════════════════════════════════════════
    // EFFECT TESTS
    // ═══════════════════════════════════════════════════════════════════

    #[test]
    fn test_lower_grant() {
        let mut lower = Lower::new();
        let grant = Expr::Grant(
            Effect::Read,
            Box::new(Expr::Unit),
        );
        let prog = lower.compile(&grant).unwrap();
        let main = prog.function(FuncId::MAIN).unwrap();
        let has_grant = main.blocks[0].instrs.iter().any(|i| {
            matches!(i.instr, Instruction::GrantCap(Effect::Read))
        });
        assert!(has_grant);
    }

    // ═══════════════════════════════════════════════════════════════════
    // REFERENCE TESTS
    // ═══════════════════════════════════════════════════════════════════

    #[test]
    fn test_lower_ref() {
        let mut lower = Lower::new();
        let ref_expr = Expr::Ref(Box::new(Expr::Int(42)), SecurityLevel::Public);
        let prog = lower.compile(&ref_expr).unwrap();
        let main = prog.function(FuncId::MAIN).unwrap();
        let has_alloc = main.blocks[0].instrs.iter().any(|i| {
            matches!(i.instr, Instruction::Alloc { .. })
        });
        assert!(has_alloc);
    }

    #[test]
    fn test_lower_deref() {
        let mut lower = Lower::new();
        let deref = Expr::Deref(Box::new(Expr::Ref(Box::new(Expr::Int(42)), SecurityLevel::Public)));
        let prog = lower.compile(&deref).unwrap();
        let main = prog.function(FuncId::MAIN).unwrap();
        let has_load = main.blocks[0].instrs.iter().any(|i| {
            matches!(i.instr, Instruction::Load(_))
        });
        assert!(has_load);
    }

    // ═══════════════════════════════════════════════════════════════════
    // NESTED STRUCTURE TESTS
    // ═══════════════════════════════════════════════════════════════════

    #[test]
    fn test_lower_nested_let() {
        let mut lower = Lower::new();
        let nested = Expr::Let(
            "x".to_string(),
            Box::new(Expr::Int(1)),
            Box::new(Expr::Let(
                "y".to_string(),
                Box::new(Expr::Int(2)),
                Box::new(Expr::Var("x".to_string())),
            )),
        );
        let prog = lower.compile(&nested).unwrap();
        assert!(prog.function(FuncId::MAIN).is_some());
    }

    #[test]
    fn test_lower_nested_pair() {
        let mut lower = Lower::new();
        let nested = Expr::Pair(
            Box::new(Expr::Pair(
                Box::new(Expr::Int(1)),
                Box::new(Expr::Int(2)),
            )),
            Box::new(Expr::Int(3)),
        );
        let prog = lower.compile(&nested).unwrap();
        let main = prog.function(FuncId::MAIN).unwrap();
        // Should have multiple pair instructions
        let pair_count = main.blocks[0].instrs.iter()
            .filter(|i| matches!(i.instr, Instruction::Pair(_, _)))
            .count();
        assert!(pair_count >= 2);
    }
}
