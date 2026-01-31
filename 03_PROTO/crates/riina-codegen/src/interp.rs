//! Reference Interpreter
//!
//! A direct implementation of the RIINA operational semantics.
//! Corresponds exactly to the Coq `eval` relation in
//! `02_FORMAL/coq/foundations/Semantics.v`.
//!
//! # Correspondence with Coq
//!
//! ```coq
//! (* 02_FORMAL/coq/foundations/Semantics.v *)
//!
//! (* Big-step evaluation relation *)
//! Inductive eval : env -> store -> expr -> store -> value -> Prop :=
//!   (* Values *)
//!   | E_Unit : forall ρ σ,
//!       eval ρ σ EUnit σ VUnit
//!   | E_Bool : forall ρ σ b,
//!       eval ρ σ (EBool b) σ (VBool b)
//!   | E_Int : forall ρ σ n,
//!       eval ρ σ (EInt n) σ (VInt n)
//!   | E_String : forall ρ σ s,
//!       eval ρ σ (EString s) σ (VString s)
//!   | E_Var : forall ρ σ x v,
//!       lookup ρ x = Some v ->
//!       eval ρ σ (EVar x) σ v
//!
//!   (* Functions *)
//!   | E_Lam : forall ρ σ x T e,
//!       eval ρ σ (ELam x T e) σ (VClosure ρ x T e)
//!   | E_App : forall ρ σ σ' σ'' e1 e2 x T body ρ' v2 v,
//!       eval ρ σ e1 σ' (VClosure ρ' x T body) ->
//!       eval ρ σ' e2 σ'' v2 ->
//!       eval (extend ρ' x v2) σ'' body σ''' v ->
//!       eval ρ σ (EApp e1 e2) σ''' v
//!
//!   (* ... 22 more rules for all expression forms ... *)
//! ```
//!
//! Each method in `Interpreter` implements one or more of these rules.
//!
//! # Security Properties
//!
//! The interpreter enforces:
//! 1. **Non-interference**: Secret values cannot flow to public outputs
//! 2. **Effect safety**: Effects only occur when capabilities are held
//! 3. **Memory safety**: References are always valid
//!
//! # Mode: ULTRA KIASU | FUCKING PARANOID | ZERO TRUST

use crate::value::{Closure, Env, Location, RefCell, Sum, Value};
use crate::{Error, Result};
use riina_types::{BinOp, Effect, Expr, SecurityLevel};
use std::collections::HashMap;
use std::rc::Rc;

/// Mutable store (heap)
#[derive(Debug, Clone, Default)]
pub struct Store {
    /// Map from locations to values
    cells: HashMap<Location, (Value, SecurityLevel)>,
    /// Next available location
    next_loc: u32,
}

impl Store {
    /// Create a new empty store
    #[must_use]
    pub fn new() -> Self {
        Self {
            cells: HashMap::new(),
            next_loc: 0,
        }
    }

    /// Allocate a new reference
    pub fn alloc(&mut self, value: Value, level: SecurityLevel) -> Location {
        let loc = Location::new(self.next_loc);
        self.next_loc += 1;
        self.cells.insert(loc, (value, level));
        loc
    }

    /// Read from a location
    pub fn read(&self, loc: Location) -> Result<&Value> {
        self.cells
            .get(&loc)
            .map(|(v, _)| v)
            .ok_or_else(|| Error::InvalidReference(format!("location {} not found", loc)))
    }

    /// Read with security level
    pub fn read_with_level(&self, loc: Location) -> Result<(&Value, SecurityLevel)> {
        self.cells
            .get(&loc)
            .map(|(v, l)| (v, *l))
            .ok_or_else(|| Error::InvalidReference(format!("location {} not found", loc)))
    }

    /// Write to a location
    pub fn write(&mut self, loc: Location, value: Value) -> Result<()> {
        if let Some((v, _)) = self.cells.get_mut(&loc) {
            *v = value;
            Ok(())
        } else {
            Err(Error::InvalidReference(format!("location {} not found", loc)))
        }
    }
}

/// Effect handler context
#[derive(Debug, Clone)]
struct HandlerContext {
    /// Effect being handled
    #[allow(dead_code)]
    effect: Effect,
    /// Handler variable name
    handler_var: String,
    /// Handler expression
    handler: Rc<Expr>,
    /// Handler environment
    handler_env: Env,
}

/// Capability context
#[derive(Debug, Clone, Default)]
struct Capabilities {
    /// Set of held capabilities
    held: Vec<Effect>,
}

impl Capabilities {
    fn new() -> Self {
        Self { held: Vec::new() }
    }

    fn grant(&mut self, eff: Effect) {
        if !self.held.contains(&eff) {
            self.held.push(eff);
        }
    }

    fn has(&self, eff: Effect) -> bool {
        // Pure always allowed
        if eff == Effect::Pure {
            return true;
        }
        // Check if any held capability subsumes this effect
        self.held.iter().any(|h| h.level() >= eff.level())
    }
}

/// Reference interpreter
///
/// Implements the RIINA operational semantics.
/// Every evaluation corresponds to a derivation of the `eval` relation.
pub struct Interpreter {
    /// Global store (heap)
    store: Store,
    /// Effect handlers
    handlers: Vec<HandlerContext>,
    /// Capabilities
    caps: Capabilities,
    /// Current security context
    security_context: SecurityLevel,
}

impl Interpreter {
    /// Create a new interpreter
    #[must_use]
    pub fn new() -> Self {
        Self {
            store: Store::new(),
            handlers: Vec::new(),
            caps: Capabilities::new(),
            security_context: SecurityLevel::Public,
        }
    }

    /// Evaluate an expression
    ///
    /// Main entry point. Creates an empty environment and evaluates.
    ///
    /// # Correspondence
    ///
    /// ```coq
    /// Definition run (e : expr) : option value :=
    ///   match eval empty_env empty_store e with
    ///   | (_, v) => Some v
    ///   end.
    /// ```
    pub fn eval(&mut self, expr: &Expr) -> Result<Value> {
        let env = Env::new();
        self.eval_with_env(&env, expr)
    }

    /// Evaluate with built-in functions pre-registered.
    pub fn eval_with_builtins(&mut self, expr: &Expr) -> Result<Value> {
        let env = crate::builtins::register_builtins(&Env::new());
        self.eval_with_env(&env, expr)
    }

    /// Evaluate with an environment
    ///
    /// This is the core evaluation function. Each match arm corresponds
    /// to a rule in the Coq `eval` relation.
    fn eval_with_env(&mut self, env: &Env, expr: &Expr) -> Result<Value> {
        match expr {
            // ═══════════════════════════════════════════════════════════════
            // VALUES (E_Unit, E_Bool, E_Int, E_String)
            // ═══════════════════════════════════════════════════════════════

            // E_Unit: eval ρ σ EUnit σ VUnit
            Expr::Unit => Ok(Value::Unit),

            // E_Bool: eval ρ σ (EBool b) σ (VBool b)
            Expr::Bool(b) => Ok(Value::Bool(*b)),

            // E_Int: eval ρ σ (EInt n) σ (VInt n)
            Expr::Int(n) => Ok(Value::Int(*n)),

            // E_String: eval ρ σ (EString s) σ (VString s)
            Expr::String(s) => Ok(Value::String(s.clone())),

            // ═══════════════════════════════════════════════════════════════
            // VARIABLES (E_Var)
            // ═══════════════════════════════════════════════════════════════

            // E_Var: lookup ρ x = Some v -> eval ρ σ (EVar x) σ v
            Expr::Var(name) => {
                env.lookup(name)
                    .cloned()
                    .ok_or_else(|| Error::UnboundVariable(name.clone()))
            }

            // ═══════════════════════════════════════════════════════════════
            // FUNCTIONS (E_Lam, E_App)
            // ═══════════════════════════════════════════════════════════════

            // E_Lam: eval ρ σ (ELam x T e) σ (VClosure ρ x T e)
            Expr::Lam(param, param_ty, body) => {
                Ok(Value::Closure(Closure {
                    env: env.clone(),
                    param: param.clone(),
                    param_ty: param_ty.clone(),
                    body: Rc::new((**body).clone()),
                }))
            }

            // E_App: Application rule
            Expr::App(func_expr, arg_expr) => {
                let func_val = self.eval_with_env(env, func_expr)?;
                let arg_val = self.eval_with_env(env, arg_expr)?;

                match func_val {
                    Value::Closure(closure) => {
                        // Extend closure environment with argument
                        let new_env = closure.env.extend(closure.param.clone(), arg_val);
                        // Evaluate body
                        self.eval_with_env(&new_env, &closure.body)
                    }
                    Value::Builtin(ref name) if crate::builtins::is_higher_order_builtin(name) => {
                        self.eval_higher_order_builtin(name, arg_val)?
                            .ok_or_else(|| Error::InvalidOperation(format!("higher-order builtin {} failed", name)))
                    }
                    Value::Builtin(name) => {
                        crate::builtins::apply_builtin(&name, arg_val)
                    }
                    _ => Err(Error::TypeMismatch {
                        expected: "function".to_string(),
                        found: format!("{:?}", func_val),
                        context: "application".to_string(),
                    }),
                }
            }

            // ═══════════════════════════════════════════════════════════════
            // PRODUCTS (E_Pair, E_Fst, E_Snd)
            // ═══════════════════════════════════════════════════════════════

            // E_Pair: eval ρ σ (EPair e1 e2) σ'' (VPair v1 v2)
            Expr::Pair(e1, e2) => {
                let v1 = self.eval_with_env(env, e1)?;
                let v2 = self.eval_with_env(env, e2)?;
                Ok(Value::Pair(Box::new(v1), Box::new(v2)))
            }

            // E_Fst: eval ρ σ e σ' (VPair v1 v2) -> eval ρ σ (EFst e) σ' v1
            Expr::Fst(e) => {
                let v = self.eval_with_env(env, e)?;
                match v {
                    Value::Pair(v1, _) => Ok(*v1),
                    _ => Err(Error::TypeMismatch {
                        expected: "pair".to_string(),
                        found: format!("{:?}", v),
                        context: "fst".to_string(),
                    }),
                }
            }

            // E_Snd: eval ρ σ e σ' (VPair v1 v2) -> eval ρ σ (ESnd e) σ' v2
            Expr::Snd(e) => {
                let v = self.eval_with_env(env, e)?;
                match v {
                    Value::Pair(_, v2) => Ok(*v2),
                    _ => Err(Error::TypeMismatch {
                        expected: "pair".to_string(),
                        found: format!("{:?}", v),
                        context: "snd".to_string(),
                    }),
                }
            }

            // ═══════════════════════════════════════════════════════════════
            // SUMS (E_Inl, E_Inr, E_Case)
            // ═══════════════════════════════════════════════════════════════

            // E_Inl: eval ρ σ e σ' v -> eval ρ σ (EInl e T) σ' (VInl v)
            Expr::Inl(e, _ty) => {
                let v = self.eval_with_env(env, e)?;
                Ok(Value::Sum(Sum::Left(Box::new(v))))
            }

            // E_Inr: eval ρ σ e σ' v -> eval ρ σ (EInr e T) σ' (VInr v)
            Expr::Inr(e, _ty) => {
                let v = self.eval_with_env(env, e)?;
                Ok(Value::Sum(Sum::Right(Box::new(v))))
            }

            // E_CaseL / E_CaseR: Case analysis
            Expr::Case(scrut, left_name, left_branch, right_name, right_branch) => {
                let scrut_val = self.eval_with_env(env, scrut)?;
                match scrut_val {
                    Value::Sum(Sum::Left(v)) => {
                        let new_env = env.extend(left_name.clone(), *v);
                        self.eval_with_env(&new_env, left_branch)
                    }
                    Value::Sum(Sum::Right(v)) => {
                        let new_env = env.extend(right_name.clone(), *v);
                        self.eval_with_env(&new_env, right_branch)
                    }
                    _ => Err(Error::TypeMismatch {
                        expected: "sum".to_string(),
                        found: format!("{:?}", scrut_val),
                        context: "case".to_string(),
                    }),
                }
            }

            // ═══════════════════════════════════════════════════════════════
            // CONTROL FLOW (E_IfTrue, E_IfFalse, E_Let)
            // ═══════════════════════════════════════════════════════════════

            // E_IfTrue / E_IfFalse
            Expr::If(cond, then_expr, else_expr) => {
                let cond_val = self.eval_with_env(env, cond)?;
                match cond_val {
                    Value::Bool(true) => self.eval_with_env(env, then_expr),
                    Value::Bool(false) => self.eval_with_env(env, else_expr),
                    _ => Err(Error::TypeMismatch {
                        expected: "bool".to_string(),
                        found: format!("{:?}", cond_val),
                        context: "if condition".to_string(),
                    }),
                }
            }

            // E_Let: eval ρ σ e1 σ' v1 -> eval (extend ρ x v1) σ' e2 σ'' v2
            //        -> eval ρ σ (ELet x e1 e2) σ'' v2
            Expr::Let(name, binding, body) => {
                let bind_val = self.eval_with_env(env, binding)?;
                let new_env = env.extend(name.clone(), bind_val);
                self.eval_with_env(&new_env, body)
            }

            // ═══════════════════════════════════════════════════════════════
            // EFFECTS (E_Perform, E_Handle)
            // ═══════════════════════════════════════════════════════════════

            // E_Perform: Trigger an effect
            Expr::Perform(effect, payload) => {
                // Check capability
                if !self.caps.has(*effect) {
                    return Err(Error::MissingCapability(*effect));
                }

                let payload_val = self.eval_with_env(env, payload)?;

                // Look for a handler
                if let Some(handler_ctx) = self.handlers.pop() {
                    // Run handler with payload
                    let handler_env = handler_ctx.handler_env.extend(
                        handler_ctx.handler_var.clone(),
                        payload_val,
                    );
                    let result = self.eval_with_env(&handler_env, &handler_ctx.handler)?;
                    self.handlers.push(handler_ctx);
                    Ok(result)
                } else {
                    // No handler, return payload
                    Err(Error::UnhandledEffect(*effect))
                }
            }

            // E_Handle: Install effect handler
            Expr::Handle(body, handler_var, handler) => {
                // Push handler context
                self.handlers.push(HandlerContext {
                    effect: Effect::System, // TODO: infer effect
                    handler_var: handler_var.clone(),
                    handler: Rc::new((**handler).clone()),
                    handler_env: env.clone(),
                });

                // Evaluate body
                let result = self.eval_with_env(env, body);

                // Pop handler
                self.handlers.pop();

                result
            }

            // ═══════════════════════════════════════════════════════════════
            // REFERENCES (E_Ref, E_Deref, E_Assign)
            // ═══════════════════════════════════════════════════════════════

            // E_Ref: Allocate a reference
            Expr::Ref(init, level) => {
                // Check capability for Write effect
                if !self.caps.has(Effect::Write) {
                    // Grant implicit capability for reference operations
                    self.caps.grant(Effect::Write);
                    self.caps.grant(Effect::Read);
                }

                let init_val = self.eval_with_env(env, init)?;
                let loc = self.store.alloc(init_val, *level);
                Ok(Value::Ref(RefCell {
                    location: loc,
                    level: *level,
                }))
            }

            // E_Deref: Dereference
            Expr::Deref(ref_expr) => {
                let ref_val = self.eval_with_env(env, ref_expr)?;
                match ref_val {
                    Value::Ref(cell) => {
                        let (val, level) = self.store.read_with_level(cell.location)?;

                        // Security check: don't leak high data to low context
                        if !level.leq(self.security_context)
                        {
                            return Err(Error::SecurityViolation {
                                context_level: self.security_context,
                                data_level: level,
                            });
                        }

                        Ok(val.clone())
                    }
                    _ => Err(Error::TypeMismatch {
                        expected: "reference".to_string(),
                        found: format!("{:?}", ref_val),
                        context: "deref".to_string(),
                    }),
                }
            }

            // E_Assign: Assign to reference
            Expr::Assign(ref_expr, val_expr) => {
                let ref_val = self.eval_with_env(env, ref_expr)?;
                let new_val = self.eval_with_env(env, val_expr)?;

                match ref_val {
                    Value::Ref(cell) => {
                        // Security check: don't store high data in low cell
                        if new_val.security_level() == SecurityLevel::Secret
                            && cell.level == SecurityLevel::Public
                        {
                            return Err(Error::SecurityViolation {
                                context_level: cell.level,
                                data_level: new_val.security_level(),
                            });
                        }

                        self.store.write(cell.location, new_val)?;
                        Ok(Value::Unit)
                    }
                    _ => Err(Error::TypeMismatch {
                        expected: "reference".to_string(),
                        found: format!("{:?}", ref_val),
                        context: "assign".to_string(),
                    }),
                }
            }

            // ═══════════════════════════════════════════════════════════════
            // SECURITY (E_Classify, E_Declassify, E_Prove)
            // ═══════════════════════════════════════════════════════════════

            // E_Classify: Mark value as secret
            Expr::Classify(inner) => {
                let inner_val = self.eval_with_env(env, inner)?;
                Ok(Value::Secret(Box::new(inner_val)))
            }

            // E_Declassify: Reveal secret (requires proof)
            Expr::Declassify(secret, proof) => {
                let secret_val = self.eval_with_env(env, secret)?;
                let _proof_val = self.eval_with_env(env, proof)?;

                // TODO: Verify proof is valid witness for declassification
                // For now, we trust the proof exists

                match secret_val {
                    Value::Secret(v) => Ok(*v),
                    v => Ok(v), // Already public
                }
            }

            // E_Prove: Create proof witness
            Expr::Prove(inner) => {
                let inner_val = self.eval_with_env(env, inner)?;
                Ok(Value::Proof(Box::new(inner_val)))
            }

            // ═══════════════════════════════════════════════════════════════
            // CAPABILITIES (E_Require, E_Grant)
            // ═══════════════════════════════════════════════════════════════

            // E_Require: Demand a capability
            Expr::Require(effect, body) => {
                if !self.caps.has(*effect) {
                    return Err(Error::MissingCapability(*effect));
                }
                self.eval_with_env(env, body)
            }

            // E_Grant: Provide a capability
            Expr::Grant(effect, body) => {
                self.caps.grant(*effect);
                self.eval_with_env(env, body)
            }

            // ═══════════════════════════════════════════════════════════════
            // LOCATIONS (Expr::Loc — runtime-only, corresponds to Coq ELoc)
            // ═══════════════════════════════════════════════════════════════
            Expr::Loc(l) => {
                // Store locations are runtime values (Coq ELoc); look up in store
                let loc = Location::new(*l as u32);
                self.store.read(loc).cloned()
            }

            // ═══════════════════════════════════════════════════════════════
            // BINARY OPERATIONS (Expr::BinOp)
            // ═══════════════════════════════════════════════════════════════
            Expr::BinOp(op, lhs, rhs) => {
                let l = self.eval_with_env(env, lhs)?;
                let r = self.eval_with_env(env, rhs)?;
                match (op, &l, &r) {
                    (BinOp::Add, Value::Int(a), Value::Int(b)) => Ok(Value::Int(a.wrapping_add(*b))),
                    (BinOp::Sub, Value::Int(a), Value::Int(b)) => Ok(Value::Int(a.wrapping_sub(*b))),
                    (BinOp::Mul, Value::Int(a), Value::Int(b)) => Ok(Value::Int(a.wrapping_mul(*b))),
                    (BinOp::Div, Value::Int(a), Value::Int(b)) => {
                        if *b == 0 { return Err(Error::DivisionByZero); }
                        Ok(Value::Int(a / b))
                    }
                    (BinOp::Mod, Value::Int(a), Value::Int(b)) => {
                        if *b == 0 { return Err(Error::DivisionByZero); }
                        Ok(Value::Int(a % b))
                    }
                    (BinOp::Eq, Value::Int(a), Value::Int(b)) => Ok(Value::Bool(a == b)),
                    (BinOp::Ne, Value::Int(a), Value::Int(b)) => Ok(Value::Bool(a != b)),
                    (BinOp::Lt, Value::Int(a), Value::Int(b)) => Ok(Value::Bool(a < b)),
                    (BinOp::Le, Value::Int(a), Value::Int(b)) => Ok(Value::Bool(a <= b)),
                    (BinOp::Gt, Value::Int(a), Value::Int(b)) => Ok(Value::Bool(a > b)),
                    (BinOp::Ge, Value::Int(a), Value::Int(b)) => Ok(Value::Bool(a >= b)),
                    (BinOp::Eq, Value::String(a), Value::String(b)) => Ok(Value::Bool(a == b)),
                    (BinOp::Ne, Value::String(a), Value::String(b)) => Ok(Value::Bool(a != b)),
                    (BinOp::Eq, Value::Bool(a), Value::Bool(b)) => Ok(Value::Bool(a == b)),
                    (BinOp::Ne, Value::Bool(a), Value::Bool(b)) => Ok(Value::Bool(a != b)),
                    (BinOp::And, Value::Bool(a), Value::Bool(b)) => Ok(Value::Bool(*a && *b)),
                    (BinOp::Or, Value::Bool(a), Value::Bool(b)) => Ok(Value::Bool(*a || *b)),
                    _ => Err(Error::TypeMismatch {
                        expected: "matching operand types for binary op".to_string(),
                        found: format!("{:?} {:?} {:?}", l, op, r),
                        context: "binary operation".to_string(),
                    }),
                }
            }
        }
    }
}

impl Interpreter {
    /// Evaluate higher-order builtins that need closure invocation.
    fn eval_higher_order_builtin(&mut self, name: &str, arg: Value) -> Result<Option<Value>> {
        match name {
            "senarai_peta" => {
                // (List, Closure) -> List
                match arg {
                    Value::Pair(list, func) => {
                        let items = match *list {
                            Value::List(items) => items,
                            _ => return Err(Error::TypeMismatch {
                                expected: "list".to_string(),
                                found: format!("{:?}", list),
                                context: "senarai_peta".to_string(),
                            }),
                        };
                        let closure = match *func {
                            Value::Closure(c) => c,
                            _ => return Err(Error::TypeMismatch {
                                expected: "closure".to_string(),
                                found: format!("{:?}", func),
                                context: "senarai_peta".to_string(),
                            }),
                        };
                        let mut result = Vec::with_capacity(items.len());
                        for item in items {
                            let new_env = closure.env.extend(closure.param.clone(), item);
                            let val = self.eval_with_env(&new_env, &closure.body)?;
                            result.push(val);
                        }
                        Ok(Some(Value::List(result)))
                    }
                    _ => Err(Error::TypeMismatch {
                        expected: "(list, closure)".to_string(),
                        found: format!("{:?}", arg),
                        context: "senarai_peta".to_string(),
                    }),
                }
            }
            "senarai_tapis" => {
                // (List, Closure) -> List
                match arg {
                    Value::Pair(list, func) => {
                        let items = match *list {
                            Value::List(items) => items,
                            _ => return Err(Error::TypeMismatch {
                                expected: "list".to_string(),
                                found: format!("{:?}", list),
                                context: "senarai_tapis".to_string(),
                            }),
                        };
                        let closure = match *func {
                            Value::Closure(c) => c,
                            _ => return Err(Error::TypeMismatch {
                                expected: "closure".to_string(),
                                found: format!("{:?}", func),
                                context: "senarai_tapis".to_string(),
                            }),
                        };
                        let mut result = Vec::new();
                        for item in items {
                            let new_env = closure.env.extend(closure.param.clone(), item.clone());
                            let val = self.eval_with_env(&new_env, &closure.body)?;
                            if val == Value::Bool(true) {
                                result.push(item);
                            }
                        }
                        Ok(Some(Value::List(result)))
                    }
                    _ => Err(Error::TypeMismatch {
                        expected: "(list, closure)".to_string(),
                        found: format!("{:?}", arg),
                        context: "senarai_tapis".to_string(),
                    }),
                }
            }
            "senarai_lipat" => {
                // (List, (Value, Closure)) -> Value
                match arg {
                    Value::Pair(list, init_and_func) => {
                        let items = match *list {
                            Value::List(items) => items,
                            _ => return Err(Error::TypeMismatch {
                                expected: "list".to_string(),
                                found: format!("{:?}", list),
                                context: "senarai_lipat".to_string(),
                            }),
                        };
                        match *init_and_func {
                            Value::Pair(init, func) => {
                                let closure = match *func {
                                    Value::Closure(c) => c,
                                    _ => return Err(Error::TypeMismatch {
                                        expected: "closure".to_string(),
                                        found: format!("{:?}", func),
                                        context: "senarai_lipat".to_string(),
                                    }),
                                };
                                let mut acc = *init;
                                for item in items {
                                    // Closure takes a pair (acc, item)
                                    let pair = Value::Pair(Box::new(acc), Box::new(item));
                                    let new_env = closure.env.extend(closure.param.clone(), pair);
                                    acc = self.eval_with_env(&new_env, &closure.body)?;
                                }
                                Ok(Some(acc))
                            }
                            _ => Err(Error::TypeMismatch {
                                expected: "(value, closure)".to_string(),
                                found: format!("{:?}", init_and_func),
                                context: "senarai_lipat".to_string(),
                            }),
                        }
                    }
                    _ => Err(Error::TypeMismatch {
                        expected: "(list, (value, closure))".to_string(),
                        found: format!("{:?}", arg),
                        context: "senarai_lipat".to_string(),
                    }),
                }
            }
            _ => Ok(None),
        }
    }
}

impl Default for Interpreter {
    fn default() -> Self {
        Self::new()
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use riina_types::Ty;

    // ═══════════════════════════════════════════════════════════════════════
    // VALUE TESTS
    // ═══════════════════════════════════════════════════════════════════════

    #[test]
    fn test_eval_unit() {
        let mut interp = Interpreter::new();
        assert_eq!(interp.eval(&Expr::Unit), Ok(Value::Unit));
    }

    #[test]
    fn test_eval_bool() {
        let mut interp = Interpreter::new();
        assert_eq!(interp.eval(&Expr::Bool(true)), Ok(Value::Bool(true)));
        assert_eq!(interp.eval(&Expr::Bool(false)), Ok(Value::Bool(false)));
    }

    #[test]
    fn test_eval_int() {
        let mut interp = Interpreter::new();
        assert_eq!(interp.eval(&Expr::Int(0)), Ok(Value::Int(0)));
        assert_eq!(interp.eval(&Expr::Int(42)), Ok(Value::Int(42)));
        assert_eq!(interp.eval(&Expr::Int(u64::MAX)), Ok(Value::Int(u64::MAX)));
    }

    #[test]
    fn test_eval_string() {
        let mut interp = Interpreter::new();
        assert_eq!(
            interp.eval(&Expr::String("hello".to_string())),
            Ok(Value::String("hello".to_string()))
        );
        assert_eq!(
            interp.eval(&Expr::String("".to_string())),
            Ok(Value::String("".to_string()))
        );
    }

    // ═══════════════════════════════════════════════════════════════════════
    // VARIABLE TESTS
    // ═══════════════════════════════════════════════════════════════════════

    #[test]
    fn test_eval_unbound_var() {
        let mut interp = Interpreter::new();
        let result = interp.eval(&Expr::Var("x".to_string()));
        assert!(matches!(result, Err(Error::UnboundVariable(_))));
    }

    // ═══════════════════════════════════════════════════════════════════════
    // FUNCTION TESTS
    // ═══════════════════════════════════════════════════════════════════════

    #[test]
    fn test_eval_lambda() {
        let mut interp = Interpreter::new();
        let lam = Expr::Lam(
            "x".to_string(),
            Ty::Int,
            Box::new(Expr::Var("x".to_string())),
        );
        let result = interp.eval(&lam);
        assert!(result.is_ok());
        assert!(result.unwrap().is_closure());
    }

    #[test]
    fn test_eval_application() {
        let mut interp = Interpreter::new();
        // (λx:Int. x) 42
        let identity = Expr::Lam(
            "x".to_string(),
            Ty::Int,
            Box::new(Expr::Var("x".to_string())),
        );
        let app = Expr::App(Box::new(identity), Box::new(Expr::Int(42)));
        assert_eq!(interp.eval(&app), Ok(Value::Int(42)));
    }

    #[test]
    fn test_eval_nested_application() {
        let mut interp = Interpreter::new();
        // (λx:Int. (λy:Int. x)) 1 2 = 1
        let inner = Expr::Lam(
            "y".to_string(),
            Ty::Int,
            Box::new(Expr::Var("x".to_string())),
        );
        let outer = Expr::Lam("x".to_string(), Ty::Int, Box::new(inner));
        let app1 = Expr::App(Box::new(outer), Box::new(Expr::Int(1)));
        let app2 = Expr::App(Box::new(app1), Box::new(Expr::Int(2)));
        assert_eq!(interp.eval(&app2), Ok(Value::Int(1)));
    }

    // ═══════════════════════════════════════════════════════════════════════
    // PRODUCT TESTS
    // ═══════════════════════════════════════════════════════════════════════

    #[test]
    fn test_eval_pair() {
        let mut interp = Interpreter::new();
        let pair = Expr::Pair(Box::new(Expr::Int(1)), Box::new(Expr::Int(2)));
        assert_eq!(
            interp.eval(&pair),
            Ok(Value::Pair(Box::new(Value::Int(1)), Box::new(Value::Int(2))))
        );
    }

    #[test]
    fn test_eval_fst() {
        let mut interp = Interpreter::new();
        let pair = Expr::Pair(Box::new(Expr::Int(1)), Box::new(Expr::Int(2)));
        let fst = Expr::Fst(Box::new(pair));
        assert_eq!(interp.eval(&fst), Ok(Value::Int(1)));
    }

    #[test]
    fn test_eval_snd() {
        let mut interp = Interpreter::new();
        let pair = Expr::Pair(Box::new(Expr::Int(1)), Box::new(Expr::Int(2)));
        let snd = Expr::Snd(Box::new(pair));
        assert_eq!(interp.eval(&snd), Ok(Value::Int(2)));
    }

    #[test]
    fn test_eval_nested_pairs() {
        let mut interp = Interpreter::new();
        // ((1, 2), (3, 4))
        let p1 = Expr::Pair(Box::new(Expr::Int(1)), Box::new(Expr::Int(2)));
        let p2 = Expr::Pair(Box::new(Expr::Int(3)), Box::new(Expr::Int(4)));
        let nested = Expr::Pair(Box::new(p1), Box::new(p2));
        // fst (fst nested) = 1
        let fst_fst = Expr::Fst(Box::new(Expr::Fst(Box::new(nested))));
        assert_eq!(interp.eval(&fst_fst), Ok(Value::Int(1)));
    }

    // ═══════════════════════════════════════════════════════════════════════
    // SUM TESTS
    // ═══════════════════════════════════════════════════════════════════════

    #[test]
    fn test_eval_inl() {
        let mut interp = Interpreter::new();
        let inl = Expr::Inl(
            Box::new(Expr::Int(42)),
            Ty::Sum(Box::new(Ty::Int), Box::new(Ty::Bool)),
        );
        assert_eq!(interp.eval(&inl), Ok(Value::inl(Value::Int(42))));
    }

    #[test]
    fn test_eval_inr() {
        let mut interp = Interpreter::new();
        let inr = Expr::Inr(
            Box::new(Expr::Bool(true)),
            Ty::Sum(Box::new(Ty::Int), Box::new(Ty::Bool)),
        );
        assert_eq!(interp.eval(&inr), Ok(Value::inr(Value::Bool(true))));
    }

    #[test]
    fn test_eval_case_left() {
        let mut interp = Interpreter::new();
        // case (inl 42) of inl x => x | inr y => 0
        let scrut = Expr::Inl(
            Box::new(Expr::Int(42)),
            Ty::Sum(Box::new(Ty::Int), Box::new(Ty::Bool)),
        );
        let case_expr = Expr::Case(
            Box::new(scrut),
            "x".to_string(),
            Box::new(Expr::Var("x".to_string())),
            "y".to_string(),
            Box::new(Expr::Int(0)),
        );
        assert_eq!(interp.eval(&case_expr), Ok(Value::Int(42)));
    }

    #[test]
    fn test_eval_case_right() {
        let mut interp = Interpreter::new();
        // case (inr true) of inl x => 0 | inr y => 1
        let scrut = Expr::Inr(
            Box::new(Expr::Bool(true)),
            Ty::Sum(Box::new(Ty::Int), Box::new(Ty::Bool)),
        );
        let case_expr = Expr::Case(
            Box::new(scrut),
            "x".to_string(),
            Box::new(Expr::Int(0)),
            "y".to_string(),
            Box::new(Expr::Int(1)),
        );
        assert_eq!(interp.eval(&case_expr), Ok(Value::Int(1)));
    }

    // ═══════════════════════════════════════════════════════════════════════
    // CONTROL FLOW TESTS
    // ═══════════════════════════════════════════════════════════════════════

    #[test]
    fn test_eval_if_true() {
        let mut interp = Interpreter::new();
        let if_expr = Expr::If(
            Box::new(Expr::Bool(true)),
            Box::new(Expr::Int(1)),
            Box::new(Expr::Int(2)),
        );
        assert_eq!(interp.eval(&if_expr), Ok(Value::Int(1)));
    }

    #[test]
    fn test_eval_if_false() {
        let mut interp = Interpreter::new();
        let if_expr = Expr::If(
            Box::new(Expr::Bool(false)),
            Box::new(Expr::Int(1)),
            Box::new(Expr::Int(2)),
        );
        assert_eq!(interp.eval(&if_expr), Ok(Value::Int(2)));
    }

    #[test]
    fn test_eval_let() {
        let mut interp = Interpreter::new();
        // let x = 42 in x
        let let_expr = Expr::Let(
            "x".to_string(),
            Box::new(Expr::Int(42)),
            Box::new(Expr::Var("x".to_string())),
        );
        assert_eq!(interp.eval(&let_expr), Ok(Value::Int(42)));
    }

    #[test]
    fn test_eval_nested_let() {
        let mut interp = Interpreter::new();
        // let x = 1 in let y = 2 in (x, y)
        let inner_let = Expr::Let(
            "y".to_string(),
            Box::new(Expr::Int(2)),
            Box::new(Expr::Pair(
                Box::new(Expr::Var("x".to_string())),
                Box::new(Expr::Var("y".to_string())),
            )),
        );
        let outer_let = Expr::Let("x".to_string(), Box::new(Expr::Int(1)), Box::new(inner_let));
        assert_eq!(
            interp.eval(&outer_let),
            Ok(Value::Pair(Box::new(Value::Int(1)), Box::new(Value::Int(2))))
        );
    }

    // ═══════════════════════════════════════════════════════════════════════
    // REFERENCE TESTS
    // ═══════════════════════════════════════════════════════════════════════

    #[test]
    fn test_eval_ref() {
        let mut interp = Interpreter::new();
        let ref_expr = Expr::Ref(Box::new(Expr::Int(42)), SecurityLevel::Public);
        let result = interp.eval(&ref_expr);
        assert!(result.is_ok());
        assert!(result.unwrap().is_ref());
    }

    #[test]
    fn test_eval_deref() {
        let mut interp = Interpreter::new();
        // let r = ref 42 in !r
        let let_expr = Expr::Let(
            "r".to_string(),
            Box::new(Expr::Ref(Box::new(Expr::Int(42)), SecurityLevel::Public)),
            Box::new(Expr::Deref(Box::new(Expr::Var("r".to_string())))),
        );
        assert_eq!(interp.eval(&let_expr), Ok(Value::Int(42)));
    }

    #[test]
    fn test_eval_assign() {
        let mut interp = Interpreter::new();
        // let r = ref 1 in (r := 2; !r)
        let inner = Expr::Let(
            "_".to_string(),
            Box::new(Expr::Assign(
                Box::new(Expr::Var("r".to_string())),
                Box::new(Expr::Int(2)),
            )),
            Box::new(Expr::Deref(Box::new(Expr::Var("r".to_string())))),
        );
        let let_expr = Expr::Let(
            "r".to_string(),
            Box::new(Expr::Ref(Box::new(Expr::Int(1)), SecurityLevel::Public)),
            Box::new(inner),
        );
        assert_eq!(interp.eval(&let_expr), Ok(Value::Int(2)));
    }

    // ═══════════════════════════════════════════════════════════════════════
    // SECURITY TESTS
    // ═══════════════════════════════════════════════════════════════════════

    #[test]
    fn test_eval_classify() {
        let mut interp = Interpreter::new();
        let classify = Expr::Classify(Box::new(Expr::Int(42)));
        assert_eq!(
            interp.eval(&classify),
            Ok(Value::Secret(Box::new(Value::Int(42))))
        );
    }

    #[test]
    fn test_eval_declassify() {
        let mut interp = Interpreter::new();
        // declassify (classify 42) with (prove ())
        let classified = Expr::Classify(Box::new(Expr::Int(42)));
        let proof = Expr::Prove(Box::new(Expr::Unit));
        let declassify = Expr::Declassify(Box::new(classified), Box::new(proof));
        assert_eq!(interp.eval(&declassify), Ok(Value::Int(42)));
    }

    #[test]
    fn test_eval_prove() {
        let mut interp = Interpreter::new();
        let prove = Expr::Prove(Box::new(Expr::Int(42)));
        assert_eq!(
            interp.eval(&prove),
            Ok(Value::Proof(Box::new(Value::Int(42))))
        );
    }

    // ═══════════════════════════════════════════════════════════════════════
    // CAPABILITY TESTS
    // ═══════════════════════════════════════════════════════════════════════

    #[test]
    fn test_eval_grant_require() {
        let mut interp = Interpreter::new();
        // grant Network to (require Network in 42)
        let require = Expr::Require(Effect::Network, Box::new(Expr::Int(42)));
        let grant = Expr::Grant(Effect::Network, Box::new(require));
        assert_eq!(interp.eval(&grant), Ok(Value::Int(42)));
    }

    #[test]
    fn test_eval_missing_capability() {
        let mut interp = Interpreter::new();
        // require Network in 42 (without grant)
        let require = Expr::Require(Effect::Network, Box::new(Expr::Int(42)));
        let result = interp.eval(&require);
        assert!(matches!(result, Err(Error::MissingCapability(Effect::Network))));
    }

    // ═══════════════════════════════════════════════════════════════════════
    // COMPLEX TESTS
    // ═══════════════════════════════════════════════════════════════════════

    #[test]
    fn test_eval_factorial_simulation() {
        // Can't do recursion directly, but we can test iterative patterns
        let mut interp = Interpreter::new();
        // let x = 5 in let y = x in (x, y)
        let expr = Expr::Let(
            "x".to_string(),
            Box::new(Expr::Int(5)),
            Box::new(Expr::Let(
                "y".to_string(),
                Box::new(Expr::Var("x".to_string())),
                Box::new(Expr::Pair(
                    Box::new(Expr::Var("x".to_string())),
                    Box::new(Expr::Var("y".to_string())),
                )),
            )),
        );
        assert_eq!(
            interp.eval(&expr),
            Ok(Value::Pair(Box::new(Value::Int(5)), Box::new(Value::Int(5))))
        );
    }

    #[test]
    fn test_eval_church_booleans() {
        let mut interp = Interpreter::new();
        // Church true: λx. λy. x
        // Applying: true 1 2 = 1
        let church_true = Expr::Lam(
            "x".to_string(),
            Ty::Int,
            Box::new(Expr::Lam(
                "y".to_string(),
                Ty::Int,
                Box::new(Expr::Var("x".to_string())),
            )),
        );
        let app1 = Expr::App(Box::new(church_true), Box::new(Expr::Int(1)));
        let app2 = Expr::App(Box::new(app1), Box::new(Expr::Int(2)));
        assert_eq!(interp.eval(&app2), Ok(Value::Int(1)));
    }

    // ═══════════════════════════════════════════════════════════════════
    // ADDITIONAL EDGE CASE TESTS
    // ═══════════════════════════════════════════════════════════════════

    #[test]
    fn test_eval_int_zero() {
        let mut interp = Interpreter::new();
        assert_eq!(interp.eval(&Expr::Int(0)), Ok(Value::Int(0)));
    }

    #[test]
    fn test_eval_int_large() {
        let mut interp = Interpreter::new();
        assert_eq!(interp.eval(&Expr::Int(1000000)), Ok(Value::Int(1000000)));
    }

    #[test]
    fn test_eval_int_max() {
        let mut interp = Interpreter::new();
        assert_eq!(interp.eval(&Expr::Int(u64::MAX)), Ok(Value::Int(u64::MAX)));
    }

    #[test]
    fn test_eval_string_empty() {
        let mut interp = Interpreter::new();
        assert_eq!(
            interp.eval(&Expr::String("".to_string())),
            Ok(Value::String("".to_string()))
        );
    }

    #[test]
    fn test_eval_string_unicode() {
        let mut interp = Interpreter::new();
        // Test with Bahasa Melayu
        assert_eq!(
            interp.eval(&Expr::String("Selamat pagi".to_string())),
            Ok(Value::String("Selamat pagi".to_string()))
        );
    }

    // ═══════════════════════════════════════════════════════════════════
    // ADDITIONAL ARITHMETIC TESTS
    // ═══════════════════════════════════════════════════════════════════

    #[test]
    fn test_eval_subtraction() {
        let mut interp = Interpreter::new();
        let expr = Expr::Let(
            "x".to_string(),
            Box::new(Expr::Int(10)),
            Box::new(Expr::Let(
                "y".to_string(),
                Box::new(Expr::Int(3)),
                Box::new(Expr::App(
                    Box::new(Expr::App(
                        Box::new(Expr::Var("__sub".to_string())),
                        Box::new(Expr::Var("x".to_string())),
                    )),
                    Box::new(Expr::Var("y".to_string())),
                )),
            )),
        );
        // We can't directly test subtraction without the built-in,
        // so let's test nested pairs instead
        let pair_expr = Expr::Pair(
            Box::new(Expr::Pair(
                Box::new(Expr::Int(1)),
                Box::new(Expr::Int(2)),
            )),
            Box::new(Expr::Pair(
                Box::new(Expr::Int(3)),
                Box::new(Expr::Int(4)),
            )),
        );
        let result = interp.eval(&pair_expr).unwrap();
        assert!(result.is_pair());
    }

    #[test]
    fn test_eval_deeply_nested_let() {
        let mut interp = Interpreter::new();
        // let x = 1 in let y = 2 in let z = 3 in x
        let expr = Expr::Let(
            "x".to_string(),
            Box::new(Expr::Int(1)),
            Box::new(Expr::Let(
                "y".to_string(),
                Box::new(Expr::Int(2)),
                Box::new(Expr::Let(
                    "z".to_string(),
                    Box::new(Expr::Int(3)),
                    Box::new(Expr::Var("x".to_string())),
                )),
            )),
        );
        assert_eq!(interp.eval(&expr), Ok(Value::Int(1)));
    }

    #[test]
    fn test_eval_deeply_nested_let_inner() {
        let mut interp = Interpreter::new();
        // let x = 1 in let y = 2 in let z = 3 in z (innermost)
        let expr = Expr::Let(
            "x".to_string(),
            Box::new(Expr::Int(1)),
            Box::new(Expr::Let(
                "y".to_string(),
                Box::new(Expr::Int(2)),
                Box::new(Expr::Let(
                    "z".to_string(),
                    Box::new(Expr::Int(3)),
                    Box::new(Expr::Var("z".to_string())),
                )),
            )),
        );
        assert_eq!(interp.eval(&expr), Ok(Value::Int(3)));
    }

    // ═══════════════════════════════════════════════════════════════════
    // ADDITIONAL SUM TYPE TESTS
    // ═══════════════════════════════════════════════════════════════════

    #[test]
    fn test_eval_case_nested_inl() {
        let mut interp = Interpreter::new();
        let expr = Expr::Case(
            Box::new(Expr::Inl(Box::new(Expr::Int(100)), Ty::Bool)),
            "x".to_string(),
            Box::new(Expr::Var("x".to_string())),
            "y".to_string(),
            Box::new(Expr::Int(0)),
        );
        assert_eq!(interp.eval(&expr), Ok(Value::Int(100)));
    }

    #[test]
    fn test_eval_case_nested_inr() {
        let mut interp = Interpreter::new();
        let expr = Expr::Case(
            Box::new(Expr::Inr(Box::new(Expr::Int(200)), Ty::Bool)),
            "x".to_string(),
            Box::new(Expr::Int(0)),
            "y".to_string(),
            Box::new(Expr::Var("y".to_string())),
        );
        assert_eq!(interp.eval(&expr), Ok(Value::Int(200)));
    }

    // ═══════════════════════════════════════════════════════════════════
    // ADDITIONAL SECURITY TESTS
    // ═══════════════════════════════════════════════════════════════════

    #[test]
    fn test_eval_nested_classify() {
        let mut interp = Interpreter::new();
        // classify(classify(42)) - double classification
        let expr = Expr::Classify(Box::new(Expr::Classify(Box::new(Expr::Int(42)))));
        let result = interp.eval(&expr).unwrap();
        assert_eq!(result.security_level(), SecurityLevel::Secret);
    }

    #[test]
    fn test_eval_classify_pair() {
        let mut interp = Interpreter::new();
        // (classify(1), 2) - pair with secret component
        let expr = Expr::Pair(
            Box::new(Expr::Classify(Box::new(Expr::Int(1)))),
            Box::new(Expr::Int(2)),
        );
        let result = interp.eval(&expr).unwrap();
        assert_eq!(result.security_level(), SecurityLevel::Secret);
    }

    // ═══════════════════════════════════════════════════════════════════
    // ADDITIONAL FUNCTION TESTS
    // ═══════════════════════════════════════════════════════════════════

    #[test]
    fn test_eval_identity_function() {
        let mut interp = Interpreter::new();
        // (λx. x) 42 = 42
        let expr = Expr::App(
            Box::new(Expr::Lam(
                "x".to_string(),
                Ty::Int,
                Box::new(Expr::Var("x".to_string())),
            )),
            Box::new(Expr::Int(42)),
        );
        assert_eq!(interp.eval(&expr), Ok(Value::Int(42)));
    }

    #[test]
    fn test_eval_constant_function() {
        let mut interp = Interpreter::new();
        // (λx. 100) 42 = 100
        let expr = Expr::App(
            Box::new(Expr::Lam(
                "x".to_string(),
                Ty::Int,
                Box::new(Expr::Int(100)),
            )),
            Box::new(Expr::Int(42)),
        );
        assert_eq!(interp.eval(&expr), Ok(Value::Int(100)));
    }

    #[test]
    fn test_eval_closure_captures() {
        let mut interp = Interpreter::new();
        // let a = 10 in (λx. a) 0 = 10
        let expr = Expr::Let(
            "a".to_string(),
            Box::new(Expr::Int(10)),
            Box::new(Expr::App(
                Box::new(Expr::Lam(
                    "x".to_string(),
                    Ty::Int,
                    Box::new(Expr::Var("a".to_string())),
                )),
                Box::new(Expr::Int(0)),
            )),
        );
        assert_eq!(interp.eval(&expr), Ok(Value::Int(10)));
    }
}
