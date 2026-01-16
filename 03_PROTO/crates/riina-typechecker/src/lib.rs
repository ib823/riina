//! RIINA Typechecker
//!
//! Implements the typing rules defined in `foundations/Typing.v`.
//! RIINA = Rigorous Immutable Integrity No-attack Assured
//!
//! Mode: ULTRA KIASU | FUCKING PARANOID | ZERO TRUST | ZERO LAZINESS

use riina_types::{Expr, Ty, SecurityLevel, Effect, Ident};
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

pub struct Context {
    vars: HashMap<Ident, Ty>,
    level: SecurityLevel,
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
                    if *arg_ty != t2 {
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
        }
    }
}

#[cfg(test)]
mod tests;
