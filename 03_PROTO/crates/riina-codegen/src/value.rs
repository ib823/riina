//! Runtime Values
//!
//! Represents the values that RIINA programs compute to.
//! Directly corresponds to the `value` type in Coq semantics.
//!
//! # Correspondence with Coq
//!
//! ```coq
//! (* 02_FORMAL/coq/foundations/Semantics.v *)
//! Inductive value : Type :=
//!   | VUnit : value
//!   | VBool : bool -> value
//!   | VInt : Z -> value
//!   | VString : string -> value
//!   | VPair : value -> value -> value
//!   | VInl : value -> value
//!   | VInr : value -> value
//!   | VClosure : env -> ident -> ty -> expr -> value
//!   | VRef : loc -> value
//!   | VSecret : value -> value
//!   | VProof : value -> value
//!   | VCap : effect -> value.
//! ```
//!
//! # Security Properties
//!
//! Values carry security information:
//! - `Value::Secret` wraps values that cannot flow to public outputs
//! - `Value::Proof` carries evidence for declassification
//! - `Value::Ref` carries security level of the reference cell
//!
//! # Mode: ULTRA KIASU | FUCKING PARANOID | ZERO TRUST

use riina_types::{Effect, Expr, Ident, SecurityLevel, Ty};
use std::collections::HashMap;
use std::rc::Rc;

/// Reference location
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct Location(pub u32);

impl Location {
    /// Create a new location
    #[must_use]
    pub const fn new(loc: u32) -> Self {
        Self(loc)
    }
}

impl std::fmt::Display for Location {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "loc{}", self.0)
    }
}

/// Environment binding names to values
#[derive(Debug, Clone, Default)]
pub struct Env {
    bindings: HashMap<Ident, Value>,
}

impl Env {
    /// Create a new empty environment
    #[must_use]
    pub fn new() -> Self {
        Self {
            bindings: HashMap::new(),
        }
    }

    /// Extend the environment with a new binding
    #[must_use]
    pub fn extend(&self, name: Ident, value: Value) -> Self {
        let mut new_env = self.clone();
        new_env.bindings.insert(name, value);
        new_env
    }

    /// Look up a name in the environment
    #[must_use]
    pub fn lookup(&self, name: &str) -> Option<&Value> {
        self.bindings.get(name)
    }

    /// Check if the environment contains a name
    #[must_use]
    pub fn contains(&self, name: &str) -> bool {
        self.bindings.contains_key(name)
    }

    /// Get the number of bindings
    #[must_use]
    pub fn len(&self) -> usize {
        self.bindings.len()
    }

    /// Check if empty
    #[must_use]
    pub fn is_empty(&self) -> bool {
        self.bindings.is_empty()
    }
}

/// Closure: captures environment and a lambda expression
#[derive(Debug, Clone)]
pub struct Closure {
    /// Captured environment
    pub env: Env,
    /// Parameter name
    pub param: Ident,
    /// Parameter type
    pub param_ty: Ty,
    /// Function body
    pub body: Rc<Expr>,
}

impl PartialEq for Closure {
    fn eq(&self, _other: &Self) -> bool {
        // Closures are compared by identity, not structure
        // This is consistent with functional language semantics
        false
    }
}

impl Eq for Closure {}

/// Sum value: left or right injection
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Sum {
    /// Left injection
    Left(Box<Value>),
    /// Right injection
    Right(Box<Value>),
}

/// Reference cell with security level
#[derive(Debug, Clone)]
pub struct RefCell {
    /// Location in the heap
    pub location: Location,
    /// Security level of this reference
    pub level: SecurityLevel,
}

impl PartialEq for RefCell {
    fn eq(&self, other: &Self) -> bool {
        self.location == other.location
    }
}

impl Eq for RefCell {}

/// Runtime values
///
/// Corresponds directly to Coq `value` type.
/// Every value constructor maps to a Coq constructor.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Value {
    // ═══════════════════════════════════════════════════════════════════
    // BASE VALUES (correspond to Expr::Unit, Expr::Bool, Expr::Int, Expr::String)
    // ═══════════════════════════════════════════════════════════════════

    /// Unit value `()`
    ///
    /// Corresponds to Coq `VUnit`.
    Unit,

    /// Boolean value
    ///
    /// Corresponds to Coq `VBool b`.
    Bool(bool),

    /// Integer value (arbitrary precision in Coq, u64 here)
    ///
    /// Corresponds to Coq `VInt n`.
    Int(u64),

    /// String value
    ///
    /// Corresponds to Coq `VString s`.
    String(String),

    // ═══════════════════════════════════════════════════════════════════
    // PRODUCT VALUES (correspond to Expr::Pair)
    // ═══════════════════════════════════════════════════════════════════

    /// Pair of values
    ///
    /// Corresponds to Coq `VPair v1 v2`.
    Pair(Box<Value>, Box<Value>),

    // ═══════════════════════════════════════════════════════════════════
    // SUM VALUES (correspond to Expr::Inl, Expr::Inr)
    // ═══════════════════════════════════════════════════════════════════

    /// Sum value (left or right)
    ///
    /// Corresponds to Coq `VInl v` or `VInr v`.
    Sum(Sum),

    // ═══════════════════════════════════════════════════════════════════
    // FUNCTION VALUES (correspond to Expr::Lam)
    // ═══════════════════════════════════════════════════════════════════

    /// Closure (function value)
    ///
    /// Corresponds to Coq `VClosure env x T e`.
    Closure(Closure),

    // ═══════════════════════════════════════════════════════════════════
    // REFERENCE VALUES (correspond to Expr::Ref)
    // ═══════════════════════════════════════════════════════════════════

    /// Reference (mutable cell)
    ///
    /// Corresponds to Coq `VRef loc`.
    Ref(RefCell),

    // ═══════════════════════════════════════════════════════════════════
    // SECURITY VALUES (correspond to Expr::Classify, Expr::Prove)
    // ═══════════════════════════════════════════════════════════════════

    /// Secret value (information hiding)
    ///
    /// Corresponds to Coq `VSecret v`.
    Secret(Box<Value>),

    /// Proof witness
    ///
    /// Corresponds to Coq `VProof v`.
    Proof(Box<Value>),

    // ═══════════════════════════════════════════════════════════════════
    // CAPABILITY VALUES (correspond to capability tokens)
    // ═══════════════════════════════════════════════════════════════════

    /// Effect capability token
    ///
    /// Corresponds to Coq `VCap eff`.
    Capability(Effect),
}

impl Value {
    // ═══════════════════════════════════════════════════════════════════
    // CONSTRUCTORS
    // ═══════════════════════════════════════════════════════════════════

    /// Create a unit value
    #[must_use]
    pub const fn unit() -> Self {
        Self::Unit
    }

    /// Create a boolean value
    #[must_use]
    pub const fn bool(b: bool) -> Self {
        Self::Bool(b)
    }

    /// Create an integer value
    #[must_use]
    pub const fn int(n: u64) -> Self {
        Self::Int(n)
    }

    /// Create a string value
    #[must_use]
    pub fn string(s: impl Into<String>) -> Self {
        Self::String(s.into())
    }

    /// Create a pair value
    #[must_use]
    pub fn pair(fst: Self, snd: Self) -> Self {
        Self::Pair(Box::new(fst), Box::new(snd))
    }

    /// Create a left-injected sum value
    #[must_use]
    pub fn inl(v: Self) -> Self {
        Self::Sum(Sum::Left(Box::new(v)))
    }

    /// Create a right-injected sum value
    #[must_use]
    pub fn inr(v: Self) -> Self {
        Self::Sum(Sum::Right(Box::new(v)))
    }

    /// Create a secret value
    #[must_use]
    pub fn secret(v: Self) -> Self {
        Self::Secret(Box::new(v))
    }

    /// Create a proof value
    #[must_use]
    pub fn proof(v: Self) -> Self {
        Self::Proof(Box::new(v))
    }

    /// Create a capability value
    #[must_use]
    pub const fn capability(eff: Effect) -> Self {
        Self::Capability(eff)
    }

    // ═══════════════════════════════════════════════════════════════════
    // PREDICATES
    // ═══════════════════════════════════════════════════════════════════

    /// Check if this is a unit value
    #[must_use]
    pub const fn is_unit(&self) -> bool {
        matches!(self, Self::Unit)
    }

    /// Check if this is a boolean value
    #[must_use]
    pub const fn is_bool(&self) -> bool {
        matches!(self, Self::Bool(_))
    }

    /// Check if this is an integer value
    #[must_use]
    pub const fn is_int(&self) -> bool {
        matches!(self, Self::Int(_))
    }

    /// Check if this is a string value
    #[must_use]
    pub const fn is_string(&self) -> bool {
        matches!(self, Self::String(_))
    }

    /// Check if this is a pair value
    #[must_use]
    pub const fn is_pair(&self) -> bool {
        matches!(self, Self::Pair(_, _))
    }

    /// Check if this is a sum value
    #[must_use]
    pub const fn is_sum(&self) -> bool {
        matches!(self, Self::Sum(_))
    }

    /// Check if this is a left-injected sum
    #[must_use]
    pub const fn is_left(&self) -> bool {
        matches!(self, Self::Sum(Sum::Left(_)))
    }

    /// Check if this is a right-injected sum
    #[must_use]
    pub const fn is_right(&self) -> bool {
        matches!(self, Self::Sum(Sum::Right(_)))
    }

    /// Check if this is a closure
    #[must_use]
    pub const fn is_closure(&self) -> bool {
        matches!(self, Self::Closure(_))
    }

    /// Check if this is a reference
    #[must_use]
    pub const fn is_ref(&self) -> bool {
        matches!(self, Self::Ref(_))
    }

    /// Check if this is a secret value
    #[must_use]
    pub const fn is_secret(&self) -> bool {
        matches!(self, Self::Secret(_))
    }

    /// Check if this is a proof value
    #[must_use]
    pub const fn is_proof(&self) -> bool {
        matches!(self, Self::Proof(_))
    }

    /// Check if this is a capability
    #[must_use]
    pub const fn is_capability(&self) -> bool {
        matches!(self, Self::Capability(_))
    }

    // ═══════════════════════════════════════════════════════════════════
    // EXTRACTORS
    // ═══════════════════════════════════════════════════════════════════

    /// Extract boolean value
    #[must_use]
    pub const fn as_bool(&self) -> Option<bool> {
        if let Self::Bool(b) = self {
            Some(*b)
        } else {
            None
        }
    }

    /// Extract integer value
    #[must_use]
    pub const fn as_int(&self) -> Option<u64> {
        if let Self::Int(n) = self {
            Some(*n)
        } else {
            None
        }
    }

    /// Extract string value
    #[must_use]
    pub fn as_string(&self) -> Option<&str> {
        if let Self::String(s) = self {
            Some(s)
        } else {
            None
        }
    }

    /// Extract pair components
    #[must_use]
    pub fn as_pair(&self) -> Option<(&Value, &Value)> {
        if let Self::Pair(fst, snd) = self {
            Some((fst, snd))
        } else {
            None
        }
    }

    /// Extract first component of pair
    #[must_use]
    pub fn fst(&self) -> Option<&Value> {
        if let Self::Pair(fst, _) = self {
            Some(fst)
        } else {
            None
        }
    }

    /// Extract second component of pair
    #[must_use]
    pub fn snd(&self) -> Option<&Value> {
        if let Self::Pair(_, snd) = self {
            Some(snd)
        } else {
            None
        }
    }

    /// Extract sum value
    #[must_use]
    pub fn as_sum(&self) -> Option<&Sum> {
        if let Self::Sum(s) = self {
            Some(s)
        } else {
            None
        }
    }

    /// Extract left-injected value
    #[must_use]
    pub fn as_left(&self) -> Option<&Value> {
        if let Self::Sum(Sum::Left(v)) = self {
            Some(v)
        } else {
            None
        }
    }

    /// Extract right-injected value
    #[must_use]
    pub fn as_right(&self) -> Option<&Value> {
        if let Self::Sum(Sum::Right(v)) = self {
            Some(v)
        } else {
            None
        }
    }

    /// Extract closure
    #[must_use]
    pub fn as_closure(&self) -> Option<&Closure> {
        if let Self::Closure(c) = self {
            Some(c)
        } else {
            None
        }
    }

    /// Extract reference
    #[must_use]
    pub fn as_ref(&self) -> Option<&RefCell> {
        if let Self::Ref(r) = self {
            Some(r)
        } else {
            None
        }
    }

    /// Extract secret value (unwrap)
    #[must_use]
    pub fn as_secret(&self) -> Option<&Value> {
        if let Self::Secret(v) = self {
            Some(v)
        } else {
            None
        }
    }

    /// Extract proof value (unwrap)
    #[must_use]
    pub fn as_proof(&self) -> Option<&Value> {
        if let Self::Proof(v) = self {
            Some(v)
        } else {
            None
        }
    }

    /// Extract capability effect
    #[must_use]
    pub const fn as_capability(&self) -> Option<Effect> {
        if let Self::Capability(eff) = self {
            Some(*eff)
        } else {
            None
        }
    }

    // ═══════════════════════════════════════════════════════════════════
    // SECURITY ANALYSIS
    // ═══════════════════════════════════════════════════════════════════

    /// Get the security level of this value
    ///
    /// - `Secret(v)` is always Secret level
    /// - `Ref(_, level)` has the reference's level
    /// - Other values are Public
    #[must_use]
    pub fn security_level(&self) -> SecurityLevel {
        match self {
            Self::Secret(_) => SecurityLevel::Secret,
            Self::Ref(r) => r.level,
            Self::Pair(a, b) => {
                // A pair is secret if either component is secret
                let a_level = a.security_level();
                let b_level = b.security_level();
                if a_level == SecurityLevel::Secret || b_level == SecurityLevel::Secret {
                    SecurityLevel::Secret
                } else {
                    SecurityLevel::Public
                }
            }
            Self::Sum(s) => match s {
                Sum::Left(v) | Sum::Right(v) => v.security_level(),
            },
            _ => SecurityLevel::Public,
        }
    }

    /// Check if this value can flow to a context with the given security level
    ///
    /// Information flow rule: High cannot flow to Low
    #[must_use]
    pub fn can_flow_to(&self, target_level: SecurityLevel) -> bool {
        !matches!(
            (self.security_level(), target_level),
            (SecurityLevel::Secret, SecurityLevel::Public)
        )
    }
}

impl std::fmt::Display for Value {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::Unit => write!(f, "()"),
            Self::Bool(b) => write!(f, "{b}"),
            Self::Int(n) => write!(f, "{n}"),
            Self::String(s) => write!(f, "\"{s}\""),
            Self::Pair(a, b) => write!(f, "({a}, {b})"),
            Self::Sum(Sum::Left(v)) => write!(f, "inl {v}"),
            Self::Sum(Sum::Right(v)) => write!(f, "inr {v}"),
            Self::Closure(c) => write!(f, "<closure({})>", c.param),
            Self::Ref(r) => write!(f, "<ref {}@{:?}>", r.location, r.level),
            Self::Secret(v) => write!(f, "secret({v})"),
            Self::Proof(v) => write!(f, "proof({v})"),
            Self::Capability(eff) => write!(f, "<cap({eff:?})>"),
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use riina_types::{Expr, Effect};

    // ═══════════════════════════════════════════════════════════════════
    // VALUE CONSTRUCTOR TESTS
    // ═══════════════════════════════════════════════════════════════════

    #[test]
    fn test_value_constructors() {
        assert!(Value::unit().is_unit());
        assert!(Value::bool(true).is_bool());
        assert!(Value::int(42).is_int());
        assert!(Value::string("hello").is_string());
    }

    #[test]
    fn test_value_bool_variants() {
        assert!(Value::bool(true).is_bool());
        assert!(Value::bool(false).is_bool());
        assert_eq!(Value::bool(true).as_bool(), Some(true));
        assert_eq!(Value::bool(false).as_bool(), Some(false));
    }

    #[test]
    fn test_value_int_edge_cases() {
        // Test boundary values
        assert_eq!(Value::int(0).as_int(), Some(0));
        assert_eq!(Value::int(-1).as_int(), Some(-1));
        assert_eq!(Value::int(i64::MAX).as_int(), Some(i64::MAX));
        assert_eq!(Value::int(i64::MIN).as_int(), Some(i64::MIN));
    }

    #[test]
    fn test_value_string_edge_cases() {
        assert_eq!(Value::string("").as_string(), Some(""));
        assert_eq!(Value::string("hello world").as_string(), Some("hello world"));
        // Unicode
        assert_eq!(Value::string("こんにちは").as_string(), Some("こんにちは"));
        // Bahasa Melayu
        assert_eq!(Value::string("Selamat pagi").as_string(), Some("Selamat pagi"));
    }

    // ═══════════════════════════════════════════════════════════════════
    // VALUE EXTRACTOR TESTS
    // ═══════════════════════════════════════════════════════════════════

    #[test]
    fn test_value_extractors() {
        assert_eq!(Value::bool(true).as_bool(), Some(true));
        assert_eq!(Value::int(42).as_int(), Some(42));
        assert_eq!(Value::string("hello").as_string(), Some("hello"));
    }

    #[test]
    fn test_value_extractor_wrong_type() {
        // Extracting wrong type returns None
        assert_eq!(Value::int(42).as_bool(), None);
        assert_eq!(Value::bool(true).as_int(), None);
        assert_eq!(Value::unit().as_string(), None);
        assert_eq!(Value::string("x").as_int(), None);
    }

    #[test]
    fn test_value_is_predicates() {
        let unit = Value::unit();
        let boolean = Value::bool(true);
        let integer = Value::int(42);
        let string = Value::string("test");

        assert!(unit.is_unit());
        assert!(!unit.is_bool());
        assert!(!unit.is_int());
        assert!(!unit.is_string());

        assert!(!boolean.is_unit());
        assert!(boolean.is_bool());
        assert!(!boolean.is_int());
        assert!(!boolean.is_string());

        assert!(!integer.is_unit());
        assert!(!integer.is_bool());
        assert!(integer.is_int());
        assert!(!integer.is_string());

        assert!(!string.is_unit());
        assert!(!string.is_bool());
        assert!(!string.is_int());
        assert!(string.is_string());
    }

    // ═══════════════════════════════════════════════════════════════════
    // PAIR TESTS
    // ═══════════════════════════════════════════════════════════════════

    #[test]
    fn test_pair_operations() {
        let pair = Value::pair(Value::int(1), Value::int(2));
        assert!(pair.is_pair());
        assert_eq!(pair.fst(), Some(&Value::Int(1)));
        assert_eq!(pair.snd(), Some(&Value::Int(2)));
    }

    #[test]
    fn test_pair_nested() {
        let inner = Value::pair(Value::int(1), Value::int(2));
        let outer = Value::pair(inner.clone(), Value::int(3));

        assert!(outer.is_pair());
        assert_eq!(outer.fst(), Some(&inner));
        assert_eq!(outer.snd(), Some(&Value::Int(3)));
    }

    #[test]
    fn test_pair_extractor_wrong_type() {
        let not_pair = Value::int(42);
        assert_eq!(not_pair.fst(), None);
        assert_eq!(not_pair.snd(), None);
    }

    // ═══════════════════════════════════════════════════════════════════
    // SUM TYPE TESTS
    // ═══════════════════════════════════════════════════════════════════

    #[test]
    fn test_sum_operations() {
        let left = Value::inl(Value::int(1));
        let right = Value::inr(Value::int(2));

        assert!(left.is_left());
        assert!(!left.is_right());
        assert!(!right.is_left());
        assert!(right.is_right());

        assert_eq!(left.as_left(), Some(&Value::Int(1)));
        assert_eq!(right.as_right(), Some(&Value::Int(2)));
    }

    #[test]
    fn test_sum_extractor_wrong_variant() {
        let left = Value::inl(Value::int(1));
        let right = Value::inr(Value::int(2));

        assert_eq!(left.as_right(), None);
        assert_eq!(right.as_left(), None);
    }

    #[test]
    fn test_sum_nested() {
        let inner = Value::inl(Value::int(42));
        let outer = Value::inr(inner.clone());

        assert!(outer.is_right());
        assert_eq!(outer.as_right(), Some(&inner));
    }

    // ═══════════════════════════════════════════════════════════════════
    // SECURITY LEVEL TESTS
    // ═══════════════════════════════════════════════════════════════════

    #[test]
    fn test_security_levels() {
        let public = Value::int(42);
        let secret = Value::secret(Value::int(42));

        assert_eq!(public.security_level(), SecurityLevel::Public);
        assert_eq!(secret.security_level(), SecurityLevel::Secret);

        // Public can flow to Secret
        assert!(public.can_flow_to(SecurityLevel::Secret));
        // Secret cannot flow to Public
        assert!(!secret.can_flow_to(SecurityLevel::Public));
    }

    #[test]
    fn test_security_flow_rules() {
        let public = Value::int(1);
        let secret = Value::secret(Value::int(2));

        // Public -> Public: OK
        assert!(public.can_flow_to(SecurityLevel::Public));
        // Public -> Secret: OK (upgrading)
        assert!(public.can_flow_to(SecurityLevel::Secret));
        // Secret -> Secret: OK
        assert!(secret.can_flow_to(SecurityLevel::Secret));
        // Secret -> Public: FORBIDDEN (downgrading)
        assert!(!secret.can_flow_to(SecurityLevel::Public));
    }

    #[test]
    fn test_pair_security_propagation() {
        let both_public = Value::pair(Value::int(1), Value::int(2));
        let has_secret = Value::pair(Value::int(1), Value::secret(Value::int(2)));

        assert_eq!(both_public.security_level(), SecurityLevel::Public);
        assert_eq!(has_secret.security_level(), SecurityLevel::Secret);
    }

    #[test]
    fn test_sum_security_propagation() {
        let public_left = Value::inl(Value::int(1));
        let secret_left = Value::inl(Value::secret(Value::int(1)));
        let secret_right = Value::inr(Value::secret(Value::int(2)));

        assert_eq!(public_left.security_level(), SecurityLevel::Public);
        assert_eq!(secret_left.security_level(), SecurityLevel::Secret);
        assert_eq!(secret_right.security_level(), SecurityLevel::Secret);
    }

    #[test]
    fn test_nested_secret_propagation() {
        // Secret inside a pair inside a pair
        let deep_secret = Value::pair(
            Value::int(1),
            Value::pair(
                Value::int(2),
                Value::secret(Value::int(3))
            )
        );
        assert_eq!(deep_secret.security_level(), SecurityLevel::Secret);
    }

    // ═══════════════════════════════════════════════════════════════════
    // SECRET/PROOF/CAPABILITY TESTS
    // ═══════════════════════════════════════════════════════════════════

    #[test]
    fn test_secret_operations() {
        let secret = Value::secret(Value::int(42));
        assert!(secret.is_secret());
        assert_eq!(secret.as_secret(), Some(&Value::Int(42)));
    }

    #[test]
    fn test_proof_operations() {
        let proof = Value::proof(Value::bool(true));
        assert!(proof.is_proof());
        assert_eq!(proof.as_proof(), Some(&Value::Bool(true)));
    }

    #[test]
    fn test_capability_operations() {
        let cap = Value::capability(Effect::Read);
        assert!(cap.is_capability());
        assert_eq!(cap.as_capability(), Some(Effect::Read));

        let cap_write = Value::capability(Effect::Write);
        assert_eq!(cap_write.as_capability(), Some(Effect::Write));

        let cap_crypto = Value::capability(Effect::Crypto);
        assert_eq!(cap_crypto.as_capability(), Some(Effect::Crypto));
    }

    // ═══════════════════════════════════════════════════════════════════
    // CLOSURE TESTS
    // ═══════════════════════════════════════════════════════════════════

    #[test]
    fn test_closure_creation() {
        let env = Env::new().extend("x".to_string(), Value::int(10));
        let body = Expr::Var("x".to_string());
        let closure = Value::closure("y".to_string(), body.clone(), env.clone());

        assert!(closure.is_closure());
        let c = closure.as_closure().unwrap();
        assert_eq!(c.param, "y");
        assert_eq!(c.env.lookup("x"), Some(&Value::Int(10)));
    }

    #[test]
    fn test_closure_extractor_wrong_type() {
        let not_closure = Value::int(42);
        assert_eq!(not_closure.as_closure(), None);
    }

    // ═══════════════════════════════════════════════════════════════════
    // ENVIRONMENT TESTS
    // ═══════════════════════════════════════════════════════════════════

    #[test]
    fn test_env_operations() {
        let env = Env::new();
        assert!(env.is_empty());

        let env = env.extend("x".to_string(), Value::int(42));
        assert!(!env.is_empty());
        assert_eq!(env.len(), 1);
        assert!(env.contains("x"));
        assert_eq!(env.lookup("x"), Some(&Value::Int(42)));
        assert_eq!(env.lookup("y"), None);
    }

    #[test]
    fn test_env_multiple_bindings() {
        let env = Env::new()
            .extend("x".to_string(), Value::int(1))
            .extend("y".to_string(), Value::int(2))
            .extend("z".to_string(), Value::int(3));

        assert_eq!(env.len(), 3);
        assert_eq!(env.lookup("x"), Some(&Value::Int(1)));
        assert_eq!(env.lookup("y"), Some(&Value::Int(2)));
        assert_eq!(env.lookup("z"), Some(&Value::Int(3)));
    }

    #[test]
    fn test_env_shadowing() {
        let env = Env::new()
            .extend("x".to_string(), Value::int(1))
            .extend("x".to_string(), Value::int(2));

        // Most recent binding should be found
        assert_eq!(env.lookup("x"), Some(&Value::Int(2)));
    }

    #[test]
    fn test_env_clone() {
        let env1 = Env::new().extend("x".to_string(), Value::int(42));
        let env2 = env1.clone();

        assert_eq!(env1.lookup("x"), env2.lookup("x"));
    }

    // ═══════════════════════════════════════════════════════════════════
    // DISPLAY TESTS
    // ═══════════════════════════════════════════════════════════════════

    #[test]
    fn test_value_display() {
        assert_eq!(Value::unit().to_string(), "()");
        assert_eq!(Value::bool(true).to_string(), "true");
        assert_eq!(Value::bool(false).to_string(), "false");
        assert_eq!(Value::int(42).to_string(), "42");
        assert_eq!(Value::int(-100).to_string(), "-100");
        assert_eq!(Value::string("hello").to_string(), "\"hello\"");
        assert_eq!(Value::pair(Value::int(1), Value::int(2)).to_string(), "(1, 2)");
        assert_eq!(Value::inl(Value::int(1)).to_string(), "inl 1");
        assert_eq!(Value::inr(Value::int(2)).to_string(), "inr 2");
        assert_eq!(Value::secret(Value::int(42)).to_string(), "secret(42)");
        assert_eq!(Value::proof(Value::bool(true)).to_string(), "proof(true)");
    }

    #[test]
    fn test_value_display_nested() {
        let nested_pair = Value::pair(
            Value::pair(Value::int(1), Value::int(2)),
            Value::int(3)
        );
        assert_eq!(nested_pair.to_string(), "((1, 2), 3)");
    }
}
