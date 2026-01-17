//! Intermediate Representation
//!
//! SSA-form IR that directly corresponds to the Coq formalization.
//! Every construct maps to a definition in `02_FORMAL/coq/foundations/IR.v`.
//!
//! # Design Principles
//!
//! 1. **SSA Form**: All values are defined exactly once
//! 2. **Explicit Control Flow**: Basic blocks with explicit terminators
//! 3. **Security Annotations**: Every value carries a security level
//! 4. **Effect Tracking**: Instructions annotated with effect requirements
//!
//! # Correspondence with Coq
//!
//! ```coq
//! (* 02_FORMAL/coq/foundations/IR.v *)
//! Inductive ir_val : Type :=
//!   | IRUnit : ir_val
//!   | IRBool : bool -> ir_val
//!   | IRInt : Z -> ir_val
//!   | IRString : string -> ir_val
//!   | IRRef : nat -> ir_val
//!   | IRClosure : env -> ident -> ir_expr -> ir_val.
//!
//! Inductive ir_instr : Type :=
//!   | IRConst : ir_val -> ir_instr
//!   | IRLoad : var_id -> ir_instr
//!   | IRStore : var_id -> var_id -> ir_instr
//!   | IRBinOp : binop -> var_id -> var_id -> ir_instr
//!   | IRCall : var_id -> var_id -> ir_instr
//!   | IRPair : var_id -> var_id -> ir_instr
//!   | IRFst : var_id -> ir_instr
//!   | IRSnd : var_id -> ir_instr
//!   | IRInl : var_id -> ir_instr
//!   | IRInr : var_id -> ir_instr.
//! ```

use riina_types::{Effect, SecurityLevel, Ty, Ident};
use std::collections::HashMap;

/// Variable identifier in IR (SSA form)
///
/// Each `VarId` represents a unique definition point.
/// Corresponds to `var_id` in Coq formalization.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct VarId(pub u32);

impl VarId {
    /// Create a new variable ID
    #[must_use]
    pub const fn new(id: u32) -> Self {
        Self(id)
    }
}

impl std::fmt::Display for VarId {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "v{}", self.0)
    }
}

/// Basic block identifier
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct BlockId(pub u32);

impl BlockId {
    /// Create a new block ID
    #[must_use]
    pub const fn new(id: u32) -> Self {
        Self(id)
    }

    /// Entry block ID (always 0)
    pub const ENTRY: Self = Self(0);
}

impl std::fmt::Display for BlockId {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "bb{}", self.0)
    }
}

/// Function identifier
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct FuncId(pub u32);

impl FuncId {
    /// Create a new function ID
    #[must_use]
    pub const fn new(id: u32) -> Self {
        Self(id)
    }

    /// Main function ID (always 0)
    pub const MAIN: Self = Self(0);
}

impl std::fmt::Display for FuncId {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "f{}", self.0)
    }
}

/// Reference location in heap
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct RefLoc(pub u32);

impl RefLoc {
    /// Create a new reference location
    #[must_use]
    pub const fn new(loc: u32) -> Self {
        Self(loc)
    }
}

impl std::fmt::Display for RefLoc {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "loc{}", self.0)
    }
}

/// Constant values in IR
///
/// Corresponds to `ir_val` in Coq formalization.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Constant {
    /// Unit value `()`
    Unit,
    /// Boolean value
    Bool(bool),
    /// Integer value (arbitrary precision in Coq, u64 here)
    Int(u64),
    /// String value
    String(String),
}

impl std::fmt::Display for Constant {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::Unit => write!(f, "()"),
            Self::Bool(b) => write!(f, "{b}"),
            Self::Int(n) => write!(f, "{n}"),
            Self::String(s) => write!(f, "\"{s}\""),
        }
    }
}

/// Binary operations
///
/// Corresponds to `binop` in Coq formalization.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum BinOp {
    // Arithmetic
    Add,
    Sub,
    Mul,
    Div,
    Mod,

    // Comparison
    Eq,
    Ne,
    Lt,
    Le,
    Gt,
    Ge,

    // Logical
    And,
    Or,
}

impl std::fmt::Display for BinOp {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let s = match self {
            Self::Add => "+",
            Self::Sub => "-",
            Self::Mul => "*",
            Self::Div => "/",
            Self::Mod => "%",
            Self::Eq => "==",
            Self::Ne => "!=",
            Self::Lt => "<",
            Self::Le => "<=",
            Self::Gt => ">",
            Self::Ge => ">=",
            Self::And => "&&",
            Self::Or => "||",
        };
        write!(f, "{s}")
    }
}

/// Unary operations
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum UnaryOp {
    /// Logical negation
    Not,
    /// Arithmetic negation
    Neg,
}

impl std::fmt::Display for UnaryOp {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let s = match self {
            Self::Not => "!",
            Self::Neg => "-",
        };
        write!(f, "{s}")
    }
}

/// IR Instructions
///
/// Each instruction produces exactly one value (SSA form).
/// Corresponds to `ir_instr` in Coq formalization.
///
/// # Invariants
///
/// - All operand `VarId`s must be defined before use (SSA)
/// - Security level must flow correctly (high → low forbidden)
/// - Effect must be subsumed by enclosing function's effect
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Instruction {
    // ═══════════════════════════════════════════════════════════════════
    // CONSTANTS (correspond to Expr::Unit, Expr::Bool, Expr::Int, Expr::String)
    // ═══════════════════════════════════════════════════════════════════

    /// Load a constant value
    ///
    /// ```text
    /// v = const c
    /// ```
    Const(Constant),

    // ═══════════════════════════════════════════════════════════════════
    // VARIABLES (correspond to Expr::Var)
    // ═══════════════════════════════════════════════════════════════════

    /// Copy a value from another variable
    ///
    /// ```text
    /// v = copy src
    /// ```
    Copy(VarId),

    // ═══════════════════════════════════════════════════════════════════
    // ARITHMETIC (binary and unary operations)
    // ═══════════════════════════════════════════════════════════════════

    /// Binary operation
    ///
    /// ```text
    /// v = binop lhs rhs
    /// ```
    BinOp(BinOp, VarId, VarId),

    /// Unary operation
    ///
    /// ```text
    /// v = unaryop operand
    /// ```
    UnaryOp(UnaryOp, VarId),

    // ═══════════════════════════════════════════════════════════════════
    // FUNCTIONS (correspond to Expr::Lam, Expr::App)
    // ═══════════════════════════════════════════════════════════════════

    /// Create a closure
    ///
    /// Captures the current environment and creates a callable value.
    ///
    /// ```text
    /// v = closure func_id [capture1, capture2, ...]
    /// ```
    Closure {
        func: FuncId,
        captures: Vec<VarId>,
    },

    /// Call a function
    ///
    /// ```text
    /// v = call func_var arg_var
    /// ```
    Call(VarId, VarId),

    // ═══════════════════════════════════════════════════════════════════
    // PRODUCTS (correspond to Expr::Pair, Expr::Fst, Expr::Snd)
    // ═══════════════════════════════════════════════════════════════════

    /// Construct a pair
    ///
    /// ```text
    /// v = pair fst snd
    /// ```
    Pair(VarId, VarId),

    /// Project first element
    ///
    /// ```text
    /// v = fst pair_var
    /// ```
    Fst(VarId),

    /// Project second element
    ///
    /// ```text
    /// v = snd pair_var
    /// ```
    Snd(VarId),

    // ═══════════════════════════════════════════════════════════════════
    // SUMS (correspond to Expr::Inl, Expr::Inr, Expr::Case)
    // ═══════════════════════════════════════════════════════════════════

    /// Inject left
    ///
    /// ```text
    /// v = inl value
    /// ```
    Inl(VarId),

    /// Inject right
    ///
    /// ```text
    /// v = inr value
    /// ```
    Inr(VarId),

    /// Check if value is left injection (for case analysis)
    ///
    /// ```text
    /// v = is_left sum_var
    /// ```
    IsLeft(VarId),

    /// Extract left value (after IsLeft check)
    ///
    /// ```text
    /// v = unwrap_left sum_var
    /// ```
    UnwrapLeft(VarId),

    /// Extract right value (after IsLeft check)
    ///
    /// ```text
    /// v = unwrap_right sum_var
    /// ```
    UnwrapRight(VarId),

    // ═══════════════════════════════════════════════════════════════════
    // REFERENCES (correspond to Expr::Ref, Expr::Deref, Expr::Assign)
    // ═══════════════════════════════════════════════════════════════════

    /// Allocate a reference
    ///
    /// ```text
    /// v = ref init_val @ security_level
    /// ```
    Alloc {
        init: VarId,
        level: SecurityLevel,
    },

    /// Read from a reference
    ///
    /// ```text
    /// v = load ref_var
    /// ```
    Load(VarId),

    /// Write to a reference
    ///
    /// ```text
    /// v = store ref_var value_var
    /// ```
    ///
    /// Returns Unit
    Store(VarId, VarId),

    // ═══════════════════════════════════════════════════════════════════
    // SECURITY (correspond to Expr::Classify, Expr::Declassify, Expr::Prove)
    // ═══════════════════════════════════════════════════════════════════

    /// Classify a value as secret
    ///
    /// ```text
    /// v = classify value
    /// ```
    Classify(VarId),

    /// Declassify a secret value (requires proof)
    ///
    /// ```text
    /// v = declassify secret_var proof_var
    /// ```
    Declassify(VarId, VarId),

    /// Create a proof witness
    ///
    /// ```text
    /// v = prove value
    /// ```
    Prove(VarId),

    // ═══════════════════════════════════════════════════════════════════
    // EFFECTS (correspond to Expr::Perform, Expr::Handle)
    // ═══════════════════════════════════════════════════════════════════

    /// Perform an effect
    ///
    /// ```text
    /// v = perform effect payload
    /// ```
    Perform {
        effect: Effect,
        payload: VarId,
    },

    // ═══════════════════════════════════════════════════════════════════
    // CAPABILITIES (correspond to Expr::Require, Expr::Grant)
    // ═══════════════════════════════════════════════════════════════════

    /// Check capability is held
    ///
    /// ```text
    /// v = require_cap effect
    /// ```
    RequireCap(Effect),

    /// Grant capability
    ///
    /// ```text
    /// v = grant_cap effect
    /// ```
    GrantCap(Effect),

    // ═══════════════════════════════════════════════════════════════════
    // PHI NODES (SSA join points)
    // ═══════════════════════════════════════════════════════════════════

    /// Phi node for SSA merge
    ///
    /// ```text
    /// v = phi [(bb1, v1), (bb2, v2), ...]
    /// ```
    Phi(Vec<(BlockId, VarId)>),
}

impl std::fmt::Display for Instruction {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::Const(c) => write!(f, "const {c}"),
            Self::Copy(v) => write!(f, "copy {v}"),
            Self::BinOp(op, l, r) => write!(f, "{op} {l} {r}"),
            Self::UnaryOp(op, v) => write!(f, "{op} {v}"),
            Self::Closure { func, captures } => {
                write!(f, "closure {func}")?;
                if !captures.is_empty() {
                    write!(f, " [")?;
                    for (i, c) in captures.iter().enumerate() {
                        if i > 0 {
                            write!(f, ", ")?;
                        }
                        write!(f, "{c}")?;
                    }
                    write!(f, "]")?;
                }
                Ok(())
            }
            Self::Call(func, arg) => write!(f, "call {func} {arg}"),
            Self::Pair(l, r) => write!(f, "pair {l} {r}"),
            Self::Fst(v) => write!(f, "fst {v}"),
            Self::Snd(v) => write!(f, "snd {v}"),
            Self::Inl(v) => write!(f, "inl {v}"),
            Self::Inr(v) => write!(f, "inr {v}"),
            Self::IsLeft(v) => write!(f, "is_left {v}"),
            Self::UnwrapLeft(v) => write!(f, "unwrap_left {v}"),
            Self::UnwrapRight(v) => write!(f, "unwrap_right {v}"),
            Self::Alloc { init, level } => write!(f, "alloc {init} @ {level:?}"),
            Self::Load(v) => write!(f, "load {v}"),
            Self::Store(r, v) => write!(f, "store {r} {v}"),
            Self::Classify(v) => write!(f, "classify {v}"),
            Self::Declassify(s, p) => write!(f, "declassify {s} {p}"),
            Self::Prove(v) => write!(f, "prove {v}"),
            Self::Perform { effect, payload } => write!(f, "perform {effect:?} {payload}"),
            Self::RequireCap(e) => write!(f, "require_cap {e:?}"),
            Self::GrantCap(e) => write!(f, "grant_cap {e:?}"),
            Self::Phi(entries) => {
                write!(f, "phi [")?;
                for (i, (bb, v)) in entries.iter().enumerate() {
                    if i > 0 {
                        write!(f, ", ")?;
                    }
                    write!(f, "({bb}, {v})")?;
                }
                write!(f, "]")
            }
        }
    }
}

/// Annotated instruction with metadata
#[derive(Debug, Clone)]
pub struct AnnotatedInstr {
    /// The instruction
    pub instr: Instruction,
    /// Result variable
    pub result: VarId,
    /// Result type (for verification)
    pub ty: Ty,
    /// Security level of result
    pub security: SecurityLevel,
    /// Effect of this instruction
    pub effect: Effect,
}

impl std::fmt::Display for AnnotatedInstr {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(
            f,
            "{} = {} : {:?} @ {:?} [ε={:?}]",
            self.result, self.instr, self.ty, self.security, self.effect
        )
    }
}

/// Block terminator
///
/// Determines control flow at the end of a basic block.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Terminator {
    /// Return from function
    ///
    /// ```text
    /// return v
    /// ```
    Return(VarId),

    /// Unconditional branch
    ///
    /// ```text
    /// br target
    /// ```
    Branch(BlockId),

    /// Conditional branch
    ///
    /// ```text
    /// br_if cond then_block else_block
    /// ```
    CondBranch {
        cond: VarId,
        then_block: BlockId,
        else_block: BlockId,
    },

    /// Effect handler installation
    ///
    /// ```text
    /// handle body_block handler_block resume_var result_block
    /// ```
    Handle {
        body_block: BlockId,
        handler_block: BlockId,
        resume_var: Ident,
        result_block: BlockId,
    },

    /// Unreachable (type error or proven impossible)
    Unreachable,
}

impl std::fmt::Display for Terminator {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::Return(v) => write!(f, "return {v}"),
            Self::Branch(bb) => write!(f, "br {bb}"),
            Self::CondBranch { cond, then_block, else_block } => {
                write!(f, "br_if {cond} {then_block} {else_block}")
            }
            Self::Handle { body_block, handler_block, resume_var, result_block } => {
                write!(f, "handle {body_block} {handler_block} {resume_var} -> {result_block}")
            }
            Self::Unreachable => write!(f, "unreachable"),
        }
    }
}

/// Basic block
///
/// A sequence of instructions with a single entry point and
/// a terminator that determines control flow.
#[derive(Debug, Clone)]
pub struct BasicBlock {
    /// Block identifier
    pub id: BlockId,
    /// Instructions in this block
    pub instrs: Vec<AnnotatedInstr>,
    /// Block terminator
    pub terminator: Option<Terminator>,
}

impl BasicBlock {
    /// Create a new empty basic block
    #[must_use]
    pub const fn new(id: BlockId) -> Self {
        Self {
            id,
            instrs: Vec::new(),
            terminator: None,
        }
    }

    /// Add an instruction to this block
    pub fn push(&mut self, instr: AnnotatedInstr) {
        self.instrs.push(instr);
    }

    /// Set the terminator
    pub fn terminate(&mut self, term: Terminator) {
        self.terminator = Some(term);
    }
}

impl std::fmt::Display for BasicBlock {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        writeln!(f, "{}:", self.id)?;
        for instr in &self.instrs {
            writeln!(f, "  {instr}")?;
        }
        if let Some(term) = &self.terminator {
            writeln!(f, "  {term}")?;
        }
        Ok(())
    }
}

/// Function definition
#[derive(Debug, Clone)]
pub struct Function {
    /// Function identifier
    pub id: FuncId,
    /// Function name (for debugging)
    pub name: String,
    /// Parameter name
    pub param: Ident,
    /// Parameter type
    pub param_ty: Ty,
    /// Return type
    pub return_ty: Ty,
    /// Effect annotation
    pub effect: Effect,
    /// Captured variables (for closures)
    pub captures: Vec<(Ident, Ty)>,
    /// Basic blocks
    pub blocks: Vec<BasicBlock>,
    /// Entry block
    pub entry: BlockId,
}

impl Function {
    /// Create a new function
    #[must_use]
    pub fn new(
        id: FuncId,
        name: String,
        param: Ident,
        param_ty: Ty,
        return_ty: Ty,
        effect: Effect,
    ) -> Self {
        Self {
            id,
            name,
            param,
            param_ty,
            return_ty,
            effect,
            captures: Vec::new(),
            blocks: vec![BasicBlock::new(BlockId::ENTRY)],
            entry: BlockId::ENTRY,
        }
    }

    /// Get a mutable reference to a block
    pub fn block_mut(&mut self, id: BlockId) -> Option<&mut BasicBlock> {
        self.blocks.iter_mut().find(|b| b.id == id)
    }

    /// Add a new block
    pub fn new_block(&mut self) -> BlockId {
        let id = BlockId::new(self.blocks.len() as u32);
        self.blocks.push(BasicBlock::new(id));
        id
    }
}

impl std::fmt::Display for Function {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(
            f,
            "fn {}({}: {:?}) -> {:?} [ε={:?}]",
            self.name, self.param, self.param_ty, self.return_ty, self.effect
        )?;
        if !self.captures.is_empty() {
            write!(f, " captures [")?;
            for (i, (name, ty)) in self.captures.iter().enumerate() {
                if i > 0 {
                    write!(f, ", ")?;
                }
                write!(f, "{name}: {ty:?}")?;
            }
            write!(f, "]")?;
        }
        writeln!(f, " {{")?;
        for block in &self.blocks {
            write!(f, "{block}")?;
        }
        writeln!(f, "}}")
    }
}

/// Complete IR program
#[derive(Debug, Clone)]
pub struct Program {
    /// All functions in the program
    pub functions: HashMap<FuncId, Function>,
    /// Main function
    pub main: FuncId,
    /// Next available function ID
    next_func_id: u32,
}

impl Program {
    /// Create a new empty program
    #[must_use]
    pub fn new() -> Self {
        Self {
            functions: HashMap::new(),
            main: FuncId::MAIN,
            next_func_id: 0,
        }
    }

    /// Add a function to the program
    pub fn add_function(&mut self, func: Function) {
        if func.id.0 >= self.next_func_id {
            self.next_func_id = func.id.0 + 1;
        }
        self.functions.insert(func.id, func);
    }

    /// Get a function by ID
    #[must_use]
    pub fn function(&self, id: FuncId) -> Option<&Function> {
        self.functions.get(&id)
    }

    /// Get a mutable reference to a function
    pub fn function_mut(&mut self, id: FuncId) -> Option<&mut Function> {
        self.functions.get_mut(&id)
    }

    /// Allocate a new function ID
    pub fn fresh_func_id(&mut self) -> FuncId {
        let id = FuncId::new(self.next_func_id);
        self.next_func_id += 1;
        id
    }
}

impl Default for Program {
    fn default() -> Self {
        Self::new()
    }
}

impl std::fmt::Display for Program {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        writeln!(f, "; RIINA IR Program")?;
        writeln!(f, "; Main: {}", self.main)?;
        writeln!(f)?;
        for func in self.functions.values() {
            write!(f, "{func}")?;
            writeln!(f)?;
        }
        Ok(())
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    // ═══════════════════════════════════════════════════════════════════
    // ID TESTS
    // ═══════════════════════════════════════════════════════════════════

    #[test]
    fn test_var_id_display() {
        assert_eq!(VarId::new(0).to_string(), "v0");
        assert_eq!(VarId::new(42).to_string(), "v42");
    }

    #[test]
    fn test_var_id_equality() {
        let v1 = VarId::new(5);
        let v2 = VarId::new(5);
        let v3 = VarId::new(6);
        assert_eq!(v1, v2);
        assert_ne!(v1, v3);
    }

    #[test]
    fn test_block_id_display() {
        assert_eq!(BlockId::ENTRY.to_string(), "bb0");
        assert_eq!(BlockId::new(5).to_string(), "bb5");
    }

    #[test]
    fn test_block_id_entry_constant() {
        assert_eq!(BlockId::ENTRY, BlockId::new(0));
    }

    #[test]
    fn test_func_id_display() {
        assert_eq!(FuncId::MAIN.to_string(), "f0");
        assert_eq!(FuncId::new(42).to_string(), "f42");
    }

    #[test]
    fn test_func_id_main_constant() {
        assert_eq!(FuncId::MAIN, FuncId::new(0));
    }

    // ═══════════════════════════════════════════════════════════════════
    // CONSTANT TESTS
    // ═══════════════════════════════════════════════════════════════════

    #[test]
    fn test_constant_display() {
        assert_eq!(Constant::Unit.to_string(), "()");
        assert_eq!(Constant::Bool(true).to_string(), "true");
        assert_eq!(Constant::Bool(false).to_string(), "false");
        assert_eq!(Constant::Int(42).to_string(), "42");
        assert_eq!(Constant::Int(-100).to_string(), "-100");
        assert_eq!(Constant::String("hello".to_string()).to_string(), "\"hello\"");
    }

    #[test]
    fn test_constant_clone() {
        let c1 = Constant::String("test".to_string());
        let c2 = c1.clone();
        assert_eq!(c1.to_string(), c2.to_string());
    }

    // ═══════════════════════════════════════════════════════════════════
    // BINOP TESTS
    // ═══════════════════════════════════════════════════════════════════

    #[test]
    fn test_binop_display_arithmetic() {
        assert_eq!(BinOp::Add.to_string(), "+");
        assert_eq!(BinOp::Sub.to_string(), "-");
        assert_eq!(BinOp::Mul.to_string(), "*");
        assert_eq!(BinOp::Div.to_string(), "/");
        assert_eq!(BinOp::Mod.to_string(), "%");
    }

    #[test]
    fn test_binop_display_comparison() {
        assert_eq!(BinOp::Eq.to_string(), "==");
        assert_eq!(BinOp::Ne.to_string(), "!=");
        assert_eq!(BinOp::Lt.to_string(), "<");
        assert_eq!(BinOp::Le.to_string(), "<=");
        assert_eq!(BinOp::Gt.to_string(), ">");
        assert_eq!(BinOp::Ge.to_string(), ">=");
    }

    #[test]
    fn test_binop_display_logical() {
        assert_eq!(BinOp::And.to_string(), "&&");
        assert_eq!(BinOp::Or.to_string(), "||");
    }

    // ═══════════════════════════════════════════════════════════════════
    // UNARYOP TESTS
    // ═══════════════════════════════════════════════════════════════════

    #[test]
    fn test_unaryop_display() {
        assert_eq!(UnaryOp::Neg.to_string(), "-");
        assert_eq!(UnaryOp::Not.to_string(), "!");
    }

    // ═══════════════════════════════════════════════════════════════════
    // INSTRUCTION TESTS
    // ═══════════════════════════════════════════════════════════════════

    #[test]
    fn test_instruction_display() {
        assert_eq!(Instruction::Const(Constant::Int(5)).to_string(), "const 5");
        assert_eq!(Instruction::Copy(VarId::new(0)).to_string(), "copy v0");
        assert_eq!(
            Instruction::BinOp(BinOp::Add, VarId::new(0), VarId::new(1)).to_string(),
            "+ v0 v1"
        );
    }

    #[test]
    fn test_instruction_display_unary() {
        assert_eq!(
            Instruction::UnaryOp(UnaryOp::Neg, VarId::new(0)).to_string(),
            "- v0"
        );
        assert_eq!(
            Instruction::UnaryOp(UnaryOp::Not, VarId::new(1)).to_string(),
            "! v1"
        );
    }

    #[test]
    fn test_instruction_display_pair_sum() {
        assert_eq!(
            Instruction::Pair(VarId::new(0), VarId::new(1)).to_string(),
            "pair v0 v1"
        );
        assert_eq!(
            Instruction::Fst(VarId::new(0)).to_string(),
            "fst v0"
        );
        assert_eq!(
            Instruction::Snd(VarId::new(0)).to_string(),
            "snd v0"
        );
        assert_eq!(
            Instruction::Inl(VarId::new(0)).to_string(),
            "inl v0"
        );
        assert_eq!(
            Instruction::Inr(VarId::new(0)).to_string(),
            "inr v0"
        );
    }

    #[test]
    fn test_instruction_display_call() {
        assert_eq!(
            Instruction::Call(FuncId::new(1), VarId::new(0)).to_string(),
            "call f1 v0"
        );
    }

    #[test]
    fn test_instruction_display_security() {
        assert_eq!(
            Instruction::Classify(VarId::new(0)).to_string(),
            "classify v0"
        );
        assert_eq!(
            Instruction::Declassify(VarId::new(0)).to_string(),
            "declassify v0"
        );
        assert_eq!(
            Instruction::Prove(VarId::new(0)).to_string(),
            "prove v0"
        );
        assert_eq!(
            Instruction::Require(VarId::new(0)).to_string(),
            "require v0"
        );
    }

    #[test]
    fn test_instruction_display_effects() {
        assert_eq!(
            Instruction::Grant(Effect::Read).to_string(),
            "grant Read"
        );
        assert_eq!(
            Instruction::Perform(Effect::Write, VarId::new(0)).to_string(),
            "perform Write v0"
        );
    }

    #[test]
    fn test_instruction_display_memory() {
        assert_eq!(
            Instruction::Alloc(VarId::new(0)).to_string(),
            "alloc v0"
        );
        assert_eq!(
            Instruction::Load(VarId::new(0)).to_string(),
            "load v0"
        );
        assert_eq!(
            Instruction::Store(VarId::new(0), VarId::new(1)).to_string(),
            "store v0 v1"
        );
    }

    // ═══════════════════════════════════════════════════════════════════
    // LABELED INSTRUCTION TESTS
    // ═══════════════════════════════════════════════════════════════════

    #[test]
    fn test_labeled_instruction() {
        let labeled = LabeledInstr {
            result: VarId::new(5),
            instr: Instruction::Const(Constant::Int(42)),
        };
        assert_eq!(labeled.to_string(), "  v5 = const 42");
    }

    // ═══════════════════════════════════════════════════════════════════
    // TERMINATOR TESTS
    // ═══════════════════════════════════════════════════════════════════

    #[test]
    fn test_terminator_display() {
        assert_eq!(
            Terminator::Return(VarId::new(0)).to_string(),
            "  ret v0"
        );
        assert_eq!(
            Terminator::Branch(BlockId::new(1)).to_string(),
            "  br bb1"
        );
    }

    #[test]
    fn test_terminator_condbranch() {
        let term = Terminator::CondBranch {
            cond: VarId::new(0),
            then_block: BlockId::new(1),
            else_block: BlockId::new(2),
        };
        assert_eq!(term.to_string(), "  br v0 bb1 bb2");
    }

    // ═══════════════════════════════════════════════════════════════════
    // BASIC BLOCK TESTS
    // ═══════════════════════════════════════════════════════════════════

    #[test]
    fn test_basic_block_creation() {
        let block = BasicBlock::new(BlockId::ENTRY);
        assert_eq!(block.id, BlockId::ENTRY);
        assert!(block.instrs.is_empty());
        assert!(matches!(block.terminator, Terminator::Return(_)));
    }

    #[test]
    fn test_basic_block_push() {
        let mut block = BasicBlock::new(BlockId::ENTRY);
        let v = block.push(Instruction::Const(Constant::Int(42)));
        assert_eq!(v, VarId::new(0));
        assert_eq!(block.instrs.len(), 1);

        let v2 = block.push(Instruction::Const(Constant::Bool(true)));
        assert_eq!(v2, VarId::new(1));
        assert_eq!(block.instrs.len(), 2);
    }

    // ═══════════════════════════════════════════════════════════════════
    // FUNCTION TESTS
    // ═══════════════════════════════════════════════════════════════════

    #[test]
    fn test_function_creation() {
        let func = Function::new(
            FuncId::MAIN,
            "main".to_string(),
            "x".to_string(),
            Ty::Unit,
            Ty::Int,
            Effect::Pure,
        );
        assert_eq!(func.id, FuncId::MAIN);
        assert_eq!(func.name, "main");
        assert_eq!(func.param, "x");
        assert_eq!(func.param_ty, Ty::Unit);
        assert_eq!(func.return_ty, Ty::Int);
        assert_eq!(func.effect, Effect::Pure);
        assert!(func.captures.is_empty());
        assert!(!func.blocks.is_empty()); // Should have entry block
    }

    #[test]
    fn test_function_entry_block() {
        let func = Function::new(
            FuncId::new(1),
            "test".to_string(),
            "y".to_string(),
            Ty::Int,
            Ty::Bool,
            Effect::Read,
        );
        assert!(func.entry().is_some());
        assert_eq!(func.entry().unwrap().id, BlockId::ENTRY);
    }

    #[test]
    fn test_function_fresh_block() {
        let mut func = Function::new(
            FuncId::MAIN,
            "main".to_string(),
            "x".to_string(),
            Ty::Unit,
            Ty::Unit,
            Effect::Pure,
        );
        let initial_blocks = func.blocks.len();
        let new_id = func.fresh_block();
        assert_eq!(func.blocks.len(), initial_blocks + 1);
        assert!(func.block(new_id).is_some());
    }

    // ═══════════════════════════════════════════════════════════════════
    // PROGRAM TESTS
    // ═══════════════════════════════════════════════════════════════════

    #[test]
    fn test_program_creation() {
        let mut prog = Program::new();
        let func = Function::new(
            FuncId::MAIN,
            "main".to_string(),
            "x".to_string(),
            Ty::Unit,
            Ty::Unit,
            Effect::Pure,
        );
        prog.add_function(func);
        assert!(prog.function(FuncId::MAIN).is_some());
    }

    #[test]
    fn test_program_default() {
        let prog = Program::default();
        assert!(prog.functions.is_empty());
        assert_eq!(prog.main, FuncId::MAIN);
    }

    #[test]
    fn test_program_fresh_func_id() {
        let mut prog = Program::new();
        let id1 = prog.fresh_func_id();
        let id2 = prog.fresh_func_id();
        assert_ne!(id1, id2);
    }

    #[test]
    fn test_program_multiple_functions() {
        let mut prog = Program::new();

        let main = Function::new(
            FuncId::MAIN,
            "main".to_string(),
            "_".to_string(),
            Ty::Unit,
            Ty::Int,
            Effect::Pure,
        );
        prog.add_function(main);

        let helper_id = prog.fresh_func_id();
        let helper = Function::new(
            helper_id,
            "helper".to_string(),
            "x".to_string(),
            Ty::Int,
            Ty::Int,
            Effect::Pure,
        );
        prog.add_function(helper);

        assert_eq!(prog.functions.len(), 2);
        assert!(prog.function(FuncId::MAIN).is_some());
        assert!(prog.function(helper_id).is_some());
    }

    #[test]
    fn test_program_function_mut() {
        let mut prog = Program::new();
        let func = Function::new(
            FuncId::MAIN,
            "main".to_string(),
            "x".to_string(),
            Ty::Unit,
            Ty::Unit,
            Effect::Pure,
        );
        prog.add_function(func);

        // Modify through mutable reference
        if let Some(f) = prog.function_mut(FuncId::MAIN) {
            f.name = "modified".to_string();
        }

        assert_eq!(prog.function(FuncId::MAIN).unwrap().name, "modified");
    }
}
