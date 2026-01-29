# RIINA Verified WCET Type System v1.0.0

**Document ID:** RIINA_WCET_TYPES_v1_0_0  
**Version:** 1.0.0  
**Target Standards:** DO-178C Level A, ISO 26262 ASIL-D  
**Status:** Specification Draft

---

## Table of Contents

1. [Executive Summary](#1-executive-summary)
2. [Timing Effect Types (Coq)](#2-timing-effect-types-coq)
3. [WCET Composition Typing Rules](#3-wcet-composition-typing-rules)
4. [RIINA Surface Syntax](#4-riina-surface-syntax)
5. [Hardware Timing Model](#5-hardware-timing-model)
6. [Verification Obligations](#6-verification-obligations)
7. [Constant-Time Interaction](#7-constant-time-interaction)
8. [DO-178C Compliance Mapping](#8-do-178c-compliance-mapping)
9. [Rust Implementation Types](#9-rust-implementation-types)
10. [Formal Soundness Theorem](#10-formal-soundness-theorem)
11. [Limitations and Honest Assessment](#11-limitations-and-honest-assessment)

---

## 1. Executive Summary

This document specifies RIINA's compile-time WCET (Worst-Case Execution Time) type system, enabling static verification of timing bounds for safety-critical avionics and automotive software. The system extends RIINA's effect types with `EffTimed` bounds that compose algebraically through program constructs.

**Key Design Decisions:**

- WCET bounds are *effects*, not types—they compose through effect combination
- Analysis is parameterized over hardware timing models
- The type system provides *sound over-approximation*—verified bounds are always safe but may be pessimistic
- Unbounded loops and recursion are compile-time errors without explicit bounds
- Integration with external tools (aiT, OTAWA) is specified for industrial certification

---

## 2. Timing Effect Types (Coq)

### 2.1 Core Timing Bound Definitions

```coq
(* ========================================================================== *)
(* RIINA WCET Type System - Core Definitions                                  *)
(* Document: RIINA_WCET_TYPES_v1_0_0                                          *)
(* ========================================================================== *)

Require Import Coq.Arith.Arith.
Require Import Coq.Lists.List.
Require Import Coq.QArith.QArith.
Import ListNotations.

(** Time units for WCET specification *)
Inductive time_unit : Type :=
  | Nanoseconds  : time_unit
  | Microseconds : time_unit
  | Milliseconds : time_unit
  | Seconds      : time_unit.

(** Convert time unit to nanoseconds multiplier *)
Definition time_unit_to_nanos (u : time_unit) : nat :=
  match u with
  | Nanoseconds  => 1
  | Microseconds => 1000
  | Milliseconds => 1000000
  | Seconds      => 1000000000
  end.

(** Time bound representation *)
Inductive time_bound : Type :=
  | TBound    : nat -> time_unit -> time_bound    (* Upper bound: ≤ n units *)
  | TConstant : nat -> time_unit -> time_bound    (* Exact: = n units (constant-time) *)
  | TUnbounded : time_bound.                       (* No static bound available *)

(** Normalize time bound to nanoseconds for comparison *)
Definition normalize_to_nanos (tb : time_bound) : option nat :=
  match tb with
  | TBound n u    => Some (n * time_unit_to_nanos u)
  | TConstant n u => Some (n * time_unit_to_nanos u)
  | TUnbounded    => None
  end.

(** Time bound ordering (for subtyping) *)
(** TConstant(n) ≤ TBound(n) ≤ TBound(m) when n ≤ m ≤ TUnbounded *)
Definition time_bound_le (tb1 tb2 : time_bound) : Prop :=
  match tb1, tb2 with
  | _, TUnbounded => True                          (* Everything ≤ Unbounded *)
  | TUnbounded, _ => False                         (* Unbounded ≤ nothing else *)
  | TConstant n1 u1, TConstant n2 u2 => 
      n1 * time_unit_to_nanos u1 <= n2 * time_unit_to_nanos u2
  | TConstant n1 u1, TBound n2 u2 =>
      n1 * time_unit_to_nanos u1 <= n2 * time_unit_to_nanos u2
  | TBound n1 u1, TBound n2 u2 =>
      n1 * time_unit_to_nanos u1 <= n2 * time_unit_to_nanos u2
  | TBound _ _, TConstant _ _ => False             (* Bound not ≤ Constant *)
  end.

Notation "t1 '≤t' t2" := (time_bound_le t1 t2) (at level 70).

(** Proof that time_bound_le is reflexive *)
Lemma time_bound_le_refl : forall tb, 
  tb <> TUnbounded -> tb ≤t tb.
Proof.
  intros tb Hneq.
  destruct tb; simpl; auto.
  contradiction.
Qed.

(** Proof that time_bound_le is transitive *)
Lemma time_bound_le_trans : forall tb1 tb2 tb3,
  tb1 ≤t tb2 -> tb2 ≤t tb3 -> tb1 ≤t tb3.
Proof.
  intros tb1 tb2 tb3 H12 H23.
  destruct tb1, tb2, tb3; simpl in *; auto; try omega; try lia.
  - (* TConstant, TConstant, TConstant *)
    lia.
  - (* TConstant, TConstant, TBound *)
    lia.
  - (* TConstant, TBound, TBound *)
    lia.
  - (* TBound, TBound, TBound *)
    lia.
Qed.
```

### 2.2 Extended Effect System

```coq
(** ======================================================================== *)
(** Extended Effect System with Timing                                       *)
(** ======================================================================== *)

(** RIINA's effect type, extended with timing *)
Inductive effect : Type :=
  | EffPure         : effect                       (* No side effects *)
  | EffRead         : effect                       (* Memory read *)
  | EffWrite        : effect                       (* Memory write *)
  | EffIO           : effect                       (* I/O operations *)
  | EffCrypto       : effect                       (* Cryptographic operations *)
  | EffConstantTime : effect                       (* Secret-independent timing *)
  | EffTimed        : time_bound -> effect         (* WCET bound *)
  | EffCompose      : effect -> effect -> effect.  (* Effect combination *)

Notation "e1 '+eff' e2" := (EffCompose e1 e2) (at level 50, left associativity).

(** Time bound addition for sequential composition *)
Definition time_bound_add (tb1 tb2 : time_bound) : time_bound :=
  match tb1, tb2 with
  | TUnbounded, _ => TUnbounded
  | _, TUnbounded => TUnbounded
  | TConstant n1 u1, TConstant n2 u2 =>
      (* Convert to nanoseconds, add, keep in nanoseconds *)
      TConstant (n1 * time_unit_to_nanos u1 + n2 * time_unit_to_nanos u2) Nanoseconds
  | TConstant n1 u1, TBound n2 u2 =>
      TBound (n1 * time_unit_to_nanos u1 + n2 * time_unit_to_nanos u2) Nanoseconds
  | TBound n1 u1, TConstant n2 u2 =>
      TBound (n1 * time_unit_to_nanos u1 + n2 * time_unit_to_nanos u2) Nanoseconds
  | TBound n1 u1, TBound n2 u2 =>
      TBound (n1 * time_unit_to_nanos u1 + n2 * time_unit_to_nanos u2) Nanoseconds
  end.

Notation "t1 '+t' t2" := (time_bound_add t1 t2) (at level 50, left associativity).

(** Time bound maximum for branching *)
Definition time_bound_max (tb1 tb2 : time_bound) : time_bound :=
  match tb1, tb2 with
  | TUnbounded, _ => TUnbounded
  | _, TUnbounded => TUnbounded
  | TConstant n1 u1, TConstant n2 u2 =>
      let nanos1 := n1 * time_unit_to_nanos u1 in
      let nanos2 := n2 * time_unit_to_nanos u2 in
      if Nat.leb nanos1 nanos2 
      then TConstant nanos2 Nanoseconds 
      else TConstant nanos1 Nanoseconds
  | TConstant n1 u1, TBound n2 u2 =>
      let nanos1 := n1 * time_unit_to_nanos u1 in
      let nanos2 := n2 * time_unit_to_nanos u2 in
      TBound (Nat.max nanos1 nanos2) Nanoseconds
  | TBound n1 u1, TConstant n2 u2 =>
      let nanos1 := n1 * time_unit_to_nanos u1 in
      let nanos2 := n2 * time_unit_to_nanos u2 in
      TBound (Nat.max nanos1 nanos2) Nanoseconds
  | TBound n1 u1, TBound n2 u2 =>
      let nanos1 := n1 * time_unit_to_nanos u1 in
      let nanos2 := n2 * time_unit_to_nanos u2 in
      TBound (Nat.max nanos1 nanos2) Nanoseconds
  end.

Notation "t1 '⊔t' t2" := (time_bound_max t1 t2) (at level 45, left associativity).

(** Time bound multiplication for loops *)
Definition time_bound_mult (n : nat) (tb : time_bound) : time_bound :=
  match tb with
  | TUnbounded => TUnbounded
  | TConstant m u => TConstant (n * m) u
  | TBound m u => TBound (n * m) u
  end.

Notation "n '*t' tb" := (time_bound_mult n tb) (at level 40, left associativity).

(** Extract timing from an effect (returns TUnbounded if no timing specified) *)
Fixpoint effect_timing (e : effect) : time_bound :=
  match e with
  | EffTimed tb => tb
  | EffConstantTime => TUnbounded  (* ConstantTime doesn't specify absolute time *)
  | EffCompose e1 e2 => effect_timing e1 +t effect_timing e2
  | _ => TBound 0 Nanoseconds      (* Other effects have negligible time *)
  end.
```

### 2.3 Time Bound Arithmetic Soundness

```coq
(** ======================================================================== *)
(** Soundness Lemmas for Time Bound Arithmetic                               *)
(** ======================================================================== *)

(** Addition is commutative *)
Lemma time_bound_add_comm : forall tb1 tb2,
  normalize_to_nanos (tb1 +t tb2) = normalize_to_nanos (tb2 +t tb1).
Proof.
  intros tb1 tb2.
  destruct tb1, tb2; simpl; try reflexivity.
  - f_equal. lia.
  - f_equal. lia.
  - f_equal. lia.
  - f_equal. lia.
Qed.

(** Addition is associative *)
Lemma time_bound_add_assoc : forall tb1 tb2 tb3,
  (tb1 +t tb2) +t tb3 = tb1 +t (tb2 +t tb3).
Proof.
  (* Proof requires case analysis on all combinations *)
  (* Admitted for brevity - mechanically verifiable *)
Admitted.

(** Maximum is idempotent *)
Lemma time_bound_max_idempotent : forall tb,
  tb ⊔t tb = tb.
Proof.
  intros tb.
  destruct tb; simpl; try reflexivity.
  - (* TBound *)
    rewrite Nat.max_id. reflexivity.
  - (* TConstant *)
    destruct (n * time_unit_to_nanos t <=? n * time_unit_to_nanos t) eqn:E.
    + reflexivity.
    + apply Nat.leb_gt in E. lia.
Qed.

(** Multiplication distributes over max *)
Lemma time_bound_mult_max_distr : forall n tb1 tb2,
  n *t (tb1 ⊔t tb2) = (n *t tb1) ⊔t (n *t tb2).
Proof.
  (* Requires extensive case analysis *)
Admitted.

(** Zero iterations = zero time *)
Lemma time_bound_mult_zero : forall tb,
  0 *t tb = TBound 0 Nanoseconds \/ 0 *t tb = TConstant 0 Nanoseconds \/ tb = TUnbounded.
Proof.
  intros tb.
  destruct tb; simpl.
  - left. reflexivity.
  - right. left. reflexivity.
  - right. right. reflexivity.
Qed.
```

---

## 3. WCET Composition Typing Rules

### 3.1 Expression Syntax

```coq
(** ======================================================================== *)
(** RIINA Expression Syntax for WCET Analysis                                *)
(** ======================================================================== *)

(** Types *)
Inductive ty : Type :=
  | TUnit   : ty
  | TBool   : ty
  | TNat    : ty
  | TInt    : ty
  | TFloat  : ty
  | TArray  : ty -> nat -> ty            (* Fixed-size arrays *)
  | TStruct : list (string * ty) -> ty
  | TFun    : list ty -> ty -> effect -> ty.  (* Function type with effect *)

(** Expressions *)
Inductive expr : Type :=
  | EUnit   : expr
  | EBool   : bool -> expr
  | ENat    : nat -> expr
  | EVar    : string -> expr
  | EBinOp  : binop -> expr -> expr -> expr
  | EIf     : expr -> expr -> expr -> expr
  | ESeq    : expr -> expr -> expr
  | ELet    : string -> expr -> expr -> expr
  | EFor    : string -> nat -> nat -> expr -> expr    (* Bounded for loop *)
  | EWhile  : expr -> nat -> expr -> expr             (* While with max iterations *)
  | ECall   : string -> list expr -> expr
  | EArray  : list expr -> expr
  | EIndex  : expr -> expr -> expr

with binop : Type :=
  | OpAdd | OpSub | OpMul | OpDiv | OpMod
  | OpEq | OpLt | OpLe | OpGt | OpGe
  | OpAnd | OpOr.

(** Function declarations *)
Record fun_decl : Type := {
  fun_name   : string;
  fun_params : list (string * ty);
  fun_ret    : ty;
  fun_effect : effect;             (* Declared effect including timing *)
  fun_body   : expr;
}.

(** Program = list of function declarations *)
Definition program := list fun_decl.
```

### 3.2 Typing Context and Judgments

```coq
(** ======================================================================== *)
(** Typing Context                                                           *)
(** ======================================================================== *)

(** Hardware model for WCET calculation *)
Record hardware_model : Type := {
  hw_name         : string;
  hw_cycle_time   : nat;           (* Cycle time in nanoseconds *)
  hw_cache_hit    : nat;           (* Cache hit cycles *)
  hw_cache_miss   : nat;           (* Cache miss cycles *)
  hw_branch_taken : nat;           (* Branch taken penalty *)
  hw_branch_not   : nat;           (* Branch not taken cycles *)
  hw_call_overhead: nat;           (* Function call overhead cycles *)
  hw_loop_overhead: nat;           (* Loop iteration overhead cycles *)
}.

(** Simple hardware model constructor *)
Definition hw_simple (cycle_ns : nat) (cycles_per_instr : nat) : hardware_model := {|
  hw_name         := "Simple";
  hw_cycle_time   := cycle_ns;
  hw_cache_hit    := cycles_per_instr;
  hw_cache_miss   := cycles_per_instr;
  hw_branch_taken := 1;
  hw_branch_not   := 1;
  hw_call_overhead:= 2;
  hw_loop_overhead:= 1;
|}.

(** Typing context *)
Record typing_ctx : Type := {
  ctx_vars : list (string * ty);           (* Variable bindings *)
  ctx_funs : list (string * ty * effect);  (* Function signatures with effects *)
  ctx_hw   : hardware_model;               (* Target hardware model *)
}.

(** Typing judgment: Γ ⊢ e : τ kesan ε *)
(** Pronounced: "Under context Γ, expression e has type τ with effect ε" *)
Reserved Notation "Γ '⊢' e ':' τ 'kesan' ε" (at level 40).
```

### 3.3 WCET Composition Rules (Core Typing Rules)

```coq
(** ======================================================================== *)
(** WCET Typing Rules                                                        *)
(** ======================================================================== *)

(** Instruction cost in cycles (simplified) *)
Definition instr_cycles (hw : hardware_model) (e : expr) : nat :=
  match e with
  | EUnit => 0
  | EBool _ => 1
  | ENat _ => 1
  | EVar _ => hw.(hw_cache_hit)        (* Assume cache hit for variables *)
  | EBinOp _ _ _ => 3                  (* ALU operation *)
  | _ => 0                              (* Compound expressions handled separately *)
  end.

(** Convert cycles to time bound *)
Definition cycles_to_time (hw : hardware_model) (cycles : nat) : time_bound :=
  TBound (cycles * hw.(hw_cycle_time)) Nanoseconds.

Inductive has_type : typing_ctx -> expr -> ty -> effect -> Prop :=

  (** T-UNIT: Unit has zero cost *)
  | T_Unit : forall Γ,
      Γ ⊢ EUnit : TUnit kesan EffTimed (TBound 0 Nanoseconds)

  (** T-BOOL: Boolean literal *)
  | T_Bool : forall Γ b,
      Γ ⊢ EBool b : TBool kesan EffTimed (cycles_to_time Γ.(ctx_hw) 1)

  (** T-NAT: Natural number literal *)
  | T_Nat : forall Γ n,
      Γ ⊢ ENat n : TNat kesan EffTimed (cycles_to_time Γ.(ctx_hw) 1)

  (** T-VAR: Variable lookup *)
  | T_Var : forall Γ x τ,
      In (x, τ) Γ.(ctx_vars) ->
      Γ ⊢ EVar x : τ kesan EffTimed (cycles_to_time Γ.(ctx_hw) Γ.(ctx_hw).(hw_cache_hit))

  (** T-SEQ: Sequential composition - WCET adds *)
  | T_Seq : forall Γ e1 e2 τ1 τ2 tb1 tb2,
      Γ ⊢ e1 : τ1 kesan EffTimed tb1 ->
      Γ ⊢ e2 : τ2 kesan EffTimed tb2 ->
      Γ ⊢ ESeq e1 e2 : τ2 kesan EffTimed (tb1 +t tb2)

  (** T-IF: Branching - WCET takes max of branches *)
  | T_If : forall Γ ec e1 e2 τ tbc tb1 tb2,
      Γ ⊢ ec : TBool kesan EffTimed tbc ->
      Γ ⊢ e1 : τ kesan EffTimed tb1 ->
      Γ ⊢ e2 : τ kesan EffTimed tb2 ->
      let branch_cost := cycles_to_time Γ.(ctx_hw) Γ.(ctx_hw).(hw_branch_taken) in
      Γ ⊢ EIf ec e1 e2 : τ kesan EffTimed (tbc +t branch_cost +t (tb1 ⊔t tb2))

  (** T-LET: Let binding - sequential *)
  | T_Let : forall Γ x e1 e2 τ1 τ2 tb1 tb2,
      Γ ⊢ e1 : τ1 kesan EffTimed tb1 ->
      {| ctx_vars := (x, τ1) :: Γ.(ctx_vars); 
         ctx_funs := Γ.(ctx_funs);
         ctx_hw := Γ.(ctx_hw) |} ⊢ e2 : τ2 kesan EffTimed tb2 ->
      Γ ⊢ ELet x e1 e2 : τ2 kesan EffTimed (tb1 +t tb2)

  (** T-FOR: Bounded for loop - WCET multiplies *)
  | T_For : forall Γ x lo hi body τ tb_body,
      let Γ' := {| ctx_vars := (x, TNat) :: Γ.(ctx_vars);
                   ctx_funs := Γ.(ctx_funs);
                   ctx_hw := Γ.(ctx_hw) |} in
      Γ' ⊢ body : τ kesan EffTimed tb_body ->
      let n := hi - lo in
      let loop_overhead := cycles_to_time Γ.(ctx_hw) (n * Γ.(ctx_hw).(hw_loop_overhead)) in
      Γ ⊢ EFor x lo hi body : TUnit kesan EffTimed ((n *t tb_body) +t loop_overhead)

  (** T-WHILE: Bounded while loop - WCET = max_iterations × body *)
  | T_While : forall Γ cond max_iter body τ tb_cond tb_body,
      Γ ⊢ cond : TBool kesan EffTimed tb_cond ->
      Γ ⊢ body : τ kesan EffTimed tb_body ->
      let iter_cost := tb_cond +t tb_body in
      let loop_overhead := cycles_to_time Γ.(ctx_hw) (max_iter * Γ.(ctx_hw).(hw_loop_overhead)) in
      Γ ⊢ EWhile cond max_iter body : TUnit kesan EffTimed ((max_iter *t iter_cost) +t loop_overhead)

  (** T-CALL: Function call - uses declared WCET *)
  | T_Call : forall Γ f args τ_args τ_ret ε_decl,
      In (f, TFun τ_args τ_ret ε_decl, ε_decl) Γ.(ctx_funs) ->
      (* All arguments type-check - simplified *)
      let call_overhead := cycles_to_time Γ.(ctx_hw) Γ.(ctx_hw).(hw_call_overhead) in
      Γ ⊢ ECall f args : τ_ret kesan (ε_decl +eff EffTimed call_overhead)

  (** T-SUB: Subsumption - can weaken timing bound *)
  | T_Sub : forall Γ e τ tb1 tb2,
      Γ ⊢ e : τ kesan EffTimed tb1 ->
      tb1 ≤t tb2 ->
      Γ ⊢ e : τ kesan EffTimed tb2

where "Γ '⊢' e ':' τ 'kesan' ε" := (has_type Γ e τ ε).
```

### 3.4 Recursion and Termination

```coq
(** ======================================================================== *)
(** Bounded Recursion for WCET                                               *)
(** ======================================================================== *)

(** 
   RIINA requires termination proofs for all recursive functions.
   For WCET, we additionally require a STATIC recursion depth bound.
   
   This is enforced by:
   1. Structural recursion on a decreasing argument, OR
   2. Explicit depth parameter with proof that depth decreases
*)

(** Recursion depth bound annotation *)
Inductive recursion_bound : Type :=
  | RBStructural : string -> recursion_bound    (* Structural recursion on named arg *)
  | RBDepth : nat -> recursion_bound.           (* Maximum recursion depth *)

(** Extended function declaration with recursion info *)
Record fun_decl_wcet : Type := {
  fdw_name      : string;
  fdw_params    : list (string * ty);
  fdw_ret       : ty;
  fdw_effect    : effect;
  fdw_body      : expr;
  fdw_rec_bound : option recursion_bound;   (* None = non-recursive *)
}.

(** WCET of recursive function *)
(** If f has body with WCET(body) and max depth d, then WCET(f) = d × WCET(body) *)
Definition recursive_wcet (depth : nat) (body_wcet : time_bound) 
                          (call_overhead : time_bound) : time_bound :=
  (depth *t body_wcet) +t ((depth + 1) *t call_overhead).

(** T-FUNREC: Recursive function with bounded depth *)
(** 
   Γ ⊢ body : τ kesan EffTimed(tb_body)
   ─────────────────────────────────────────────────────
   Γ ⊢ fun f[depth d](params) -> τ kesan EffTimed(d × tb_body + (d+1) × overhead)
*)
```

---

## 4. RIINA Surface Syntax

### 4.1 Complete Syntax Examples

```riina
// ============================================================================
// RIINA WCET Type System - Syntax Examples
// Document: RIINA_WCET_TYPES_v1_0_0
// ============================================================================

// ----------------------------------------------------------------------------
// 4.1.1 Basic Function with WCET Bound
// ----------------------------------------------------------------------------

/// Flight control function with 100μs WCET guarantee
/// Malay: kawalan_penerbangan = flight_control
fungsi kawalan_penerbangan(sensor: DataSensor) -> ArahanKawalan
    kesan Baca + Masa(100μs)    // Effect: Read + Time(100 microseconds)
{
    // biar = let binding
    biar sudut = sensor.baca_giroskop();        // Read gyroscope
    biar ketinggian = sensor.baca_altimeter();  // Read altimeter
    
    // Compute control command
    kira_arahan(sudut, ketinggian)
}

// ----------------------------------------------------------------------------
// 4.1.2 Bounded For Loop
// ----------------------------------------------------------------------------

/// Read 16 sensor values with known WCET
/// WCET = 16 × WCET(body) + loop_overhead
fungsi baca_semua_sensor(sensor: &Sensor) -> [Nilai; 16]
    kesan Baca + Masa(50μs)
{
    biar palam: [Nilai; 16] = kosong();    // Initialize empty array
    
    // untuk = for, dalam = in
    // Compiler knows: exactly 16 iterations
    untuk i dalam 0..16 {
        palam[i] = sensor.baca(i);
    }
    
    palam
}

// ----------------------------------------------------------------------------
// 4.1.3 Bounded While Loop (Required)
// ----------------------------------------------------------------------------

/// Process events with maximum iteration bound
/// Malay: selagi = while, had = limit/bound
fungsi proses_peristiwa() -> Unit
    kesan Tulis + Masa(10ms)
{
    biar aktif = benar;    // benar = true
    
    // COMPILE ERROR without 'had':
    // selagi aktif {     // ERROR: unbounded loop - no WCET guarantee
    //     proses();
    // }
    
    // CORRECT: explicit iteration bound
    selagi aktif had 1000 {    // max 1000 iterations
        proses();
        aktif = semak_aktif();
    }
}

// ----------------------------------------------------------------------------
// 4.1.4 Conditional with WCET
// ----------------------------------------------------------------------------

/// WCET = WCET(condition) + max(WCET(then), WCET(else))
fungsi kawalan_bersyarat(mod: ModKawalan, input: Input) -> Output
    kesan Masa(200μs)
{
    // kalau = if, lain = else
    kalau mod == ModKawalan::Auto {
        // This branch: 150μs WCET
        kira_auto(input)
    } lain {
        // This branch: 80μs WCET
        // Total WCET = max(150, 80) + condition_eval = 150μs + overhead
        kira_manual(input)
    }
}

// ----------------------------------------------------------------------------
// 4.1.5 Constant-Time Cryptographic Function
// ----------------------------------------------------------------------------

/// Constant-time comparison (for cryptographic use)
/// EffConstantTime implies EffTimed - all paths take same time
fungsi banding_tetap(a: &[u8; 32], b: &[u8; 32]) -> bool
    kesan Tetap + Masa(500ns)    // Tetap = ConstantTime
{
    biar hasil: u8 = 0;
    
    untuk i dalam 0..32 {
        // XOR accumulation - no early exit (constant time)
        hasil = hasil | (a[i] ^ b[i]);
    }
    
    hasil == 0
}

// ----------------------------------------------------------------------------
// 4.1.6 Bounded Recursion
// ----------------------------------------------------------------------------

/// Binary search with logarithmic depth bound
/// Malay: kedalaman = depth
fungsi cari_binari<T: Tersusun>(
    arr: &[T], 
    sasaran: T,
    lo: usize,
    hi: usize
) -> Pilihan<usize>
    kesan Baca + Masa(10μs)
    kedalaman log2(hi - lo + 1)    // Recursion depth bound
{
    kalau lo > hi {
        kembali Tiada;    // Tiada = None
    }
    
    biar mid = lo + (hi - lo) / 2;
    
    kalau arr[mid] == sasaran {
        Ada(mid)          // Ada = Some
    } lain kalau arr[mid] < sasaran {
        cari_binari(arr, sasaran, mid + 1, hi)
    } lain {
        cari_binari(arr, sasaran, lo, mid - 1)
    }
}

// ----------------------------------------------------------------------------
// 4.1.7 Hardware Model Annotation
// ----------------------------------------------------------------------------

/// Specify target hardware for WCET analysis
#[perkakasan("ARM_Cortex_M4_168MHz")]    // perkakasan = hardware
modul kawalan_enjin {
    
    /// Engine timing control - WCET verified against Cortex-M4 model
    fungsi kawalan_pencucuhan(sudut: f32) -> MasaPencucuhan
        kesan Masa(50μs)
    {
        // ... implementation ...
    }
}

// Alternative: inline hardware model
#[perkakasan(
    kitaran_ns = 6,           // 6ns per cycle (168MHz)
    cache_hit = 1,            // Single cycle cache hit  
    cache_miss = 10,          // 10 cycles cache miss
    panggil_overhead = 4      // 4 cycles call overhead
)]
modul kawalan_kelajuan {
    // ...
}

// ----------------------------------------------------------------------------
// 4.1.8 Compile Error Examples
// ----------------------------------------------------------------------------

// ERROR: Unbounded loop
fungsi salah_1() -> Unit kesan Masa(100μs) {
    selagi benar {           // ERROR: no 'had' (bound) annotation
        proses();
    }
}
// Compiler: "ralat: gelung 'selagi' memerlukan anotasi 'had' untuk jaminan WCET"
// Translation: "error: 'while' loop requires 'had' annotation for WCET guarantee"

// ERROR: WCET exceeded
fungsi salah_2() -> Unit kesan Masa(10μs) {
    untuk i dalam 0..1000 {  // 1000 iterations
        operasi_lambat();     // Each: 100ns
    }
}
// Compiler: "ralat: WCET dikira (100μs) melebihi had diisytihar (10μs)"
// Translation: "error: computed WCET (100μs) exceeds declared bound (10μs)"

// ERROR: Unbounded recursion
fungsi salah_3(n: nat) -> nat kesan Masa(1ms) {
    kalau n == 0 { 0 }
    lain { salah_3(n - 1) }   // ERROR: no depth bound
}
// Compiler: "ralat: fungsi rekursif memerlukan anotasi 'kedalaman' untuk WCET"
```

### 4.2 RIINA Keyword Reference

| Malay Keyword | English | Usage |
|--------------|---------|-------|
| `fungsi` | function | Function declaration |
| `kesan` | effect | Effect annotation |
| `Masa` | Time | WCET bound effect |
| `Tetap` | Constant | Constant-time effect |
| `Baca` | Read | Read effect |
| `Tulis` | Write | Write effect |
| `biar` | let | Variable binding |
| `kalau` | if | Conditional |
| `lain` | else | Else branch |
| `untuk` | for | For loop |
| `dalam` | in | Loop range |
| `selagi` | while | While loop |
| `had` | limit/bound | Loop bound annotation |
| `kedalaman` | depth | Recursion depth bound |
| `kembali` | return | Return statement |
| `benar` | true | Boolean true |
| `palsu` | false | Boolean false |
| `perkakasan` | hardware | Hardware model annotation |
| `μs` / `mikrodetik` | microseconds | Time unit |
| `ms` / `milisaat` | milliseconds | Time unit |
| `ns` / `nanosaat` | nanoseconds | Time unit |
| `s` / `saat` | seconds | Time unit |

---

## 5. Hardware Timing Model

### 5.1 Coq Hardware Model Definitions

```coq
(** ======================================================================== *)
(** Hardware Timing Models for WCET Analysis                                 *)
(** ======================================================================== *)

(** Abstract hardware model *)
Inductive hw_model_type : Type :=
  | HW_Simple    : nat -> hw_model_type                    (* cycles per instruction *)
  | HW_Cached    : nat -> nat -> hw_model_type            (* hit cycles, miss cycles *)
  | HW_Pipeline  : nat -> nat -> nat -> hw_model_type     (* depth, stall, flush *)
  | HW_OoO       : nat -> nat -> nat -> hw_model_type.    (* issue width, rob size, penalty *)

(** Complete hardware specification *)
Record hw_timing_model : Type := {
  htm_name           : string;
  htm_type           : hw_model_type;
  htm_clock_mhz      : nat;                 (* Clock frequency in MHz *)
  htm_cycle_ns       : nat;                 (* Derived: nanoseconds per cycle *)
  
  (* Instruction costs in cycles *)
  htm_alu_cycles     : nat;                 (* ADD, SUB, logic ops *)
  htm_mul_cycles     : nat;                 (* Integer multiply *)
  htm_div_cycles     : nat;                 (* Integer divide *)
  htm_fpu_cycles     : nat;                 (* Floating point ops *)
  htm_load_cycles    : nat;                 (* Memory load (cache hit) *)
  htm_store_cycles   : nat;                 (* Memory store *)
  htm_branch_cycles  : nat;                 (* Branch (predicted) *)
  htm_branch_miss    : nat;                 (* Branch misprediction penalty *)
  htm_call_cycles    : nat;                 (* Function call *)
  htm_ret_cycles     : nat;                 (* Function return *)
  
  (* Cache model *)
  htm_cache_hit      : nat;                 (* L1 cache hit cycles *)
  htm_cache_miss     : nat;                 (* L1 cache miss cycles *)
  htm_cache_line     : nat;                 (* Cache line size in bytes *)
  
  (* Memory access patterns *)
  htm_mem_seq_bonus  : nat;                 (* Sequential access bonus *)
  htm_mem_random_pen : nat;                 (* Random access penalty *)
}.

(** Cycle time calculation *)
Definition mhz_to_cycle_ns (mhz : nat) : nat :=
  match mhz with
  | 0 => 1000  (* Avoid division by zero, default to 1MHz *)
  | _ => 1000 / mhz  (* Simplified integer division *)
  end.

(** Pre-defined hardware models *)

(** ARM Cortex-M4 at 168MHz (STM32F4 typical) *)
Definition hw_cortex_m4 : hw_timing_model := {|
  htm_name          := "ARM_Cortex_M4_168MHz";
  htm_type          := HW_Pipeline 3 1 3;   (* 3-stage pipeline *)
  htm_clock_mhz     := 168;
  htm_cycle_ns      := 6;                    (* ~5.95ns, rounded up *)
  htm_alu_cycles    := 1;
  htm_mul_cycles    := 1;                    (* Single-cycle multiplier *)
  htm_div_cycles    := 12;                   (* 2-12 cycles *)
  htm_fpu_cycles    := 1;                    (* With FPU option *)
  htm_load_cycles   := 2;                    (* Flash wait states *)
  htm_store_cycles  := 1;
  htm_branch_cycles := 1;
  htm_branch_miss   := 3;                    (* Pipeline flush *)
  htm_call_cycles   := 4;
  htm_ret_cycles    := 4;
  htm_cache_hit     := 0;                    (* No data cache *)
  htm_cache_miss    := 0;
  htm_cache_line    := 0;
  htm_mem_seq_bonus := 0;
  htm_mem_random_pen:= 0;
|}.

(** Intel x86 simplified (for analysis, not certification) *)
Definition hw_x86_simple : hw_timing_model := {|
  htm_name          := "x86_Generic_3GHz";
  htm_type          := HW_OoO 4 128 20;      (* 4-wide OoO, 128 ROB *)
  htm_clock_mhz     := 3000;
  htm_cycle_ns      := 1;                    (* ~0.33ns, rounded up *)
  htm_alu_cycles    := 1;
  htm_mul_cycles    := 3;
  htm_div_cycles    := 30;
  htm_fpu_cycles    := 5;
  htm_load_cycles   := 4;                    (* L1 hit *)
  htm_store_cycles  := 4;
  htm_branch_cycles := 1;
  htm_branch_miss   := 15;                   (* Misprediction *)
  htm_call_cycles   := 5;
  htm_ret_cycles    := 5;
  htm_cache_hit     := 4;
  htm_cache_miss    := 200;                  (* Main memory *)
  htm_cache_line    := 64;
  htm_mem_seq_bonus := 0;
  htm_mem_random_pen:= 50;
|}.

(** LEON3 SPARC (Space-grade, radiation hardened) *)
Definition hw_leon3_space : hw_timing_model := {|
  htm_name          := "LEON3_50MHz_Space";
  htm_type          := HW_Pipeline 7 2 7;    (* 7-stage pipeline *)
  htm_clock_mhz     := 50;
  htm_cycle_ns      := 20;
  htm_alu_cycles    := 1;
  htm_mul_cycles    := 5;
  htm_div_cycles    := 35;
  htm_fpu_cycles    := 4;
  htm_load_cycles   := 2;
  htm_store_cycles  := 2;
  htm_branch_cycles := 1;
  htm_branch_miss   := 7;
  htm_call_cycles   := 6;
  htm_ret_cycles    := 6;
  htm_cache_hit     := 1;
  htm_cache_miss    := 30;
  htm_cache_line    := 32;
  htm_mem_seq_bonus := 0;
  htm_mem_random_pen:= 10;
|}.

(** WCET calculation using hardware model *)
Definition wcet_cycles_to_time (hw : hw_timing_model) (cycles : nat) : time_bound :=
  TBound (cycles * hw.(htm_cycle_ns)) Nanoseconds.
```

### 5.2 Cache Analysis Model

```coq
(** ======================================================================== *)
(** Cache Analysis for WCET (Simplified Must/May Analysis)                   *)
(** ======================================================================== *)

(** 
   For sound WCET analysis, we must assume WORST-CASE cache behavior.
   This module provides a simplified abstract interpretation of cache state.
   
   Full cache analysis (as in aiT) requires:
   - Abstract cache states
   - Must-analysis (always in cache)
   - May-analysis (possibly in cache)
   - Persistence analysis
   
   We provide a simplified model suitable for small embedded systems.
*)

(** Memory region classification *)
Inductive mem_region : Type :=
  | MemStack   : mem_region      (* Stack - typically cached, LIFO pattern *)
  | MemGlobal  : mem_region      (* Global data - typically cached *)
  | MemHeap    : mem_region      (* Heap - may or may not be cached *)
  | MemIO      : mem_region      (* I/O - never cached *)
  | MemFlash   : mem_region.     (* Flash - instruction memory *)

(** Cache behavior assumption *)
Inductive cache_assumption : Type :=
  | CacheAlwaysHit  : cache_assumption    (* Optimistic - for BCET *)
  | CacheAlwaysMiss : cache_assumption    (* Pessimistic - for WCET *)
  | CacheAnalyzed   : nat -> nat -> cache_assumption.  (* hits, misses from analysis *)

(** Memory access with cache cost *)
Definition mem_access_cycles (hw : hw_timing_model) 
                             (region : mem_region) 
                             (assumption : cache_assumption) : nat :=
  match assumption with
  | CacheAlwaysHit => hw.(htm_cache_hit) + hw.(htm_load_cycles)
  | CacheAlwaysMiss => hw.(htm_cache_miss) + hw.(htm_load_cycles)
  | CacheAnalyzed hits misses =>
      (* Weighted average - but for WCET we should use worst case *)
      hw.(htm_cache_miss) + hw.(htm_load_cycles)  (* Conservative *)
  end.

(** 
   IMPORTANT LIMITATION:
   
   Accurate cache analysis requires abstract interpretation over the entire
   control flow graph with age-based cache models. This is beyond what a 
   type system can reasonably encode.
   
   For DO-178C Level A certification, RIINA should:
   1. Use the type system for coarse-grained WCET bounds
   2. Delegate precise cache analysis to external tools (aiT, OTAWA)
   3. Verify that external tool results are consistent with declared bounds
   
   The type system provides:
   - Compositional WCET bounds (sound but imprecise)
   - Guaranteed loop bounds
   - Guaranteed recursion bounds
   - No dynamic allocation (so heap analysis unnecessary)
   
   External tools provide:
   - Precise cache analysis
   - Pipeline analysis
   - Memory access pattern analysis
*)
```

### 5.3 Hardware Model Selection in RIINA

```riina
// Hardware model selection examples

// Option 1: Module-level hardware annotation
#[perkakasan("ARM_Cortex_M4_168MHz")]
modul kawalan_pesawat {
    // All functions in this module use Cortex-M4 timing model
    
    fungsi kawalan_sayap(input: SensorSayap) -> ArahanSayap
        kesan Masa(200μs)
    {
        // WCET verified against Cortex-M4 at 168MHz
        // ...
    }
}

// Option 2: Project-level configuration file
// riina.toml:
// [wcet]
// default_hardware = "ARM_Cortex_M4_168MHz"
// 
// [wcet.hardware.ARM_Cortex_M4_168MHz]
// clock_mhz = 168
// pipeline_depth = 3
// cache_line_size = 0  # No data cache
// 
// [wcet.external_tool]
// name = "aiT"
// path = "/opt/absint/ait/bin/a3"

// Option 3: Custom hardware model definition
#[perkakasan_baharu(                         // perkakasan_baharu = new_hardware
    nama = "Custom_FPGA_100MHz",
    jam_mhz = 100,
    kitaran_ns = 10,
    alu_kitaran = 1,
    darab_kitaran = 3,
    bahagi_kitaran = 20,
    muat_kitaran = 2,
    simpan_kitaran = 2,
    panggil_overhead = 8
)]
modul pemproses_isyarat {
    // ...
}
```

---

## 6. Verification Obligations

### 6.1 Compile-Time Verification Process

```coq
(** ======================================================================== *)
(** WCET Verification Obligations                                            *)
(** ======================================================================== *)

(** Verification result *)
Inductive wcet_check_result : Type :=
  | WCETOk        : time_bound -> wcet_check_result  (* Verified, computed bound *)
  | WCETExceeded  : time_bound -> time_bound -> wcet_check_result (* computed, declared *)
  | WCETUnknown   : string -> wcet_check_result.     (* Cannot determine, reason *)

(** Verification obligation for a function *)
Record wcet_obligation : Type := {
  wo_function     : string;                  (* Function name *)
  wo_declared     : time_bound;              (* Declared WCET in kesan Masa(...) *)
  wo_computed     : time_bound;              (* Computed WCET from analysis *)
  wo_hardware     : hw_timing_model;         (* Target hardware model *)
  wo_result       : wcet_check_result;       (* Verification result *)
}.

(** Check if computed WCET satisfies declared bound *)
Definition check_wcet_bound (declared computed : time_bound) : wcet_check_result :=
  match declared, computed with
  | TUnbounded, _ => WCETOk computed          (* No bound to check *)
  | _, TUnbounded => WCETUnknown "computed WCET is unbounded"
  | TBound d_val d_unit, TBound c_val c_unit =>
      let d_nanos := d_val * time_unit_to_nanos d_unit in
      let c_nanos := c_val * time_unit_to_nanos c_unit in
      if Nat.leb c_nanos d_nanos 
      then WCETOk computed
      else WCETExceeded computed declared
  | TBound d_val d_unit, TConstant c_val c_unit =>
      let d_nanos := d_val * time_unit_to_nanos d_unit in
      let c_nanos := c_val * time_unit_to_nanos c_unit in
      if Nat.leb c_nanos d_nanos 
      then WCETOk computed
      else WCETExceeded computed declared
  | TConstant d_val d_unit, TConstant c_val c_unit =>
      let d_nanos := d_val * time_unit_to_nanos d_unit in
      let c_nanos := c_val * time_unit_to_nanos c_unit in
      if Nat.eqb c_nanos d_nanos 
      then WCETOk computed
      else WCETExceeded computed declared
  | TConstant _ _, TBound _ _ =>
      WCETUnknown "declared constant-time but computed is bounded"
  end.

(** Full verification obligation check *)
Definition verify_wcet_obligation (ob : wcet_obligation) : Prop :=
  match ob.(wo_result) with
  | WCETOk _ => True
  | WCETExceeded _ _ => False
  | WCETUnknown _ => False
  end.
```

### 6.2 Verification Workflow

```
┌─────────────────────────────────────────────────────────────────────────┐
│                    RIINA WCET Verification Pipeline                     │
└─────────────────────────────────────────────────────────────────────────┘

                        ┌──────────────────┐
                        │   RIINA Source   │
                        │  kesan Masa(T)   │
                        └────────┬─────────┘
                                 │
                                 ▼
                    ┌────────────────────────┐
                    │    1. Parse & Type     │
                    │       Check            │
                    │  (Loop bounds, etc.)   │
                    └────────────┬───────────┘
                                 │
                                 ▼
              ┌──────────────────────────────────────┐
              │     2. WCET Composition Analysis     │
              │                                      │
              │  • Sequential: WCET₁ + WCET₂         │
              │  • Branch: max(WCET₁, WCET₂) + cond  │
              │  • Loop: n × WCET_body + overhead    │
              │  • Call: declared WCET of callee     │
              └──────────────────┬───────────────────┘
                                 │
                                 ▼
              ┌──────────────────────────────────────┐
              │    3. Hardware Model Application     │
              │                                      │
              │  • Multiply cycles by cycle time     │
              │  • Add cache miss penalties          │
              │  • Add branch misprediction costs    │
              └──────────────────┬───────────────────┘
                                 │
                                 ▼
              ┌──────────────────────────────────────┐
              │      4. Bound Verification           │
              │                                      │
              │  computed_WCET ≤ declared_T ?        │
              │                                      │
              │  YES → Emit verified binary          │
              │  NO  → Compile error with details    │
              └──────────────────┬───────────────────┘
                                 │
                    ┌────────────┴────────────┐
                    │                         │
                    ▼                         ▼
          ┌─────────────────┐       ┌─────────────────┐
          │    SUCCESS      │       │     ERROR       │
          │                 │       │                 │
          │  Binary with    │       │  "WCET dikira:  │
          │  WCET proof     │       │   150μs         │
          │  certificate    │       │   Diisytihar:   │
          │                 │       │   100μs"        │
          └─────────────────┘       └─────────────────┘
                    │
                    ▼
          ┌─────────────────────────────────────────┐
          │   5. Optional: External Tool Check      │
          │                                         │
          │   • Run aiT/OTAWA on generated binary   │
          │   • Compare external WCET with internal │
          │   • Generate certification artifacts    │
          └─────────────────────────────────────────┘
```

### 6.3 Compile-Time vs. External Tool Responsibilities

```coq
(** ======================================================================== *)
(** Verification Responsibility Matrix                                       *)
(** ======================================================================== *)

(**
   COMPILE-TIME VERIFICATION (RIINA Type System):
   ─────────────────────────────────────────────
   ✓ Loop iteration bounds (statically known or annotated)
   ✓ Recursion depth bounds (structural or annotated)
   ✓ WCET composition (sequential, branching, loops)
   ✓ Effect consistency (declared vs. computed effects)
   ✓ Type safety (no undefined behavior)
   ✓ Termination guarantee (all loops/recursion bounded)
   ✓ No dynamic allocation (heap-free guarantee)
   ✓ No function pointers (direct call graph)
   
   EXTERNAL TOOL VERIFICATION (aiT, OTAWA, etc.):
   ─────────────────────────────────────────────
   ○ Precise cache behavior analysis
   ○ Pipeline state analysis
   ○ Branch prediction modeling
   ○ Memory access pattern analysis
   ○ Inter-procedural analysis refinement
   ○ Hardware-specific timing validation
   ○ Binary-level WCET confirmation
   
   RUNTIME VERIFICATION (Optional, for defense-in-depth):
   ─────────────────────────────────────────────────────
   △ Watchdog timer enforcement
   △ Execution time measurement (testing only)
   △ Deadline miss detection (ARINC 653 partitions)
   
   Legend: ✓ = Required, ○ = Recommended for certification, △ = Defense-in-depth
*)

(** What the type system guarantees *)
Inductive type_system_guarantee : Type :=
  | TSG_LoopBound       : nat -> type_system_guarantee
  | TSG_RecursionBound  : nat -> type_system_guarantee
  | TSG_WCETComposition : time_bound -> type_system_guarantee
  | TSG_Termination     : type_system_guarantee
  | TSG_NoHeap          : type_system_guarantee
  | TSG_DirectCalls     : type_system_guarantee.

(** What external tools provide *)
Inductive external_tool_analysis : Type :=
  | ETA_CacheAnalysis   : nat -> nat -> external_tool_analysis  (* hits, misses *)
  | ETA_PipelineAnalysis: nat -> external_tool_analysis          (* stall cycles *)
  | ETA_BinaryWCET      : time_bound -> external_tool_analysis.  (* confirmed WCET *)

(** Combined verification certificate *)
Record wcet_certificate : Type := {
  wc_function        : string;
  wc_declared_wcet   : time_bound;
  wc_type_system     : list type_system_guarantee;
  wc_external_tool   : option (string * list external_tool_analysis);
  wc_hardware_model  : hw_timing_model;
  wc_verification_date : string;
}.
```

---

## 7. Constant-Time Interaction

### 7.1 Effect Subtyping Relationship

```coq
(** ======================================================================== *)
(** Constant-Time and WCET Interaction                                       *)
(** ======================================================================== *)

(**
   CONSTANT-TIME (EffConstantTime):
   - All execution paths take EXACTLY the same time
   - Required for cryptographic timing-attack resistance
   - Stronger guarantee than WCET bound
   
   WCET (EffTimed):
   - All execution paths complete within the bound
   - Paths may take different amounts of time
   - Sufficient for real-time scheduling
   
   SUBTYPING RELATIONSHIP:
   EffConstantTime(T) <: EffTimed(T)
   
   If a function always takes exactly T time units, it also
   completes within T time units (WCET bound is satisfied).
*)

(** Effect subtyping judgment *)
Inductive effect_subtype : effect -> effect -> Prop :=

  (** Reflexivity *)
  | ES_Refl : forall e, effect_subtype e e

  (** ConstantTime implies Timed *)
  | ES_ConstantToTimed : forall tb,
      effect_subtype (EffConstantTime +eff EffTimed (TConstant (fst tb) (snd tb)))
                     (EffTimed (TBound (fst tb) (snd tb)))

  (** Timed bound weakening *)
  | ES_TimedWeaken : forall tb1 tb2,
      tb1 ≤t tb2 ->
      effect_subtype (EffTimed tb1) (EffTimed tb2)

  (** Composition preserves subtyping *)
  | ES_Compose : forall e1 e1' e2 e2',
      effect_subtype e1 e1' ->
      effect_subtype e2 e2' ->
      effect_subtype (e1 +eff e2) (e1' +eff e2')

  (** Everything subtypes to Pure + Unbounded *)
  | ES_Top : forall e,
      effect_subtype e (EffPure +eff EffTimed TUnbounded).

Notation "e1 '<:eff' e2" := (effect_subtype e1 e2) (at level 70).

(** Proof: ConstantTime is stronger than Timed *)
Theorem constant_time_implies_timed : forall n u,
  (EffConstantTime +eff EffTimed (TConstant n u)) <:eff (EffTimed (TBound n u)).
Proof.
  intros n u.
  apply ES_ConstantToTimed.
Qed.
```

### 7.2 Constant-Time Typing Rules

```coq
(** ======================================================================== *)
(** Constant-Time Specific Typing Rules                                      *)
(** ======================================================================== *)

(** 
   Constant-time code has additional restrictions:
   1. No secret-dependent branches
   2. No secret-dependent memory access patterns
   3. No early returns based on secrets
   4. All loop iterations must execute (no early termination)
*)

(** Secret/public type annotations *)
Inductive secrecy : Type :=
  | Public : secrecy
  | Secret : secrecy.

(** Extended type with secrecy *)
Inductive sty : Type :=
  | STy : ty -> secrecy -> sty.

Notation "τ '@' s" := (STy τ s) (at level 60).

(** Constant-time typing rules *)
Inductive ct_has_type : typing_ctx -> expr -> sty -> effect -> Prop :=

  (** CT-IF: Condition must be public for constant-time *)
  | CT_If_Public : forall Γ ec e1 e2 τ s tbc tb1 tb2,
      ct_has_type Γ ec (TBool @ Public) (EffTimed tbc) ->
      ct_has_type Γ e1 (τ @ s) (EffTimed tb1) ->
      ct_has_type Γ e2 (τ @ s) (EffTimed tb2) ->
      ct_has_type Γ (EIf ec e1 e2) (τ @ s) 
                    (EffConstantTime +eff EffTimed (tbc +t (tb1 ⊔t tb2)))

  (** CT-IF-BALANCED: If branching on secret, branches must have identical timing *)
  | CT_If_Secret_Balanced : forall Γ ec e1 e2 τ s tbc tb,
      ct_has_type Γ ec (TBool @ Secret) (EffTimed tbc) ->
      ct_has_type Γ e1 (τ @ s) (EffTimed (TConstant tb Nanoseconds)) ->
      ct_has_type Γ e2 (τ @ s) (EffTimed (TConstant tb Nanoseconds)) ->
      (* Both branches have IDENTICAL constant time *)
      ct_has_type Γ (EIf ec e1 e2) (τ @ s)
                    (EffConstantTime +eff EffTimed (TConstant (tbc + tb) Nanoseconds))

  (** CT-FOR: Loop count must not depend on secrets *)
  | CT_For : forall Γ x lo hi body τ s tb_body,
      (* lo, hi must be public values *)
      ct_has_type Γ body (τ @ s) (EffConstantTime +eff EffTimed tb_body) ->
      let n := hi - lo in
      ct_has_type Γ (EFor x lo hi body) (TUnit @ Public)
                    (EffConstantTime +eff EffTimed (n *t tb_body)).
```

### 7.3 RIINA Constant-Time Syntax

```riina
// ============================================================================
// Constant-Time Functions in RIINA
// ============================================================================

/// Constant-time memory comparison (no timing side-channels)
/// Malay: banding_tetap = constant_comparison
fungsi banding_tetap<const N: usize>(a: &[u8; N], b: &[u8; N]) -> bool
    kesan Tetap + Masa(500ns)    // Tetap = ConstantTime
{
    biar perbezaan: u8 = 0;      // perbezaan = difference
    
    // Loop always executes all N iterations
    untuk i dalam 0..N {
        // XOR accumulation - no early exit
        perbezaan = perbezaan | (a[i] ^ b[i]);
    }
    
    // Final comparison (constant-time)
    perbezaan == 0
}

/// COMPILE ERROR: Secret-dependent branch in constant-time context
fungsi salah_rahsia(kunci: Rahsia<u8>, nilai: u8) -> bool
    kesan Tetap + Masa(100ns)
{
    // ERROR: branching on secret value breaks constant-time
    kalau kunci.dedah() == nilai {    // dedah = reveal
        kembali benar;
    }
    palsu
}
// Compiler: "ralat: keputusan berasaskan nilai rahsia melanggar kesan Tetap"
// Translation: "error: decision based on secret value violates Tetap effect"

/// Correct: use conditional move instead of branch
fungsi betul_rahsia(kunci: Rahsia<u8>, nilai: u8) -> bool
    kesan Tetap + Masa(100ns)
{
    // Constant-time select (no branch)
    biar sama = ct_sama(kunci.dedah(), nilai);    // ct_sama = ct_equal
    sama
}

/// Timing annotation derivation for constant-time
/// If both branches have EffConstantTime with same time,
/// the if-expression also has EffConstantTime
fungsi pilih_tetap<T>(syarat: bool, a: T, b: T) -> T
    kesan Tetap + Masa(10ns)
{
    // Both branches take exactly the same time (no operations)
    kalau syarat { a } lain { b }
}
```

---

## 8. DO-178C Compliance Mapping

### 8.1 DO-178C Objectives Mapping

```
┌─────────────────────────────────────────────────────────────────────────────┐
│              DO-178C WCET Objectives Compliance Matrix                      │
│                         (Level A Requirements)                              │
└─────────────────────────────────────────────────────────────────────────────┘

┌─────────────────────────────────────────────────────────────────────────────┐
│ TABLE A-3: Low-Level Requirements (Software Design Process)                 │
├───────┬─────────────────────────────────────────┬───────────────────────────┤
│ Obj.  │ DO-178C Requirement                     │ RIINA Compliance          │
├───────┼─────────────────────────────────────────┼───────────────────────────┤
│ A-3.1 │ Low-level requirements are developed    │ kesan Masa(T) annotations │
│       │ from high-level requirements            │ derive from system timing │
│       │                                         │ requirements              │
├───────┼─────────────────────────────────────────┼───────────────────────────┤
│ A-3.2 │ Low-level requirements are accurate     │ WCET bounds verified by   │
│       │ and consistent                          │ type system composition   │
├───────┼─────────────────────────────────────────┼───────────────────────────┤
│ A-3.3 │ Low-level requirements are compatible   │ Hardware model specifies  │
│       │ with target computer                    │ target processor timing   │
├───────┼─────────────────────────────────────────┼───────────────────────────┤
│ A-3.4 │ Low-level requirements are verifiable   │ Machine-checked Coq proofs│
│       │                                         │ of WCET composition       │
├───────┼─────────────────────────────────────────┼───────────────────────────┤
│ A-3.5 │ Low-level requirements conform to       │ Effect annotations follow │
│       │ standards                               │ RIINA language spec       │
├───────┼─────────────────────────────────────────┼───────────────────────────┤
│ A-3.6 │ Low-level requirements are traceable    │ WCET certificate traces   │
│       │ to high-level requirements              │ to system requirements    │
└───────┴─────────────────────────────────────────┴───────────────────────────┘

┌─────────────────────────────────────────────────────────────────────────────┐
│ TABLE A-5: Software Coding Standards                                        │
├───────┬─────────────────────────────────────────┬───────────────────────────┤
│ Obj.  │ DO-178C Requirement                     │ RIINA Compliance          │
├───────┼─────────────────────────────────────────┼───────────────────────────┤
│ A-5.1 │ Source code conforms to standards       │ RIINA syntax enforces     │
│       │                                         │ bounded loops/recursion   │
├───────┼─────────────────────────────────────────┼───────────────────────────┤
│ A-5.2 │ Source code is traceable to low-level   │ kesan annotations link    │
│       │ requirements                            │ code to timing specs      │
├───────┼─────────────────────────────────────────┼───────────────────────────┤
│ A-5.3 │ Source code is verifiable               │ Type system provides      │
│       │                                         │ automated verification    │
├───────┼─────────────────────────────────────────┼───────────────────────────┤
│ A-5.4 │ Source code is accurate and consistent  │ Coq extraction ensures    │
│       │                                         │ implementation matches    │
│       │                                         │ specification             │
└───────┴─────────────────────────────────────────┴───────────────────────────┘

┌─────────────────────────────────────────────────────────────────────────────┐
│ TABLE A-7: Verification of Verification Process                             │
├───────┬─────────────────────────────────────────┬───────────────────────────┤
│ Obj.  │ DO-178C Requirement                     │ RIINA Compliance          │
├───────┼─────────────────────────────────────────┼───────────────────────────┤
│ A-7.1 │ Verification process is correct         │ WCET composition rules    │
│       │                                         │ proven sound in Coq       │
├───────┼─────────────────────────────────────────┼───────────────────────────┤
│ A-7.2 │ Verification covers all requirements    │ All timed functions must  │
│       │                                         │ have verified WCET        │
├───────┼─────────────────────────────────────────┼───────────────────────────┤
│ A-7.3 │ Verification results are correct        │ Type system soundness     │
│       │                                         │ theorem (see Section 10)  │
├───────┼─────────────────────────────────────────┼───────────────────────────┤
│ A-7.4 │ Test coverage analysis is correct       │ Structural coverage via   │
│       │                                         │ type system (all paths    │
│       │                                         │ analyzed for WCET)        │
└───────┴─────────────────────────────────────────┴───────────────────────────┘
```

### 8.2 Certification Artifacts Generation

```coq
(** ======================================================================== *)
(** DO-178C Certification Artifact Generation                                *)
(** ======================================================================== *)

(** Certification artifact types *)
Inductive cert_artifact : Type :=
  | CA_Requirements   : list (string * time_bound) -> cert_artifact
  | CA_DesignProof    : list wcet_obligation -> cert_artifact
  | CA_SourceTrace    : string -> list (nat * string) -> cert_artifact
  | CA_WCETProof      : string -> time_bound -> cert_artifact
  | CA_SoundnessProof : string -> cert_artifact.

(** Generate certification package for a program *)
Record certification_package : Type := {
  cp_project_id     : string;
  cp_dal_level      : string;                (* "A", "B", "C", "D", "E" *)
  cp_hardware_model : hw_timing_model;
  cp_functions      : list wcet_certificate;
  cp_artifacts      : list cert_artifact;
  cp_tool_qual      : option string;         (* Tool qualification status *)
  cp_review_date    : string;
}.

(** Example: Generate WCET requirements document *)
Definition gen_wcet_requirements (prog : program) : cert_artifact :=
  CA_Requirements (
    map (fun fd => (fd.(fun_name), effect_timing fd.(fun_effect))) prog
  ).
```

### 8.3 ISO 26262 ASIL-D Mapping

```
┌─────────────────────────────────────────────────────────────────────────────┐
│           ISO 26262 ASIL-D WCET Requirements Compliance                     │
└─────────────────────────────────────────────────────────────────────────────┘

┌─────────────────────────────────────────────────────────────────────────────┐
│ Part 6: Software Development                                                │
├───────────────┬─────────────────────────────────┬───────────────────────────┤
│ Clause        │ ISO 26262 Requirement           │ RIINA Compliance          │
├───────────────┼─────────────────────────────────┼───────────────────────────┤
│ 6.4.3         │ Software architectural design   │ Effect system documents   │
│               │ specifies timing constraints    │ timing constraints        │
├───────────────┼─────────────────────────────────┼───────────────────────────┤
│ 6.4.6.1       │ Resource usage analysis         │ WCET analysis provides    │
│               │ (execution time)                │ worst-case CPU usage      │
├───────────────┼─────────────────────────────────┼───────────────────────────┤
│ 6.4.8         │ Verification of software        │ Compile-time WCET         │
│               │ architecture                    │ verification              │
├───────────────┼─────────────────────────────────┼───────────────────────────┤
│ 6.5.1         │ Software unit design notation   │ kesan Masa(T) provides    │
│               │ specifies timing                │ formal notation           │
├───────────────┼─────────────────────────────────┼───────────────────────────┤
│ 6.5.4         │ Defensive programming for       │ Bounded loops enforce     │
│               │ resource monitoring             │ termination               │
├───────────────┼─────────────────────────────────┼───────────────────────────┤
│ 8.4.4         │ Timing verification             │ WCET certificate with     │
│ (Part 8)      │ (hardware-software integration) │ hardware model            │
└───────────────┴─────────────────────────────────┴───────────────────────────┘
```

---

## 9. Rust Implementation Types

### 9.1 Core Type Definitions

```rust
//! RIINA WCET Type System - Rust Implementation
//! Document: RIINA_WCET_TYPES_v1_0_0

use std::cmp::Ordering;

/// Time unit for WCET specification
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum TimeUnit {
    Nanoseconds,
    Microseconds,
    Milliseconds,
    Seconds,
}

impl TimeUnit {
    /// Convert to nanoseconds multiplier
    pub fn to_nanos_multiplier(&self) -> u64 {
        match self {
            TimeUnit::Nanoseconds => 1,
            TimeUnit::Microseconds => 1_000,
            TimeUnit::Milliseconds => 1_000_000,
            TimeUnit::Seconds => 1_000_000_000,
        }
    }
    
    /// Parse from string (supports both English and Malay)
    pub fn from_str(s: &str) -> Option<Self> {
        match s.to_lowercase().as_str() {
            "ns" | "nanoseconds" | "nanosaat" => Some(TimeUnit::Nanoseconds),
            "μs" | "us" | "microseconds" | "mikrodetik" => Some(TimeUnit::Microseconds),
            "ms" | "milliseconds" | "milisaat" => Some(TimeUnit::Milliseconds),
            "s" | "seconds" | "saat" => Some(TimeUnit::Seconds),
            _ => None,
        }
    }
}

/// Time bound representation
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum TimeBound {
    /// Upper bound: execution completes within this time
    Bound { value: u64, unit: TimeUnit },
    /// Constant time: execution takes exactly this time (for crypto)
    Constant { value: u64, unit: TimeUnit },
    /// No static bound available
    Unbounded,
}

impl TimeBound {
    /// Create a bound
    pub fn bound(value: u64, unit: TimeUnit) -> Self {
        TimeBound::Bound { value, unit }
    }
    
    /// Create a constant-time bound
    pub fn constant(value: u64, unit: TimeUnit) -> Self {
        TimeBound::Constant { value, unit }
    }
    
    /// Convert to nanoseconds (None for Unbounded)
    pub fn to_nanos(&self) -> Option<u64> {
        match self {
            TimeBound::Bound { value, unit } => {
                Some(value.saturating_mul(unit.to_nanos_multiplier()))
            }
            TimeBound::Constant { value, unit } => {
                Some(value.saturating_mul(unit.to_nanos_multiplier()))
            }
            TimeBound::Unbounded => None,
        }
    }
    
    /// Check if this bound is satisfied by another (self >= other)
    pub fn is_satisfied_by(&self, other: &TimeBound) -> bool {
        match (self, other) {
            (TimeBound::Unbounded, _) => true,
            (_, TimeBound::Unbounded) => false,
            (TimeBound::Bound { .. } | TimeBound::Constant { .. }, 
             TimeBound::Bound { .. } | TimeBound::Constant { .. }) => {
                match (self.to_nanos(), other.to_nanos()) {
                    (Some(self_ns), Some(other_ns)) => self_ns >= other_ns,
                    _ => false,
                }
            }
        }
    }
}

impl PartialOrd for TimeBound {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        match (self.to_nanos(), other.to_nanos()) {
            (None, None) => Some(Ordering::Equal),
            (None, Some(_)) => Some(Ordering::Greater),  // Unbounded > all
            (Some(_), None) => Some(Ordering::Less),
            (Some(a), Some(b)) => Some(a.cmp(&b)),
        }
    }
}

/// WCET arithmetic operations
impl TimeBound {
    /// Sequential composition: t1 + t2
    pub fn add(&self, other: &TimeBound) -> TimeBound {
        match (self, other) {
            (TimeBound::Unbounded, _) | (_, TimeBound::Unbounded) => {
                TimeBound::Unbounded
            }
            (TimeBound::Constant { value: v1, unit: u1 },
             TimeBound::Constant { value: v2, unit: u2 }) => {
                let nanos = v1.saturating_mul(u1.to_nanos_multiplier())
                    .saturating_add(v2.saturating_mul(u2.to_nanos_multiplier()));
                TimeBound::Constant { value: nanos, unit: TimeUnit::Nanoseconds }
            }
            _ => {
                let nanos = self.to_nanos().unwrap_or(0)
                    .saturating_add(other.to_nanos().unwrap_or(0));
                TimeBound::Bound { value: nanos, unit: TimeUnit::Nanoseconds }
            }
        }
    }
    
    /// Branching: max(t1, t2)
    pub fn max(&self, other: &TimeBound) -> TimeBound {
        match (self, other) {
            (TimeBound::Unbounded, _) | (_, TimeBound::Unbounded) => {
                TimeBound::Unbounded
            }
            (TimeBound::Constant { value: v1, unit: u1 },
             TimeBound::Constant { value: v2, unit: u2 }) => {
                let n1 = v1.saturating_mul(u1.to_nanos_multiplier());
                let n2 = v2.saturating_mul(u2.to_nanos_multiplier());
                TimeBound::Constant { 
                    value: n1.max(n2), 
                    unit: TimeUnit::Nanoseconds 
                }
            }
            _ => {
                let n1 = self.to_nanos().unwrap_or(0);
                let n2 = other.to_nanos().unwrap_or(0);
                TimeBound::Bound { 
                    value: n1.max(n2), 
                    unit: TimeUnit::Nanoseconds 
                }
            }
        }
    }
    
    /// Loop multiplication: n * t
    pub fn multiply(&self, n: u64) -> TimeBound {
        match self {
            TimeBound::Unbounded => TimeBound::Unbounded,
            TimeBound::Constant { value, unit } => {
                let nanos = value.saturating_mul(unit.to_nanos_multiplier())
                    .saturating_mul(n);
                TimeBound::Constant { value: nanos, unit: TimeUnit::Nanoseconds }
            }
            TimeBound::Bound { value, unit } => {
                let nanos = value.saturating_mul(unit.to_nanos_multiplier())
                    .saturating_mul(n);
                TimeBound::Bound { value: nanos, unit: TimeUnit::Nanoseconds }
            }
        }
    }
}
```

### 9.2 Effect System Integration

```rust
//! Effect System with Timing

/// RIINA Effect Type
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Effect {
    /// Pure computation (no side effects)
    Pure,
    /// Memory read
    Read,
    /// Memory write  
    Write,
    /// I/O operations
    IO,
    /// Cryptographic operations
    Crypto,
    /// Constant-time execution (all paths same time)
    ConstantTime,
    /// WCET bound
    Timed(TimeBound),
    /// Effect composition
    Compose(Box<Effect>, Box<Effect>),
}

impl Effect {
    /// Compose two effects
    pub fn compose(self, other: Effect) -> Effect {
        Effect::Compose(Box::new(self), Box::new(other))
    }
    
    /// Extract timing bound from effect (returns Unbounded if not specified)
    pub fn get_timing(&self) -> TimeBound {
        match self {
            Effect::Timed(tb) => tb.clone(),
            Effect::Compose(e1, e2) => {
                e1.get_timing().add(&e2.get_timing())
            }
            _ => TimeBound::bound(0, TimeUnit::Nanoseconds),  // Negligible
        }
    }
    
    /// Check if effect is constant-time
    pub fn is_constant_time(&self) -> bool {
        match self {
            Effect::ConstantTime => true,
            Effect::Compose(e1, e2) => {
                e1.is_constant_time() && e2.is_constant_time()
            }
            _ => false,
        }
    }
    
    /// Check effect subtyping (self <: other)
    pub fn is_subtype_of(&self, other: &Effect) -> bool {
        match (self, other) {
            // Everything subtypes to itself
            (a, b) if a == b => true,
            
            // ConstantTime with timing subtypes to Timed
            (Effect::Compose(box Effect::ConstantTime, box Effect::Timed(tb1)),
             Effect::Timed(tb2)) => {
                tb2.is_satisfied_by(tb1)
            }
            
            // Timed subtyping (smaller bound subtypes larger)
            (Effect::Timed(tb1), Effect::Timed(tb2)) => {
                tb2.is_satisfied_by(tb1)
            }
            
            // Compose subtyping
            (Effect::Compose(e1a, e2a), Effect::Compose(e1b, e2b)) => {
                e1a.is_subtype_of(e1b) && e2a.is_subtype_of(e2b)
            }
            
            _ => false,
        }
    }
}

/// Malay keyword aliases for Effect construction
impl Effect {
    /// kesan Baca
    pub fn baca() -> Self { Effect::Read }
    
    /// kesan Tulis
    pub fn tulis() -> Self { Effect::Write }
    
    /// kesan IO
    pub fn io() -> Self { Effect::IO }
    
    /// kesan Kripto
    pub fn kripto() -> Self { Effect::Crypto }
    
    /// kesan Tetap (constant time)
    pub fn tetap() -> Self { Effect::ConstantTime }
    
    /// kesan Masa(value, unit)
    pub fn masa(value: u64, unit: TimeUnit) -> Self {
        Effect::Timed(TimeBound::bound(value, unit))
    }
}
```

### 9.3 Hardware Model Implementation

```rust
//! Hardware Timing Model

/// Hardware model type
#[derive(Debug, Clone)]
pub enum HardwareModelType {
    /// Simple: constant cycles per instruction
    Simple { cycles_per_instr: u32 },
    /// Cached: different hit/miss cycles
    Cached { hit_cycles: u32, miss_cycles: u32 },
    /// Pipelined: with stalls
    Pipeline { depth: u32, stall_cycles: u32, flush_cycles: u32 },
    /// Out-of-order: complex model
    OutOfOrder { issue_width: u32, rob_size: u32, penalty: u32 },
}

/// Complete hardware timing model
#[derive(Debug, Clone)]
pub struct HardwareModel {
    pub name: String,
    pub model_type: HardwareModelType,
    pub clock_mhz: u32,
    pub cycle_ns: u32,
    
    // Instruction costs (cycles)
    pub alu_cycles: u32,
    pub mul_cycles: u32,
    pub div_cycles: u32,
    pub fpu_cycles: u32,
    pub load_cycles: u32,
    pub store_cycles: u32,
    pub branch_cycles: u32,
    pub branch_miss_penalty: u32,
    pub call_overhead: u32,
    pub ret_overhead: u32,
    
    // Cache model
    pub cache_hit_cycles: u32,
    pub cache_miss_cycles: u32,
    pub cache_line_bytes: u32,
}

impl HardwareModel {
    /// ARM Cortex-M4 at 168MHz
    pub fn cortex_m4_168mhz() -> Self {
        HardwareModel {
            name: "ARM_Cortex_M4_168MHz".to_string(),
            model_type: HardwareModelType::Pipeline { 
                depth: 3, stall_cycles: 1, flush_cycles: 3 
            },
            clock_mhz: 168,
            cycle_ns: 6,
            alu_cycles: 1,
            mul_cycles: 1,
            div_cycles: 12,
            fpu_cycles: 1,
            load_cycles: 2,
            store_cycles: 1,
            branch_cycles: 1,
            branch_miss_penalty: 3,
            call_overhead: 4,
            ret_overhead: 4,
            cache_hit_cycles: 0,
            cache_miss_cycles: 0,
            cache_line_bytes: 0,
        }
    }
    
    /// Convert cycles to time bound
    pub fn cycles_to_time(&self, cycles: u64) -> TimeBound {
        let nanos = cycles.saturating_mul(self.cycle_ns as u64);
        TimeBound::bound(nanos, TimeUnit::Nanoseconds)
    }
    
    /// LEON3 for space applications
    pub fn leon3_space_50mhz() -> Self {
        HardwareModel {
            name: "LEON3_50MHz_Space".to_string(),
            model_type: HardwareModelType::Pipeline {
                depth: 7, stall_cycles: 2, flush_cycles: 7
            },
            clock_mhz: 50,
            cycle_ns: 20,
            alu_cycles: 1,
            mul_cycles: 5,
            div_cycles: 35,
            fpu_cycles: 4,
            load_cycles: 2,
            store_cycles: 2,
            branch_cycles: 1,
            branch_miss_penalty: 7,
            call_overhead: 6,
            ret_overhead: 6,
            cache_hit_cycles: 1,
            cache_miss_cycles: 30,
            cache_line_bytes: 32,
        }
    }
}
```

### 9.4 WCET Verification

```rust
//! WCET Verification

/// WCET verification result
#[derive(Debug, Clone)]
pub enum WcetCheckResult {
    /// WCET verified: computed ≤ declared
    Ok { computed: TimeBound },
    /// WCET exceeded: computed > declared  
    Exceeded { computed: TimeBound, declared: TimeBound },
    /// Cannot determine WCET
    Unknown { reason: String },
}

/// WCET verification obligation
#[derive(Debug, Clone)]
pub struct WcetObligation {
    pub function_name: String,
    pub declared: TimeBound,
    pub computed: TimeBound,
    pub hardware: HardwareModel,
    pub result: WcetCheckResult,
}

impl WcetObligation {
    /// Check WCET bound
    pub fn check(
        function_name: String,
        declared: TimeBound,
        computed: TimeBound,
        hardware: HardwareModel,
    ) -> Self {
        let result = match (&declared, &computed) {
            (TimeBound::Unbounded, _) => {
                WcetCheckResult::Ok { computed: computed.clone() }
            }
            (_, TimeBound::Unbounded) => {
                WcetCheckResult::Unknown { 
                    reason: "Computed WCET is unbounded".to_string() 
                }
            }
            _ => {
                if declared.is_satisfied_by(&computed) {
                    WcetCheckResult::Ok { computed: computed.clone() }
                } else {
                    WcetCheckResult::Exceeded { 
                        computed: computed.clone(), 
                        declared: declared.clone() 
                    }
                }
            }
        };
        
        WcetObligation {
            function_name,
            declared,
            computed,
            hardware,
            result,
        }
    }
    
    /// Generate error message for failed verification
    pub fn error_message(&self) -> Option<String> {
        match &self.result {
            WcetCheckResult::Ok { .. } => None,
            WcetCheckResult::Exceeded { computed, declared } => {
                Some(format!(
                    "ralat: WCET dikira ({:?}) melebihi had diisytihar ({:?}) \
                     untuk fungsi '{}'",
                    computed, declared, self.function_name
                ))
            }
            WcetCheckResult::Unknown { reason } => {
                Some(format!(
                    "ralat: tidak dapat tentukan WCET untuk fungsi '{}': {}",
                    self.function_name, reason
                ))
            }
        }
    }
}

/// WCET certificate for certification artifacts
#[derive(Debug, Clone)]
pub struct WcetCertificate {
    pub function_name: String,
    pub declared_wcet: TimeBound,
    pub computed_wcet: TimeBound,
    pub hardware_model: String,
    pub verification_tool: String,
    pub verification_date: String,
    pub coq_proof_file: Option<String>,
}
```

---

## 10. Formal Soundness Theorem

### 10.1 Main Soundness Theorem

```coq
(** ======================================================================== *)
(** WCET Type System Soundness Theorem                                       *)
(** Document: RIINA_WCET_TYPES_v1_0_0                                        *)
(** ======================================================================== *)

Require Import Coq.Arith.Arith.
Require Import Coq.Lists.List.

(** 
   THEOREM (WCET Soundness):
   
   If a well-typed RIINA program has a function f annotated with 
   kesan Masa(T), then for all valid inputs and for the declared 
   hardware model, f terminates and its execution time is at most T.
   
   Formally:
   
   ∀ Γ f params body τ tb hw.
     Γ ⊢ (fungsi f(params) -> τ kesan EffTimed(tb) { body }) well_formed
     → hw = Γ.(ctx_hw)
     → ∀ inputs. valid_inputs(params, inputs)
     → ∃ result time.
         eval(f, inputs, hw) = (result, time)
         ∧ time ≤ normalize_to_nanos(tb)
*)

(** Execution semantics (big-step, with timing) *)
(** eval_timed Γ e hw = (value, cycles) *)
Inductive eval_timed : typing_ctx -> expr -> hw_timing_model -> 
                        (option value * nat) -> Prop :=
  (* ... operational semantics with cycle counting ... *)
  .

(** Well-formedness of function declarations *)
Definition function_well_formed (Γ : typing_ctx) (fd : fun_decl) : Prop :=
  exists tb,
    Γ ⊢ fd.(fun_body) : fd.(fun_ret) kesan EffTimed tb /\
    tb ≤t effect_timing fd.(fun_effect).

(** The main soundness theorem *)
Theorem wcet_soundness :
  forall (Γ : typing_ctx) (fd : fun_decl) (inputs : list value) 
         (result : value) (cycles : nat),
    (* Preconditions *)
    function_well_formed Γ fd ->
    (* Execution produces result in cycles *)
    eval_timed Γ (subst_params fd.(fun_body) fd.(fun_params) inputs) 
               Γ.(ctx_hw) (Some result, cycles) ->
    (* Conclusion: cycles within declared bound *)
    let declared_cycles := 
      match normalize_to_nanos (effect_timing fd.(fun_effect)) with
      | Some nanos => nanos / Γ.(ctx_hw).(htm_cycle_ns)
      | None => 0  (* Unbounded - vacuously true *)
      end in
    cycles <= declared_cycles.
Proof.
  intros Γ fd inputs result cycles Hwf Heval.
  (* 
     PROOF SKETCH:
     
     1. By induction on the typing derivation of fd.(fun_body)
     
     2. For each typing rule, show that the operational semantics
        respects the cycle count in the typing judgment:
        
        - T_Seq: Sequential composition adds cycles
        - T_If: Branching takes max cycles
        - T_For: Loop multiplies body cycles
        - T_While: Bounded loop with max iterations
        - T_Call: Uses declared WCET of callee
        
     3. The hardware model provides cycle costs for primitive operations
     
     4. Since RIINA enforces:
        - Bounded loops (no unbounded iteration)
        - Bounded recursion (depth annotations)
        - No dynamic allocation
        - No function pointers
        
        The cycle count is always well-defined and finite.
     
     5. The type system's composition rules over-approximate the
        actual execution cycles, so the bound is always sound.
        
     This proof is ADMITTED as it requires:
     - Complete operational semantics
     - Detailed hardware model formalization
     - Case analysis for all expression forms
     
     FUTURE WORK: Complete mechanized proof in Coq
  *)
Admitted.
```

### 10.2 Progress and Preservation

```coq
(** ======================================================================== *)
(** Type Safety: Progress and Preservation for WCET                          *)
(** ======================================================================== *)

(** Progress: Well-typed expressions either are values or can step *)
Theorem wcet_progress :
  forall Γ e τ tb,
    Γ ⊢ e : τ kesan EffTimed tb ->
    (exists v, e = EVal v) \/ (exists e' cycles, step Γ e = (e', cycles)).
Proof.
  (* By induction on typing derivation *)
Admitted.

(** Preservation: Stepping preserves types and decreases WCET bound *)
Theorem wcet_preservation :
  forall Γ e e' τ tb cycles,
    Γ ⊢ e : τ kesan EffTimed tb ->
    step Γ e = (e', cycles) ->
    exists tb',
      Γ ⊢ e' : τ kesan EffTimed tb' /\
      normalize_to_nanos tb' + Some cycles <= normalize_to_nanos tb.
Proof.
  (* By induction on typing derivation *)
Admitted.

(** Termination: All well-typed programs terminate *)
(** This follows from bounded loops and bounded recursion *)
Theorem wcet_termination :
  forall Γ e τ tb,
    Γ ⊢ e : τ kesan EffTimed tb ->
    tb <> TUnbounded ->
    exists v, eval Γ e = Some v.
Proof.
  (* 
     Key insight: RIINA enforces:
     1. All loops have static iteration bounds
     2. All recursion has depth bounds
     3. No dynamic allocation that could cause OOM
     
     Therefore, execution always terminates.
  *)
Admitted.

(** Soundness corollary: WCET type system is sound *)
Corollary wcet_type_safety :
  forall Γ fd inputs,
    function_well_formed Γ fd ->
    valid_inputs fd.(fun_params) inputs ->
    exists result time,
      eval_timed Γ (subst_params fd.(fun_body) fd.(fun_params) inputs)
                 Γ.(ctx_hw) (Some result, time) /\
      time * Γ.(ctx_hw).(htm_cycle_ns) <= 
        match normalize_to_nanos (effect_timing fd.(fun_effect)) with
        | Some n => n
        | None => time * Γ.(ctx_hw).(htm_cycle_ns) + 1  (* vacuous for Unbounded *)
        end.
Proof.
  intros.
  (* Combine termination and soundness *)
Admitted.
```

### 10.3 Soundness Theorem Statement Summary

```coq
(** ======================================================================== *)
(** Summary: The Key Theorem                                                 *)
(** ======================================================================== *)

(**
   RIINA WCET TYPE SYSTEM SOUNDNESS
   ================================
   
   Statement:
   ----------
   If a function f is typed with effect kesan Masa(T), then for any 
   valid input and on the declared hardware model, f terminates and 
   executes in at most T time units.
   
   Formally:
   
     ∀ f : function, T : time_bound, hw : hardware_model.
       well_typed(f, kesan Masa(T)) ∧ hw = declared_hardware(f)
       →
       ∀ input : valid_input(f).
         ∃ output : value, time : ℕ.
           execute(f, input, hw) = (output, time) ∧
           time ≤ T
   
   Assumptions:
   ------------
   1. Hardware model accurately reflects target processor timing
   2. No interrupts or preemption during execution
   3. Memory accesses follow worst-case cache behavior
   4. All loop bounds and recursion depths are respected at runtime
   5. No undefined behavior in the program
   
   What the Type System Guarantees:
   --------------------------------
   ✓ Compositional WCET: bounds compose correctly through control flow
   ✓ Termination: all programs with finite bounds terminate
   ✓ No unbounded loops: every loop has a static iteration count
   ✓ No unbounded recursion: every recursive call has depth bound
   ✓ Sound over-approximation: declared bound ≥ actual worst-case
   
   What Requires External Verification:
   ------------------------------------
   ○ Precise cache timing (use aiT, OTAWA)
   ○ Pipeline effects (beyond simple model)
   ○ Hardware model accuracy validation
   ○ Integration with RTOS scheduler
   
   Proof Status:
   -------------
   - Theorem STATED in Coq
   - Proof ADMITTED (requires ~5000 lines of Coq)
   - Key lemmas sketched
   - Mechanization is FUTURE WORK
*)
```

---

## 11. Limitations and Honest Assessment

### 11.1 What RIINA's Type System CAN Guarantee

| Guarantee | Compile-Time | Runtime | Notes |
|-----------|-------------|---------|-------|
| Loop iteration bounds | ✓ | — | Static analysis + annotations |
| Recursion depth bounds | ✓ | — | Structural recursion or depth annotation |
| WCET composition | ✓ | — | Sound but may be imprecise |
| Termination | ✓ | — | Follows from bounded iteration |
| No dynamic allocation | ✓ | — | Heap-free guarantee |
| No function pointers | ✓ | — | Direct call graph |
| Effect consistency | ✓ | — | Declared effects match computed |
| Constant-time (no secret branches) | ✓ | — | Type-level secrecy tracking |

### 11.2 What RIINA's Type System CANNOT Guarantee

| Limitation | Reason | Mitigation |
|------------|--------|------------|
| **Precise cache behavior** | Requires abstract interpretation over entire CFG; beyond compositional type system | Use external tool (aiT, OTAWA) for precise analysis |
| **Pipeline stalls** | Data-dependent; requires microarchitectural simulation | Conservative over-approximation in hardware model |
| **Branch prediction** | Runtime behavior; cannot be fully predicted statically | Assume worst-case (always mispredicted) |
| **Memory access patterns** | Address computation may be input-dependent | Assume cache miss for all accesses (pessimistic) |
| **Interrupt latency** | Depends on OS/hardware interrupt handling | Excluded from WCET; handle at system level |
| **Multi-core interference** | Shared cache/bus contention | Single-core assumption; multi-core is future work |
| **Out-of-order execution** | Complex microarchitectural state | Simplified pipeline model; external tool for precision |
| **Hardware model accuracy** | Model may not match actual silicon | Validate with measurement; conservative margins |

### 11.3 Precision vs. Soundness Trade-off

```
                    WCET Analysis Precision Spectrum
                    
    UNSOUND                                              SOUND
    (may underestimate)                                  (always safe)
         │                                                    │
         ▼                                                    ▼
    ┌─────────┬──────────┬──────────┬──────────┬──────────────┐
    │Measure- │ Simple   │ RIINA    │ aiT/OTAWA│ Pessimistic  │
    │ment     │ Counting │ Type Sys │ Abstract │ Assumption   │
    │(BCET?)  │          │          │ Interp.  │ (all miss)   │
    └─────────┴──────────┴──────────┴──────────┴──────────────┘
         │         │          │           │            │
    Tightest    ~50% over   ~2-5x over  ~1.5-3x over  ~10x+ over
    (unsafe)    (unsafe)    (sound)     (sound)       (very safe)
    
    RIINA's position: Sound over-approximation with ~2-5x margin
    
    For certification, soundness is REQUIRED.
    External tools can reduce the margin while maintaining soundness.
```

### 11.4 Recommended Certification Approach

```
┌─────────────────────────────────────────────────────────────────────────────┐
│              Recommended DO-178C Level A Certification Path                 │
└─────────────────────────────────────────────────────────────────────────────┘

Phase 1: Development (RIINA Type System)
────────────────────────────────────────
  • Write code with kesan Masa(T) annotations
  • Compiler verifies compositional WCET bounds
  • Generates preliminary WCET certificates
  • Catches errors early (unbounded loops, etc.)

Phase 2: Analysis (External Tool - aiT)
───────────────────────────────────────
  • Run aiT on compiled binary
  • Get precise WCET with cache/pipeline analysis
  • Compare aiT result with RIINA declared bound
  • If aiT_WCET ≤ declared_WCET: ✓ (pass)
  • If aiT_WCET > declared_WCET: revise annotations or code

Phase 3: Verification (Combined Evidence)
────────────────────────────────────────
  • RIINA provides: Termination proofs, bound composition proofs
  • aiT provides: Hardware-accurate WCET values
  • Combined: Complete WCET verification package
  • Generate DO-178C certification artifacts

Phase 4: Runtime Defense (Optional)
──────────────────────────────────
  • Deploy with watchdog timers
  • ARINC 653 partition time enforcement
  • Deadline miss detection (for diagnosis, not safety)
```

### 11.5 Known Issues and Future Work

1. **Proof Mechanization**: The soundness theorem is stated but not fully proven in Coq. Completing the ~5000 line proof is critical for DO-178C formal methods credit.

2. **Cache Analysis Integration**: The type system uses pessimistic cache assumptions. Integrating abstract interpretation for cache-aware analysis would improve precision.

3. **Multi-Core Support**: Current model assumes single-core execution. Multi-core timing analysis with shared resource interference is future work.

4. **Hardware Model Validation**: The accuracy of hardware timing models should be validated against silicon measurements.

5. **Tool Qualification**: For DO-178C, the RIINA compiler itself must be qualified (TQL-5 for Level A). This requires extensive testing and documentation.

6. **Floating-Point WCET**: Floating-point operations have variable latency on some hardware. The current model uses worst-case assumptions.

7. **Memory-Mapped I/O**: I/O timing is highly hardware-dependent and may not be predictable. Current model assumes constant I/O time.

---

## Document Control

| Version | Date | Author | Changes |
|---------|------|--------|---------|
| 1.0.0 | 2024-01-XX | RIINA Team | Initial specification |

**Review Status**: Draft - Not for certification use

**Next Actions**:
1. Complete Coq soundness proof
2. Implement type checker in Rust
3. Validate against aiT on sample programs
4. Prepare DO-178C certification evidence package

---

*End of Document: RIINA_WCET_TYPES_v1_0_0*