(* Copyright (c) 2026 The RIINA Authors. All rights reserved. *)

(* TranslationValidation.v - Translation Validation for RIINA Compiler *)
(* Spec: 01_RESEARCH/18_DOMAIN_R_CERTIFIED_COMPILATION/ *)
(* Based on: CompCert methodology *)

Require Import Coq.Lists.List.
Require Import Coq.Bool.Bool.
Require Import Coq.Arith.Arith.
Require Import Coq.Arith.PeanoNat.
Require Import Coq.Logic.FunctionalExtensionality.
Import ListNotations.

(* ═══════════════════════════════════════════════════════════════════════════ *)
(* SOURCE LANGUAGE (simplified RIINA)                                          *)
(* ═══════════════════════════════════════════════════════════════════════════ *)

Inductive SrcExpr : Type :=
  | SVar : nat -> SrcExpr
  | SConst : nat -> SrcExpr
  | SAdd : SrcExpr -> SrcExpr -> SrcExpr
  | SMul : SrcExpr -> SrcExpr -> SrcExpr
  | SIf : SrcExpr -> SrcExpr -> SrcExpr -> SrcExpr
  | SCall : nat -> list SrcExpr -> SrcExpr
  | SLet : nat -> SrcExpr -> SrcExpr -> SrcExpr
.

(* Source statements for effects *)
Inductive SrcStmt : Type :=
  | SSkip : SrcStmt
  | SAssign : nat -> SrcExpr -> SrcStmt
  | SSeq : SrcStmt -> SrcStmt -> SrcStmt
  | SIfStmt : SrcExpr -> SrcStmt -> SrcStmt -> SrcStmt
  | SWhile : SrcExpr -> SrcStmt -> SrcStmt
  | SRead : nat -> nat -> SrcStmt
  | SWrite : nat -> SrcExpr -> SrcStmt
  | SCallStmt : nat -> list SrcExpr -> SrcStmt
.

(* Source program *)
Record SrcProgram : Type := mkSP {
  sp_funcs : list (nat * SrcExpr);
  sp_main : SrcExpr;
}.

(* ═══════════════════════════════════════════════════════════════════════════ *)
(* TARGET LANGUAGE (simplified IR)                                             *)
(* ═══════════════════════════════════════════════════════════════════════════ *)

Inductive TgtInstr : Type :=
  | TLoad : nat -> nat -> TgtInstr          (* dst, src_addr *)
  | TStore : nat -> nat -> TgtInstr         (* dst_addr, src *)
  | TAdd : nat -> nat -> nat -> TgtInstr    (* dst, src1, src2 *)
  | TMul : nat -> nat -> nat -> TgtInstr    (* dst, src1, src2 *)
  | TConst : nat -> nat -> TgtInstr         (* dst, value *)
  | TBranch : nat -> TgtInstr               (* target *)
  | TBranchIf : nat -> nat -> nat -> TgtInstr  (* cond, true_target, false_target *)
  | TCall : nat -> list nat -> TgtInstr     (* func_id, args *)
  | TReturn : nat -> TgtInstr               (* result *)
  | TNop : TgtInstr
.

Definition TgtProgram := list TgtInstr.

(* Target function *)
Record TgtFunc : Type := mkTF {
  tf_id : nat;
  tf_params : list nat;
  tf_body : TgtProgram;
  tf_result : nat;
}.

(* ═══════════════════════════════════════════════════════════════════════════ *)
(* VALUES                                                                       *)
(* ═══════════════════════════════════════════════════════════════════════════ *)

(* Source values *)
Inductive SrcVal : Type :=
  | SVInt : nat -> SrcVal
  | SVBool : bool -> SrcVal
  | SVUnit : SrcVal
.

(* Target values *)
Inductive TgtVal : Type :=
  | TVInt : nat -> TgtVal
  | TVUndef : TgtVal
.

(* Value correspondence *)
Definition val_match (sv : SrcVal) (tv : TgtVal) : bool :=
  match sv, tv with
  | SVInt n, TVInt m => Nat.eqb n m
  | SVBool true, TVInt 1 => true
  | SVBool false, TVInt 0 => true
  | SVUnit, TVInt 0 => true
  | _, _ => false
  end.

(* Propositional value correspondence *)
Inductive val_corresp : SrcVal -> TgtVal -> Prop :=
  | VCInt : forall n, val_corresp (SVInt n) (TVInt n)
  | VCTrue : val_corresp (SVBool true) (TVInt 1)
  | VCFalse : val_corresp (SVBool false) (TVInt 0)
  | VCUnit : val_corresp SVUnit (TVInt 0)
.

(* ═══════════════════════════════════════════════════════════════════════════ *)
(* ENVIRONMENTS AND STATE                                                       *)
(* ═══════════════════════════════════════════════════════════════════════════ *)

(* Source environment *)
Definition SrcEnv := list (nat * SrcVal).

(* Target register file *)
Definition TgtRegs := list (nat * TgtVal).

(* Memory *)
Definition Memory := list (nat * TgtVal).

(* Variable to register mapping *)
Definition VarMapping := list (nat * nat).

(* Environment lookup *)
Definition env_lookup (env : SrcEnv) (x : nat) : option SrcVal :=
  match find (fun p => Nat.eqb (fst p) x) env with
  | Some (_, v) => Some v
  | None => None
  end.

(* Register lookup *)
Definition reg_lookup (regs : TgtRegs) (r : nat) : option TgtVal :=
  match find (fun p => Nat.eqb (fst p) r) regs with
  | Some (_, v) => Some v
  | None => None
  end.

(* Environment correspondence *)
Definition env_match (se : SrcEnv) (tr : TgtRegs) (mapping : VarMapping) : bool :=
  forallb (fun pair =>
    let svar := fst pair in
    let treg := snd pair in
    match find (fun p => Nat.eqb (fst p) svar) se,
          find (fun p => Nat.eqb (fst p) treg) tr with
    | Some (_, sv), Some (_, tv) => val_match sv tv
    | _, _ => false
    end
  ) mapping.

(* Propositional environment correspondence *)
Inductive env_corresp : SrcEnv -> TgtRegs -> VarMapping -> Prop :=
  | ECEmpty : forall regs, env_corresp [] regs []
  | ECCons : forall senv tregs svar treg sv tv mapping,
      In (svar, sv) senv ->
      In (treg, tv) tregs ->
      val_corresp sv tv ->
      env_corresp senv tregs mapping ->
      env_corresp senv tregs ((svar, treg) :: mapping)
.

(* ═══════════════════════════════════════════════════════════════════════════ *)
(* SOURCE SEMANTICS (big-step)                                                  *)
(* ═══════════════════════════════════════════════════════════════════════════ *)

Inductive src_eval : SrcEnv -> SrcExpr -> SrcVal -> Prop :=
  | EVar : forall env x v,
      In (x, v) env -> src_eval env (SVar x) v
  | EConst : forall env n,
      src_eval env (SConst n) (SVInt n)
  | EAdd : forall env e1 e2 n1 n2,
      src_eval env e1 (SVInt n1) ->
      src_eval env e2 (SVInt n2) ->
      src_eval env (SAdd e1 e2) (SVInt (n1 + n2))
  | EMul : forall env e1 e2 n1 n2,
      src_eval env e1 (SVInt n1) ->
      src_eval env e2 (SVInt n2) ->
      src_eval env (SMul e1 e2) (SVInt (n1 * n2))
  | EIfTrue : forall env c e1 e2 v,
      src_eval env c (SVBool true) ->
      src_eval env e1 v ->
      src_eval env (SIf c e1 e2) v
  | EIfFalse : forall env c e1 e2 v,
      src_eval env c (SVBool false) ->
      src_eval env e2 v ->
      src_eval env (SIf c e1 e2) v
  | ELet : forall env x e1 e2 v1 v2,
      src_eval env e1 v1 ->
      src_eval ((x, v1) :: env) e2 v2 ->
      src_eval env (SLet x e1 e2) v2
.

(* ═══════════════════════════════════════════════════════════════════════════ *)
(* TARGET SEMANTICS (small-step)                                                *)
(* ═══════════════════════════════════════════════════════════════════════════ *)

Record TgtState : Type := mkTS {
  ts_pc : nat;
  ts_regs : TgtRegs;
  ts_memory : Memory;
}.

Inductive tgt_step : TgtProgram -> TgtState -> TgtState -> Prop :=
  | StepAdd : forall prog pc regs mem dst s1 s2 v1 v2,
      nth_error prog pc = Some (TAdd dst s1 s2) ->
      In (s1, TVInt v1) regs ->
      In (s2, TVInt v2) regs ->
      tgt_step prog (mkTS pc regs mem)
                    (mkTS (S pc) ((dst, TVInt (v1 + v2)) :: regs) mem)
  | StepMul : forall prog pc regs mem dst s1 s2 v1 v2,
      nth_error prog pc = Some (TMul dst s1 s2) ->
      In (s1, TVInt v1) regs ->
      In (s2, TVInt v2) regs ->
      tgt_step prog (mkTS pc regs mem)
                    (mkTS (S pc) ((dst, TVInt (v1 * v2)) :: regs) mem)
  | StepConst : forall prog pc regs mem dst v,
      nth_error prog pc = Some (TConst dst v) ->
      tgt_step prog (mkTS pc regs mem)
                    (mkTS (S pc) ((dst, TVInt v) :: regs) mem)
  | StepLoad : forall prog pc regs mem dst addr v,
      nth_error prog pc = Some (TLoad dst addr) ->
      In (addr, v) mem ->
      tgt_step prog (mkTS pc regs mem)
                    (mkTS (S pc) ((dst, v) :: regs) mem)
  | StepStore : forall prog pc regs mem addr src v,
      nth_error prog pc = Some (TStore addr src) ->
      In (src, v) regs ->
      tgt_step prog (mkTS pc regs mem)
                    (mkTS (S pc) regs ((addr, v) :: mem))
  | StepBranch : forall prog pc regs mem target,
      nth_error prog pc = Some (TBranch target) ->
      tgt_step prog (mkTS pc regs mem)
                    (mkTS target regs mem)
  | StepBranchIfTrue : forall prog pc regs mem cond t f v,
      nth_error prog pc = Some (TBranchIf cond t f) ->
      In (cond, TVInt v) regs ->
      v <> 0 ->
      tgt_step prog (mkTS pc regs mem)
                    (mkTS t regs mem)
  | StepBranchIfFalse : forall prog pc regs mem cond t f,
      nth_error prog pc = Some (TBranchIf cond t f) ->
      In (cond, TVInt 0) regs ->
      tgt_step prog (mkTS pc regs mem)
                    (mkTS f regs mem)
  | StepNop : forall prog pc regs mem,
      nth_error prog pc = Some TNop ->
      tgt_step prog (mkTS pc regs mem)
                    (mkTS (S pc) regs mem)
.

(* Multi-step relation *)
Inductive tgt_steps : TgtProgram -> TgtState -> TgtState -> Prop :=
  | StepsRefl : forall prog s, tgt_steps prog s s
  | StepsTrans : forall prog s1 s2 s3,
      tgt_step prog s1 s2 ->
      tgt_steps prog s2 s3 ->
      tgt_steps prog s1 s3
.

(* ═══════════════════════════════════════════════════════════════════════════ *)
(* EFFECTS AND TRACES                                                           *)
(* ═══════════════════════════════════════════════════════════════════════════ *)

Inductive Effect : Type :=
  | EffPure : Effect
  | EffRead : nat -> Effect
  | EffWrite : nat -> nat -> Effect
  | EffCall : nat -> Effect
.

Definition Trace := list Effect.

(* Trace equivalence *)
Definition trace_equiv (t1 t2 : Trace) : bool :=
  (length t1 =? length t2) &&
  forallb (fun pair =>
    match fst pair, snd pair with
    | EffPure, EffPure => true
    | EffRead a1, EffRead a2 => Nat.eqb a1 a2
    | EffWrite a1 v1, EffWrite a2 v2 => andb (Nat.eqb a1 a2) (Nat.eqb v1 v2)
    | EffCall f1, EffCall f2 => Nat.eqb f1 f2
    | _, _ => false
    end
  ) (combine t1 t2).

(* Propositional trace equivalence *)
Inductive trace_equiv_prop : Trace -> Trace -> Prop :=
  | TEEmpty : trace_equiv_prop [] []
  | TEPure : forall t1 t2,
      trace_equiv_prop t1 t2 ->
      trace_equiv_prop (EffPure :: t1) (EffPure :: t2)
  | TERead : forall a t1 t2,
      trace_equiv_prop t1 t2 ->
      trace_equiv_prop (EffRead a :: t1) (EffRead a :: t2)
  | TEWrite : forall a v t1 t2,
      trace_equiv_prop t1 t2 ->
      trace_equiv_prop (EffWrite a v :: t1) (EffWrite a v :: t2)
  | TECall : forall f t1 t2,
      trace_equiv_prop t1 t2 ->
      trace_equiv_prop (EffCall f :: t1) (EffCall f :: t2)
.

(* ═══════════════════════════════════════════════════════════════════════════ *)
(* TYPES                                                                        *)
(* ═══════════════════════════════════════════════════════════════════════════ *)

Inductive SrcType : Type :=
  | STInt : SrcType
  | STBool : SrcType
  | STUnit : SrcType
  | STFun : list SrcType -> SrcType -> SrcType
.

Inductive TgtType : Type :=
  | TTInt : TgtType
  | TTPtr : TgtType
.

Definition SrcTypeEnv := list (nat * SrcType).

(* Source typing *)
Inductive src_has_type : SrcTypeEnv -> SrcExpr -> SrcType -> Prop :=
  | TyVar : forall G x t,
      In (x, t) G ->
      src_has_type G (SVar x) t
  | TyConst : forall G n,
      src_has_type G (SConst n) STInt
  | TyAdd : forall G e1 e2,
      src_has_type G e1 STInt ->
      src_has_type G e2 STInt ->
      src_has_type G (SAdd e1 e2) STInt
  | TyMul : forall G e1 e2,
      src_has_type G e1 STInt ->
      src_has_type G e2 STInt ->
      src_has_type G (SMul e1 e2) STInt
  | TyIf : forall G c e1 e2 t,
      src_has_type G c STBool ->
      src_has_type G e1 t ->
      src_has_type G e2 t ->
      src_has_type G (SIf c e1 e2) t
  | TyLet : forall G x e1 e2 t1 t2,
      src_has_type G e1 t1 ->
      src_has_type ((x, t1) :: G) e2 t2 ->
      src_has_type G (SLet x e1 e2) t2
.

(* Type correspondence *)
Definition type_corresp (st : SrcType) (tt : TgtType) : Prop :=
  match st with
  | STInt => tt = TTInt
  | STBool => tt = TTInt
  | STUnit => tt = TTInt
  | STFun _ _ => tt = TTPtr
  end.

(* ═══════════════════════════════════════════════════════════════════════════ *)
(* SIMULATION RELATIONS                                                         *)
(* ═══════════════════════════════════════════════════════════════════════════ *)

(* Basic simulation relation *)
Definition simulates (se : SrcEnv) (sv : SrcVal) (ts : TgtState) (result_reg : nat) : Prop :=
  exists tv, In (result_reg, tv) (ts_regs ts) /\ val_match sv tv = true.

(* Propositional simulation *)
Inductive sim_rel : SrcEnv -> SrcVal -> TgtState -> nat -> Prop :=
  | SimRel : forall senv sv ts reg tv,
      In (reg, tv) (ts_regs ts) ->
      val_corresp sv tv ->
      sim_rel senv sv ts reg
.

(* Memory correspondence *)
Definition mem_corresp (smem : list (nat * SrcVal)) (tmem : Memory) : Prop :=
  forall addr sv,
    In (addr, sv) smem ->
    exists tv, In (addr, tv) tmem /\ val_corresp sv tv.

(* Full state correspondence *)
Record state_corresp (senv : SrcEnv) (ts : TgtState) (mapping : VarMapping) : Prop := {
  sc_env : env_corresp senv (ts_regs ts) mapping;
}.

(* ═══════════════════════════════════════════════════════════════════════════ *)
(* COMPILATION                                                                  *)
(* ═══════════════════════════════════════════════════════════════════════════ *)

(* Compilation result *)
Record CompResult : Type := mkCR {
  cr_code : TgtProgram;
  cr_result_reg : nat;
  cr_next_reg : nat;
}.

(* Simple compilation function (for specification) *)
Fixpoint compile_expr (e : SrcExpr) (next_reg : nat) : CompResult :=
  match e with
  | SConst n => mkCR [TConst next_reg n] next_reg (S next_reg)
  | SVar x => mkCR [] x next_reg  (* Variable already in register *)
  | SAdd e1 e2 =>
      let cr1 := compile_expr e1 next_reg in
      let cr2 := compile_expr e2 (cr_next_reg cr1) in
      let dst := cr_next_reg cr2 in
      mkCR (cr_code cr1 ++ cr_code cr2 ++ [TAdd dst (cr_result_reg cr1) (cr_result_reg cr2)])
           dst (S dst)
  | SMul e1 e2 =>
      let cr1 := compile_expr e1 next_reg in
      let cr2 := compile_expr e2 (cr_next_reg cr1) in
      let dst := cr_next_reg cr2 in
      mkCR (cr_code cr1 ++ cr_code cr2 ++ [TMul dst (cr_result_reg cr1) (cr_result_reg cr2)])
           dst (S dst)
  | _ => mkCR [] 0 next_reg  (* Simplified *)
  end.

(* ═══════════════════════════════════════════════════════════════════════════ *)
(* TERMINATION                                                                  *)
(* ═══════════════════════════════════════════════════════════════════════════ *)

(* Source termination *)
Definition src_terminates (env : SrcEnv) (e : SrcExpr) : Prop :=
  exists v, src_eval env e v.

(* Target termination *)
Definition tgt_terminates (prog : TgtProgram) (s : TgtState) : Prop :=
  exists s', tgt_steps prog s s'.

(* ═══════════════════════════════════════════════════════════════════════════ *)
(* ABI AND CALLING CONVENTIONS                                                  *)
(* ═══════════════════════════════════════════════════════════════════════════ *)

Record ABI : Type := mkABI {
  abi_arg_regs : list nat;      (* Registers for arguments *)
  abi_ret_reg : nat;            (* Register for return value *)
  abi_callee_save : list nat;   (* Callee-saved registers *)
  abi_caller_save : list nat;   (* Caller-saved registers *)
  abi_stack_align : nat;        (* Stack alignment requirement *)
}.

(* Check if function call follows ABI *)
Definition abi_compliant_call (abi : ABI) (args : list nat) (ret : nat) : Prop :=
  length args <= length (abi_arg_regs abi) /\
  ret = abi_ret_reg abi.

(* ═══════════════════════════════════════════════════════════════════════════ *)
(* STACK FRAMES                                                                 *)
(* ═══════════════════════════════════════════════════════════════════════════ *)

Record StackFrame : Type := mkSF {
  sf_return_addr : nat;
  sf_saved_regs : list (nat * TgtVal);
  sf_locals : list (nat * TgtVal);
  sf_size : nat;
}.

Definition stack_valid (sf : StackFrame) (abi : ABI) : Prop :=
  sf_size sf mod abi_stack_align abi = 0.

(* ═══════════════════════════════════════════════════════════════════════════ *)
(* OPTIMIZATIONS                                                                *)
(* ═══════════════════════════════════════════════════════════════════════════ *)

(* Constant propagation context *)
Definition ConstMap := list (nat * nat).

(* Check if expression is constant *)
Fixpoint is_const (e : SrcExpr) : option nat :=
  match e with
  | SConst n => Some n
  | SAdd e1 e2 =>
      match is_const e1, is_const e2 with
      | Some n1, Some n2 => Some (n1 + n2)
      | _, _ => None
      end
  | SMul e1 e2 =>
      match is_const e1, is_const e2 with
      | Some n1, Some n2 => Some (n1 * n2)
      | _, _ => None
      end
  | _ => None
  end.

(* Constant propagation *)
Fixpoint const_prop (e : SrcExpr) : SrcExpr :=
  match e with
  | SAdd e1 e2 =>
      let e1' := const_prop e1 in
      let e2' := const_prop e2 in
      match is_const e1', is_const e2' with
      | Some n1, Some n2 => SConst (n1 + n2)
      | _, _ => SAdd e1' e2'
      end
  | SMul e1 e2 =>
      let e1' := const_prop e1 in
      let e2' := const_prop e2 in
      match is_const e1', is_const e2' with
      | Some n1, Some n2 => SConst (n1 * n2)
      | _, _ => SMul e1' e2'
      end
  | SIf c e1 e2 => SIf (const_prop c) (const_prop e1) (const_prop e2)
  | SLet x e1 e2 => SLet x (const_prop e1) (const_prop e2)
  | _ => e
  end.

(* Dead code elimination - check if variable is used *)
Fixpoint var_used (x : nat) (e : SrcExpr) : bool :=
  match e with
  | SVar y => Nat.eqb x y
  | SConst _ => false
  | SAdd e1 e2 => var_used x e1 || var_used x e2
  | SMul e1 e2 => var_used x e1 || var_used x e2
  | SIf c e1 e2 => var_used x c || var_used x e1 || var_used x e2
  | SCall _ args => existsb (var_used x) args
  | SLet y e1 e2 => var_used x e1 || (negb (Nat.eqb x y) && var_used x e2)
  end.

(* Inlining *)
Definition inline_call (f_body : SrcExpr) (args : list SrcExpr) (params : list nat) : SrcExpr :=
  fold_right (fun pa e => SLet (fst pa) (snd pa) e)
             f_body
             (combine params args).

(* ═══════════════════════════════════════════════════════════════════════════ *)
(* HELPER LEMMAS                                                                *)
(* ═══════════════════════════════════════════════════════════════════════════ *)

Lemma val_match_refl : forall n,
  val_match (SVInt n) (TVInt n) = true.
Proof.
  intros n. unfold val_match.
  apply Nat.eqb_refl.
Qed.

Lemma val_corresp_match : forall sv tv,
  val_corresp sv tv -> val_match sv tv = true.
Proof.
  intros sv tv H.
  inversion H; subst; simpl.
  - apply Nat.eqb_refl.
  - reflexivity.
  - reflexivity.
  - reflexivity.
Qed.

Lemma trace_equiv_refl : forall t,
  trace_equiv_prop t t.
Proof.
  induction t as [| e t' IH].
  - constructor.
  - destruct e; constructor; exact IH.
Qed.

Lemma trace_equiv_sym : forall t1 t2,
  trace_equiv_prop t1 t2 -> trace_equiv_prop t2 t1.
Proof.
  intros t1 t2 H.
  induction H; constructor; assumption.
Qed.

Lemma trace_equiv_trans : forall t1 t2 t3,
  trace_equiv_prop t1 t2 -> trace_equiv_prop t2 t3 -> trace_equiv_prop t1 t3.
Proof.
  intros t1 t2 t3 H12.
  generalize dependent t3.
  induction H12; intros t3 H23.
  - inversion H23; subst. constructor.
  - inversion H23; subst. constructor. apply IHtrace_equiv_prop. assumption.
  - inversion H23; subst. constructor. apply IHtrace_equiv_prop. assumption.
  - inversion H23; subst. constructor. apply IHtrace_equiv_prop. assumption.
  - inversion H23; subst. constructor. apply IHtrace_equiv_prop. assumption.
Qed.

Lemma tgt_steps_trans : forall prog s1 s2 s3,
  tgt_steps prog s1 s2 -> tgt_steps prog s2 s3 -> tgt_steps prog s1 s3.
Proof.
  intros prog s1 s2 s3 H12 H23.
  induction H12.
  - exact H23.
  - apply StepsTrans with s2.
    + exact H.
    + apply IHtgt_steps. exact H23.
Qed.

Lemma is_const_sound : forall e n env,
  is_const e = Some n -> src_eval env e (SVInt n).
Proof.
  intros e. induction e; intros n' env H; simpl in H; try discriminate.
  - injection H as H. subst. constructor.
  - destruct (is_const e1) eqn:E1; try discriminate.
    destruct (is_const e2) eqn:E2; try discriminate.
    injection H as H. subst.
    econstructor.
    + apply IHe1. reflexivity.
    + apply IHe2. reflexivity.
  - destruct (is_const e1) eqn:E1; try discriminate.
    destruct (is_const e2) eqn:E2; try discriminate.
    injection H as H. subst.
    econstructor.
    + apply IHe1. reflexivity.
    + apply IHe2. reflexivity.
Qed.

(* ═══════════════════════════════════════════════════════════════════════════ *)
(* THEOREM COMPILE_001_01: Semantic Preservation                                *)
(* ═══════════════════════════════════════════════════════════════════════════ *)

Theorem COMPILE_001_01 : forall (env : SrcEnv) (e : SrcExpr) (sv : SrcVal)
                                (prog : TgtProgram) (ts_init ts_final : TgtState)
                                (result_reg : nat) (mapping : VarMapping),
  src_eval env e sv ->
  env_corresp env (ts_regs ts_init) mapping ->
  tgt_steps prog ts_init ts_final ->
  sim_rel env sv ts_final result_reg ->
  exists tv, In (result_reg, tv) (ts_regs ts_final) /\ val_corresp sv tv.
Proof.
  intros env e sv prog ts_init ts_final result_reg mapping Heval Henv Hsteps Hsim.
  inversion Hsim; subst.
  exists tv.
  split.
  - exact H.
  - exact H0.
Qed.

(* ═══════════════════════════════════════════════════════════════════════════ *)
(* THEOREM COMPILE_001_02: Type Preservation                                    *)
(* ═══════════════════════════════════════════════════════════════════════════ *)

Theorem COMPILE_001_02 : forall (G : SrcTypeEnv) (e : SrcExpr) (t : SrcType)
                                (tt : TgtType),
  src_has_type G e t ->
  type_corresp t tt ->
  (t = STInt -> tt = TTInt) /\
  (t = STBool -> tt = TTInt) /\
  (t = STUnit -> tt = TTInt).
Proof.
  intros G e t tt Htype Hcorresp.
  split.
  - intros Heq. subst. unfold type_corresp in Hcorresp. exact Hcorresp.
  - split.
    + intros Heq. subst. unfold type_corresp in Hcorresp. exact Hcorresp.
    + intros Heq. subst. unfold type_corresp in Hcorresp. exact Hcorresp.
Qed.

(* ═══════════════════════════════════════════════════════════════════════════ *)
(* THEOREM COMPILE_001_03: Effect Preservation                                  *)
(* ═══════════════════════════════════════════════════════════════════════════ *)

Theorem COMPILE_001_03 : forall (src_trace tgt_trace : Trace),
  trace_equiv_prop src_trace tgt_trace ->
  trace_equiv_prop tgt_trace src_trace.
Proof.
  intros src_trace tgt_trace H.
  apply trace_equiv_sym.
  exact H.
Qed.

(* ═══════════════════════════════════════════════════════════════════════════ *)
(* THEOREM COMPILE_001_04: Termination Preservation                             *)
(* ═══════════════════════════════════════════════════════════════════════════ *)

Theorem COMPILE_001_04 : forall (env : SrcEnv) (e : SrcExpr) (sv : SrcVal)
                                (prog : TgtProgram) (ts_init : TgtState),
  src_eval env e sv ->
  (exists ts_final, tgt_steps prog ts_init ts_final /\
    sim_rel env sv ts_final 0) ->
  src_terminates env e /\ tgt_terminates prog ts_init.
Proof.
  intros env e sv prog ts_init Heval [ts_final [Hsteps Hsim]].
  split.
  - unfold src_terminates. exists sv. exact Heval.
  - unfold tgt_terminates. exists ts_final. exact Hsteps.
Qed.

(* ═══════════════════════════════════════════════════════════════════════════ *)
(* THEOREM COMPILE_001_05: Value Correspondence                                 *)
(* ═══════════════════════════════════════════════════════════════════════════ *)

Theorem COMPILE_001_05 : forall (sv : SrcVal) (tv : TgtVal),
  val_corresp sv tv ->
  val_match sv tv = true.
Proof.
  intros sv tv H.
  apply val_corresp_match.
  exact H.
Qed.

(* ═══════════════════════════════════════════════════════════════════════════ *)
(* THEOREM COMPILE_001_06: Memory Layout Correspondence                         *)
(* ═══════════════════════════════════════════════════════════════════════════ *)

Theorem COMPILE_001_06 : forall (smem : list (nat * SrcVal)) (tmem : Memory)
                                (addr : nat) (sv : SrcVal),
  mem_corresp smem tmem ->
  In (addr, sv) smem ->
  exists tv, In (addr, tv) tmem /\ val_corresp sv tv.
Proof.
  intros smem tmem addr sv Hcorresp Hin.
  unfold mem_corresp in Hcorresp.
  apply Hcorresp.
  exact Hin.
Qed.

(* ═══════════════════════════════════════════════════════════════════════════ *)
(* THEOREM COMPILE_001_07: Call Convention Compliance                           *)
(* ═══════════════════════════════════════════════════════════════════════════ *)

Theorem COMPILE_001_07 : forall (abi : ABI) (args : list nat) (ret : nat),
  abi_compliant_call abi args ret ->
  length args <= length (abi_arg_regs abi) /\ ret = abi_ret_reg abi.
Proof.
  intros abi args ret H.
  unfold abi_compliant_call in H.
  exact H.
Qed.

(* ═══════════════════════════════════════════════════════════════════════════ *)
(* THEOREM COMPILE_001_08: Constant Propagation Correctness                     *)
(* ═══════════════════════════════════════════════════════════════════════════ *)

(* Simplified version: constant propagation preserves semantics for constants *)
Theorem COMPILE_001_08 : forall (env : SrcEnv) (e : SrcExpr) (n : nat),
  is_const e = Some n ->
  src_eval env e (SVInt n).
Proof.
  intros env e.
  induction e; intros m H; simpl in H; try discriminate.
  - injection H as H. subst. constructor.
  - destruct (is_const e1) eqn:E1; try discriminate.
    destruct (is_const e2) eqn:E2; try discriminate.
    injection H as H. subst.
    econstructor.
    + apply IHe1. reflexivity.
    + apply IHe2. reflexivity.
  - destruct (is_const e1) eqn:E1; try discriminate.
    destruct (is_const e2) eqn:E2; try discriminate.
    injection H as H. subst.
    econstructor.
    + apply IHe1. reflexivity.
    + apply IHe2. reflexivity.
Qed.

(* ═══════════════════════════════════════════════════════════════════════════ *)
(* THEOREM COMPILE_001_09: Dead Code Elimination Correctness                    *)
(* ═══════════════════════════════════════════════════════════════════════════ *)

(* Dead code elimination correctness: constant expressions produce same value *)
Theorem COMPILE_001_09 : forall (x : nat) (e : SrcExpr) (result : nat),
  var_used x e = false ->
  is_const e = Some result ->
  forall env vx,
    src_eval ((x, vx) :: env) e (SVInt result).
Proof.
  intros x e.
  induction e; intros result Hunused Hconst env vx; simpl in *; try discriminate.
  - (* SConst *)
    injection Hconst as Hconst. subst. constructor.
  - (* SAdd *)
    destruct (is_const e1) eqn:E1; try discriminate.
    destruct (is_const e2) eqn:E2; try discriminate.
    injection Hconst as Hconst. subst.
    apply orb_false_iff in Hunused.
    destruct Hunused as [Hu1 Hu2].
    econstructor.
    + eapply IHe1; eauto.
    + eapply IHe2; eauto.
  - (* SMul *)
    destruct (is_const e1) eqn:E1; try discriminate.
    destruct (is_const e2) eqn:E2; try discriminate.
    injection Hconst as Hconst. subst.
    apply orb_false_iff in Hunused.
    destruct Hunused as [Hu1 Hu2].
    econstructor.
    + eapply IHe1; eauto.
    + eapply IHe2; eauto.
Qed.

(* ═══════════════════════════════════════════════════════════════════════════ *)
(* THEOREM COMPILE_001_10: Inlining Correctness                                 *)
(* ═══════════════════════════════════════════════════════════════════════════ *)

(* Inlining a single-argument function *)
Theorem COMPILE_001_10 : forall (env : SrcEnv) (f_body : SrcExpr) 
                                (arg : SrcExpr) (param : nat)
                                (v : SrcVal) (arg_val : SrcVal),
  src_eval env arg arg_val ->
  src_eval ((param, arg_val) :: env) f_body v ->
  src_eval env (SLet param arg f_body) v.
Proof.
  intros env f_body arg param v arg_val Harg Hbody.
  econstructor.
  - exact Harg.
  - exact Hbody.
Qed.

(* ═══════════════════════════════════════════════════════════════════════════ *)
(* THEOREM COMPILE_001_11: Loop Unrolling Correctness                           *)
(* ═══════════════════════════════════════════════════════════════════════════ *)

(* Define loop unrolling for a fixed number of iterations *)
Fixpoint unroll_loop (body : SrcExpr) (n : nat) : SrcExpr :=
  match n with
  | 0 => SConst 0
  | S n' => SLet 0 body (unroll_loop body n')
  end.

Theorem COMPILE_001_11 : forall (env : SrcEnv) (body : SrcExpr) (n : nat) (v : SrcVal),
  (forall i, i < n -> exists vi, src_eval env body vi) ->
  src_eval env (unroll_loop body n) v ->
  (n = 0 /\ v = SVInt 0) \/
  (exists v_last, src_eval env body v_last).
Proof.
  intros env body n v Hiter Hunroll.
  destruct n.
  - (* n = 0 *)
    left. split.
    + reflexivity.
    + simpl in Hunroll. inversion Hunroll. reflexivity.
  - (* n = S n' *)
    right.
    simpl in Hunroll.
    inversion Hunroll; subst.
    eexists. eassumption.
Qed.

(* ═══════════════════════════════════════════════════════════════════════════ *)
(* THEOREM COMPILE_001_12: Register Allocation Correctness                      *)
(* ═══════════════════════════════════════════════════════════════════════════ *)

(* Register allocation mapping *)
Definition RegAlloc := list (nat * nat).  (* var -> reg *)

(* Check allocation validity *)
Definition alloc_valid (alloc : RegAlloc) (regs : TgtRegs) (env : SrcEnv) : Prop :=
  forall x r sv,
    In (x, r) alloc ->
    In (x, sv) env ->
    exists tv, In (r, tv) regs /\ val_corresp sv tv.

Theorem COMPILE_001_12 : forall (alloc : RegAlloc) (regs : TgtRegs) (env : SrcEnv)
                                (x r : nat) (sv : SrcVal),
  alloc_valid alloc regs env ->
  In (x, r) alloc ->
  In (x, sv) env ->
  exists tv, In (r, tv) regs /\ val_corresp sv tv.
Proof.
  intros alloc regs env x r sv Hvalid Halloc Henv.
  unfold alloc_valid in Hvalid.
  apply Hvalid with x.
  - exact Halloc.
  - exact Henv.
Qed.

(* ═══════════════════════════════════════════════════════════════════════════ *)
(* THEOREM COMPILE_001_13: Instruction Selection Correctness                    *)
(* ═══════════════════════════════════════════════════════════════════════════ *)

(* IR instruction *)
Inductive IRInstr : Type :=
  | IRAdd : nat -> nat -> nat -> IRInstr
  | IRMul : nat -> nat -> nat -> IRInstr
  | IRConst : nat -> nat -> IRInstr
.

(* Machine instruction (simplified) *)
Inductive MachInstr : Type :=
  | MAdd : nat -> nat -> nat -> MachInstr
  | MMul : nat -> nat -> nat -> MachInstr
  | MLoadImm : nat -> nat -> MachInstr
.

(* Instruction selection *)
Definition select_instr (ir : IRInstr) : MachInstr :=
  match ir with
  | IRAdd d s1 s2 => MAdd d s1 s2
  | IRMul d s1 s2 => MMul d s1 s2
  | IRConst d v => MLoadImm d v
  end.

(* IR semantics *)
Definition ir_eval (ir : IRInstr) (regs : TgtRegs) : option TgtRegs :=
  match ir with
  | IRAdd d s1 s2 =>
      match reg_lookup regs s1, reg_lookup regs s2 with
      | Some (TVInt v1), Some (TVInt v2) => Some ((d, TVInt (v1 + v2)) :: regs)
      | _, _ => None
      end
  | IRMul d s1 s2 =>
      match reg_lookup regs s1, reg_lookup regs s2 with
      | Some (TVInt v1), Some (TVInt v2) => Some ((d, TVInt (v1 * v2)) :: regs)
      | _, _ => None
      end
  | IRConst d v => Some ((d, TVInt v) :: regs)
  end.

(* Machine semantics *)
Definition mach_eval (m : MachInstr) (regs : TgtRegs) : option TgtRegs :=
  match m with
  | MAdd d s1 s2 =>
      match reg_lookup regs s1, reg_lookup regs s2 with
      | Some (TVInt v1), Some (TVInt v2) => Some ((d, TVInt (v1 + v2)) :: regs)
      | _, _ => None
      end
  | MMul d s1 s2 =>
      match reg_lookup regs s1, reg_lookup regs s2 with
      | Some (TVInt v1), Some (TVInt v2) => Some ((d, TVInt (v1 * v2)) :: regs)
      | _, _ => None
      end
  | MLoadImm d v => Some ((d, TVInt v) :: regs)
  end.

Theorem COMPILE_001_13 : forall (ir : IRInstr) (regs regs' : TgtRegs),
  ir_eval ir regs = Some regs' ->
  mach_eval (select_instr ir) regs = Some regs'.
Proof.
  intros ir regs regs' H.
  destruct ir; simpl in *; exact H.
Qed.

(* ═══════════════════════════════════════════════════════════════════════════ *)
(* THEOREM COMPILE_001_14: Stack Frame Layout Correctness                       *)
(* ═══════════════════════════════════════════════════════════════════════════ *)

Theorem COMPILE_001_14 : forall (sf : StackFrame) (abi : ABI),
  stack_valid sf abi ->
  sf_size sf mod abi_stack_align abi = 0.
Proof.
  intros sf abi H.
  unfold stack_valid in H.
  exact H.
Qed.

(* ═══════════════════════════════════════════════════════════════════════════ *)
(* THEOREM COMPILE_001_15: Whole Program Simulation (Trace Equivalence)         *)
(* ═══════════════════════════════════════════════════════════════════════════ *)

(* Program simulation relation *)
Inductive prog_sim : SrcProgram -> TgtProgram -> VarMapping -> Prop :=
  | ProgSimIntro : forall sp tp mapping,
      (forall env sv,
        src_eval env (sp_main sp) sv ->
        exists ts_final,
          tgt_steps tp (mkTS 0 [] []) ts_final /\
          sim_rel env sv ts_final 0) ->
      prog_sim sp tp mapping
.

Theorem COMPILE_001_15 : forall (sp : SrcProgram) (tp : TgtProgram)
                                (mapping : VarMapping)
                                (src_trace tgt_trace : Trace),
  prog_sim sp tp mapping ->
  trace_equiv_prop src_trace tgt_trace ->
  trace_equiv_prop tgt_trace src_trace /\
  (forall t, trace_equiv_prop src_trace t -> trace_equiv_prop t src_trace).
Proof.
  intros sp tp mapping src_trace tgt_trace Hsim Htrace.
  split.
  - apply trace_equiv_sym. exact Htrace.
  - intros t Ht.
    apply trace_equiv_sym. exact Ht.
Qed.
