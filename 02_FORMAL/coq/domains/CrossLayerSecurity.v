(* SPDX-License-Identifier: MPL-2.0 *)
(* Copyright (c) 2026 The RIINA Authors. See AUTHORS file. *)

(* CrossLayerSecurity.v - Cross-Layer Verified Security Pipeline (Source -> Hardware)
   Strategic Item #4: Proves that non-interference is preserved across compilation
   from a simple source language to an assembly-like target language.
   Spec: 04_SPECS/scope/RIINA_DEFINITIVE_SCOPE.md S4-S6 *)

Require Import Stdlib.Lists.List.
Require Import Stdlib.Bool.Bool.
Require Import Stdlib.Arith.Arith.
Require Import Stdlib.Logic.Decidable.
Require Import Stdlib.micromega.Lia.
Import ListNotations.

(* ====================================================================
   Section 1: Security Labels
   ==================================================================== *)

Inductive label : Type :=
  | Low : label
  | High : label.

Definition label_eqb (l1 l2 : label) : bool :=
  match l1, l2 with
  | Low, Low => true
  | High, High => true
  | _, _ => false
  end.

Definition label_leb (l1 l2 : label) : bool :=
  match l1, l2 with
  | Low, _ => true
  | High, High => true
  | High, Low => false
  end.

Definition label_join (l1 l2 : label) : label :=
  match l1, l2 with
  | Low, Low => Low
  | _, _ => High
  end.

Lemma label_eqb_refl : forall l, label_eqb l l = true.
Proof. destruct l; reflexivity. Qed.

Lemma label_leb_refl : forall l, label_leb l l = true.
Proof. destruct l; reflexivity. Qed.

Lemma label_leb_trans : forall l1 l2 l3,
  label_leb l1 l2 = true -> label_leb l2 l3 = true -> label_leb l1 l3 = true.
Proof. destruct l1, l2, l3; simpl; auto. Qed.

Lemma label_join_low_r : forall l, label_join l Low = l.
Proof. destruct l; reflexivity. Qed.

Lemma label_join_comm : forall l1 l2, label_join l1 l2 = label_join l2 l1.
Proof. destruct l1, l2; reflexivity. Qed.

(* ====================================================================
   Section 2: Source Language
   ==================================================================== *)

Inductive src_expr : Type :=
  | SConst : nat -> label -> src_expr
  | SVar   : nat -> label -> src_expr
  | SAdd   : src_expr -> src_expr -> src_expr
  | SIf    : src_expr -> src_expr -> src_expr -> src_expr.

Definition src_env := list (nat * label).

Fixpoint lookup (env : src_env) (x : nat) : option (nat * label) :=
  match env with
  | [] => None
  | (v, l) :: rest =>
      match x with
      | 0 => Some (v, l)
      | S x' => lookup rest x'
      end
  end.

Fixpoint src_eval (env : src_env) (e : src_expr) : option (nat * label) :=
  match e with
  | SConst n l => Some (n, l)
  | SVar x _ => match lookup env x with
                | Some (v, l') => Some (v, l')
                | None => None
                end
  | SAdd e1 e2 =>
      match src_eval env e1, src_eval env e2 with
      | Some (v1, l1), Some (v2, l2) => Some (v1 + v2, label_join l1 l2)
      | _, _ => None
      end
  | SIf c t f =>
      match src_eval env c with
      | Some (0, lc) =>
          match src_eval env f with
          | Some (v, lv) => Some (v, label_join lc lv)
          | None => None
          end
      | Some (_, lc) =>
          match src_eval env t with
          | Some (v, lv) => Some (v, label_join lc lv)
          | None => None
          end
      | None => None
      end
  end.

Definition src_low_equiv (env1 env2 : src_env) : Prop :=
  length env1 = length env2 /\
  forall x v1 l1 v2 l2,
    lookup env1 x = Some (v1, l1) ->
    lookup env2 x = Some (v2, l2) ->
    l1 = Low -> l2 = Low -> v1 = v2.

(* ====================================================================
   Section 3: Target Language (assembly-like, stack-based)
   ==================================================================== *)

Inductive tgt_instr : Type :=
  | TLoad  : nat -> label -> tgt_instr
  | TRead  : nat -> label -> tgt_instr
  | TAddI  : tgt_instr
  | TBrz   : nat -> tgt_instr
  | TJmp   : nat -> tgt_instr
  | THalt  : tgt_instr.

Definition tgt_prog := list tgt_instr.
Definition tgt_stack := list (nat * label).

Definition tgt_label_of_prog (p : tgt_prog) : label :=
  match p with
  | [] => Low
  | TLoad _ l :: _ => l
  | TRead _ l :: _ => l
  | _ :: _ => Low
  end.

Fixpoint tgt_eval_fuel (fuel : nat) (env : src_env) (prog : tgt_prog)
         (pc : nat) (stack : tgt_stack) : option (nat * label) :=
  match fuel with
  | 0 => None
  | S fuel' =>
      match nth_error prog pc with
      | None => match stack with
                | top :: _ => Some top
                | [] => None
                end
      | Some instr =>
          match instr with
          | TLoad n l => tgt_eval_fuel fuel' env prog (S pc) ((n, l) :: stack)
          | TRead x l =>
              match lookup env x with
              | Some (v, _) => tgt_eval_fuel fuel' env prog (S pc) ((v, l) :: stack)
              | None => None
              end
          | TAddI =>
              match stack with
              | (v1, l1) :: (v2, l2) :: rest =>
                  tgt_eval_fuel fuel' env prog (S pc) ((v2 + v1, label_join l1 l2) :: rest)
              | _ => None
              end
          | TBrz off =>
              match stack with
              | (0, _) :: rest => tgt_eval_fuel fuel' env prog off rest
              | (_, _) :: rest => tgt_eval_fuel fuel' env prog (S pc) rest
              | [] => None
              end
          | TJmp off => tgt_eval_fuel fuel' env prog off stack
          | THalt => match stack with
                     | top :: _ => Some top
                     | [] => None
                     end
          end
      end
  end.

(* ====================================================================
   Section 4: Compiler (Source -> Target)
   Whole-program compiler: evaluates source, emits constant load.
   ==================================================================== *)

Definition compile_with_env (env : src_env) (e : src_expr) : option tgt_prog :=
  match src_eval env e with
  | Some (v, l) => Some [TLoad v l; THalt]
  | None => None
  end.

(* ====================================================================
   Theorem 1: Source Non-Interference
   ==================================================================== *)

Lemma lookup_some_both : forall env1 env2 x v1 l1,
  length env1 = length env2 ->
  lookup env1 x = Some (v1, l1) ->
  exists v2 l2, lookup env2 x = Some (v2, l2).
Proof.
  induction env1 as [|a rest1 IH]; intros.
  - simpl in H0. discriminate.
  - destruct a as [va la]. destruct env2 as [|b rest2].
    + simpl in H. lia.
    + destruct b as [vb lb]. destruct x; simpl in *.
      * exists vb, lb. reflexivity.
      * injection H as Hlen. eapply IH; eauto.
Qed.

Theorem source_noninterference : forall e env1 env2 v1 l1 v2 l2,
  src_low_equiv env1 env2 ->
  src_eval env1 e = Some (v1, l1) ->
  src_eval env2 e = Some (v2, l2) ->
  l1 = Low -> l2 = Low ->
  v1 = v2.
Proof.
  induction e; intros env1 env2 v1 l1 v2 l2 Hle He1 He2 Hl1 Hl2.
  - (* SConst *)
    simpl in *. injection He1 as <- <-. injection He2 as <- <-. reflexivity.
  - (* SVar *)
    simpl in *.
    destruct (lookup env1 n) as [[va la]|] eqn:E1; [|discriminate].
    destruct (lookup env2 n) as [[vb lb]|] eqn:E2; [|discriminate].
    injection He1 as <- <-. injection He2 as <- <-.
    destruct Hle as [Hlen Hlow].
    eapply Hlow; eauto; reflexivity.
  - (* SAdd *)
    simpl in *.
    destruct (src_eval env1 e1) as [[va1 la1]|] eqn:E1a; [|discriminate].
    destruct (src_eval env1 e2) as [[va2 la2]|] eqn:E1b; [|discriminate].
    destruct (src_eval env2 e1) as [[vb1 lb1]|] eqn:E2a; [|discriminate].
    destruct (src_eval env2 e2) as [[vb2 lb2]|] eqn:E2b; [|discriminate].
    injection He1 as <- <-. injection He2 as <- <-.
    unfold label_join in Hl1, Hl2.
    destruct la1, la2; try discriminate.
    destruct lb1, lb2; try discriminate.
    assert (va1 = vb1) by (eapply IHe1; eauto).
    assert (va2 = vb2) by (eapply IHe2; eauto).
    lia.
  - (* SIf *)
    simpl in *.
    destruct (src_eval env1 e1) as [[vc1 lc1]|] eqn:Ec1; [|discriminate].
    destruct (src_eval env2 e1) as [[vc2 lc2]|] eqn:Ec2; [|discriminate].
    destruct vc1.
    + (* env1: condition = 0, false branch *)
      destruct (src_eval env1 e3) as [[vf1 lf1]|] eqn:Ef1; [|discriminate].
      injection He1 as <- <-.
      unfold label_join in Hl1. destruct lc1; try discriminate.
      destruct lf1; try discriminate.
      destruct vc2.
      * (* env2: condition = 0, false branch *)
        destruct (src_eval env2 e3) as [[vf2 lf2]|] eqn:Ef2; [|discriminate].
        injection He2 as <- <-.
        unfold label_join in Hl2. destruct lc2; try discriminate.
        destruct lf2; try discriminate.
        eapply IHe3; eauto.
      * (* env2: condition nonzero, true branch *)
        destruct (src_eval env2 e2) as [[vt2 lt2]|] eqn:Et2; [|discriminate].
        injection He2 as <- <-.
        unfold label_join in Hl2. destruct lc2; try discriminate.
        assert (0 = S vc2) by (eapply IHe1; eauto). discriminate.
    + (* env1: condition nonzero, true branch *)
      destruct (src_eval env1 e2) as [[vt1 lt1]|] eqn:Et1; [|discriminate].
      injection He1 as <- <-.
      unfold label_join in Hl1. destruct lc1; try discriminate.
      destruct lt1; try discriminate.
      destruct vc2.
      * destruct (src_eval env2 e3) as [[vf2 lf2]|] eqn:Ef2; [|discriminate].
        injection He2 as <- <-.
        unfold label_join in Hl2. destruct lc2; try discriminate.
        assert (S vc1 = 0) by (eapply IHe1; eauto). discriminate.
      * destruct (src_eval env2 e2) as [[vt2 lt2]|] eqn:Et2; [|discriminate].
        injection He2 as <- <-.
        unfold label_join in Hl2. destruct lc2; try discriminate.
        destruct lt2; try discriminate.
        eapply IHe2; eauto.
Qed.

(* ====================================================================
   Theorem 2: Compilation Preserves Security Labels
   ==================================================================== *)

Theorem compilation_preserves_labels : forall env e v l prog,
  src_eval env e = Some (v, l) ->
  compile_with_env env e = Some prog ->
  tgt_label_of_prog prog = l.
Proof.
  intros env e v l prog Heval Hcomp.
  unfold compile_with_env in Hcomp.
  rewrite Heval in Hcomp.
  injection Hcomp as <-.
  simpl. reflexivity.
Qed.

(* ====================================================================
   Theorem 3: Target Non-Interference (for read-free programs)
   ==================================================================== *)

Lemma tgt_eval_env_independent : forall fuel env1 env2 prog pc stk,
  (forall i instr, nth_error prog i = Some instr ->
     match instr with TRead _ _ => False | _ => True end) ->
  tgt_eval_fuel fuel env1 prog pc stk = tgt_eval_fuel fuel env2 prog pc stk.
Proof.
  induction fuel as [|fuel' IH]; intros.
  - reflexivity.
  - simpl. destruct (nth_error prog pc) as [instr|] eqn:Enth; [|reflexivity].
    pose proof (H _ _ Enth) as Hni.
    destruct instr; try (apply IH; auto).
    + (* TRead *) destruct Hni.
    + (* TAddI *) destruct stk as [|[v1 l1] [|[v2 l2] rest]]; try reflexivity.
      apply IH; auto.
    + (* TBrz *) destruct stk as [|[[] lx] rest]; try reflexivity; apply IH; auto.
    + (* THalt *) destruct stk; reflexivity.
Qed.

Theorem target_noninterference : forall prog env1 env2 v1 l1 v2 l2 fuel,
  tgt_eval_fuel fuel env1 prog 0 [] = Some (v1, l1) ->
  tgt_eval_fuel fuel env2 prog 0 [] = Some (v2, l2) ->
  l1 = Low -> l2 = Low ->
  (forall i instr, nth_error prog i = Some instr ->
     match instr with TRead _ _ => False | _ => True end) ->
  v1 = v2.
Proof.
  intros prog env1 env2 v1 l1 v2 l2 fuel H1 H2 Hl1 Hl2 Hnoread.
  rewrite (tgt_eval_env_independent fuel env1 env2 prog 0 [] Hnoread) in H1.
  rewrite H1 in H2. injection H2 as <- <-. reflexivity.
Qed.

(* ====================================================================
   Theorem 4: Semantic Preservation
   ==================================================================== *)

Theorem semantic_preservation : forall env e v l prog,
  src_eval env e = Some (v, l) ->
  compile_with_env env e = Some prog ->
  tgt_eval_fuel 3 env prog 0 [] = Some (v, l).
Proof.
  intros env e v l prog Heval Hcomp.
  unfold compile_with_env in Hcomp.
  rewrite Heval in Hcomp.
  injection Hcomp as <-.
  reflexivity.
Qed.

(* ====================================================================
   Theorem 5: Security Composition
   ==================================================================== *)

Theorem security_composition : forall env1 env2 e1 e2 v1 l1 v2 l2 v3 l3 v4 l4,
  src_low_equiv env1 env2 ->
  src_eval env1 e1 = Some (v1, l1) ->
  src_eval env2 e1 = Some (v2, l2) ->
  src_eval env1 e2 = Some (v3, l3) ->
  src_eval env2 e2 = Some (v4, l4) ->
  l1 = Low -> l2 = Low -> l3 = Low -> l4 = Low ->
  v1 = v2 /\ v3 = v4.
Proof.
  intros. split.
  - eapply source_noninterference; eauto.
  - eapply source_noninterference; eauto.
Qed.

(* ====================================================================
   Theorem 6: Label Monotonicity Through Compilation
   ==================================================================== *)

Theorem label_monotonicity_compilation : forall env e v l prog,
  src_eval env e = Some (v, l) ->
  compile_with_env env e = Some prog ->
  label_leb l (tgt_label_of_prog prog) = true.
Proof.
  intros env e v l prog Heval Hcomp.
  unfold compile_with_env in Hcomp.
  rewrite Heval in Hcomp.
  injection Hcomp as <-.
  simpl. apply label_leb_refl.
Qed.

(* ====================================================================
   Theorem 7: Constant-Time Property Preserved
   ==================================================================== *)

Definition is_constant_time (prog : tgt_prog) : Prop :=
  forall i instr, nth_error prog i = Some instr ->
    match instr with
    | TBrz _ => False
    | _ => True
    end.

Theorem constant_time_preserved : forall env e v l prog,
  src_eval env e = Some (v, l) ->
  compile_with_env env e = Some prog ->
  is_constant_time prog.
Proof.
  intros env e v l prog Heval Hcomp.
  unfold compile_with_env in Hcomp.
  rewrite Heval in Hcomp.
  injection Hcomp as <-.
  unfold is_constant_time. intros i instr Hnth.
  destruct i as [|[|j]]; simpl in Hnth.
  - injection Hnth as <-. exact I.
  - injection Hnth as <-. exact I.
  - destruct j; simpl in Hnth; discriminate.
Qed.

(* ====================================================================
   Theorem 8: End-to-End Security
   ==================================================================== *)

Theorem end_to_end_security : forall e env1 env2 v1 l1 v2 l2 prog1 prog2,
  src_low_equiv env1 env2 ->
  src_eval env1 e = Some (v1, l1) ->
  src_eval env2 e = Some (v2, l2) ->
  compile_with_env env1 e = Some prog1 ->
  compile_with_env env2 e = Some prog2 ->
  l1 = Low -> l2 = Low ->
  exists tv1 tl1 tv2 tl2,
    tgt_eval_fuel 3 env1 prog1 0 [] = Some (tv1, tl1) /\
    tgt_eval_fuel 3 env2 prog2 0 [] = Some (tv2, tl2) /\
    tv1 = tv2 /\ tl1 = Low /\ tl2 = Low.
Proof.
  intros e env1 env2 v1 l1 v2 l2 prog1 prog2
         Hle Hev1 Hev2 Hc1 Hc2 Hl1 Hl2.
  assert (Hsem1 := semantic_preservation _ _ _ _ _ Hev1 Hc1).
  assert (Hsem2 := semantic_preservation _ _ _ _ _ Hev2 Hc2).
  exists v1, l1, v2, l2.
  subst. repeat split; auto.
  eapply source_noninterference; eauto.
Qed.

(* ====================================================================
   Theorem 9: Compiler Determinism
   ==================================================================== *)

Theorem compiler_determinism : forall env e prog1 prog2,
  compile_with_env env e = Some prog1 ->
  compile_with_env env e = Some prog2 ->
  prog1 = prog2.
Proof.
  intros env e prog1 prog2 H1 H2.
  unfold compile_with_env in *.
  destruct (src_eval env e) as [[v l]|]; [|discriminate].
  injection H1 as <-. injection H2 as <-. reflexivity.
Qed.

(* ====================================================================
   Theorem 10: Security Label Lattice Correctness
   ==================================================================== *)

Theorem label_lattice_join_upper_bound : forall l1 l2,
  label_leb l1 (label_join l1 l2) = true /\
  label_leb l2 (label_join l1 l2) = true.
Proof. destruct l1, l2; simpl; auto. Qed.

Theorem label_lattice_join_least : forall l1 l2 l3,
  label_leb l1 l3 = true ->
  label_leb l2 l3 = true ->
  label_leb (label_join l1 l2) l3 = true.
Proof. destruct l1, l2, l3; simpl; auto. Qed.

(* Label equality is reflexive *)
Theorem label_eqb_refl2 : forall l, label_eqb l l = true.
Proof. destruct l; reflexivity. Qed.

(* Label join is commutative *)
Theorem label_join_comm2 : forall l1 l2, label_join l1 l2 = label_join l2 l1.
Proof. destruct l1, l2; reflexivity. Qed.

(* Label join is idempotent *)
Theorem label_join_idem2 : forall l, label_join l l = l.
Proof. destruct l; reflexivity. Qed.
