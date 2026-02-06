(* SPDX-License-Identifier: MPL-2.0 *)
(* Copyright (c) 2026 The RIINA Authors. See AUTHORS file. *)

(*
 * RIINA Effect Algebra - Isabelle/HOL Port
 *
 * Exact port of 02_FORMAL/coq/effects/EffectAlgebra.v (108 lines, 8 Qed).
 *
 * Reference: CTSS_v1_0_1.md, Section 5 (Effects)
 *
 * Mode: ULTRA KIASU | FUCKING PARANOID | ZERO TRUST | ZERO LAZINESS
 *
 * Correspondence Table:
 *
 * | Coq Definition     | Isabelle Definition  | Status |
 * |--------------------|----------------------|--------|
 * | effect_leq         | effect_leq           | OK     |
 * | effect_leq_refl    | effect_leq_refl      | OK     |
 * | effect_leq_trans   | effect_leq_trans     | OK     |
 * | effect_leq_antisym | effect_leq_antisym   | OK     |
 * | effect_join_comm   | effect_join_comm     | OK     |
 * | effect_level_join  | effect_level_join    | OK     |
 * | effect_join_assoc  | effect_join_assoc    | OK     |
 * | effect_join_ub_l   | effect_join_ub_l     | OK     |
 * | effect_join_ub_r   | effect_join_ub_r     | OK     |
 * | effect_join_lub    | effect_join_lub      | OK     |
 *)

theory EffectAlgebra
  imports Syntax
begin

section \<open>Effect Ordering\<close>

text \<open>
  Effect ordering based on effect levels.
  Forms a partial order (reflexive, transitive, antisymmetric).
\<close>

(* Effect ordering based on levels (matches Coq: Definition effect_leq) *)
definition effect_leq :: "effect \<Rightarrow> effect \<Rightarrow> bool" where
  "effect_leq e1 e2 \<equiv> effect_level e1 \<le> effect_level e2"


section \<open>Partial Order Properties\<close>

(* Reflexivity of effect ordering (matches Coq: Lemma effect_leq_refl) *)
lemma effect_leq_refl: "effect_leq e e"
  unfolding effect_leq_def by simp

(* Transitivity of effect ordering (matches Coq: Lemma effect_leq_trans) *)
lemma effect_leq_trans:
  assumes "effect_leq e1 e2" and "effect_leq e2 e3"
  shows "effect_leq e1 e3"
  using assms unfolding effect_leq_def by simp

(* Helper: effect level determines effect equality *)
lemma effect_eq_of_level_eq:
  assumes "effect_level e1 = effect_level e2"
  shows "e1 = e2"
  using assms by (cases e1; cases e2) auto

(* Antisymmetry of effect ordering (matches Coq: Lemma effect_leq_antisym) *)
lemma effect_leq_antisym:
  assumes "effect_leq e1 e2" and "effect_leq e2 e1"
  shows "e1 = e2"
proof -
  have "effect_level e1 = effect_level e2"
    using assms unfolding effect_leq_def by simp
  thus ?thesis by (rule effect_eq_of_level_eq)
qed


section \<open>Join Semilattice Properties\<close>

(* Effect level of join is max of levels (matches Coq: Lemma effect_level_join) *)
lemma effect_level_join:
  "effect_level (effect_join e1 e2) = max (effect_level e1) (effect_level e2)"
  unfolding effect_join_def by auto

(* Commutativity of effect join (matches Coq: Lemma effect_join_comm) *)
lemma effect_join_comm: "effect_join e1 e2 = effect_join e2 e1"
proof (rule effect_eq_of_level_eq)
  show "effect_level (effect_join e1 e2) = effect_level (effect_join e2 e1)"
    unfolding effect_level_join by auto
qed

(* Associativity of effect join (matches Coq: Lemma effect_join_assoc) *)
lemma effect_join_assoc:
  "effect_join e1 (effect_join e2 e3) = effect_join (effect_join e1 e2) e3"
proof (rule effect_eq_of_level_eq)
  show "effect_level (effect_join e1 (effect_join e2 e3)) =
        effect_level (effect_join (effect_join e1 e2) e3)"
    unfolding effect_level_join by auto
qed

(* Left upper bound of join (matches Coq: Lemma effect_join_ub_l) *)
lemma effect_join_ub_l: "effect_leq e1 (effect_join e1 e2)"
  unfolding effect_leq_def effect_join_def by auto

(* Right upper bound of join (matches Coq: Lemma effect_join_ub_r) *)
lemma effect_join_ub_r: "effect_leq e2 (effect_join e1 e2)"
  unfolding effect_leq_def effect_join_def by auto

(* Join is least upper bound (matches Coq: Lemma effect_join_lub) *)
lemma effect_join_lub:
  assumes "effect_leq e1 e3" and "effect_leq e2 e3"
  shows "effect_leq (effect_join e1 e2) e3"
  using assms unfolding effect_leq_def effect_join_def by auto


section \<open>Additional Properties\<close>

(* Pure is bottom element (matches Coq: Lemma effect_leq_pure in EffectSystem.v) *)
lemma effect_leq_pure: "effect_leq EffPure e"
  unfolding effect_leq_def by simp

(* Effect join is idempotent *)
lemma effect_join_idem: "effect_join e e = e"
  unfolding effect_join_def by simp

(* Pure is left identity for join *)
lemma effect_join_pure_l_eq: "effect_join EffPure e = e"
  by (rule effect_join_pure_l)

(* Pure is right identity for join *)
lemma effect_join_pure_r_eq: "effect_join e EffPure = e"
  by (rule effect_join_pure_r)


section \<open>Verification Summary\<close>

text \<open>
  This theory ports EffectAlgebra.v (108 lines Coq) to Isabelle/HOL.

  | Coq Lemma           | Isabelle Lemma       | Status   |
  |---------------------|----------------------|----------|
  | effect_leq_refl     | effect_leq_refl      | Proved   |
  | effect_leq_trans    | effect_leq_trans     | Proved   |
  | effect_leq_antisym  | effect_leq_antisym   | Proved   |
  | effect_join_comm    | effect_join_comm     | Proved   |
  | effect_level_join   | effect_level_join    | Proved   |
  | effect_join_assoc   | effect_join_assoc    | Proved   |
  | effect_join_ub_l    | effect_join_ub_l     | Proved   |
  | effect_join_ub_r    | effect_join_ub_r     | Proved   |
  | effect_join_lub     | effect_join_lub      | Proved   |
  | effect_leq_pure     | effect_leq_pure      | Proved   |

  Total: 10 lemmas proved (vs 8 in Coq + 1 from EffectSystem.v + 1 extra)
\<close>

end
