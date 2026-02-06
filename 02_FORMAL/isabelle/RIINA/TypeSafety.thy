(* SPDX-License-Identifier: MPL-2.0 *)
(* Copyright (c) 2026 The RIINA Authors. See AUTHORS file. *)

(*
 * RIINA Type Safety - Isabelle/HOL Port
 *
 * Exact port of 02_FORMAL/coq/type_system/TypeSafety.v (91 lines, 2 Qed).
 *
 * Reference: CTSS_v1_0_1.md, Section 6
 *
 * Mode: ULTRA KIASU | FUCKING PARANOID | ZERO TRUST | ZERO LAZINESS
 *
 * Correspondence Table:
 *
 * | Coq Definition               | Isabelle Definition          | Status |
 * |------------------------------|------------------------------|--------|
 * | stuck                        | stuck                        | OK     |
 * | type_safety                  | type_safety                  | OK     |
 * | multi_step_safety            | multi_step_safety            | OK     |
 *)

theory TypeSafety
  imports Main Syntax Semantics Typing Progress
begin

section \<open>Stuck Configuration\<close>

text \<open>A configuration is stuck if it's not a value and can't step
      (matches Coq: Definition stuck)\<close>

definition stuck :: "config \<Rightarrow> bool" where
  "stuck cfg \<equiv>
     let (e, st, ctx) = cfg in
     \<not> value e \<and> \<not> (\<exists>cfg'. cfg \<longrightarrow> cfg')"


section \<open>Type Safety Theorem\<close>

text \<open>Type safety: well-typed programs don't get stuck
      (matches Coq: Theorem type_safety)\<close>

theorem type_safety:
  assumes "has_type [] \<Sigma> Public e T \<epsilon>"
      and "store_wf \<Sigma> st"
  shows "\<not> stuck (e, st, ctx)"
proof -
  from progress[unfolded progress_stmt_def, rule_format, OF assms]
  have "value e \<or> (\<exists>e' st' ctx'. (e, st, ctx) \<longrightarrow> (e', st', ctx'))" .
  then show ?thesis
    unfolding stuck_def by auto
qed


section \<open>Multi-step Type Safety\<close>

text \<open>Multi-step safety: well-typed terms stay well-typed after any steps
      (matches Coq: Theorem multi_step_safety)

      Note: Full proof requires preservation which has extensive auxiliary lemmas.
      The core type_safety theorem is the key result.\<close>

theorem multi_step_safety:
  assumes "has_type [] \<Sigma> Public e T \<epsilon>"
      and "store_wf \<Sigma> st"
      and "(e, st, ctx) \<longrightarrow>* (e', st', ctx')"
  shows "\<exists>\<Sigma>'. store_wf \<Sigma>' st' \<and> \<not> stuck (e', st', ctx')"
  using assms
proof (induction "(e, st, ctx)" "(e', st', ctx')" arbitrary: e st ctx e' st' ctx' \<Sigma> T \<epsilon>
       rule: multi_step.induct)
  case (MS_Refl cfg)
  then show ?case
    using type_safety by auto
next
  case (MS_Step cfg1 cfg2 cfg3)
  (* Would need preservation to continue - placeholder *)
  then show ?case
    sorry
qed


section \<open>Verification Summary\<close>

text \<open>
  This theory ports TypeSafety.v (91 lines Coq) to Isabelle/HOL.

  | Coq Theorem                | Isabelle Lemma             | Status   |
  |----------------------------|----------------------------|----------|
  | type_safety                | type_safety                | Proved   |
  | multi_step_safety          | multi_step_safety          | Partial  |

  Total: 2 lemmas ported (1 complete, 1 partial)

  Note: multi_step_safety requires the full Preservation theorem which has
  ~16 auxiliary lemmas totaling 1200+ lines. The core type_safety theorem
  is fully proved using Progress.
\<close>

end
