(* Copyright (c) 2026 The RIINA Authors. All rights reserved. *)

(*
 * RIINA Effect System - Isabelle/HOL Port
 *
 * Exact port of 02_FORMAL/coq/effects/EffectSystem.v (325 lines, 5 Qed).
 *
 * Reference: CTSS_v1_0_1.md, Section 5 (Effects)
 *
 * Mode: ULTRA KIASU | FUCKING PARANOID | ZERO TRUST | ZERO LAZINESS
 *
 * Correspondence Table:
 *
 * | Coq Definition           | Isabelle Definition       | Status |
 * |--------------------------|---------------------------|--------|
 * | performs_within          | performs_within           | OK     |
 * | performs_within_mono     | performs_within_mono      | OK     |
 * | effect_leq_join_ub_l_trans | effect_leq_join_ub_l_trans | OK  |
 * | effect_leq_join_ub_r_trans | effect_leq_join_ub_r_trans | OK  |
 * | core_effects_within      | core_effects_within       | Stated |
 * | has_type_full            | has_type_full             | OK     |
 * | effect_safety            | effect_safety             | OK     |
 *)

theory EffectSystem
  imports Syntax Semantics Typing EffectAlgebra
begin

section \<open>Effect Occurrence Predicate\<close>

text \<open>
  The performs_within predicate tracks whether an expression's effects
  are bounded by a given effect level.
\<close>

(* A configuration performs effects within the given bound
   (matches Coq: Fixpoint performs_within) *)
fun performs_within :: "expr \<Rightarrow> effect \<Rightarrow> bool" where
  "performs_within EUnit _ = True"
| "performs_within (EBool _) _ = True"
| "performs_within (EInt _) _ = True"
| "performs_within (EString _) _ = True"
| "performs_within (ELoc _) _ = True"
| "performs_within (EVar _) _ = True"
| "performs_within (ELam _ _ _) _ = True"  (* Lambda body not evaluated at creation *)
| "performs_within (EApp e1 e2) eff = (performs_within e1 eff \<and> performs_within e2 eff)"
| "performs_within (EPair e1 e2) eff = (performs_within e1 eff \<and> performs_within e2 eff)"
| "performs_within (EFst e1) eff = performs_within e1 eff"
| "performs_within (ESnd e1) eff = performs_within e1 eff"
| "performs_within (EInl e1 _) eff = performs_within e1 eff"
| "performs_within (EInr e1 _) eff = performs_within e1 eff"
| "performs_within (ECase e0 _ e1 _ e2) eff =
     (performs_within e0 eff \<and> performs_within e1 eff \<and> performs_within e2 eff)"
| "performs_within (EIf e1 e2 e3) eff =
     (performs_within e1 eff \<and> performs_within e2 eff \<and> performs_within e3 eff)"
| "performs_within (ELet _ e1 e2) eff = (performs_within e1 eff \<and> performs_within e2 eff)"
| "performs_within (EPerform eff' e1) eff = (effect_leq eff' eff \<and> performs_within e1 eff)"
| "performs_within (EHandle e1 _ h) eff = (performs_within e1 eff \<and> performs_within h eff)"
| "performs_within (ERef e1 _) eff = performs_within e1 eff"
| "performs_within (EDeref e1) eff = performs_within e1 eff"
| "performs_within (EAssign e1 e2) eff = (performs_within e1 eff \<and> performs_within e2 eff)"
| "performs_within (EClassify e1) eff = performs_within e1 eff"
| "performs_within (EDeclassify e1 e2) eff = (performs_within e1 eff \<and> performs_within e2 eff)"
| "performs_within (EProve e1) eff = performs_within e1 eff"
| "performs_within (ERequire _ e1) eff = performs_within e1 eff"
| "performs_within (EGrant _ e1) eff = performs_within e1 eff"


section \<open>Monotonicity\<close>

(* performs_within is monotonic in the effect bound
   (matches Coq: Lemma performs_within_mono) *)
lemma performs_within_mono:
  assumes "effect_leq eff1 eff2" and "performs_within e eff1"
  shows "performs_within e eff2"
using assms
proof (induction e)
  case EUnit thus ?case by simp
next
  case (EBool _) thus ?case by simp
next
  case (EInt _) thus ?case by simp
next
  case (EString _) thus ?case by simp
next
  case (ELoc _) thus ?case by simp
next
  case (EVar _) thus ?case by simp
next
  case (ELam _ _ _) thus ?case by simp
next
  case (EApp e1 e2)
  thus ?case by auto
next
  case (EPair e1 e2)
  thus ?case by auto
next
  case (EFst e1)
  thus ?case by simp
next
  case (ESnd e1)
  thus ?case by simp
next
  case (EInl e1 _)
  thus ?case by simp
next
  case (EInr e1 _)
  thus ?case by simp
next
  case (ECase e0 x1 e1 x2 e2)
  thus ?case by auto
next
  case (EIf e1 e2 e3)
  thus ?case by auto
next
  case (ELet x e1 e2)
  thus ?case by auto
next
  case (EPerform eff' e1)
  then have "effect_leq eff' eff1" and "performs_within e1 eff1" by auto
  hence "effect_leq eff' eff2" using \<open>effect_leq eff1 eff2\<close>
    by (rule effect_leq_trans)
  moreover have "performs_within e1 eff2"
    using EPerform by auto
  ultimately show ?case by simp
next
  case (EHandle e1 _ h)
  thus ?case by auto
next
  case (ERef e1 _)
  thus ?case by simp
next
  case (EDeref e1)
  thus ?case by simp
next
  case (EAssign e1 e2)
  thus ?case by auto
next
  case (EClassify e1)
  thus ?case by simp
next
  case (EDeclassify e1 e2)
  thus ?case by auto
next
  case (EProve e1)
  thus ?case by simp
next
  case (ERequire _ e1)
  thus ?case by simp
next
  case (EGrant _ e1)
  thus ?case by simp
qed


section \<open>Helper Lemmas for Join Upper Bounds\<close>

(* Helper: e1 \<le> join e2 (join e1 e3)
   (matches Coq: Lemma effect_leq_join_ub_l_trans) *)
lemma effect_leq_join_ub_l_trans:
  "effect_leq e1 (effect_join e2 (effect_join e1 e3))"
proof -
  have "effect_leq e1 (effect_join e1 e3)" by (rule effect_join_ub_l)
  moreover have "effect_leq (effect_join e1 e3) (effect_join e2 (effect_join e1 e3))"
    by (rule effect_join_ub_r)
  ultimately show ?thesis by (rule effect_leq_trans)
qed

(* Helper: e3 \<le> join e2 (join e1 e3)
   (matches Coq: Lemma effect_leq_join_ub_r_trans) *)
lemma effect_leq_join_ub_r_trans:
  "effect_leq e3 (effect_join e2 (effect_join e1 e3))"
proof -
  have "effect_leq e3 (effect_join e1 e3)" by (rule effect_join_ub_r)
  moreover have "effect_leq (effect_join e1 e3) (effect_join e2 (effect_join e1 e3))"
    by (rule effect_join_ub_r)
  ultimately show ?thesis by (rule effect_leq_trans)
qed


section \<open>Core Effects Within\<close>

text \<open>
  Note: Full proof requires induction on has_type with 28 cases.
  The theorem is stated here and can be filled in when needed.
\<close>

(* Well-typed expressions perform effects within their declared effect bound
   (matches Coq: Lemma core_effects_within) *)
theorem core_effects_within:
  assumes "has_type G S D e T eff"
  shows "performs_within e eff"
  using assms
proof (induction rule: has_type.induct)
  (* === Category A: Trivially true (performs_within returns True for values/vars) === *)
  case (T_Unit \<Gamma> \<Sigma> \<Delta>) thus ?case by simp
next
  case (T_Bool \<Gamma> \<Sigma> \<Delta> b) thus ?case by simp
next
  case (T_Int \<Gamma> \<Sigma> \<Delta> n) thus ?case by simp
next
  case (T_String \<Gamma> \<Sigma> \<Delta> s) thus ?case by simp
next
  case (T_Loc l \<Sigma> T sl \<Gamma> \<Delta>) thus ?case by simp
next
  case (T_Var x \<Gamma> T \<Sigma> \<Delta>) thus ?case by simp
next
  case (T_Lam x T1 \<Gamma> \<Sigma> \<Delta> e T2 \<epsilon>) thus ?case by simp
next
  (* === Category B: Single subexpression, same effect === *)
  case (T_Fst \<Gamma> \<Sigma> \<Delta> e T1 T2 \<epsilon>)
  thus ?case by simp
next
  case (T_Snd \<Gamma> \<Sigma> \<Delta> e T1 T2 \<epsilon>)
  thus ?case by simp
next
  case (T_Inl \<Gamma> \<Sigma> \<Delta> e T1 \<epsilon> T2)
  thus ?case by simp
next
  case (T_Inr \<Gamma> \<Sigma> \<Delta> e T2 \<epsilon> T1)
  thus ?case by simp
next
  case (T_Ref \<Gamma> \<Sigma> \<Delta> e T \<epsilon> l)
  thus ?case by simp
next
  case (T_Deref \<Gamma> \<Sigma> \<Delta> e T l \<epsilon>)
  thus ?case by simp
next
  case (T_Classify \<Gamma> \<Sigma> \<Delta> e T \<epsilon>)
  thus ?case by simp
next
  case (T_Prove \<Gamma> \<Sigma> \<Delta> e T \<epsilon>)
  thus ?case by simp
next
  case (T_Require \<Gamma> \<Sigma> \<Delta> e T \<epsilon> eff)
  thus ?case by simp
next
  case (T_Grant \<Gamma> \<Sigma> \<Delta> e T \<epsilon> eff)
  thus ?case by simp
next
  (* === Category C: Two subexpressions joined with effect_join === *)
  case (T_App \<Gamma> \<Sigma> \<Delta> e1 T1 T2 \<epsilon>_fn \<epsilon>1 e2 \<epsilon>2)
  (* IH: pw(e1, \<epsilon>1) and pw(e2, \<epsilon>2) *)
  (* Need: pw(e1, join(\<epsilon>1, \<epsilon>2)) and pw(e2, join(\<epsilon>1, \<epsilon>2)) *)
  have "performs_within e1 (effect_join \<epsilon>1 \<epsilon>2)"
    using T_App.IH(1) performs_within_mono effect_join_ub_l by blast
  moreover have "performs_within e2 (effect_join \<epsilon>1 \<epsilon>2)"
    using T_App.IH(2) performs_within_mono effect_join_ub_r by blast
  ultimately show ?case by simp
next
  case (T_Pair \<Gamma> \<Sigma> \<Delta> e1 T1 \<epsilon>1 e2 T2 \<epsilon>2)
  have "performs_within e1 (effect_join \<epsilon>1 \<epsilon>2)"
    using T_Pair.IH(1) performs_within_mono effect_join_ub_l by blast
  moreover have "performs_within e2 (effect_join \<epsilon>1 \<epsilon>2)"
    using T_Pair.IH(2) performs_within_mono effect_join_ub_r by blast
  ultimately show ?case by simp
next
  case (T_Let \<Gamma> \<Sigma> \<Delta> e1 T1 \<epsilon>1 x e2 T2 \<epsilon>2)
  have "performs_within e1 (effect_join \<epsilon>1 \<epsilon>2)"
    using T_Let.IH(1) performs_within_mono effect_join_ub_l by blast
  moreover have "performs_within e2 (effect_join \<epsilon>1 \<epsilon>2)"
    using T_Let.IH(2) performs_within_mono effect_join_ub_r by blast
  ultimately show ?case by simp
next
  case (T_Handle \<Gamma> \<Sigma> \<Delta> e T1 \<epsilon>1 x h T2 \<epsilon>2)
  have "performs_within e (effect_join \<epsilon>1 \<epsilon>2)"
    using T_Handle.IH(1) performs_within_mono effect_join_ub_l by blast
  moreover have "performs_within h (effect_join \<epsilon>1 \<epsilon>2)"
    using T_Handle.IH(2) performs_within_mono effect_join_ub_r by blast
  ultimately show ?case by simp
next
  case (T_Assign \<Gamma> \<Sigma> \<Delta> e1 T l \<epsilon>1 e2 \<epsilon>2)
  have "performs_within e1 (effect_join \<epsilon>1 \<epsilon>2)"
    using T_Assign.IH(1) performs_within_mono effect_join_ub_l by blast
  moreover have "performs_within e2 (effect_join \<epsilon>1 \<epsilon>2)"
    using T_Assign.IH(2) performs_within_mono effect_join_ub_r by blast
  ultimately show ?case by simp
next
  case (T_Declassify \<Gamma> \<Sigma> \<Delta> e1 T \<epsilon>1 e2 \<epsilon>2 ok)
  have "performs_within e1 (effect_join \<epsilon>1 \<epsilon>2)"
    using T_Declassify.IH(1) performs_within_mono effect_join_ub_l by blast
  moreover have "performs_within e2 (effect_join \<epsilon>1 \<epsilon>2)"
    using T_Declassify.IH(2) performs_within_mono effect_join_ub_r by blast
  ultimately show ?case by simp
next
  (* === Category D: Perform — effect_leq check + subexpression === *)
  case (T_Perform \<Gamma> \<Sigma> \<Delta> e T \<epsilon> eff)
  (* performs_within (EPerform eff e) (effect_join \<epsilon> eff) =
     effect_leq eff (effect_join \<epsilon> eff) \<and> performs_within e (effect_join \<epsilon> eff) *)
  have "effect_leq eff (effect_join \<epsilon> eff)" by (rule effect_join_ub_r)
  moreover have "performs_within e (effect_join \<epsilon> eff)"
    using T_Perform.IH performs_within_mono effect_join_ub_l by blast
  ultimately show ?case by simp
next
  (* === Category E: Three subexpressions with nested join === *)
  case (T_Case \<Gamma> \<Sigma> \<Delta> e T1 T2 \<epsilon> x1 e1 T \<epsilon>1 x2 e2 \<epsilon>2)
  (* Effect is effect_join \<epsilon> (effect_join \<epsilon>1 \<epsilon>2) *)
  have pw0: "performs_within e (effect_join \<epsilon> (effect_join \<epsilon>1 \<epsilon>2))"
    using T_Case.IH(1) performs_within_mono effect_join_ub_l by blast
  have pw1: "performs_within e1 (effect_join \<epsilon> (effect_join \<epsilon>1 \<epsilon>2))"
    using T_Case.IH(2) performs_within_mono effect_leq_join_ub_l_trans by blast
  have pw2: "performs_within e2 (effect_join \<epsilon> (effect_join \<epsilon>1 \<epsilon>2))"
    using T_Case.IH(3) performs_within_mono effect_leq_join_ub_r_trans by blast
  from pw0 pw1 pw2 show ?case by simp
next
  case (T_If \<Gamma> \<Sigma> \<Delta> e1 \<epsilon>1 e2 T \<epsilon>2 e3 \<epsilon>3)
  (* Effect is effect_join \<epsilon>1 (effect_join \<epsilon>2 \<epsilon>3) *)
  have pw1: "performs_within e1 (effect_join \<epsilon>1 (effect_join \<epsilon>2 \<epsilon>3))"
    using T_If.IH(1) performs_within_mono effect_join_ub_l by blast
  have pw2: "performs_within e2 (effect_join \<epsilon>1 (effect_join \<epsilon>2 \<epsilon>3))"
    using T_If.IH(2) performs_within_mono effect_leq_join_ub_l_trans by blast
  have pw3: "performs_within e3 (effect_join \<epsilon>1 (effect_join \<epsilon>2 \<epsilon>3))"
    using T_If.IH(3) performs_within_mono effect_leq_join_ub_r_trans by blast
  from pw1 pw2 pw3 show ?case by simp
qed


section \<open>Extended Typing with Full Effect Operations\<close>

(* Extended typing relation including effect operations
   (matches Coq: Inductive has_type_full) *)
inductive has_type_full ::
    "type_env \<Rightarrow> store_ty \<Rightarrow> security_level \<Rightarrow> expr \<Rightarrow> ty \<Rightarrow> effect \<Rightarrow> bool" where
  (* Core typing rules embed into full typing *)
  T_Core: "has_type G S D e T eff \<Longrightarrow> has_type_full G S D e T eff"

  (* Perform an effect operation *)
| T_Perform_Full:
    "has_type_full G S D e T eff1 \<Longrightarrow>
     has_type_full G S D (EPerform eff2 e) T (effect_join eff1 eff2)"

  (* Handle an effect *)
| T_Handle_Full:
    "\<lbrakk> has_type_full G S D e T1 eff1;
       has_type_full ((y, T1) # G) S D h T2 eff2 \<rbrakk> \<Longrightarrow>
     has_type_full G S D (EHandle e y h) T2 (effect_join eff1 eff2)"

  (* Require a capability *)
| T_Require_Full:
    "has_type_full G S D e T eff_e \<Longrightarrow>
     has_type_full G S D (ERequire eff e) T (effect_join eff eff_e)"

  (* Grant a capability *)
| T_Grant_Full:
    "has_type_full G S D e T eff_e \<Longrightarrow>
     has_type_full G S D (EGrant eff e) T eff_e"

  (* Classify a value as secret *)
| T_Classify_Full:
    "has_type_full G S D e T eff \<Longrightarrow>
     has_type_full G S D (EClassify e) (TSecret T) eff"

  (* Declassify a secret value with proof *)
| T_Declassify_Full:
    "\<lbrakk> has_type_full G S D e1 (TSecret T) eff1;
       has_type_full G S D e2 (TProof (TSecret T)) eff2;
       declass_ok e1 e2 \<rbrakk> \<Longrightarrow>
     has_type_full G S D (EDeclassify e1 e2) T (effect_join eff1 eff2)"

  (* Create a proof *)
| T_Prove_Full:
    "has_type_full G S D e T eff \<Longrightarrow>
     has_type_full G S D (EProve e) (TProof T) eff"


section \<open>Effect Safety Theorem\<close>

(* Effect Safety: Well-typed expressions perform only their declared effects
   (matches Coq: Theorem effect_safety) *)
theorem effect_safety:
  assumes "has_type_full G S D e T eff"
  shows "performs_within e eff"
using assms
proof (induction rule: has_type_full.induct)
  case (T_Core G S D e T eff)
  thus ?case by (rule core_effects_within)
next
  case (T_Perform_Full G S D e T eff1 eff2)
  have "effect_leq eff2 (effect_join eff1 eff2)" by (rule effect_join_ub_r)
  moreover have "performs_within e eff1" by fact
  hence "performs_within e (effect_join eff1 eff2)"
    using effect_join_ub_l performs_within_mono by blast
  ultimately show ?case by simp
next
  case (T_Handle_Full G S D e T1 eff1 y h T2 eff2)
  have "performs_within e eff1" by fact
  hence pe: "performs_within e (effect_join eff1 eff2)"
    using effect_join_ub_l performs_within_mono by blast
  have "performs_within h eff2" by fact
  hence ph: "performs_within h (effect_join eff1 eff2)"
    using effect_join_ub_r performs_within_mono by blast
  from pe ph show ?case by simp
next
  case (T_Require_Full G S D e T eff_e eff)
  have "performs_within e eff_e" by fact
  thus ?case using effect_join_ub_r performs_within_mono by fastforce
next
  case (T_Grant_Full G S D e T eff_e eff)
  thus ?case by simp
next
  case (T_Classify_Full G S D e T eff)
  thus ?case by simp
next
  case (T_Declassify_Full G S D e1 T eff1 e2 eff2)
  have "performs_within e1 eff1" by fact
  hence pe1: "performs_within e1 (effect_join eff1 eff2)"
    using effect_join_ub_l performs_within_mono by blast
  have "performs_within e2 eff2" by fact
  hence pe2: "performs_within e2 (effect_join eff1 eff2)"
    using effect_join_ub_r performs_within_mono by blast
  from pe1 pe2 show ?case by simp
next
  case (T_Prove_Full G S D e T eff)
  thus ?case by simp
qed


section \<open>Verification Summary\<close>

text \<open>
  This theory ports EffectSystem.v (325 lines Coq) to Isabelle/HOL.

  | Coq Lemma                    | Isabelle Lemma              | Status |
  |------------------------------|------------------------------|--------|
  | performs_within              | performs_within              | Def    |
  | performs_within_mono         | performs_within_mono         | Proved |
  | effect_leq_join_ub_l_trans   | effect_leq_join_ub_l_trans   | Proved |
  | effect_leq_join_ub_r_trans   | effect_leq_join_ub_r_trans   | Proved |
  | core_effects_within          | core_effects_within          | Proved |
  | has_type_full                | has_type_full                | Def    |
  | effect_safety                | effect_safety                | Proved |

  Total: 7 definitions/theorems ported — ALL PROVED (0 unfinished)

  core_effects_within proved by 26-case induction on has_type using
  performs_within_mono and effect_join upper bound lemmas.
\<close>

end
