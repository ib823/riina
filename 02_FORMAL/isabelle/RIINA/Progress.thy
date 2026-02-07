(* Copyright (c) 2026 The RIINA Authors. All rights reserved. *)

(*
 * RIINA Progress Theorem - Isabelle/HOL Port
 *
 * Exact port of 02_FORMAL/coq/type_system/Progress.v (284 lines, ~10 Qed).
 *
 * Reference: CTSS_v1_0_1.md, Section 6
 *
 * Mode: Comprehensive Verification | Zero Trust
 *
 * Correspondence Table:
 *
 * | Coq Definition               | Isabelle Definition          | Status |
 * |------------------------------|------------------------------|--------|
 * | progress_stmt                | progress_stmt                | OK     |
 * | canonical_bool               | canonical_bool               | OK     |
 * | canonical_fn                 | canonical_fn                 | OK     |
 * | canonical_pair               | canonical_pair               | OK     |
 * | canonical_sum                | canonical_sum                | OK     |
 * | canonical_ref                | canonical_ref                | OK     |
 * | canonical_secret             | canonical_secret             | OK     |
 * | canonical_proof              | canonical_proof              | OK     |
 * | lookup_nil_contra            | lookup_nil_contra            | OK     |
 * | progress                     | progress                     | OK     |
 *)

theory Progress
  imports Main Syntax Semantics Typing
begin

section \<open>Progress Statement\<close>

text \<open>Progress statement: well-typed closed expressions are values or can step
      (matches Coq: Definition progress_stmt)\<close>

definition progress_stmt :: bool where
  "progress_stmt \<equiv>
     \<forall>e T \<epsilon> st ctx \<Sigma>.
       has_type [] \<Sigma> Public e T \<epsilon> \<longrightarrow>
       store_wf \<Sigma> st \<longrightarrow>
       value e \<or> (\<exists>e' st' ctx'. (e, st, ctx) \<longrightarrow> (e', st', ctx'))"


section \<open>Canonical Forms (Closed Context Variants)\<close>

text \<open>Canonical form for bool (matches Coq: canonical_bool)\<close>

lemma canonical_bool:
  assumes "has_type [] \<Sigma> Public v TBool \<epsilon>"
      and "value v"
  shows "\<exists>b. v = EBool b"
  using assms by (cases v rule: value.cases; auto elim: has_type.cases)

text \<open>Canonical form for function (matches Coq: canonical_fn)\<close>

lemma canonical_fn:
  assumes "has_type [] \<Sigma> Public v (TFn T1 T2 \<epsilon>) \<epsilon>'"
      and "value v"
  shows "\<exists>x body. v = ELam x T1 body"
  using assms by (cases v rule: value.cases; auto elim: has_type.cases)

text \<open>Canonical form for pair (matches Coq: canonical_pair)\<close>

lemma canonical_pair:
  assumes "has_type [] \<Sigma> Public v (TProd T1 T2) \<epsilon>"
      and "value v"
  shows "\<exists>v1 v2. v = EPair v1 v2 \<and> value v1 \<and> value v2"
  using assms
proof (cases v rule: value.cases)
  case (VPair v1 v2)
  then show ?thesis using assms by (auto elim: has_type.cases)
qed (auto elim: has_type.cases)

text \<open>Canonical form for sum (matches Coq: canonical_sum)\<close>

lemma canonical_sum:
  assumes "has_type [] \<Sigma> Public v (TSum T1 T2) \<epsilon>"
      and "value v"
  shows "(\<exists>v'. v = EInl v' T2 \<and> value v') \<or> (\<exists>v'. v = EInr v' T1 \<and> value v')"
  using assms
proof (cases v rule: value.cases)
  case (VInl v0 T)
  then show ?thesis using assms by (auto elim: has_type.cases)
next
  case (VInr v0 T)
  then show ?thesis using assms by (auto elim: has_type.cases)
qed (auto elim: has_type.cases)

text \<open>Canonical form for reference (matches Coq: canonical_ref)\<close>

lemma canonical_ref:
  assumes "has_type [] \<Sigma> Public v (TRef T l) \<epsilon>"
      and "value v"
  shows "\<exists>l'. v = ELoc l'"
  using assms by (cases v rule: value.cases; auto elim: has_type.cases)

text \<open>Canonical form for secret (matches Coq: canonical_secret)\<close>

lemma canonical_secret:
  assumes "has_type [] \<Sigma> Public v (TSecret T) \<epsilon>"
      and "value v"
  shows "\<exists>v'. v = EClassify v' \<and> value v'"
  using assms
proof (cases v rule: value.cases)
  case (VClassify v0)
  then show ?thesis using assms by (auto elim: has_type.cases)
qed (auto elim: has_type.cases)

text \<open>Canonical form for proof (matches Coq: canonical_proof)\<close>

lemma canonical_proof:
  assumes "has_type [] \<Sigma> Public v (TProof T) \<epsilon>"
      and "value v"
  shows "\<exists>v'. v = EProve v' \<and> value v'"
  using assms
proof (cases v rule: value.cases)
  case (VProve v0)
  then show ?thesis using assms by (auto elim: has_type.cases)
qed (auto elim: has_type.cases)

text \<open>Lookup in nil gives None (matches Coq: lookup_nil_contra)\<close>

lemma lookup_nil_contra:
  assumes "env_lookup x [] = Some T"
  shows "False"
  using assms by simp


section \<open>Progress Theorem\<close>

text \<open>Progress: well-typed closed expression is value or can step
      (matches Coq: Theorem progress)\<close>

theorem progress: "progress_stmt"
  unfolding progress_stmt_def
proof (intro allI impI)
  fix e T \<epsilon> st ctx \<Sigma>
  assume Hty: "has_type [] \<Sigma> Public e T \<epsilon>"
     and Hwf: "store_wf \<Sigma> st"
  show "value e \<or> (\<exists>e' st' ctx'. (e, st, ctx) \<longrightarrow> (e', st', ctx'))"
    using Hty Hwf
  proof (induction "[] :: type_env" \<Sigma> Public e T \<epsilon> arbitrary: st ctx rule: has_type.induct)
    case (T_Unit \<Sigma> \<Delta>)
    then show ?case by (auto intro: value.VUnit)
  next
    case (T_Bool \<Sigma> \<Delta> b)
    then show ?case by (auto intro: value.VBool)
  next
    case (T_Int \<Sigma> \<Delta> n)
    then show ?case by (auto intro: value.VInt)
  next
    case (T_String \<Sigma> \<Delta> s)
    then show ?case by (auto intro: value.VString)
  next
    case (T_Loc l \<Sigma> T sl \<Delta>)
    then show ?case by (auto intro: value.VLoc)
  next
    case (T_Var x T \<Sigma> \<Delta>)
    (* Variable in empty context: contradiction *)
    then show ?case by simp
  next
    case (T_Lam x T1 T2 e \<epsilon> \<Sigma> \<Delta>)
    then show ?case by (auto intro: value.VLam)
  next
    case (T_App \<Sigma> \<Delta> e1 T1 T2 \<epsilon> \<epsilon>1 e2 \<epsilon>2)
    from T_App.prems obtain Hwf: "store_wf \<Sigma> st" by simp
    show ?case
    proof (cases "value e1")
      case hv1: True
      show ?thesis
      proof (cases "value e2")
        case hv2: True
        (* Both values: can beta reduce *)
        from canonical_fn[OF T_App.hyps(1) hv1]
        obtain x body where heq: "e1 = ELam x T1 body" by auto
        show ?thesis
          using heq hv2 by (auto intro: step.ST_AppAbs)
      next
        case False
        (* e2 steps *)
        from T_App.IH(2)[OF _ Hwf] False
        obtain e2' st2' ctx2' where "(e2, st, ctx) \<longrightarrow> (e2', st2', ctx2')" by auto
        then show ?thesis using hv1 by (auto intro: step.ST_App2)
      qed
    next
      case False
      (* e1 steps *)
      from T_App.IH(1)[OF _ Hwf] False
      obtain e1' st1' ctx1' where "(e1, st, ctx) \<longrightarrow> (e1', st1', ctx1')" by auto
      then show ?thesis by (auto intro: step.ST_App1)
    qed
  next
    case (T_Pair \<Sigma> \<Delta> e1 T1 \<epsilon>1 e2 T2 \<epsilon>2)
    from T_Pair.prems obtain Hwf: "store_wf \<Sigma> st" by simp
    show ?case
    proof (cases "value e1")
      case hv1: True
      show ?thesis
      proof (cases "value e2")
        case hv2: True
        then show ?thesis using hv1 by (auto intro: value.VPair)
      next
        case False
        from T_Pair.IH(2)[OF _ Hwf] False
        obtain e2' st2' ctx2' where "(e2, st, ctx) \<longrightarrow> (e2', st2', ctx2')" by auto
        then show ?thesis using hv1 by (auto intro: step.ST_Pair2)
      qed
    next
      case False
      from T_Pair.IH(1)[OF _ Hwf] False
      obtain e1' st1' ctx1' where "(e1, st, ctx) \<longrightarrow> (e1', st1', ctx1')" by auto
      then show ?thesis by (auto intro: step.ST_Pair1)
    qed
  next
    case (T_Fst \<Sigma> \<Delta> e T1 T2 \<epsilon>)
    from T_Fst.prems obtain Hwf: "store_wf \<Sigma> st" by simp
    show ?case
    proof (cases "value e")
      case hv: True
      from canonical_pair[OF T_Fst.hyps hv]
      obtain v1 v2 where heq: "e = EPair v1 v2" "value v1" "value v2" by auto
      then show ?thesis by (auto intro: step.ST_Fst)
    next
      case False
      from T_Fst.IH[OF _ Hwf] False
      obtain e' st' ctx' where "(e, st, ctx) \<longrightarrow> (e', st', ctx')" by auto
      then show ?thesis by (auto intro: step.ST_FstStep)
    qed
  next
    case (T_Snd \<Sigma> \<Delta> e T1 T2 \<epsilon>)
    from T_Snd.prems obtain Hwf: "store_wf \<Sigma> st" by simp
    show ?case
    proof (cases "value e")
      case hv: True
      from canonical_pair[OF T_Snd.hyps hv]
      obtain v1 v2 where heq: "e = EPair v1 v2" "value v1" "value v2" by auto
      then show ?thesis by (auto intro: step.ST_Snd)
    next
      case False
      from T_Snd.IH[OF _ Hwf] False
      obtain e' st' ctx' where "(e, st, ctx) \<longrightarrow> (e', st', ctx')" by auto
      then show ?thesis by (auto intro: step.ST_SndStep)
    qed
  next
    case (T_Inl \<Sigma> \<Delta> e T1 \<epsilon> T2)
    from T_Inl.prems obtain Hwf: "store_wf \<Sigma> st" by simp
    show ?case
    proof (cases "value e")
      case True
      then show ?thesis by (auto intro: value.VInl)
    next
      case False
      from T_Inl.IH[OF _ Hwf] False
      obtain e' st' ctx' where "(e, st, ctx) \<longrightarrow> (e', st', ctx')" by auto
      then show ?thesis by (auto intro: step.ST_InlStep)
    qed
  next
    case (T_Inr \<Sigma> \<Delta> e T2 \<epsilon> T1)
    from T_Inr.prems obtain Hwf: "store_wf \<Sigma> st" by simp
    show ?case
    proof (cases "value e")
      case True
      then show ?thesis by (auto intro: value.VInr)
    next
      case False
      from T_Inr.IH[OF _ Hwf] False
      obtain e' st' ctx' where "(e, st, ctx) \<longrightarrow> (e', st', ctx')" by auto
      then show ?thesis by (auto intro: step.ST_InrStep)
    qed
  next
    case (T_Case \<Sigma> \<Delta> e T1 T2 \<epsilon> x1 e1 T \<epsilon>1 x2 e2 \<epsilon>2)
    from T_Case.prems obtain Hwf: "store_wf \<Sigma> st" by simp
    show ?case
    proof (cases "value e")
      case hv: True
      from canonical_sum[OF T_Case.hyps(1) hv]
      show ?thesis
      proof
        assume "\<exists>v'. e = EInl v' T2 \<and> value v'"
        then obtain v' where heq: "e = EInl v' T2" "value v'" by auto
        then show ?thesis by (auto intro: step.ST_CaseInl)
      next
        assume "\<exists>v'. e = EInr v' T1 \<and> value v'"
        then obtain v' where heq: "e = EInr v' T1" "value v'" by auto
        then show ?thesis by (auto intro: step.ST_CaseInr)
      qed
    next
      case False
      from T_Case.IH(1)[OF _ Hwf] False
      obtain e' st' ctx' where "(e, st, ctx) \<longrightarrow> (e', st', ctx')" by auto
      then show ?thesis by (auto intro: step.ST_CaseStep)
    qed
  next
    case (T_If \<Sigma> \<Delta> e1 \<epsilon>1 e2 T \<epsilon>2 e3 \<epsilon>3)
    from T_If.prems obtain Hwf: "store_wf \<Sigma> st" by simp
    show ?case
    proof (cases "value e1")
      case hv: True
      from canonical_bool[OF T_If.hyps(1) hv]
      obtain b where heq: "e1 = EBool b" by auto
      show ?thesis
      proof (cases b)
        case True
        then show ?thesis using heq by (auto intro: step.ST_IfTrue)
      next
        case False
        then show ?thesis using heq by (auto intro: step.ST_IfFalse)
      qed
    next
      case False
      from T_If.IH(1)[OF _ Hwf] False
      obtain e1' st' ctx' where "(e1, st, ctx) \<longrightarrow> (e1', st', ctx')" by auto
      then show ?thesis by (auto intro: step.ST_IfStep)
    qed
  next
    case (T_Let \<Sigma> \<Delta> e1 T1 \<epsilon>1 x e2 T2 \<epsilon>2)
    from T_Let.prems obtain Hwf: "store_wf \<Sigma> st" by simp
    show ?case
    proof (cases "value e1")
      case True
      then show ?thesis by (auto intro: step.ST_LetValue)
    next
      case False
      from T_Let.IH(1)[OF _ Hwf] False
      obtain e1' st' ctx' where "(e1, st, ctx) \<longrightarrow> (e1', st', ctx')" by auto
      then show ?thesis by (auto intro: step.ST_LetStep)
    qed
  next
    case (T_Perform \<Sigma> \<Delta> e T \<epsilon> eff)
    from T_Perform.prems obtain Hwf: "store_wf \<Sigma> st" by simp
    show ?case
    proof (cases "value e")
      case True
      then show ?thesis by (auto intro: step.ST_PerformValue)
    next
      case False
      from T_Perform.IH[OF _ Hwf] False
      obtain e' st' ctx' where "(e, st, ctx) \<longrightarrow> (e', st', ctx')" by auto
      then show ?thesis by (auto intro: step.ST_PerformStep)
    qed
  next
    case (T_Handle \<Sigma> \<Delta> e T1 \<epsilon>1 x h T2 \<epsilon>2)
    from T_Handle.prems obtain Hwf: "store_wf \<Sigma> st" by simp
    show ?case
    proof (cases "value e")
      case True
      then show ?thesis by (auto intro: step.ST_HandleValue)
    next
      case False
      from T_Handle.IH(1)[OF _ Hwf] False
      obtain e' st' ctx' where "(e, st, ctx) \<longrightarrow> (e', st', ctx')" by auto
      then show ?thesis by (auto intro: step.ST_HandleStep)
    qed
  next
    case (T_Ref \<Sigma> \<Delta> e T \<epsilon> l)
    from T_Ref.prems obtain Hwf: "store_wf \<Sigma> st" by simp
    show ?case
    proof (cases "value e")
      case True
      then show ?thesis
        by (auto intro: step.ST_RefValue[where l = "fresh_loc st"])
    next
      case False
      from T_Ref.IH[OF _ Hwf] False
      obtain e' st' ctx' where "(e, st, ctx) \<longrightarrow> (e', st', ctx')" by auto
      then show ?thesis by (auto intro: step.ST_RefStep)
    qed
  next
    case (T_Deref \<Sigma> \<Delta> e T l \<epsilon>)
    from T_Deref.prems obtain Hwf: "store_wf \<Sigma> st" by simp
    show ?case
    proof (cases "value e")
      case hv: True
      from canonical_ref[OF T_Deref.hyps hv]
      obtain l' where heq: "e = ELoc l'" by auto
      from T_Deref.hyps heq have "has_type [] \<Sigma> Public (ELoc l') (TRef T l) \<epsilon>" by simp
      then obtain Tl sl where Hlook: "store_ty_lookup l' \<Sigma> = Some (Tl, sl)"
        by (auto elim: has_type.cases)
      from Hwf[unfolded store_wf_def] Hlook
      obtain v where Hst: "store_lookup l' st = Some v" by auto
      then show ?thesis using heq by (auto intro: step.ST_DerefLoc)
    next
      case False
      from T_Deref.IH[OF _ Hwf] False
      obtain e' st' ctx' where "(e, st, ctx) \<longrightarrow> (e', st', ctx')" by auto
      then show ?thesis by (auto intro: step.ST_DerefStep)
    qed
  next
    case (T_Assign \<Sigma> \<Delta> e1 T l \<epsilon>1 e2 \<epsilon>2)
    from T_Assign.prems obtain Hwf: "store_wf \<Sigma> st" by simp
    show ?case
    proof (cases "value e1")
      case hv1: True
      from canonical_ref[OF T_Assign.hyps(1) hv1]
      obtain l' where heq: "e1 = ELoc l'" by auto
      from T_Assign.hyps(1) heq have "has_type [] \<Sigma> Public (ELoc l') (TRef T l) \<epsilon>1" by simp
      then obtain Tl sl where Hlook: "store_ty_lookup l' \<Sigma> = Some (Tl, sl)"
        by (auto elim: has_type.cases)
      from Hwf[unfolded store_wf_def] Hlook
      obtain v1 where Hst: "store_lookup l' st = Some v1" by auto
      show ?thesis
      proof (cases "value e2")
        case hv2: True
        then show ?thesis using heq Hst by (auto intro: step.ST_AssignLoc)
      next
        case False
        from T_Assign.IH(2)[OF _ Hwf] False
        obtain e2' st' ctx' where "(e2, st, ctx) \<longrightarrow> (e2', st', ctx')" by auto
        then show ?thesis using heq by (auto intro: step.ST_Assign2 value.VLoc)
      qed
    next
      case False
      from T_Assign.IH(1)[OF _ Hwf] False
      obtain e1' st' ctx' where "(e1, st, ctx) \<longrightarrow> (e1', st', ctx')" by auto
      then show ?thesis by (auto intro: step.ST_Assign1)
    qed
  next
    case (T_Classify \<Sigma> \<Delta> e T \<epsilon>)
    from T_Classify.prems obtain Hwf: "store_wf \<Sigma> st" by simp
    show ?case
    proof (cases "value e")
      case True
      then show ?thesis by (auto intro: value.VClassify)
    next
      case False
      from T_Classify.IH[OF _ Hwf] False
      obtain e' st' ctx' where "(e, st, ctx) \<longrightarrow> (e', st', ctx')" by auto
      then show ?thesis by (auto intro: step.ST_ClassifyStep)
    qed
  next
    case (T_Declassify \<Sigma> \<Delta> e1 T \<epsilon>1 e2 \<epsilon>2 ok)
    from T_Declassify.prems obtain Hwf: "store_wf \<Sigma> st" by simp
    show ?case
    proof (cases "value e1")
      case hv1: True
      from canonical_secret[OF T_Declassify.hyps(1) hv1]
      obtain v1 where heq1: "e1 = EClassify v1" "value v1" by auto
      show ?thesis
      proof (cases "value e2")
        case hv2: True
        from T_Declassify.hyps(3) heq1(1)
        obtain v0 where hok: "declass_ok (EClassify v1) e2" by simp
        then obtain v' where hok': "value v'" "EClassify v1 = EClassify v'" "e2 = EProve (EClassify v')"
          unfolding declass_ok_def by auto
        then show ?thesis using heq1 hok by (auto intro: step.ST_DeclassifyValue)
      next
        case False
        from T_Declassify.IH(2)[OF _ Hwf] False
        obtain e2' st' ctx' where "(e2, st, ctx) \<longrightarrow> (e2', st', ctx')" by auto
        then show ?thesis using heq1 by (auto intro: step.ST_Declassify2 value.VClassify)
      qed
    next
      case False
      from T_Declassify.IH(1)[OF _ Hwf] False
      obtain e1' st' ctx' where "(e1, st, ctx) \<longrightarrow> (e1', st', ctx')" by auto
      then show ?thesis by (auto intro: step.ST_Declassify1)
    qed
  next
    case (T_Prove \<Sigma> \<Delta> e T \<epsilon>)
    from T_Prove.prems obtain Hwf: "store_wf \<Sigma> st" by simp
    show ?case
    proof (cases "value e")
      case True
      then show ?thesis by (auto intro: value.VProve)
    next
      case False
      from T_Prove.IH[OF _ Hwf] False
      obtain e' st' ctx' where "(e, st, ctx) \<longrightarrow> (e', st', ctx')" by auto
      then show ?thesis by (auto intro: step.ST_ProveStep)
    qed
  next
    case (T_Require \<Sigma> \<Delta> e T \<epsilon> eff)
    from T_Require.prems obtain Hwf: "store_wf \<Sigma> st" by simp
    show ?case
    proof (cases "value e")
      case True
      then show ?thesis by (auto intro: step.ST_RequireValue)
    next
      case False
      from T_Require.IH[OF _ Hwf] False
      obtain e' st' ctx' where "(e, st, ctx) \<longrightarrow> (e', st', ctx')" by auto
      then show ?thesis by (auto intro: step.ST_RequireStep)
    qed
  next
    case (T_Grant \<Sigma> \<Delta> e T \<epsilon> eff)
    from T_Grant.prems obtain Hwf: "store_wf \<Sigma> st" by simp
    show ?case
    proof (cases "value e")
      case True
      then show ?thesis by (auto intro: step.ST_GrantValue)
    next
      case False
      from T_Grant.IH[OF _ Hwf] False
      obtain e' st' ctx' where "(e, st, ctx) \<longrightarrow> (e', st', ctx')" by auto
      then show ?thesis by (auto intro: step.ST_GrantStep)
    qed
  qed
qed


section \<open>Verification Summary\<close>

text \<open>
  This theory ports Progress.v (284 lines Coq) to Isabelle/HOL.

  | Coq Theorem                | Isabelle Lemma             | Status   |
  |----------------------------|----------------------------|----------|
  | canonical_bool             | canonical_bool             | Proved   |
  | canonical_fn               | canonical_fn               | Proved   |
  | canonical_pair             | canonical_pair             | Proved   |
  | canonical_sum              | canonical_sum              | Proved   |
  | canonical_ref              | canonical_ref              | Proved   |
  | canonical_secret           | canonical_secret           | Proved   |
  | canonical_proof            | canonical_proof            | Proved   |
  | lookup_nil_contra          | lookup_nil_contra          | Proved   |
  | progress                   | progress                   | Proved   |

  Total: 9 lemmas ported
\<close>

end
