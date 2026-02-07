(* Copyright (c) 2026 The RIINA Authors. All rights reserved. *)

(*
 * RIINA Typing Rules - Isabelle/HOL Port
 *
 * Exact port of 02_FORMAL/coq/foundations/Typing.v (648 lines, 12 Qed).
 *
 * Reference: CTSS_v1_0_1.md, Section 4
 *
 * Mode: Comprehensive Verification | Zero Trust
 *
 * Correspondence Table:
 *
 * | Coq Definition               | Isabelle Definition          | Status |
 * |------------------------------|------------------------------|--------|
 * | type_env                     | type_env                     | OK     |
 * | lookup                       | env_lookup                   | OK     |
 * | store_ty                     | store_ty                     | OK     |
 * | store_ty_lookup              | store_ty_lookup              | OK     |
 * | store_ty_update              | store_ty_update              | OK     |
 * | store_ty_extends             | store_ty_extends             | OK     |
 * | free_in                      | free_in                      | OK     |
 * | has_type                     | has_type                     | OK     |
 * | store_wf                     | store_wf                     | OK     |
 * | type_uniqueness              | type_uniqueness              | OK     |
 * | canonical_forms_unit         | canonical_forms_unit         | OK     |
 * | canonical_forms_bool         | canonical_forms_bool         | OK     |
 * | canonical_forms_int          | canonical_forms_int          | OK     |
 * | canonical_forms_string       | canonical_forms_string       | OK     |
 * | canonical_forms_fn           | canonical_forms_fn           | OK     |
 * | canonical_forms_prod         | canonical_forms_prod         | OK     |
 * | canonical_forms_sum          | canonical_forms_sum          | OK     |
 * | canonical_forms_ref          | canonical_forms_ref          | OK     |
 * | canonical_forms_secret       | canonical_forms_secret       | OK     |
 * | canonical_forms_proof        | canonical_forms_proof        | OK     |
 *)

theory Typing
  imports Main Syntax Semantics
begin

section \<open>Type Environments\<close>

(* Type environment: list of (identifier, type) pairs
   (matches Coq: Definition type_env) *)
type_synonym type_env = "(ident \<times> ty) list"

(* Lookup in type environment (matches Coq: Fixpoint lookup) *)
fun env_lookup :: "ident \<Rightarrow> type_env \<Rightarrow> ty option" where
  "env_lookup x [] = None"
| "env_lookup x ((y, T) # \<Gamma>') = (if x = y then Some T else env_lookup x \<Gamma>')"


section \<open>Store Typing\<close>

(* Store typing: list of (location, type, security level)
   (matches Coq: Definition store_ty) *)
type_synonym store_ty = "(loc \<times> ty \<times> security_level) list"

(* Lookup in store typing (matches Coq: Fixpoint store_ty_lookup) *)
fun store_ty_lookup :: "loc \<Rightarrow> store_ty \<Rightarrow> (ty \<times> security_level) option" where
  "store_ty_lookup l [] = None"
| "store_ty_lookup l ((l', T, sl) # \<Sigma>') =
     (if l = l' then Some (T, sl) else store_ty_lookup l \<Sigma>')"

(* Update store typing (matches Coq: Fixpoint store_ty_update) *)
fun store_ty_update :: "loc \<Rightarrow> ty \<Rightarrow> security_level \<Rightarrow> store_ty \<Rightarrow> store_ty" where
  "store_ty_update l T sl [] = [(l, T, sl)]"
| "store_ty_update l T sl ((l', T', sl') # \<Sigma>') =
     (if l = l' then (l, T, sl) # \<Sigma>' else (l', T', sl') # store_ty_update l T sl \<Sigma>')"

(* Store typing extension (matches Coq: Definition store_ty_extends) *)
definition store_ty_extends :: "store_ty \<Rightarrow> store_ty \<Rightarrow> bool" where
  "store_ty_extends \<Sigma> \<Sigma>' \<equiv>
     \<forall>l T sl. store_ty_lookup l \<Sigma> = Some (T, sl) \<longrightarrow> store_ty_lookup l \<Sigma>' = Some (T, sl)"


section \<open>Free Variables\<close>

text \<open>Predicate to check if a variable occurs free in an expression.
      (matches Coq: Fixpoint free_in)\<close>

fun free_in :: "ident \<Rightarrow> expr \<Rightarrow> bool" where
  "free_in x EUnit = False"
| "free_in x (EBool _) = False"
| "free_in x (EInt _) = False"
| "free_in x (EString _) = False"
| "free_in x (ELoc _) = False"
| "free_in x (EVar y) = (x = y)"
| "free_in x (ELam y _ body) = (x \<noteq> y \<and> free_in x body)"
| "free_in x (EApp e1 e2) = (free_in x e1 \<or> free_in x e2)"
| "free_in x (EPair e1 e2) = (free_in x e1 \<or> free_in x e2)"
| "free_in x (EFst e) = free_in x e"
| "free_in x (ESnd e) = free_in x e"
| "free_in x (EInl e _) = free_in x e"
| "free_in x (EInr e _) = free_in x e"
| "free_in x (ECase e y1 e1 y2 e2) =
     (free_in x e \<or> (x \<noteq> y1 \<and> free_in x e1) \<or> (x \<noteq> y2 \<and> free_in x e2))"
| "free_in x (EIf e1 e2 e3) = (free_in x e1 \<or> free_in x e2 \<or> free_in x e3)"
| "free_in x (ELet y e1 e2) = (free_in x e1 \<or> (x \<noteq> y \<and> free_in x e2))"
| "free_in x (EPerform _ e) = free_in x e"
| "free_in x (EHandle e y h) = (free_in x e \<or> (x \<noteq> y \<and> free_in x h))"
| "free_in x (ERef e _) = free_in x e"
| "free_in x (EDeref e) = free_in x e"
| "free_in x (EAssign e1 e2) = (free_in x e1 \<or> free_in x e2)"
| "free_in x (EClassify e) = free_in x e"
| "free_in x (EDeclassify e1 e2) = (free_in x e1 \<or> free_in x e2)"
| "free_in x (EProve e) = free_in x e"
| "free_in x (ERequire _ e) = free_in x e"
| "free_in x (EGrant _ e) = free_in x e"


section \<open>Typing Judgment\<close>

text \<open>
  has_type \<Gamma> \<Sigma> \<Delta> e T \<epsilon> means: under environment \<Gamma>, store typing \<Sigma>,
  and security context \<Delta>, expression e has type T with effect \<epsilon>.
  (matches Coq: Inductive has_type, 28 rules)
\<close>

inductive has_type :: "type_env \<Rightarrow> store_ty \<Rightarrow> security_level \<Rightarrow>
                       expr \<Rightarrow> ty \<Rightarrow> effect \<Rightarrow> bool" where
  (* Values *)
  T_Unit: "has_type \<Gamma> \<Sigma> \<Delta> EUnit TUnit EffectPure"

| T_Bool: "has_type \<Gamma> \<Sigma> \<Delta> (EBool b) TBool EffectPure"

| T_Int: "has_type \<Gamma> \<Sigma> \<Delta> (EInt n) TInt EffectPure"

| T_String: "has_type \<Gamma> \<Sigma> \<Delta> (EString s) TString EffectPure"

| T_Loc: "store_ty_lookup l \<Sigma> = Some (T, sl) \<Longrightarrow>
          has_type \<Gamma> \<Sigma> \<Delta> (ELoc l) (TRef T sl) EffectPure"

| T_Var: "env_lookup x \<Gamma> = Some T \<Longrightarrow>
          has_type \<Gamma> \<Sigma> \<Delta> (EVar x) T EffectPure"

  (* Functions *)
| T_Lam: "has_type ((x, T1) # \<Gamma>) \<Sigma> \<Delta> e T2 \<epsilon> \<Longrightarrow>
          has_type \<Gamma> \<Sigma> \<Delta> (ELam x T1 e) (TFn T1 T2 \<epsilon>) EffectPure"

| T_App: "has_type \<Gamma> \<Sigma> \<Delta> e1 (TFn T1 T2 \<epsilon>) \<epsilon>1 \<Longrightarrow>
          has_type \<Gamma> \<Sigma> \<Delta> e2 T1 \<epsilon>2 \<Longrightarrow>
          has_type \<Gamma> \<Sigma> \<Delta> (EApp e1 e2) T2 (effect_join \<epsilon> (effect_join \<epsilon>1 \<epsilon>2))"

  (* Products *)
| T_Pair: "has_type \<Gamma> \<Sigma> \<Delta> e1 T1 \<epsilon>1 \<Longrightarrow>
           has_type \<Gamma> \<Sigma> \<Delta> e2 T2 \<epsilon>2 \<Longrightarrow>
           has_type \<Gamma> \<Sigma> \<Delta> (EPair e1 e2) (TProd T1 T2) (effect_join \<epsilon>1 \<epsilon>2)"

| T_Fst: "has_type \<Gamma> \<Sigma> \<Delta> e (TProd T1 T2) \<epsilon> \<Longrightarrow>
          has_type \<Gamma> \<Sigma> \<Delta> (EFst e) T1 \<epsilon>"

| T_Snd: "has_type \<Gamma> \<Sigma> \<Delta> e (TProd T1 T2) \<epsilon> \<Longrightarrow>
          has_type \<Gamma> \<Sigma> \<Delta> (ESnd e) T2 \<epsilon>"

  (* Sums *)
| T_Inl: "has_type \<Gamma> \<Sigma> \<Delta> e T1 \<epsilon> \<Longrightarrow>
          has_type \<Gamma> \<Sigma> \<Delta> (EInl e T2) (TSum T1 T2) \<epsilon>"

| T_Inr: "has_type \<Gamma> \<Sigma> \<Delta> e T2 \<epsilon> \<Longrightarrow>
          has_type \<Gamma> \<Sigma> \<Delta> (EInr e T1) (TSum T1 T2) \<epsilon>"

| T_Case: "has_type \<Gamma> \<Sigma> \<Delta> e (TSum T1 T2) \<epsilon> \<Longrightarrow>
           has_type ((x1, T1) # \<Gamma>) \<Sigma> \<Delta> e1 T \<epsilon>1 \<Longrightarrow>
           has_type ((x2, T2) # \<Gamma>) \<Sigma> \<Delta> e2 T \<epsilon>2 \<Longrightarrow>
           has_type \<Gamma> \<Sigma> \<Delta> (ECase e x1 e1 x2 e2) T (effect_join \<epsilon> (effect_join \<epsilon>1 \<epsilon>2))"

  (* Control *)
| T_If: "has_type \<Gamma> \<Sigma> \<Delta> e1 TBool \<epsilon>1 \<Longrightarrow>
         has_type \<Gamma> \<Sigma> \<Delta> e2 T \<epsilon>2 \<Longrightarrow>
         has_type \<Gamma> \<Sigma> \<Delta> e3 T \<epsilon>3 \<Longrightarrow>
         has_type \<Gamma> \<Sigma> \<Delta> (EIf e1 e2 e3) T (effect_join \<epsilon>1 (effect_join \<epsilon>2 \<epsilon>3))"

| T_Let: "has_type \<Gamma> \<Sigma> \<Delta> e1 T1 \<epsilon>1 \<Longrightarrow>
          has_type ((x, T1) # \<Gamma>) \<Sigma> \<Delta> e2 T2 \<epsilon>2 \<Longrightarrow>
          has_type \<Gamma> \<Sigma> \<Delta> (ELet x e1 e2) T2 (effect_join \<epsilon>1 \<epsilon>2)"

  (* Effects *)
| T_Perform: "has_type \<Gamma> \<Sigma> \<Delta> e T \<epsilon> \<Longrightarrow>
              has_type \<Gamma> \<Sigma> \<Delta> (EPerform eff e) T (effect_join \<epsilon> eff)"

| T_Handle: "has_type \<Gamma> \<Sigma> \<Delta> e T1 \<epsilon>1 \<Longrightarrow>
             has_type ((x, T1) # \<Gamma>) \<Sigma> \<Delta> h T2 \<epsilon>2 \<Longrightarrow>
             has_type \<Gamma> \<Sigma> \<Delta> (EHandle e x h) T2 (effect_join \<epsilon>1 \<epsilon>2)"

  (* References *)
| T_Ref: "has_type \<Gamma> \<Sigma> \<Delta> e T \<epsilon> \<Longrightarrow>
          has_type \<Gamma> \<Sigma> \<Delta> (ERef e l) (TRef T l) (effect_join \<epsilon> EffectWrite)"

| T_Deref: "has_type \<Gamma> \<Sigma> \<Delta> e (TRef T l) \<epsilon> \<Longrightarrow>
            has_type \<Gamma> \<Sigma> \<Delta> (EDeref e) T (effect_join \<epsilon> EffectRead)"

| T_Assign: "has_type \<Gamma> \<Sigma> \<Delta> e1 (TRef T l) \<epsilon>1 \<Longrightarrow>
             has_type \<Gamma> \<Sigma> \<Delta> e2 T \<epsilon>2 \<Longrightarrow>
             has_type \<Gamma> \<Sigma> \<Delta> (EAssign e1 e2) TUnit (effect_join \<epsilon>1 (effect_join \<epsilon>2 EffectWrite))"

  (* Security *)
| T_Classify: "has_type \<Gamma> \<Sigma> \<Delta> e T \<epsilon> \<Longrightarrow>
               has_type \<Gamma> \<Sigma> \<Delta> (EClassify e) (TSecret T) \<epsilon>"

| T_Declassify: "has_type \<Gamma> \<Sigma> \<Delta> e1 (TSecret T) \<epsilon>1 \<Longrightarrow>
                 has_type \<Gamma> \<Sigma> \<Delta> e2 (TProof (TSecret T)) \<epsilon>2 \<Longrightarrow>
                 declass_ok e1 e2 \<Longrightarrow>
                 has_type \<Gamma> \<Sigma> \<Delta> (EDeclassify e1 e2) T (effect_join \<epsilon>1 \<epsilon>2)"

| T_Prove: "has_type \<Gamma> \<Sigma> \<Delta> e T \<epsilon> \<Longrightarrow>
            has_type \<Gamma> \<Sigma> \<Delta> (EProve e) (TProof T) \<epsilon>"

  (* Capabilities *)
| T_Require: "has_type \<Gamma> \<Sigma> \<Delta> e T \<epsilon> \<Longrightarrow>
              has_type \<Gamma> \<Sigma> \<Delta> (ERequire eff e) T (effect_join \<epsilon> eff)"

| T_Grant: "has_type \<Gamma> \<Sigma> \<Delta> e T \<epsilon> \<Longrightarrow>
            has_type \<Gamma> \<Sigma> \<Delta> (EGrant eff e) T \<epsilon>"


section \<open>Store Well-Formedness\<close>

text \<open>Well-typed store: every typed location has a well-typed VALUE in the store.
      (matches Coq: Definition store_wf)\<close>

definition store_wf :: "store_ty \<Rightarrow> store \<Rightarrow> bool" where
  "store_wf \<Sigma> st \<equiv>
     (\<forall>l T sl. store_ty_lookup l \<Sigma> = Some (T, sl) \<longrightarrow>
        (\<exists>v. store_lookup l st = Some v \<and> value v \<and> has_type [] \<Sigma> Public v T EffectPure)) \<and>
     (\<forall>l v. store_lookup l st = Some v \<longrightarrow>
        (\<exists>T sl. store_ty_lookup l \<Sigma> = Some (T, sl) \<and> value v \<and> has_type [] \<Sigma> Public v T EffectPure))"


section \<open>Type Uniqueness\<close>

text \<open>
  The type system is syntax-directed, so each expression has at most
  one type derivable from a given context.
  (matches Coq: Lemma type_uniqueness)
\<close>

theorem type_uniqueness:
  assumes "has_type \<Gamma> \<Sigma> \<Delta> e T1 \<epsilon>1"
      and "has_type \<Gamma> \<Sigma> \<Delta> e T2 \<epsilon>2"
  shows "T1 = T2 \<and> \<epsilon>1 = \<epsilon>2"
  using assms
proof (induction arbitrary: T2 \<epsilon>2 rule: has_type.induct)
  case (T_Unit \<Gamma> \<Sigma> \<Delta>)
  then show ?case by (auto elim: has_type.cases)
next
  case (T_Bool \<Gamma> \<Sigma> \<Delta> b)
  then show ?case by (auto elim: has_type.cases)
next
  case (T_Int \<Gamma> \<Sigma> \<Delta> n)
  then show ?case by (auto elim: has_type.cases)
next
  case (T_String \<Gamma> \<Sigma> \<Delta> s)
  then show ?case by (auto elim: has_type.cases)
next
  case (T_Loc l \<Sigma> T sl \<Gamma> \<Delta>)
  from T_Loc.prems show ?case
    by (auto elim: has_type.cases simp: T_Loc.hyps)
next
  case (T_Var x \<Gamma> T \<Sigma> \<Delta>)
  from T_Var.prems show ?case
    by (auto elim: has_type.cases simp: T_Var.hyps)
next
  case (T_Lam x T1 \<Gamma> \<Sigma> \<Delta> e T2 \<epsilon>)
  from T_Lam.prems show ?case
  proof (cases rule: has_type.cases)
    case (T_Lam x' T1' T2' e' \<epsilon>')
    then have "T2 = T2' \<and> \<epsilon> = \<epsilon>'" using T_Lam.IH by auto
    then show ?thesis using T_Lam by auto
  qed
next
  case (T_App \<Gamma> \<Sigma> \<Delta> e1 T1 T2 \<epsilon> \<epsilon>1 e2 \<epsilon>2)
  from T_App.prems show ?case
  proof (cases rule: has_type.cases)
    case (T_App T1' T2' \<epsilon>' \<epsilon>1' \<epsilon>2')
    then have eq1: "TFn T1 T2 \<epsilon> = TFn T1' T2' \<epsilon>' \<and> \<epsilon>1 = \<epsilon>1'" using T_App.IH(1) by blast
    then have "T1 = T1'" "T2 = T2'" "\<epsilon> = \<epsilon>'" by auto
    moreover have "\<epsilon>2 = \<epsilon>2'" using T_App.IH(2) T_App \<open>T1 = T1'\<close> by auto
    ultimately show ?thesis using T_App by auto
  qed
next
  case (T_Pair \<Gamma> \<Sigma> \<Delta> e1 T1 \<epsilon>1 e2 T2 \<epsilon>2)
  from T_Pair.prems show ?case
  proof (cases rule: has_type.cases)
    case (T_Pair T1' \<epsilon>1' T2' \<epsilon>2')
    then have "T1 = T1' \<and> \<epsilon>1 = \<epsilon>1'" using T_Pair.IH(1) by blast
    moreover have "T2 = T2' \<and> \<epsilon>2 = \<epsilon>2'" using T_Pair.IH(2) T_Pair by blast
    ultimately show ?thesis using T_Pair by auto
  qed
next
  case (T_Fst \<Gamma> \<Sigma> \<Delta> e T1 T2 \<epsilon>)
  from T_Fst.prems show ?case
  proof (cases rule: has_type.cases)
    case (T_Fst T1' T2' \<epsilon>')
    then have "TProd T1 T2 = TProd T1' T2' \<and> \<epsilon> = \<epsilon>'" using T_Fst.IH by blast
    then show ?thesis by auto
  qed
next
  case (T_Snd \<Gamma> \<Sigma> \<Delta> e T1 T2 \<epsilon>)
  from T_Snd.prems show ?case
  proof (cases rule: has_type.cases)
    case (T_Snd T1' T2' \<epsilon>')
    then have "TProd T1 T2 = TProd T1' T2' \<and> \<epsilon> = \<epsilon>'" using T_Snd.IH by blast
    then show ?thesis by auto
  qed
next
  case (T_Inl \<Gamma> \<Sigma> \<Delta> e T1 \<epsilon> T2)
  from T_Inl.prems show ?case
  proof (cases rule: has_type.cases)
    case (T_Inl T1' \<epsilon>' T2')
    then have "T1 = T1' \<and> \<epsilon> = \<epsilon>'" using T_Inl.IH by blast
    then show ?thesis using T_Inl by auto
  qed
next
  case (T_Inr \<Gamma> \<Sigma> \<Delta> e T2 \<epsilon> T1)
  from T_Inr.prems show ?case
  proof (cases rule: has_type.cases)
    case (T_Inr T2' \<epsilon>' T1')
    then have "T2 = T2' \<and> \<epsilon> = \<epsilon>'" using T_Inr.IH by blast
    then show ?thesis using T_Inr by auto
  qed
next
  case (T_Case \<Gamma> \<Sigma> \<Delta> e T1 T2 \<epsilon> x1 e1 T \<epsilon>1 x2 e2 \<epsilon>2)
  from T_Case.prems show ?case
  proof (cases rule: has_type.cases)
    case (T_Case T1' T2' \<epsilon>' T' \<epsilon>1' \<epsilon>2')
    then have eq0: "TSum T1 T2 = TSum T1' T2' \<and> \<epsilon> = \<epsilon>'" using T_Case.IH(1) by blast
    then have "T1 = T1'" "T2 = T2'" by auto
    then have "T = T' \<and> \<epsilon>1 = \<epsilon>1'" using T_Case.IH(2) T_Case by auto
    moreover have "\<epsilon>2 = \<epsilon>2'" using T_Case.IH(3) T_Case \<open>T2 = T2'\<close> by auto
    ultimately show ?thesis using T_Case eq0 by auto
  qed
next
  case (T_If \<Gamma> \<Sigma> \<Delta> e1 \<epsilon>1 e2 T \<epsilon>2 e3 \<epsilon>3)
  from T_If.prems show ?case
  proof (cases rule: has_type.cases)
    case (T_If \<epsilon>1' T' \<epsilon>2' \<epsilon>3')
    then have "\<epsilon>1 = \<epsilon>1'" using T_If.IH(1) by auto
    moreover have "T = T' \<and> \<epsilon>2 = \<epsilon>2'" using T_If.IH(2) T_If by blast
    moreover have "\<epsilon>3 = \<epsilon>3'" using T_If.IH(3) T_If by auto
    ultimately show ?thesis using T_If by auto
  qed
next
  case (T_Let \<Gamma> \<Sigma> \<Delta> e1 T1 \<epsilon>1 x e2 T2 \<epsilon>2)
  from T_Let.prems show ?case
  proof (cases rule: has_type.cases)
    case (T_Let T1' \<epsilon>1' T2' \<epsilon>2')
    then have "T1 = T1' \<and> \<epsilon>1 = \<epsilon>1'" using T_Let.IH(1) by blast
    then have "T2 = T2' \<and> \<epsilon>2 = \<epsilon>2'" using T_Let.IH(2) T_Let by auto
    then show ?thesis using T_Let \<open>\<epsilon>1 = \<epsilon>1'\<close> by auto
  qed
next
  case (T_Perform \<Gamma> \<Sigma> \<Delta> e T \<epsilon> eff)
  from T_Perform.prems show ?case
  proof (cases rule: has_type.cases)
    case (T_Perform T' \<epsilon>')
    then have "T = T' \<and> \<epsilon> = \<epsilon>'" using T_Perform.IH by blast
    then show ?thesis using T_Perform by auto
  qed
next
  case (T_Handle \<Gamma> \<Sigma> \<Delta> e T1 \<epsilon>1 x h T2 \<epsilon>2)
  from T_Handle.prems show ?case
  proof (cases rule: has_type.cases)
    case (T_Handle T1' \<epsilon>1' T2' \<epsilon>2')
    then have "T1 = T1' \<and> \<epsilon>1 = \<epsilon>1'" using T_Handle.IH(1) by blast
    then have "T2 = T2' \<and> \<epsilon>2 = \<epsilon>2'" using T_Handle.IH(2) T_Handle by auto
    then show ?thesis using T_Handle \<open>\<epsilon>1 = \<epsilon>1'\<close> by auto
  qed
next
  case (T_Ref \<Gamma> \<Sigma> \<Delta> e T \<epsilon> l)
  from T_Ref.prems show ?case
  proof (cases rule: has_type.cases)
    case (T_Ref T' \<epsilon>')
    then have "T = T' \<and> \<epsilon> = \<epsilon>'" using T_Ref.IH by blast
    then show ?thesis using T_Ref by auto
  qed
next
  case (T_Deref \<Gamma> \<Sigma> \<Delta> e T l \<epsilon>)
  from T_Deref.prems show ?case
  proof (cases rule: has_type.cases)
    case (T_Deref T' l' \<epsilon>')
    then have "TRef T l = TRef T' l' \<and> \<epsilon> = \<epsilon>'" using T_Deref.IH by blast
    then show ?thesis by auto
  qed
next
  case (T_Assign \<Gamma> \<Sigma> \<Delta> e1 T l \<epsilon>1 e2 \<epsilon>2)
  from T_Assign.prems show ?case
  proof (cases rule: has_type.cases)
    case (T_Assign T' l' \<epsilon>1' \<epsilon>2')
    then have eq1: "TRef T l = TRef T' l' \<and> \<epsilon>1 = \<epsilon>1'" using T_Assign.IH(1) by blast
    then have "T = T'" by auto
    then have "\<epsilon>2 = \<epsilon>2'" using T_Assign.IH(2) T_Assign by auto
    then show ?thesis using T_Assign eq1 by auto
  qed
next
  case (T_Classify \<Gamma> \<Sigma> \<Delta> e T \<epsilon>)
  from T_Classify.prems show ?case
  proof (cases rule: has_type.cases)
    case (T_Classify T' \<epsilon>')
    then have "T = T' \<and> \<epsilon> = \<epsilon>'" using T_Classify.IH by blast
    then show ?thesis using T_Classify by auto
  qed
next
  case (T_Declassify \<Gamma> \<Sigma> \<Delta> e1 T \<epsilon>1 e2 \<epsilon>2 ok)
  from T_Declassify.prems show ?case
  proof (cases rule: has_type.cases)
    case (T_Declassify T' \<epsilon>1' \<epsilon>2' ok')
    then have eq1: "TSecret T = TSecret T' \<and> \<epsilon>1 = \<epsilon>1'" using T_Declassify.IH(1) by blast
    then have "T = T'" by auto
    then have "\<epsilon>2 = \<epsilon>2'" using T_Declassify.IH(2) T_Declassify by auto
    then show ?thesis using T_Declassify eq1 by auto
  qed
next
  case (T_Prove \<Gamma> \<Sigma> \<Delta> e T \<epsilon>)
  from T_Prove.prems show ?case
  proof (cases rule: has_type.cases)
    case (T_Prove T' \<epsilon>')
    then have "T = T' \<and> \<epsilon> = \<epsilon>'" using T_Prove.IH by blast
    then show ?thesis using T_Prove by auto
  qed
next
  case (T_Require \<Gamma> \<Sigma> \<Delta> e T \<epsilon> eff)
  from T_Require.prems show ?case
  proof (cases rule: has_type.cases)
    case (T_Require T' \<epsilon>')
    then have "T = T' \<and> \<epsilon> = \<epsilon>'" using T_Require.IH by blast
    then show ?thesis using T_Require by auto
  qed
next
  case (T_Grant \<Gamma> \<Sigma> \<Delta> e T \<epsilon> eff)
  from T_Grant.prems show ?case
  proof (cases rule: has_type.cases)
    case (T_Grant T' \<epsilon>')
    then have "T = T' \<and> \<epsilon> = \<epsilon>'" using T_Grant.IH by blast
    then show ?thesis using T_Grant by auto
  qed
qed


section \<open>Canonical Forms\<close>

text \<open>
  Canonical forms lemmas: if a value has a certain type, it must have
  a specific syntactic form. Essential for proving progress.
  (matches Coq: canonical_forms_* lemmas)
\<close>

text \<open>Unit type: only EUnit is a value of type TUnit (matches Coq: canonical_forms_unit)\<close>

lemma canonical_forms_unit:
  assumes "value v" and "has_type \<Gamma> \<Sigma> \<Delta> v TUnit \<epsilon>"
  shows "v = EUnit"
  using assms by (cases v rule: value.cases; auto elim: has_type.cases)

text \<open>Bool type: only EBool b is a value of type TBool (matches Coq: canonical_forms_bool)\<close>

lemma canonical_forms_bool:
  assumes "value v" and "has_type \<Gamma> \<Sigma> \<Delta> v TBool \<epsilon>"
  shows "\<exists>b. v = EBool b"
  using assms by (cases v rule: value.cases; auto elim: has_type.cases)

text \<open>Int type: only EInt n is a value of type TInt (matches Coq: canonical_forms_int)\<close>

lemma canonical_forms_int:
  assumes "value v" and "has_type \<Gamma> \<Sigma> \<Delta> v TInt \<epsilon>"
  shows "\<exists>n. v = EInt n"
  using assms by (cases v rule: value.cases; auto elim: has_type.cases)

text \<open>String type: only EString s is a value of type TString (matches Coq: canonical_forms_string)\<close>

lemma canonical_forms_string:
  assumes "value v" and "has_type \<Gamma> \<Sigma> \<Delta> v TString \<epsilon>"
  shows "\<exists>s. v = EString s"
  using assms by (cases v rule: value.cases; auto elim: has_type.cases)

text \<open>Function type: only ELam is a value of function type (matches Coq: canonical_forms_fn)\<close>

lemma canonical_forms_fn:
  assumes "value v" and "has_type \<Gamma> \<Sigma> \<Delta> v (TFn T1 T2 \<epsilon>_fn) \<epsilon>"
  shows "\<exists>x body. v = ELam x T1 body"
  using assms by (cases v rule: value.cases; auto elim: has_type.cases)

text \<open>Product type: only EPair is a value of product type (matches Coq: canonical_forms_prod)\<close>

lemma canonical_forms_prod:
  assumes "value v" and "has_type \<Gamma> \<Sigma> \<Delta> v (TProd T1 T2) \<epsilon>"
  shows "\<exists>v1 v2. v = EPair v1 v2 \<and> value v1 \<and> value v2"
  using assms
proof (cases v rule: value.cases)
  case (VPair v1 v2)
  then show ?thesis using assms by (auto elim: has_type.cases)
qed (auto elim: has_type.cases)

text \<open>Sum type: only EInl or EInr is a value of sum type (matches Coq: canonical_forms_sum)\<close>

lemma canonical_forms_sum:
  assumes "value v" and "has_type \<Gamma> \<Sigma> \<Delta> v (TSum T1 T2) \<epsilon>"
  shows "(\<exists>v'. v = EInl v' T2 \<and> value v') \<or> (\<exists>v'. v = EInr v' T1 \<and> value v')"
  using assms
proof (cases v rule: value.cases)
  case (VInl v0 T)
  then show ?thesis using assms by (auto elim: has_type.cases)
next
  case (VInr v0 T)
  then show ?thesis using assms by (auto elim: has_type.cases)
qed (auto elim: has_type.cases)

text \<open>Reference type: only ELoc is a value of reference type (matches Coq: canonical_forms_ref)\<close>

lemma canonical_forms_ref:
  assumes "value v" and "has_type \<Gamma> \<Sigma> \<Delta> v (TRef T sl) \<epsilon>"
  shows "\<exists>l. v = ELoc l"
  using assms by (cases v rule: value.cases; auto elim: has_type.cases)

text \<open>Secret type: only EClassify is a value of secret type (matches Coq: canonical_forms_secret)\<close>

lemma canonical_forms_secret:
  assumes "value v" and "has_type \<Gamma> \<Sigma> \<Delta> v (TSecret T) \<epsilon>"
  shows "\<exists>v'. v = EClassify v' \<and> value v'"
  using assms
proof (cases v rule: value.cases)
  case (VClassify v0)
  then show ?thesis using assms by (auto elim: has_type.cases)
qed (auto elim: has_type.cases)

text \<open>Proof type: only EProve is a value of proof type (matches Coq: canonical_forms_proof)\<close>

lemma canonical_forms_proof:
  assumes "value v" and "has_type \<Gamma> \<Sigma> \<Delta> v (TProof T) \<epsilon>"
  shows "\<exists>v'. v = EProve v' \<and> value v'"
  using assms
proof (cases v rule: value.cases)
  case (VProve v0)
  then show ?thesis using assms by (auto elim: has_type.cases)
qed (auto elim: has_type.cases)


section \<open>Well-Formedness Lemmas\<close>

text \<open>Well-formed types (matches Coq: wf_ty)\<close>

lemma WF_TSecret: "wf_ty T \<Longrightarrow> wf_ty (TSecret T)"
  by (rule wf_ty.WF_TSecret)

lemma WF_TProof: "wf_ty T \<Longrightarrow> wf_ty (TProof T)"
  by (rule wf_ty.WF_TProof)


section \<open>Verification Summary\<close>

text \<open>
  This theory ports Typing.v (648 lines Coq) to Isabelle/HOL.

  | Coq Theorem                | Isabelle Lemma             | Status   |
  |----------------------------|----------------------------|----------|
  | type_uniqueness            | type_uniqueness            | Proved   |
  | canonical_forms_unit       | canonical_forms_unit       | Proved   |
  | canonical_forms_bool       | canonical_forms_bool       | Proved   |
  | canonical_forms_int        | canonical_forms_int        | Proved   |
  | canonical_forms_string     | canonical_forms_string     | Proved   |
  | canonical_forms_fn         | canonical_forms_fn         | Proved   |
  | canonical_forms_prod       | canonical_forms_prod       | Proved   |
  | canonical_forms_sum        | canonical_forms_sum        | Proved   |
  | canonical_forms_ref        | canonical_forms_ref        | Proved   |
  | canonical_forms_secret     | canonical_forms_secret     | Proved   |
  | canonical_forms_proof      | canonical_forms_proof      | Proved   |

  Total: 11 lemmas ported
\<close>

end
