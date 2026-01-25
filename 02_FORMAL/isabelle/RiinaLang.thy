(*
  RIINA Formal Verification - Isabelle/HOL Port
  
  This file provides the foundation for porting proofs to Isabelle/HOL.
  Cross-verification in multiple proof assistants increases confidence.
  
  Generated: 2026-01-25
  Status: SKELETON - types and statement structure only
*)

theory RiinaLang
  imports Main
begin

section \<open>Security Labels\<close>

datatype sec_label = L | H

fun label_leq :: "sec_label \<Rightarrow> sec_label \<Rightarrow> bool" where
  "label_leq L _ = True"
| "label_leq H H = True"
| "label_leq H L = False"

section \<open>Types\<close>

datatype ty = 
    TUnit
  | TBool
  | TNat
  | TRef ty sec_label
  | TProd ty ty
  | TSum ty ty
  | TArrow ty ty

section \<open>Expressions\<close>

datatype expr =
    EVar nat
  | EUnit
  | EBool bool
  | ENat nat
  | ELoc nat
  | EPair expr expr
  | EFst expr
  | ESnd expr
  | EInl expr
  | EInr expr
  | ELam ty expr
  | EApp expr expr
  | ERef sec_label expr
  | EDeref expr
  | EAssign expr expr

section \<open>Values\<close>

inductive is_value :: "expr \<Rightarrow> bool" where
  V_Unit: "is_value EUnit"
| V_Bool: "is_value (EBool b)"
| V_Nat: "is_value (ENat n)"
| V_Loc: "is_value (ELoc l)"
| V_Pair: "\<lbrakk>is_value v1; is_value v2\<rbrakk> \<Longrightarrow> is_value (EPair v1 v2)"
| V_Inl: "is_value v \<Longrightarrow> is_value (EInl v)"
| V_Inr: "is_value v \<Longrightarrow> is_value (EInr v)"
| V_Lam: "is_value (ELam T e)"

section \<open>Store and Store Typing\<close>

type_synonym store = "nat \<Rightarrow> expr option"
type_synonym store_typing = "nat \<Rightarrow> (ty \<times> sec_label) option"

definition store_empty :: store where
  "store_empty = (\<lambda>_. None)"

definition store_ty_empty :: store_typing where
  "store_ty_empty = (\<lambda>_. None)"

definition store_lookup :: "store \<Rightarrow> nat \<Rightarrow> expr option" where
  "store_lookup s l = s l"

definition store_ty_lookup :: "store_typing \<Rightarrow> nat \<Rightarrow> (ty \<times> sec_label) option" where
  "store_ty_lookup \<Sigma> l = \<Sigma> l"

definition store_update :: "store \<Rightarrow> nat \<Rightarrow> expr \<Rightarrow> store" where
  "store_update s l v = (\<lambda>l'. if l = l' then Some v else s l')"

section \<open>Step-Indexed Value Relation\<close>

fun val_rel_n :: "nat \<Rightarrow> store_typing \<Rightarrow> ty \<Rightarrow> expr \<Rightarrow> expr \<Rightarrow> bool" where
  "val_rel_n 0 \<Sigma> T v1 v2 = True"
| "val_rel_n (Suc n) \<Sigma> TUnit v1 v2 = 
     (is_value v1 \<and> is_value v2 \<and> v1 = EUnit \<and> v2 = EUnit)"
| "val_rel_n (Suc n) \<Sigma> TBool v1 v2 = 
     (is_value v1 \<and> is_value v2 \<and> (\<exists>b. v1 = EBool b \<and> v2 = EBool b))"
| "val_rel_n (Suc n) \<Sigma> TNat v1 v2 = 
     (is_value v1 \<and> is_value v2 \<and> (\<exists>m. v1 = ENat m \<and> v2 = ENat m))"
| "val_rel_n (Suc n) \<Sigma> (TRef T sl) v1 v2 = 
     (is_value v1 \<and> is_value v2 \<and> 
      (\<exists>l. v1 = ELoc l \<and> v2 = ELoc l \<and> store_ty_lookup \<Sigma> l = Some (T, sl)))"
| "val_rel_n (Suc n) \<Sigma> (TProd T1 T2) v1 v2 = 
     (is_value v1 \<and> is_value v2 \<and>
      (\<exists>v1a v1b v2a v2b. v1 = EPair v1a v1b \<and> v2 = EPair v2a v2b \<and>
       val_rel_n n \<Sigma> T1 v1a v2a \<and> val_rel_n n \<Sigma> T2 v1b v2b))"
| "val_rel_n (Suc n) \<Sigma> (TSum T1 T2) v1 v2 = 
     (is_value v1 \<and> is_value v2 \<and>
      ((\<exists>v1' v2'. v1 = EInl v1' \<and> v2 = EInl v2' \<and> val_rel_n n \<Sigma> T1 v1' v2') \<or>
       (\<exists>v1' v2'. v1 = EInr v1' \<and> v2 = EInr v2' \<and> val_rel_n n \<Sigma> T2 v1' v2')))"
| "val_rel_n (Suc n) \<Sigma> (TArrow T1 T2) v1 v2 = 
     (is_value v1 \<and> is_value v2 \<and>
      (\<exists>e1 e2. v1 = ELam T1 e1 \<and> v2 = ELam T1 e2))"

section \<open>Store Relation\<close>

definition store_rel_n :: "nat \<Rightarrow> store_typing \<Rightarrow> store \<Rightarrow> store \<Rightarrow> bool" where
  "store_rel_n n \<Sigma> s1 s2 = 
     (\<forall>l T sl. store_ty_lookup \<Sigma> l = Some (T, sl) \<longrightarrow>
      (\<forall>v1 v2. store_lookup s1 l = Some v1 \<longrightarrow> store_lookup s2 l = Some v2 \<longrightarrow>
       val_rel_n n \<Sigma> T v1 v2))"

section \<open>Proven Lemmas\<close>

text \<open>LEMMA 1: val_rel_n_zero - Step 0 is trivial\<close>
lemma val_rel_n_zero: "val_rel_n 0 \<Sigma> T v1 v2"
  by simp

text \<open>LEMMA 2: val_rel_n_unit - Unit values are related\<close>
lemma val_rel_n_unit: 
  assumes "n > 0"
  shows "val_rel_n n \<Sigma> TUnit EUnit EUnit"
  using assms by (cases n) (auto intro: is_value.intros)

text \<open>LEMMA 3: val_rel_n_bool - Bool values are related\<close>
lemma val_rel_n_bool:
  assumes "n > 0"
  shows "val_rel_n n \<Sigma> TBool (EBool b) (EBool b)"
  using assms by (cases n) (auto intro: is_value.intros)

text \<open>LEMMA 4: val_rel_n_nat - Nat values are related\<close>
lemma val_rel_n_nat:
  assumes "n > 0"
  shows "val_rel_n n \<Sigma> TNat (ENat m) (ENat m)"
  using assms by (cases n) (auto intro: is_value.intros)

text \<open>LEMMA 5: val_rel_n_ref - Reference values are related\<close>
lemma val_rel_n_ref:
  assumes "n > 0"
  assumes "store_ty_lookup \<Sigma> l = Some (T, lab)"
  shows "val_rel_n n \<Sigma> (TRef T lab) (ELoc l) (ELoc l)"
  using assms by (cases n) (auto intro: is_value.intros)

text \<open>LEMMA 6: val_rel_n_step_down - Step monotonicity\<close>
lemma val_rel_n_step_down:
  assumes "m \<le> n"
  assumes "val_rel_n n \<Sigma> T v1 v2"
  shows "val_rel_n m \<Sigma> T v1 v2"
  using assms
proof (induction n arbitrary: m T v1 v2)
  case 0
  then show ?case by simp
next
  case (Suc n)
  then show ?case
  proof (cases m)
    case 0
    then show ?thesis by simp
  next
    case (Suc m')
    then have "m' \<le> n" using Suc.prems(1) by simp
    show ?thesis
    proof (cases T)
      case TUnit
      then show ?thesis using Suc.prems(2) \<open>m = Suc m'\<close> by simp
    next
      case TBool
      then show ?thesis using Suc.prems(2) \<open>m = Suc m'\<close> by simp
    next
      case TNat
      then show ?thesis using Suc.prems(2) \<open>m = Suc m'\<close> by simp
    next
      case (TRef x1 x2)
      then show ?thesis using Suc.prems(2) \<open>m = Suc m'\<close> by simp
    next
      case (TProd T1 T2)
      then obtain v1a v1b v2a v2b where 
        "v1 = EPair v1a v1b" "v2 = EPair v2a v2b"
        "val_rel_n n \<Sigma> T1 v1a v2a" "val_rel_n n \<Sigma> T2 v1b v2b"
        using Suc.prems(2) by auto
      then show ?thesis 
        using Suc.IH[OF \<open>m' \<le> n\<close>] TProd \<open>m = Suc m'\<close> Suc.prems(2) by auto
    next
      case (TSum T1 T2)
      then show ?thesis 
        using Suc.IH[OF \<open>m' \<le> n\<close>] \<open>m = Suc m'\<close> Suc.prems(2) by fastforce
    next
      case (TArrow T1 T2)
      then show ?thesis using Suc.prems(2) \<open>m = Suc m'\<close> by simp
    qed
  qed
qed

text \<open>LEMMA 7: store_rel_n_zero - Step 0 store relation\<close>
lemma store_rel_n_zero: "store_rel_n 0 \<Sigma> s1 s2"
  unfolding store_rel_n_def by simp

text \<open>LEMMA 8: store_rel_n_step_down - Store relation monotonicity\<close>
lemma store_rel_n_step_down:
  assumes "m \<le> n"
  assumes "store_rel_n n \<Sigma> s1 s2"
  shows "store_rel_n m \<Sigma> s1 s2"
  using assms val_rel_n_step_down
  unfolding store_rel_n_def by blast

section \<open>Verification Status\<close>

text \<open>
  PROVEN IN THIS FILE:
  1. val_rel_n_zero
  2. val_rel_n_unit
  3. val_rel_n_bool
  4. val_rel_n_nat
  5. val_rel_n_ref
  6. val_rel_n_step_down
  7. store_rel_n_zero
  8. store_rel_n_step_down
  
  REMAINING (26 - 8 = 18 axioms):
  - Expression relation lemmas
  - Store update lemmas
  - Fundamental theorem
  - Non-interference theorem
\<close>

end
