(** * Preservation Theorem for TERAS-LANG

    If a well-typed expression takes a step,
    the resulting expression is also well-typed with the same type.

    Reference: CTSS_v1_0_1.md, Section 6

    Mode: ULTRA KIASU | FUCKING PARANOID | ZERO TRUST | ZERO LAZINESS
*)

Require Import Coq.Strings.String.
Require Import Coq.Lists.List.
Require Import TERAS.foundations.Syntax.
Require Import TERAS.foundations.Semantics.
Require Import TERAS.foundations.Typing.
Import ListNotations.

(** ** Preservation Statement *)

Definition preservation_stmt := forall e e' T ε st st' ctx ctx',
  has_type nil nil Public e T ε ->
  (e, st, ctx) --> (e', st', ctx') ->
  has_type nil nil Public e' T ε.

(** ** Substitution Lemma

    Key lemma: substitution preserves typing.

    If v has type T1 in empty context, and e has type T2 in context
    extended with x:T1, then [x := v] e has type T2 in the original context.

    NOTE: This is a standard but non-trivial lemma. The complete proof
    requires:
    1. Induction on the typing derivation of e
    2. Context weakening lemma (closed terms can be typed in any context)
    3. Careful handling of variable capture in lambda abstractions

    The key insight is that when substituting, we replace all free
    occurrences of x with v, and since v has the same type as x's binding,
    the overall type is preserved.
*)

Lemma substitution_preserves_typing : forall Γ Σ Δ x v e T1 T2 ε1 ε2,
  has_type nil Σ Δ v T1 ε1 ->
  has_type ((x, T1) :: Γ) Σ Δ e T2 ε2 ->
  has_type Γ Σ Δ ([x := v] e) T2 ε2.
Proof.
  intros Γ Σ Δ x v e T1 T2 ε1 ε2 Hv Hty.
  (* Proof sketch:
     - Induction on the typing derivation of e
     - Case EVar x0:
       * If x0 = x, then [x := v](EVar x) = v, and we use Hv with weakening
       * If x0 ≠ x, then [x := v](EVar x0) = EVar x0, and we use the lookup fact
     - Case ELam y T body:
       * If y = x, no substitution in body (variable captured), use original typing
       * If y ≠ x, recurse on body with extended context
     - Other cases: apply IH to subterms and reconstruct typing derivation
  *)
Admitted.

(** ** Preservation Theorem

    The preservation theorem states that if a well-typed expression
    takes a step, the result is also well-typed with the same type.

    The proof proceeds by induction on the step derivation and uses
    the substitution lemma for beta reduction cases.
*)

Theorem preservation : preservation_stmt.
Proof.
  unfold preservation_stmt.
  intros e e' T ε st st' ctx ctx' Hty Hstep.
  generalize dependent ε.
  generalize dependent T.
  induction Hstep; intros T' ε' Hty; inversion Hty; subst;
    (* Try substitution lemma for beta reductions *)
    try (eapply substitution_preserves_typing; eauto; fail);
    (* Try reconstructing typing for congruence cases *)
    try (econstructor; eauto; fail).
  (* Remaining cases require careful inversion.
     The proof depends on substitution_preserves_typing (admitted above).
     Once that lemma is proven, this proof completes.
     For now, we admit the remaining cases which involve:
     - ST_Fst/ST_Snd: inversion on pair typing
     - ST_CaseInl/ST_CaseInr: inversion + substitution
     - ST_IfTrue/ST_IfFalse: selecting the correct branch type
  *)
  all: admit.
Admitted.

(** End of Preservation.v *)
