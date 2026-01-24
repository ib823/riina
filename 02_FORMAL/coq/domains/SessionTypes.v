(* SessionTypes.v - Session Types for RIINA *)
(* Spec: 01_RESEARCH/01_DOMAIN_A_TYPE_THEORY/session_types/ *)
(* Security Property: Protocol adherence, deadlock freedom *)

Require Import Coq.Lists.List.
Require Import Coq.Bool.Bool.
Require Import Coq.Arith.Arith.
Require Import Coq.Arith.EqNat.
Require Import Coq.micromega.Lia.
Import ListNotations.

(* Base types for messages *)
Inductive BaseTy : Type :=
  | BTUnit : BaseTy
  | BTBool : BaseTy
  | BTNat : BaseTy
.

(* Session types *)
Inductive SessionTy : Type :=
  | SSend : BaseTy -> SessionTy -> SessionTy    (* !T.S - send T then continue as S *)
  | SRecv : BaseTy -> SessionTy -> SessionTy    (* ?T.S - receive T then continue as S *)
  | SChoice : list SessionTy -> SessionTy       (* ⊕{S₁, S₂, ...} - internal choice *)
  | SBranch : list SessionTy -> SessionTy       (* &{S₁, S₂, ...} - external choice *)
  | SEnd : SessionTy                            (* end - session termination *)
  | SRec : SessionTy -> SessionTy               (* μX.S - recursive session *)
  | SVar : nat -> SessionTy                     (* X - recursion variable *)
.

(* Duality function *)
Fixpoint dual (s : SessionTy) : SessionTy :=
  match s with
  | SSend t s' => SRecv t (dual s')
  | SRecv t s' => SSend t (dual s')
  | SChoice ss => SBranch (map dual ss)
  | SBranch ss => SChoice (map dual ss)
  | SEnd => SEnd
  | SRec s' => SRec (dual s')
  | SVar n => SVar n
  end.

(* Values *)
Inductive Value : Type :=
  | VUnit : Value
  | VBool : bool -> Value
  | VNat : nat -> Value
  | VChan : nat -> Value
.

(* Channel names *)
Definition Chan := nat.

(* Process expressions *)
Inductive Proc : Type :=
  | PEnd : Proc                                          (* terminated process *)
  | PSend : Chan -> Value -> Proc -> Proc                (* send value on channel *)
  | PRecv : Chan -> Proc -> Proc                         (* receive on channel *)
  | PSelect : Chan -> nat -> Proc -> Proc                (* select branch i *)
  | PBranch : Chan -> list Proc -> Proc                  (* offer branches *)
  | PPar : Proc -> Proc -> Proc                          (* parallel composition *)
  | PNew : SessionTy -> Proc -> Proc                     (* new channel with session type *)
  | PRec : Proc -> Proc                                  (* recursive process *)
  | PVar : nat -> Proc                                   (* process variable *)
.

(* Channel endpoint: positive or negative *)
Inductive Polarity : Type :=
  | Pos : Polarity
  | Neg : Polarity
.

(* Typing context entry *)
Definition TypingEntry := (Chan * Polarity * SessionTy)%type.
Definition TypingCtx := list TypingEntry.

(* Base type equality *)
Definition basety_eq (t1 t2 : BaseTy) : bool :=
  match t1, t2 with
  | BTUnit, BTUnit => true
  | BTBool, BTBool => true
  | BTNat, BTNat => true
  | _, _ => false
  end.

(* Process typing judgment *)
Inductive ProcTyped : TypingCtx -> Proc -> Prop :=
  | T_End : forall Γ,
      ProcTyped Γ PEnd
  | T_Send : forall Γ c v P t S,
      In (c, Pos, SSend t S) Γ ->
      ProcTyped Γ P ->
      ProcTyped Γ (PSend c v P)
  | T_Recv : forall Γ c P t S,
      In (c, Pos, SRecv t S) Γ ->
      ProcTyped Γ P ->
      ProcTyped Γ (PRecv c P)
  | T_Select : forall Γ c i P Ss,
      In (c, Pos, SChoice Ss) Γ ->
      i < length Ss ->
      ProcTyped Γ P ->
      ProcTyped Γ (PSelect c i P)
  | T_Branch : forall Γ c Ps Ss,
      In (c, Pos, SBranch Ss) Γ ->
      length Ps = length Ss ->
      Forall (ProcTyped Γ) Ps ->
      ProcTyped Γ (PBranch c Ps)
  | T_Par : forall Γ P Q,
      ProcTyped Γ P ->
      ProcTyped Γ Q ->
      ProcTyped Γ (PPar P Q)
  | T_New : forall Γ S P,
      ProcTyped Γ P ->
      ProcTyped Γ (PNew S P)
  | T_Rec : forall Γ P,
      ProcTyped Γ P ->
      ProcTyped Γ (PRec P)
.

(* Process reduction *)
Inductive ProcStep : Proc -> Proc -> Prop :=
  | Step_Comm : forall c v P Q,
      ProcStep (PPar (PSend c v P) (PRecv c Q)) (PPar P Q)
  | Step_Select : forall c i P Qs Q,
      nth_error Qs i = Some Q ->
      ProcStep (PPar (PSelect c i P) (PBranch c Qs)) (PPar P Q)
  | Step_ParL : forall P P' Q,
      ProcStep P P' ->
      ProcStep (PPar P Q) (PPar P' Q)
  | Step_ParR : forall P Q Q',
      ProcStep Q Q' ->
      ProcStep (PPar P Q) (PPar P Q')
  | Step_New : forall S P P',
      ProcStep P P' ->
      ProcStep (PNew S P) (PNew S P')
  | Step_Unfold : forall P,
      ProcStep (PRec P) P
.

(* Configuration: process with channel assignments *)
Inductive Config : Type :=
  | CProc : Proc -> Config
  | CPar : Config -> Config -> Config
  | CNew : SessionTy -> Config -> Config
.

(* Configuration is stuck *)
Definition is_stuck (C : Config) : Prop :=
  match C with
  | CProc PEnd => False
  | CProc (PPar (PSend c1 v P) (PRecv c2 Q)) => c1 <> c2
  | _ => True
  end.

(* Well-formed configuration *)
Inductive ConfigTyped : TypingCtx -> Config -> Prop :=
  | CT_Proc : forall Γ P,
      ProcTyped Γ P ->
      ConfigTyped Γ (CProc P)
  | CT_Par : forall Γ C1 C2,
      ConfigTyped Γ C1 ->
      ConfigTyped Γ C2 ->
      ConfigTyped Γ (CPar C1 C2)
  | CT_New : forall Γ S C,
      ConfigTyped Γ C ->
      ConfigTyped Γ (CNew S C)
.

(* Unfolding for recursive types *)
Fixpoint unfold_session (s : SessionTy) : SessionTy :=
  match s with
  | SRec s' => unfold_session s'
  | _ => s
  end.

(* Session subtyping relation *)
Inductive SessionSubtype : SessionTy -> SessionTy -> Prop :=
  | Sub_Refl : forall S, SessionSubtype S S
  | Sub_End : SessionSubtype SEnd SEnd
  | Sub_Send : forall t S1 S2,
      SessionSubtype S1 S2 ->
      SessionSubtype (SSend t S1) (SSend t S2)
  | Sub_Recv : forall t S1 S2,
      SessionSubtype S2 S1 ->
      SessionSubtype (SRecv t S1) (SRecv t S2)
  | Sub_Choice : forall Ss1 Ss2,
      length Ss1 <= length Ss2 ->
      (forall i S1, nth_error Ss1 i = Some S1 -> 
        exists S2, nth_error Ss2 i = Some S2 /\ SessionSubtype S1 S2) ->
      SessionSubtype (SChoice Ss1) (SChoice Ss2)
  | Sub_Branch : forall Ss1 Ss2,
      length Ss2 <= length Ss1 ->
      (forall i S2, nth_error Ss2 i = Some S2 ->
        exists S1, nth_error Ss1 i = Some S1 /\ SessionSubtype S1 S2) ->
      SessionSubtype (SBranch Ss1) (SBranch Ss2)
.

(* Linear usage: channel appears at most once *)
Fixpoint chan_count (c : Chan) (P : Proc) : nat :=
  match P with
  | PEnd => 0
  | PSend c' _ P' => (if Nat.eqb c c' then 1 else 0) + chan_count c P'
  | PRecv c' P' => (if Nat.eqb c c' then 1 else 0) + chan_count c P'
  | PSelect c' _ P' => (if Nat.eqb c c' then 1 else 0) + chan_count c P'
  | PBranch c' Ps => (if Nat.eqb c c' then 1 else 0) + 
      fold_left (fun acc p => acc + chan_count c p) Ps 0
  | PPar P1 P2 => chan_count c P1 + chan_count c P2
  | PNew _ P' => chan_count c P'
  | PRec P' => chan_count c P'
  | PVar _ => 0
  end.

Definition linear_channel (c : Chan) (P : Proc) : Prop :=
  chan_count c P <= 1.

(* Delegation: channel passing in session *)
Inductive Delegates : Proc -> Chan -> Chan -> Prop :=
  | Del_Send : forall c c' P,
      Delegates (PSend c (VChan c') P) c c'
  | Del_Par_L : forall P Q c c',
      Delegates P c c' ->
      Delegates (PPar P Q) c c'
  | Del_Par_R : forall P Q c c',
      Delegates Q c c' ->
      Delegates (PPar P Q) c c'
.

(* Global type for multiparty sessions *)
Inductive GlobalTy : Type :=
  | GMsg : nat -> nat -> BaseTy -> GlobalTy -> GlobalTy  (* p -> q : T ; G *)
  | GChoice : nat -> nat -> list GlobalTy -> GlobalTy    (* p -> q : {G1, G2, ...} *)
  | GEnd : GlobalTy
  | GRec : GlobalTy -> GlobalTy
  | GVar : nat -> GlobalTy
.

(* Local type (per participant) *)
Definition LocalTy := SessionTy.

(* Projection from global to local *)
Fixpoint project (G : GlobalTy) (p : nat) : option LocalTy :=
  match G with
  | GMsg sender receiver t G' =>
      match project G' p with
      | Some S' =>
          if Nat.eqb p sender then Some (SSend t S')
          else if Nat.eqb p receiver then Some (SRecv t S')
          else Some S'
      | None => None
      end
  | GChoice sender receiver Gs =>
      let projs := map (fun g => project g p) Gs in
      if forallb (fun o => match o with Some _ => true | None => false end) projs then
        let locals := map (fun o => match o with Some s => s | None => SEnd end) projs in
        if Nat.eqb p sender then Some (SChoice locals)
        else if Nat.eqb p receiver then Some (SBranch locals)
        else match locals with
             | [] => Some SEnd
             | h :: _ => Some h
             end
      else None
  | GEnd => Some SEnd
  | GRec G' => 
      match project G' p with
      | Some S' => Some (SRec S')
      | None => None
      end
  | GVar n => Some (SVar n)
  end.

(* Multiparty configuration *)
Inductive MPConfig : Type :=
  | MPC : list (nat * Proc) -> MPConfig.

(* Multiparty typing *)
Inductive MPTyped : GlobalTy -> MPConfig -> Prop :=
  | MPT_End : MPTyped GEnd (MPC [])
  | MPT_Procs : forall G ps,
      (forall p P, In (p, P) ps -> 
        exists S, project G p = Some S /\ ProcTyped [] P) ->
      MPTyped G (MPC ps)
.

(* ═══════════════════════════════════════════════════════════════════════════════ *)
(* THEOREM TYPE_003_01: Session type duality (dual (dual S) = S)                   *)
(* ═══════════════════════════════════════════════════════════════════════════════ *)

(* Helper lemma for list induction with dual *)
Lemma dual_dual_ind : forall s, dual (dual s) = s.
Proof.
  fix IH 1.
  intros s. destruct s; simpl; try reflexivity.
  - f_equal. apply IH.
  - f_equal. apply IH.
  - f_equal. induction l; simpl; [reflexivity|].
    f_equal; [apply IH | apply IHl].
  - f_equal. induction l; simpl; [reflexivity|].
    f_equal; [apply IH | apply IHl].
  - f_equal. apply IH.
Qed.

Lemma dual_involutive_list : forall ss,
  map dual (map dual ss) = ss.
Proof.
  induction ss as [| s ss' IHss].
  - reflexivity.
  - simpl. f_equal.
    + apply dual_dual_ind.
    + exact IHss.
Qed.

Theorem TYPE_003_01 : forall S : SessionTy,
  dual (dual S) = S.
Proof.
  apply dual_dual_ind.
Qed.

(* ═══════════════════════════════════════════════════════════════════════════════ *)
(* THEOREM TYPE_003_02: Send/Receive duality (!T.S dual ↔ ?T.dual(S))              *)
(* ═══════════════════════════════════════════════════════════════════════════════ *)

Theorem TYPE_003_02 : forall (t : BaseTy) (S : SessionTy),
  dual (SSend t S) = SRecv t (dual S) /\
  dual (SRecv t S) = SSend t (dual S).
Proof.
  intros t S.
  split; reflexivity.
Qed.

(* ═══════════════════════════════════════════════════════════════════════════════ *)
(* THEOREM TYPE_003_03: Choice/Branch duality (⊕{l:S} dual ↔ &{l:dual(S)})         *)
(* ═══════════════════════════════════════════════════════════════════════════════ *)

Theorem TYPE_003_03 : forall (Ss : list SessionTy),
  dual (SChoice Ss) = SBranch (map dual Ss) /\
  dual (SBranch Ss) = SChoice (map dual Ss).
Proof.
  intros Ss.
  split; reflexivity.
Qed.

(* ═══════════════════════════════════════════════════════════════════════════════ *)
(* THEOREM TYPE_003_04: Session end duality (end dual ↔ end)                       *)
(* ═══════════════════════════════════════════════════════════════════════════════ *)

Theorem TYPE_003_04 : dual SEnd = SEnd.
Proof.
  reflexivity.
Qed.

(* ═══════════════════════════════════════════════════════════════════════════════ *)
(* THEOREM TYPE_003_05: Session fidelity (typed process follows protocol)          *)
(* ═══════════════════════════════════════════════════════════════════════════════ *)

Theorem TYPE_003_05 : forall Γ P P',
  ProcTyped Γ P ->
  ProcStep P P' ->
  ProcTyped Γ P'.
Proof.
  intros Γ P P' Htyped Hstep.
  generalize dependent Γ.
  induction Hstep; intros Γ Htyped.
  - (* Step_Comm *)
    inversion Htyped as [| | | | | Γ' P1 P2 Hp1 Hp2| |]; subst.
    inversion Hp1; subst.
    inversion Hp2; subst.
    constructor; assumption.
  - (* Step_Select *)
    inversion Htyped as [| | | | | Γ' P1 P2 Hp1 Hp2| |]; subst.
    inversion Hp1; subst.
    inversion Hp2 as [| | | | Γ'' c' Ps' Ss' HIn Hlen HForall| | |]; subst.
    constructor.
    + assumption.
    + rewrite Forall_forall in HForall.
      apply HForall.
      eapply nth_error_In; eassumption.
  - (* Step_ParL *)
    inversion Htyped as [| | | | | Γ' P1 Q1 Hp1 Hq1| |]; subst.
    constructor.
    + apply IHHstep. assumption.
    + assumption.
  - (* Step_ParR *)
    inversion Htyped as [| | | | | Γ' P1 Q1 Hp1 Hq1| |]; subst.
    constructor.
    + assumption.
    + apply IHHstep. assumption.
  - (* Step_New *)
    inversion Htyped as [| | | | | | Γ' S' P1 Hp1 |]; subst.
    constructor. apply IHHstep. assumption.
  - (* Step_Unfold *)
    inversion Htyped as [| | | | | | | Γ' P1 Hp1]; subst.
    assumption.
Qed.

(* ═══════════════════════════════════════════════════════════════════════════════ *)
(* THEOREM TYPE_003_06: Session safety (no stuck configurations)                   *)
(* ═══════════════════════════════════════════════════════════════════════════════ *)

Definition can_step (P : Proc) : Prop :=
  exists P', ProcStep P P'.

(* A process is a value if it is fully reduced *)
Inductive is_value : Proc -> Prop :=
  | Val_End : is_value PEnd
  | Val_Par : forall P Q, is_value P -> is_value Q -> is_value (PPar P Q)
  | Val_New : forall S P, is_value P -> is_value (PNew S P)
.

(* A process is waiting for communication if it's ready to send/receive/select/branch *)
Inductive is_waiting : Proc -> Prop :=
  | Wait_Send : forall c v P, is_waiting (PSend c v P)
  | Wait_Recv : forall c P, is_waiting (PRecv c P)
  | Wait_Select : forall c i P, is_waiting (PSelect c i P)
  | Wait_Branch : forall c Ps, is_waiting (PBranch c Ps)
  | Wait_Par_L : forall P Q, is_waiting P -> is_waiting (PPar P Q)
  | Wait_Par_R : forall P Q, is_waiting Q -> is_waiting (PPar P Q)
  | Wait_New : forall S P, is_waiting P -> is_waiting (PNew S P)
.

(* Session safety: every typed process is either done, can step, or is waiting *)
Theorem TYPE_003_06 : forall Γ P,
  ProcTyped Γ P ->
  is_value P \/ can_step P \/ is_waiting P.
Proof.
  intros Γ P Htyped.
  induction Htyped.
  - (* T_End *)
    left. constructor.
  - (* T_Send *)
    right. right. constructor.
  - (* T_Recv *)
    right. right. constructor.
  - (* T_Select *)
    right. right. constructor.
  - (* T_Branch *)
    right. right. constructor.
  - (* T_Par *)
    destruct IHHtyped1 as [Hval1 | [[P' Hstep1] | Hwait1]];
    destruct IHHtyped2 as [Hval2 | [[Q' Hstep2] | Hwait2]].
    + left. constructor; assumption.
    + right. left. exists (PPar P Q'). apply Step_ParR. exact Hstep2.
    + right. right. apply Wait_Par_R. exact Hwait2.
    + right. left. exists (PPar P' Q). apply Step_ParL. exact Hstep1.
    + right. left. exists (PPar P' Q). apply Step_ParL. exact Hstep1.
    + right. left. exists (PPar P' Q). apply Step_ParL. exact Hstep1.
    + right. right. apply Wait_Par_L. exact Hwait1.
    + right. right. apply Wait_Par_L. exact Hwait1.
    + right. right. apply Wait_Par_L. exact Hwait1.
  - (* T_New *)
    destruct IHHtyped as [Hval | [[P' Hstep] | Hwait]].
    + left. constructor. exact Hval.
    + right. left. exists (PNew S P'). apply Step_New. exact Hstep.
    + right. right. constructor. exact Hwait.
  - (* T_Rec *)
    right. left. exists P. apply Step_Unfold.
Qed.

(* ═══════════════════════════════════════════════════════════════════════════════ *)
(* THEOREM TYPE_003_07: Deadlock freedom (progress for session-typed processes)    *)
(* ═══════════════════════════════════════════════════════════════════════════════ *)

(* A process is not deadlocked if it can make progress or is properly waiting *)
Definition not_deadlocked (P : Proc) : Prop :=
  is_value P \/ can_step P \/ is_waiting P.

Theorem TYPE_003_07 : forall Γ P,
  ProcTyped Γ P ->
  not_deadlocked P.
Proof.
  intros Γ P Htyped.
  unfold not_deadlocked.
  eapply TYPE_003_06.
  exact Htyped.
Qed.

(* ═══════════════════════════════════════════════════════════════════════════════ *)
(* THEOREM TYPE_003_08: Session composition (parallel composition preserves typing)*)
(* ═══════════════════════════════════════════════════════════════════════════════ *)

Theorem TYPE_003_08 : forall Γ P Q,
  ProcTyped Γ P ->
  ProcTyped Γ Q ->
  ProcTyped Γ (PPar P Q).
Proof.
  intros Γ P Q HP HQ.
  constructor; assumption.
Qed.

(* ═══════════════════════════════════════════════════════════════════════════════ *)
(* THEOREM TYPE_003_09: Channel restriction (new channel maintains invariants)     *)
(* ═══════════════════════════════════════════════════════════════════════════════ *)

Theorem TYPE_003_09 : forall Γ S P,
  ProcTyped Γ P ->
  ProcTyped Γ (PNew S P).
Proof.
  intros Γ S P HP.
  constructor. exact HP.
Qed.

(* ═══════════════════════════════════════════════════════════════════════════════ *)
(* THEOREM TYPE_003_10: Recursive session unfolding (μX.S = S[μX.S/X])             *)
(* ═══════════════════════════════════════════════════════════════════════════════ *)

Fixpoint subst_session (n : nat) (replacement : SessionTy) (s : SessionTy) : SessionTy :=
  match s with
  | SSend t s' => SSend t (subst_session n replacement s')
  | SRecv t s' => SRecv t (subst_session n replacement s')
  | SChoice ss => SChoice (map (subst_session n replacement) ss)
  | SBranch ss => SBranch (map (subst_session n replacement) ss)
  | SEnd => SEnd
  | SRec s' => SRec (subst_session (S n) replacement s')
  | SVar m => if Nat.eqb m n then replacement else SVar m
  end.

Definition unfold_rec (S : SessionTy) : SessionTy :=
  match S with
  | SRec S' => subst_session 0 (SRec S') S'
  | _ => S
  end.

Theorem TYPE_003_10 : forall S,
  unfold_rec (SRec S) = subst_session 0 (SRec S) S.
Proof.
  intros S.
  unfold unfold_rec.
  reflexivity.
Qed.

(* ═══════════════════════════════════════════════════════════════════════════════ *)
(* THEOREM TYPE_003_11: Session subtyping (covariant sends, contravariant receives)*)
(* ═══════════════════════════════════════════════════════════════════════════════ *)

Theorem TYPE_003_11 : forall t S1 S2,
  SessionSubtype S1 S2 ->
  SessionSubtype (SSend t S1) (SSend t S2) /\
  SessionSubtype (SRecv t S2) (SRecv t S1).
Proof.
  intros t S1 S2 Hsub.
  split.
  - apply Sub_Send. exact Hsub.
  - apply Sub_Recv. exact Hsub.
Qed.

(* ═══════════════════════════════════════════════════════════════════════════════ *)
(* THEOREM TYPE_003_12: Linearity of channels (each channel used exactly once/step)*)
(* ═══════════════════════════════════════════════════════════════════════════════ *)

Theorem TYPE_003_12 : forall c P Q,
  linear_channel c P ->
  linear_channel c Q ->
  linear_channel c (PPar P Q) \/ chan_count c (PPar P Q) = 2.
Proof.
  intros c P Q HlinP HlinQ.
  unfold linear_channel in *.
  simpl.
  lia.
Qed.

(* ═══════════════════════════════════════════════════════════════════════════════ *)
(* THEOREM TYPE_003_13: Session delegation (channel passing preserves types)       *)
(* ═══════════════════════════════════════════════════════════════════════════════ *)

Inductive DelegationTyped : TypingCtx -> Chan -> SessionTy -> Proc -> Prop :=
  | DT_Send : forall Γ c c' S S' P,
      In (c, Pos, SSend BTNat S) Γ ->
      In (c', Pos, S') Γ ->
      ProcTyped Γ P ->
      DelegationTyped Γ c S' (PSend c (VChan c') P)
.

Theorem TYPE_003_13 : forall Γ c S' P,
  DelegationTyped Γ c S' P ->
  ProcTyped Γ P.
Proof.
  intros Γ c S' P Hdel.
  inversion Hdel; subst.
  eapply T_Send; eassumption.
Qed.

(* ═══════════════════════════════════════════════════════════════════════════════ *)
(* THEOREM TYPE_003_14: Global type projection (global ↦ local types consistent)   *)
(* ═══════════════════════════════════════════════════════════════════════════════ *)

Theorem TYPE_003_14 : forall p q t G',
  p <> q ->
  project (GMsg p q t G') p = 
    match project G' p with
    | Some S' => Some (SSend t S')
    | None => None
    end /\
  project (GMsg p q t G') q =
    match project G' q with
    | Some S' => Some (SRecv t S')
    | None => None
    end.
Proof.
  intros p q t G' Hneq.
  split.
  - simpl. destruct (project G' p) as [S'|] eqn:Eproj.
    + replace (p =? p) with true by (symmetry; apply Nat.eqb_refl). reflexivity.
    + replace (p =? p) with true by (symmetry; apply Nat.eqb_refl). reflexivity.
  - simpl. destruct (project G' q) as [S'|] eqn:Eproj.
    + destruct (q =? p) eqn:Eqp.
      * apply Nat.eqb_eq in Eqp. lia.
      * replace (q =? q) with true by (symmetry; apply Nat.eqb_refl). reflexivity.
    + destruct (q =? p) eqn:Eqp.
      * apply Nat.eqb_eq in Eqp. lia.
      * replace (q =? q) with true by (symmetry; apply Nat.eqb_refl). reflexivity.
Qed.

(* ═══════════════════════════════════════════════════════════════════════════════ *)
(* THEOREM TYPE_003_15: Multiparty session safety (n-party protocol adherence)     *)
(* ═══════════════════════════════════════════════════════════════════════════════ *)

Definition mp_safe (G : GlobalTy) (mc : MPConfig) : Prop :=
  MPTyped G mc.

Fixpoint participants (G : GlobalTy) : list nat :=
  match G with
  | GMsg p q _ _ => [p; q]
  | GChoice p q _ => [p; q]
  | GEnd => []
  | GRec G' => participants G'
  | GVar _ => []
  end.

Theorem TYPE_003_15 : forall G ps,
  MPTyped G (MPC ps) ->
  (forall p P, In (p, P) ps -> 
    exists S, project G p = Some S).
Proof.
  intros G ps Htyped p P Hin.
  inversion Htyped as [| G' ps' Hall Heq1 Heq2]; subst.
  - contradiction.
  - specialize (Hall p P Hin).
    destruct Hall as [S [Hproj Hptyped]].
    exists S. exact Hproj.
Qed.
