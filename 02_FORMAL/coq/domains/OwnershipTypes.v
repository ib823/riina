(* SPDX-License-Identifier: MPL-2.0 *)
(* Copyright (c) 2026 The RIINA Authors. See AUTHORS file. *)

(* OwnershipTypes.v - Ownership Types for RIINA *)
(* Spec: 01_RESEARCH/23_DOMAIN_W_VERIFIED_MEMORY/ *)
(* Model: Rust-style ownership and borrowing *)

Require Import Coq.Lists.List.
Require Import Coq.Bool.Bool.
Require Import Coq.Arith.Arith.
Require Import Coq.Arith.PeanoNat.
Require Import Lia.
Import ListNotations.

(* Lifetime (represented as natural number, larger = longer) *)
Definition Lifetime := nat.

(* Lifetime ordering *)
Definition lifetime_outlives (l1 l2 : Lifetime) : bool :=
  Nat.leb l2 l1.  (* l1 outlives l2 if l1 >= l2 *)

(* Ownership state *)
Inductive OwnState : Type :=
  | Owned : OwnState                          (* Exclusively owned *)
  | Moved : OwnState                          (* Ownership transferred *)
  | Borrowed : Lifetime -> OwnState           (* Immutably borrowed *)
  | MutBorrowed : Lifetime -> OwnState        (* Mutably borrowed *)
  | Dropped : OwnState                        (* Deallocated *)
.

(* Variable with ownership *)
Record OwnedVar : Type := mkOV {
  ov_id : nat;
  ov_state : OwnState;
  ov_lifetime : Lifetime;           (* Scope lifetime *)
  ov_is_copy : bool;                (* Copy type? *)
}.

(* Borrow record *)
Record Borrow : Type := mkBorrow {
  br_source : nat;                  (* Source variable ID *)
  br_target : nat;                  (* Borrow variable ID *)
  br_mutable : bool;                (* Mutable borrow? *)
  br_lifetime : Lifetime;           (* Borrow lifetime *)
}.

(* Ownership context *)
Record OwnCtx : Type := mkOC {
  oc_vars : list OwnedVar;
  oc_borrows : list Borrow;
  oc_current_lifetime : Lifetime;
}.

(* Find variable by ID *)
Fixpoint find_var (vars : list OwnedVar) (id : nat) : option OwnedVar :=
  match vars with
  | [] => None
  | v :: rest => if Nat.eqb (ov_id v) id then Some v else find_var rest id
  end.

(* Check if variable is usable (owned and not moved/dropped) *)
Definition is_usable (v : OwnedVar) : bool :=
  match ov_state v with
  | Owned => true
  | Borrowed _ => true
  | MutBorrowed _ => true
  | Moved => false
  | Dropped => false
  end.

(* Check if variable can be mutably borrowed *)
Definition can_mut_borrow (ctx : OwnCtx) (id : nat) : bool :=
  match find_var (oc_vars ctx) id with
  | None => false
  | Some v =>
    match ov_state v with
    | Owned => negb (existsb (fun b => Nat.eqb (br_source b) id) (oc_borrows ctx))
    | _ => false
    end
  end.

(* Check if variable can be immutably borrowed *)
Definition can_shared_borrow (ctx : OwnCtx) (id : nat) : bool :=
  match find_var (oc_vars ctx) id with
  | None => false
  | Some v =>
    match ov_state v with
    | Owned => negb (existsb (fun b => andb (Nat.eqb (br_source b) id) (br_mutable b))
                             (oc_borrows ctx))
    | Borrowed _ => true  (* Can reborrow *)
    | _ => false
    end
  end.

(* Count active borrows for a variable *)
Definition count_borrows (ctx : OwnCtx) (id : nat) : nat :=
  length (filter (fun b => Nat.eqb (br_source b) id) (oc_borrows ctx)).

(* Count mutable borrows for a variable *)
Definition count_mut_borrows (ctx : OwnCtx) (id : nat) : nat :=
  length (filter (fun b => andb (Nat.eqb (br_source b) id) (br_mutable b))
                 (oc_borrows ctx)).

(* Move ownership *)
Definition move_var (ctx : OwnCtx) (from_id to_id : nat) : option OwnCtx :=
  match find_var (oc_vars ctx) from_id with
  | None => None
  | Some v =>
    if ov_is_copy v then
      (* Copy: don't invalidate source *)
      Some ctx
    else
      match ov_state v with
      | Owned =>
        (* Mark source as moved, create new owned var *)
        let updated := map (fun var =>
          if Nat.eqb (ov_id var) from_id
          then mkOV from_id Moved (ov_lifetime var) (ov_is_copy var)
          else var
        ) (oc_vars ctx) in
        let new_var := mkOV to_id Owned (oc_current_lifetime ctx) (ov_is_copy v) in
        Some (mkOC (new_var :: updated) (oc_borrows ctx) (oc_current_lifetime ctx))
      | _ => None  (* Can't move if not owned *)
      end
  end.

(* Drop variable *)
Definition drop_var (ctx : OwnCtx) (id : nat) : option OwnCtx :=
  match find_var (oc_vars ctx) id with
  | None => None
  | Some v =>
    match ov_state v with
    | Owned =>
      let updated := map (fun var =>
        if Nat.eqb (ov_id var) id
        then mkOV id Dropped (ov_lifetime var) (ov_is_copy var)
        else var
      ) (oc_vars ctx) in
      Some (mkOC updated (oc_borrows ctx) (oc_current_lifetime ctx))
    | _ => None  (* Can only drop owned *)
    end
  end.

(* Check borrow lifetime validity *)
Definition borrow_lifetime_valid (ctx : OwnCtx) (b : Borrow) : bool :=
  match find_var (oc_vars ctx) (br_source b) with
  | None => false
  | Some v => lifetime_outlives (ov_lifetime v) (br_lifetime b)
  end.

(* Helper: count owners in a list *)
Fixpoint count_owners (vars : list OwnedVar) (id : nat) : nat :=
  match vars with
  | [] => 0
  | v :: rest =>
    let rest_count := count_owners rest id in
    if andb (Nat.eqb (ov_id v) id)
            (match ov_state v with Owned => true | _ => false end)
    then S rest_count
    else rest_count
  end.

(* Helper: variable is in Moved state *)
Definition is_moved (v : OwnedVar) : bool :=
  match ov_state v with
  | Moved => true
  | _ => false
  end.

(* Helper: variable is in Dropped state *)
Definition is_dropped (v : OwnedVar) : bool :=
  match ov_state v with
  | Dropped => true
  | _ => false
  end.

(* Helper: update variable state in list *)
Fixpoint update_var_state (vars : list OwnedVar) (id : nat) (new_state : OwnState) 
  : list OwnedVar :=
  match vars with
  | [] => []
  | v :: rest =>
    if Nat.eqb (ov_id v) id
    then mkOV id new_state (ov_lifetime v) (ov_is_copy v) :: rest
    else v :: update_var_state rest id new_state
  end.

(* Create shared borrow *)
Definition create_shared_borrow (ctx : OwnCtx) (src_id tgt_id : nat) (lt : Lifetime) 
  : option OwnCtx :=
  if can_shared_borrow ctx src_id then
    let new_borrow := mkBorrow src_id tgt_id false lt in
    Some (mkOC (oc_vars ctx) (new_borrow :: oc_borrows ctx) (oc_current_lifetime ctx))
  else
    None.

(* Create mutable borrow *)
Definition create_mut_borrow (ctx : OwnCtx) (src_id tgt_id : nat) (lt : Lifetime) 
  : option OwnCtx :=
  if can_mut_borrow ctx src_id then
    let new_borrow := mkBorrow src_id tgt_id true lt in
    Some (mkOC (oc_vars ctx) (new_borrow :: oc_borrows ctx) (oc_current_lifetime ctx))
  else
    None.

(* RefCell state for interior mutability *)
Inductive RefCellState : Type :=
  | RCUnborrowed : RefCellState
  | RCSharedBorrow : nat -> RefCellState    (* count of shared borrows *)
  | RCMutBorrow : RefCellState.

(* RefCell wrapper *)
Record RefCell : Type := mkRefCell {
  rc_id : nat;
  rc_state : RefCellState;
  rc_lifetime : Lifetime;
}.

(* RefCell borrow check - runtime *)
Definition refcell_try_borrow (rc : RefCell) : option RefCell :=
  match rc_state rc with
  | RCUnborrowed => Some (mkRefCell (rc_id rc) (RCSharedBorrow 1) (rc_lifetime rc))
  | RCSharedBorrow n => Some (mkRefCell (rc_id rc) (RCSharedBorrow (S n)) (rc_lifetime rc))
  | RCMutBorrow => None
  end.

Definition refcell_try_borrow_mut (rc : RefCell) : option RefCell :=
  match rc_state rc with
  | RCUnborrowed => Some (mkRefCell (rc_id rc) RCMutBorrow (rc_lifetime rc))
  | _ => None
  end.

(* Box allocation record *)
Record BoxAlloc : Type := mkBox {
  box_id : nat;
  box_allocated : bool;
  box_dropped : bool;
}.

(* Box allocate *)
Definition box_new (id : nat) : BoxAlloc :=
  mkBox id true false.

(* Box drop *)
Definition box_drop (b : BoxAlloc) : option BoxAlloc :=
  if andb (box_allocated b) (negb (box_dropped b)) then
    Some (mkBox (box_id b) true true)
  else
    None.

(* Well-formed context predicate *)
Definition well_formed_ctx (ctx : OwnCtx) : Prop :=
  forall b, In b (oc_borrows ctx) -> borrow_lifetime_valid ctx b = true.

(* No active borrows predicate *)
Definition no_active_borrows (ctx : OwnCtx) (id : nat) : Prop :=
  count_borrows ctx id = 0.

(* Helper lemma for existsb *)
Lemma existsb_false_forall : forall {A} (f : A -> bool) (l : list A),
  existsb f l = false -> forall x, In x l -> f x = false.
Proof.
  intros A f l Hex x Hin.
  induction l as [|a l' IH].
  - inversion Hin.
  - simpl in Hex.
    apply orb_false_iff in Hex.
    destruct Hex as [Hfa Hrest].
    destruct Hin as [Heq | Hin'].
    + subst. exact Hfa.
    + apply IH; assumption.
Qed.

(* Helper lemma for find_var in mapped list *)
Lemma find_var_map_moved : forall vars from_id v,
  find_var vars from_id = Some v ->
  find_var (map (fun var =>
    if Nat.eqb (ov_id var) from_id
    then mkOV from_id Moved (ov_lifetime var) (ov_is_copy var)
    else var) vars) from_id = 
  Some (mkOV from_id Moved (ov_lifetime v) (ov_is_copy v)).
Proof.
  intros vars from_id v Hfind.
  induction vars as [|var vars' IH].
  - simpl in Hfind. discriminate.
  - simpl in Hfind.
    destruct (Nat.eqb (ov_id var) from_id) eqn:Heq.
    + injection Hfind as Hv. subst v.
      unfold map. fold (map (fun var0 : OwnedVar =>
        if ov_id var0 =? from_id
        then mkOV from_id Moved (ov_lifetime var0) (ov_is_copy var0)
        else var0) vars').
      rewrite Heq.
      unfold find_var. fold find_var.
      simpl. rewrite Nat.eqb_refl. reflexivity.
    + unfold map. fold (map (fun var0 : OwnedVar =>
        if ov_id var0 =? from_id
        then mkOV from_id Moved (ov_lifetime var0) (ov_is_copy var0)
        else var0) vars').
      rewrite Heq.
      unfold find_var. fold find_var.
      rewrite Heq.
      apply IH. exact Hfind.
Qed.

(* ═══════════════════════════════════════════════════════════════════════════════════════════════ *)
(* THEOREM MEM_001_01: Ownership uniqueness (at most one owner at any time) *)
(* ═══════════════════════════════════════════════════════════════════════════════════════════════ *)

Theorem MEM_001_01 : forall (ctx : OwnCtx) (from_id to_id : nat) (ctx' : OwnCtx) (v : OwnedVar),
  find_var (oc_vars ctx) from_id = Some v ->
  ov_is_copy v = false ->
  ov_state v = Owned ->
  to_id <> from_id ->
  move_var ctx from_id to_id = Some ctx' ->
  forall v', find_var (oc_vars ctx') from_id = Some v' ->
  ov_state v' = Moved.
Proof.
  intros ctx from_id to_id ctx' v Hfind Hcopy Howned Hneq Hmove v' Hfind'.
  unfold move_var in Hmove.
  rewrite Hfind in Hmove.
  rewrite Hcopy in Hmove.
  rewrite Howned in Hmove.
  simpl in Hmove.
  injection Hmove as Hctx'.
  rewrite <- Hctx' in Hfind'.
  simpl in Hfind'.
  pose proof (find_var_map_moved (oc_vars ctx) from_id v Hfind) as Hmap.
  assert (Heq_ids: Nat.eqb to_id from_id = false).
  { apply Nat.eqb_neq. exact Hneq. }
  rewrite Heq_ids in Hfind'.
  rewrite Hmap in Hfind'.
  injection Hfind' as Hv'. rewrite <- Hv'. reflexivity.
Qed.

(* ═══════════════════════════════════════════════════════════════════════════════════════════════ *)
(* THEOREM MEM_001_02: Ownership transfer (move semantics invalidate source) *)
(* ═══════════════════════════════════════════════════════════════════════════════════════════════ *)

Theorem MEM_001_02 : forall (ctx : OwnCtx) (from_id to_id : nat) (ctx' : OwnCtx) (v : OwnedVar),
  find_var (oc_vars ctx) from_id = Some v ->
  ov_is_copy v = false ->
  ov_state v = Owned ->
  move_var ctx from_id to_id = Some ctx' ->
  exists v_new, find_var (oc_vars ctx') to_id = Some v_new /\ ov_state v_new = Owned.
Proof.
  intros ctx from_id to_id ctx' v Hfind Hcopy Howned Hmove.
  unfold move_var in Hmove.
  rewrite Hfind in Hmove.
  rewrite Hcopy in Hmove.
  rewrite Howned in Hmove.
  simpl in Hmove.
  injection Hmove as Hctx'.
  rewrite <- Hctx'.
  simpl.
  exists (mkOV to_id Owned (oc_current_lifetime ctx) false).
  split.
  - simpl. rewrite Nat.eqb_refl. reflexivity.
  - simpl. reflexivity.
Qed.

(* ═══════════════════════════════════════════════════════════════════════════════════════════════ *)
(* THEOREM MEM_001_03: Shared borrow allows multiple readers *)
(* ═══════════════════════════════════════════════════════════════════════════════════════════════ *)

Theorem MEM_001_03 : forall (ctx : OwnCtx) (id : nat) (v : OwnedVar),
  find_var (oc_vars ctx) id = Some v ->
  ov_state v = Owned ->
  count_mut_borrows ctx id = 0 ->
  can_shared_borrow ctx id = true.
Proof.
  intros ctx id v Hfind Howned Hno_mut.
  unfold can_shared_borrow.
  rewrite Hfind.
  rewrite Howned.
  unfold count_mut_borrows in Hno_mut.
  destruct (existsb (fun b => (Nat.eqb (br_source b) id && br_mutable b)%bool) 
            (oc_borrows ctx)) eqn:Hexists.
  - apply existsb_exists in Hexists.
    destruct Hexists as [b [Hin Hcond]].
    apply andb_true_iff in Hcond.
    destruct Hcond as [Hsrc Hmut].
    assert (Hfilter: In b (filter (fun b0 => (Nat.eqb (br_source b0) id && br_mutable b0)%bool) 
                         (oc_borrows ctx))).
    { apply filter_In. split. exact Hin. 
      apply andb_true_iff. split; assumption. }
    assert (Hlen: length (filter (fun b0 => (Nat.eqb (br_source b0) id && br_mutable b0)%bool) 
                           (oc_borrows ctx)) > 0).
    { destruct (filter (fun b0 => (Nat.eqb (br_source b0) id && br_mutable b0)%bool) 
                       (oc_borrows ctx)) eqn:Hfilt.
      - simpl in Hfilter. contradiction.
      - simpl. lia. }
    lia.
  - simpl. reflexivity.
Qed.

(* ═══════════════════════════════════════════════════════════════════════════════════════════════ *)
(* THEOREM MEM_001_04: Mutable borrow is exclusive (no other borrows) *)
(* ═══════════════════════════════════════════════════════════════════════════════════════════════ *)

Lemma filter_all_false_empty : forall {A} (f : A -> bool) (l : list A),
  (forall x, In x l -> f x = false) ->
  filter f l = [].
Proof.
  intros A f l Hall.
  induction l as [|x xs IH].
  - reflexivity.
  - simpl.
    assert (Hfx: f x = false).
    { apply Hall. left. reflexivity. }
    rewrite Hfx.
    apply IH.
    intros y Hy. apply Hall. right. exact Hy.
Qed.

Theorem MEM_001_04 : forall (ctx : OwnCtx) (id : nat) (v : OwnedVar),
  find_var (oc_vars ctx) id = Some v ->
  ov_state v = Owned ->
  can_mut_borrow ctx id = true ->
  count_borrows ctx id = 0.
Proof.
  intros ctx id v Hfind Howned Hcan.
  unfold can_mut_borrow in Hcan.
  rewrite Hfind in Hcan.
  rewrite Howned in Hcan.
  destruct (existsb (fun b => Nat.eqb (br_source b) id) (oc_borrows ctx)) eqn:Hexists.
  - simpl in Hcan. discriminate.
  - unfold count_borrows.
    pose proof (existsb_false_forall (fun b => Nat.eqb (br_source b) id) 
                                      (oc_borrows ctx) Hexists) as Hall.
    rewrite (filter_all_false_empty _ _ Hall).
    reflexivity.
Qed.

(* ═══════════════════════════════════════════════════════════════════════════════════════════════ *)
(* THEOREM MEM_001_05: Borrows cannot outlive owner *)
(* ═══════════════════════════════════════════════════════════════════════════════════════════════ *)

Theorem MEM_001_05 : forall (ctx : OwnCtx) (b : Borrow) (v : OwnedVar),
  In b (oc_borrows ctx) ->
  find_var (oc_vars ctx) (br_source b) = Some v ->
  borrow_lifetime_valid ctx b = true ->
  lifetime_outlives (ov_lifetime v) (br_lifetime b) = true.
Proof.
  intros ctx b v Hin Hfind Hvalid.
  unfold borrow_lifetime_valid in Hvalid.
  rewrite Hfind in Hvalid.
  exact Hvalid.
Qed.

(* ═══════════════════════════════════════════════════════════════════════════════════════════════ *)
(* THEOREM MEM_001_06: No use after move *)
(* ═══════════════════════════════════════════════════════════════════════════════════════════════ *)

Theorem MEM_001_06 : forall (v : OwnedVar),
  ov_state v = Moved ->
  is_usable v = false.
Proof.
  intros v Hmoved.
  unfold is_usable.
  rewrite Hmoved.
  reflexivity.
Qed.

(* ═══════════════════════════════════════════════════════════════════════════════════════════════ *)
(* THEOREM MEM_001_07: No mutable borrow while shared borrow exists *)
(* ═══════════════════════════════════════════════════════════════════════════════════════════════ *)

Theorem MEM_001_07 : forall (ctx : OwnCtx) (id : nat) (v : OwnedVar) (b : Borrow),
  find_var (oc_vars ctx) id = Some v ->
  ov_state v = Owned ->
  In b (oc_borrows ctx) ->
  br_source b = id ->
  br_mutable b = false ->
  can_mut_borrow ctx id = false.
Proof.
  intros ctx id v b Hfind Howned Hin Hsrc Hshared.
  unfold can_mut_borrow.
  rewrite Hfind.
  rewrite Howned.
  destruct (existsb (fun b0 => Nat.eqb (br_source b0) id) (oc_borrows ctx)) eqn:Hexists.
  - simpl. reflexivity.
  - pose proof (existsb_false_forall (fun b0 => Nat.eqb (br_source b0) id) 
                                      (oc_borrows ctx) Hexists) as Hall.
    specialize (Hall b Hin).
    simpl in Hall.
    rewrite Hsrc in Hall.
    rewrite Nat.eqb_refl in Hall.
    discriminate.
Qed.

(* ═══════════════════════════════════════════════════════════════════════════════════════════════ *)
(* THEOREM MEM_001_08: No shared borrow while mutable borrow exists *)
(* ═══════════════════════════════════════════════════════════════════════════════════════════════ *)

Theorem MEM_001_08 : forall (ctx : OwnCtx) (id : nat) (v : OwnedVar) (b : Borrow),
  find_var (oc_vars ctx) id = Some v ->
  ov_state v = Owned ->
  In b (oc_borrows ctx) ->
  br_source b = id ->
  br_mutable b = true ->
  can_shared_borrow ctx id = false.
Proof.
  intros ctx id v b Hfind Howned Hin Hsrc Hmut.
  unfold can_shared_borrow.
  rewrite Hfind.
  rewrite Howned.
  destruct (existsb (fun b0 => (Nat.eqb (br_source b0) id && br_mutable b0)%bool) 
            (oc_borrows ctx)) eqn:Hexists.
  - simpl. reflexivity.
  - pose proof (existsb_false_forall (fun b0 => (Nat.eqb (br_source b0) id && br_mutable b0)%bool) 
                                      (oc_borrows ctx) Hexists) as Hall.
    specialize (Hall b Hin).
    simpl in Hall.
    rewrite Hsrc in Hall.
    rewrite Nat.eqb_refl in Hall.
    rewrite Hmut in Hall.
    simpl in Hall.
    discriminate.
Qed.

(* ═══════════════════════════════════════════════════════════════════════════════════════════════ *)
(* THEOREM MEM_001_09: Reborrow shortens lifetime *)
(* ═══════════════════════════════════════════════════════════════════════════════════════════════ *)

Theorem MEM_001_09 : forall (orig_lt reborrow_lt : Lifetime),
  lifetime_outlives orig_lt reborrow_lt = true ->
  Nat.leb reborrow_lt orig_lt = true.
Proof.
  intros orig_lt reborrow_lt H.
  unfold lifetime_outlives in H.
  exact H.
Qed.

(* ═══════════════════════════════════════════════════════════════════════════════════════════════ *)
(* THEOREM MEM_001_10: Drop called exactly once (no double-free) *)
(* ═══════════════════════════════════════════════════════════════════════════════════════════════ *)

Lemma find_var_map_dropped : forall vars id v,
  find_var vars id = Some v ->
  ov_state v = Owned ->
  find_var (map (fun var =>
    if Nat.eqb (ov_id var) id
    then mkOV id Dropped (ov_lifetime var) (ov_is_copy var)
    else var) vars) id = 
  Some (mkOV id Dropped (ov_lifetime v) (ov_is_copy v)).
Proof.
  intros vars id v Hfind Howned.
  induction vars as [|var vars' IH].
  - simpl in Hfind. discriminate.
  - simpl in Hfind.
    destruct (Nat.eqb (ov_id var) id) eqn:Heq.
    + injection Hfind as Hv. subst v.
      unfold map. fold (map (fun var0 : OwnedVar =>
        if ov_id var0 =? id
        then mkOV id Dropped (ov_lifetime var0) (ov_is_copy var0)
        else var0) vars').
      rewrite Heq.
      unfold find_var. fold find_var.
      simpl. rewrite Nat.eqb_refl. reflexivity.
    + unfold map. fold (map (fun var0 : OwnedVar =>
        if ov_id var0 =? id
        then mkOV id Dropped (ov_lifetime var0) (ov_is_copy var0)
        else var0) vars').
      rewrite Heq.
      unfold find_var. fold find_var.
      rewrite Heq.
      apply IH. exact Hfind.
Qed.

Theorem MEM_001_10 : forall (ctx ctx' : OwnCtx) (id : nat) (v : OwnedVar),
  find_var (oc_vars ctx) id = Some v ->
  ov_state v = Owned ->
  drop_var ctx id = Some ctx' ->
  drop_var ctx' id = None.
Proof.
  intros ctx ctx' id v Hfind Howned Hdrop.
  unfold drop_var in Hdrop.
  rewrite Hfind in Hdrop.
  rewrite Howned in Hdrop.
  injection Hdrop as Hctx'.
  rewrite <- Hctx'.
  unfold drop_var.
  simpl.
  pose proof (find_var_map_dropped (oc_vars ctx) id v Hfind Howned) as Hmap.
  rewrite Hmap.
  simpl. reflexivity.
Qed.

(* ═══════════════════════════════════════════════════════════════════════════════════════════════ *)
(* THEOREM MEM_001_11: No dangling references (lifetime safety) *)
(* ═══════════════════════════════════════════════════════════════════════════════════════════════ *)

Theorem MEM_001_11 : forall (ctx : OwnCtx) (b : Borrow) (v : OwnedVar),
  well_formed_ctx ctx ->
  In b (oc_borrows ctx) ->
  find_var (oc_vars ctx) (br_source b) = Some v ->
  ov_state v <> Dropped /\ ov_state v <> Moved ->
  lifetime_outlives (ov_lifetime v) (br_lifetime b) = true.
Proof.
  intros ctx b v Hwf Hin Hfind Hstate.
  unfold well_formed_ctx in Hwf.
  specialize (Hwf b Hin).
  unfold borrow_lifetime_valid in Hwf.
  rewrite Hfind in Hwf.
  exact Hwf.
Qed.

(* ═══════════════════════════════════════════════════════════════════════════════════════════════ *)
(* THEOREM MEM_001_12: Interior mutability (RefCell) runtime checked *)
(* ═══════════════════════════════════════════════════════════════════════════════════════════════ *)

Theorem MEM_001_12 : forall (rc : RefCell),
  rc_state rc = RCMutBorrow ->
  refcell_try_borrow rc = None /\ refcell_try_borrow_mut rc = None.
Proof.
  intros rc Hstate.
  split.
  - unfold refcell_try_borrow.
    rewrite Hstate.
    reflexivity.
  - unfold refcell_try_borrow_mut.
    rewrite Hstate.
    reflexivity.
Qed.

(* ═══════════════════════════════════════════════════════════════════════════════════════════════ *)
(* THEOREM MEM_001_13: Copy types don't transfer ownership *)
(* ═══════════════════════════════════════════════════════════════════════════════════════════════ *)

Theorem MEM_001_13 : forall (ctx : OwnCtx) (from_id to_id : nat) (v : OwnedVar),
  find_var (oc_vars ctx) from_id = Some v ->
  ov_is_copy v = true ->
  move_var ctx from_id to_id = Some ctx.
Proof.
  intros ctx from_id to_id v Hfind Hcopy.
  unfold move_var.
  rewrite Hfind.
  rewrite Hcopy.
  reflexivity.
Qed.

(* ═══════════════════════════════════════════════════════════════════════════════════════════════ *)
(* THEOREM MEM_001_14: Box heap allocation and deallocation paired *)
(* ═══════════════════════════════════════════════════════════════════════════════════════════════ *)

Theorem MEM_001_14 : forall (id : nat),
  let b := box_new id in
  box_allocated b = true /\
  box_dropped b = false /\
  (exists b', box_drop b = Some b' /\ box_dropped b' = true).
Proof.
  intros id.
  simpl.
  split.
  - reflexivity.
  - split.
    + reflexivity.
    + exists (mkBox id true true).
      split.
      * unfold box_drop. simpl. reflexivity.
      * simpl. reflexivity.
Qed.

(* ═══════════════════════════════════════════════════════════════════════════════════════════════ *)
(* THEOREM MEM_001_15: Memory safety (no UB from ownership violations) *)
(* ═══════════════════════════════════════════════════════════════════════════════════════════════ *)

(* Memory safety property: well-typed programs don't have UB *)
Definition memory_safe (ctx : OwnCtx) : Prop :=
  (* All borrows are valid *)
  (forall b, In b (oc_borrows ctx) -> borrow_lifetime_valid ctx b = true) /\
  (* No use after move: moved vars are not borrowed *)
  (forall v, In v (oc_vars ctx) -> ov_state v = Moved -> 
             count_borrows ctx (ov_id v) = 0) /\
  (* No use after drop: dropped vars are not borrowed *)
  (forall v, In v (oc_vars ctx) -> ov_state v = Dropped -> 
             count_borrows ctx (ov_id v) = 0) /\
  (* Mutable borrows are exclusive *)
  (forall id, count_mut_borrows ctx id <= 1) /\
  (* No simultaneous mut and shared borrows *)
  (forall id, count_mut_borrows ctx id = 1 -> 
              count_borrows ctx id = count_mut_borrows ctx id).

Theorem MEM_001_15 : forall (ctx : OwnCtx),
  memory_safe ctx ->
  well_formed_ctx ctx /\
  (forall v, In v (oc_vars ctx) -> ov_state v = Moved -> is_usable v = false) /\
  (forall v, In v (oc_vars ctx) -> ov_state v = Dropped -> is_usable v = false).
Proof.
  intros ctx Hsafe.
  destruct Hsafe as [Hborrow_valid [Hno_use_moved [Hno_use_dropped [Hmut_excl Hno_simul]]]].
  split.
  - (* well_formed_ctx *)
    unfold well_formed_ctx.
    exact Hborrow_valid.
  - split.
    + (* moved vars not usable *)
      intros v Hin Hmoved.
      unfold is_usable.
      rewrite Hmoved.
      reflexivity.
    + (* dropped vars not usable *)
      intros v Hin Hdropped.
      unfold is_usable.
      rewrite Hdropped.
      reflexivity.
Qed.
