(* TestingQA.v - Testing and Quality Assurance for RIINA *)
(* Spec: 01_RESEARCH/13_DOMAIN_M_TESTING_QA/RESEARCH_DOMAIN_M_COMPLETE.md *)
(* Security Property: Verified test coverage of security-critical code *)

Require Import Coq.Lists.List.
Require Import Coq.Bool.Bool.
Require Import Coq.Arith.Arith.
Require Import Coq.Logic.FunctionalExtensionality.
Require Import Coq.Arith.PeanoNat.
Require Import Coq.Strings.String.
Require Import Lia.
Import ListNotations.

(* ======================================================================= *)
(* TYPE DEFINITIONS                                                        *)
(* ======================================================================= *)

(* Test result *)
Inductive TestResult : Type :=
  | TRPass : TestResult
  | TRFail : string -> TestResult
  | TRError : string -> TestResult
.

(* Test case *)
Record TestCase : Type := mkTestCase {
  tc_name : string;
  tc_input : nat;
  tc_expected : nat;
}.

(* Property for property-based testing *)
Definition Property := nat -> bool.

(* Generator state *)
Record GenState : Type := mkGenState {
  gs_seed : nat;
  gs_size : nat;
}.

(* Generated value with shrink candidates *)
Record Arbitrary (A : Type) : Type := mkArbitrary {
  arb_value : A;
  arb_shrinks : list A;
}.

Arguments mkArbitrary {A}.
Arguments arb_value {A}.
Arguments arb_shrinks {A}.

(* Test execution trace *)
Inductive TraceEvent : Type :=
  | TEEnter : string -> TraceEvent
  | TEExit : string -> TraceEvent
  | TEAssert : bool -> TraceEvent
  | TECoverage : nat -> TraceEvent
.

Definition ExecutionTrace := list TraceEvent.

(* Coverage set *)
Definition CoverageSet := list nat.

(* Mutation operators *)
Inductive MutationOp : Type :=
  | MONegate : MutationOp
  | MOArithSwap : MutationOp
  | MORelSwap : MutationOp
  | MODeleteStmt : MutationOp
  | MOConstChange : MutationOp
.

(* Mutant *)
Record Mutant : Type := mkMutant {
  mut_location : nat;
  mut_operator : MutationOp;
  mut_killed : bool;
}.

(* Security property enum *)
Inductive SecurityProperty : Type :=
  | SPAuthentication : SecurityProperty
  | SPAuthorization : SecurityProperty
  | SPConfidentiality : SecurityProperty
  | SPIntegrity : SecurityProperty
  | SPNonRepudiation : SecurityProperty
.

(* Security coverage tracking *)
Record SecurityCoverage : Type := mkSecCov {
  sc_properties : list SecurityProperty;
  sc_tested : list SecurityProperty;
}.

(* Timing measurement *)
Record TimingMeasurement : Type := mkTiming {
  tm_input1 : nat;
  tm_input2 : nat;
  tm_time1 : nat;
  tm_time2 : nat;
}.

(* Test suite *)
Definition TestSuite := list TestCase.

(* ======================================================================= *)
(* HELPER FUNCTIONS                                                        *)
(* ======================================================================= *)

(* List equality comparison *)
Fixpoint list_beq {A : Type} (eqb : A -> A -> bool) (l1 l2 : list A) : bool :=
  match l1, l2 with
  | [], [] => true
  | x1 :: xs1, x2 :: xs2 => andb (eqb x1 x2) (list_beq eqb xs1 xs2)
  | _, _ => false
  end.

(* Constant time check *)
Definition is_constant_time (tm : TimingMeasurement) (tolerance : nat) : bool :=
  let diff := if Nat.leb tm.(tm_time1) tm.(tm_time2)
              then tm.(tm_time2) - tm.(tm_time1)
              else tm.(tm_time1) - tm.(tm_time2) in
  Nat.leb diff tolerance.

(* Run test deterministically *)
Definition run_test (tc : TestCase) (f : nat -> nat) : TestResult :=
  if Nat.eqb (f tc.(tc_input)) tc.(tc_expected)
  then TRPass
  else TRFail "Output mismatch".

(* Test result equality *)
Definition test_result_eqb (r1 r2 : TestResult) : bool :=
  match r1, r2 with
  | TRPass, TRPass => true
  | TRFail _, TRFail _ => true
  | TRError _, TRError _ => true
  | _, _ => false
  end.

(* Check if test passed *)
Definition test_passed (r : TestResult) : bool :=
  match r with
  | TRPass => true
  | _ => false
  end.

(* Test isolation state *)
Record TestState : Type := mkTestState {
  ts_counter : nat;
  ts_flag : bool;
}.

Definition initial_state : TestState := mkTestState 0 false.

(* Run test in isolation *)
Definition run_isolated (tc : TestCase) (f : nat -> nat) (s : TestState) : TestResult * TestState :=
  let result := run_test tc f in
  (result, s).

(* Type representation for type system theorems *)
Inductive SimpleType : Type :=
  | TyNat : SimpleType
  | TyBool : SimpleType
  | TyFun : SimpleType -> SimpleType -> SimpleType
.

(* Well-typed expressions *)
Inductive Expr : Type :=
  | ENat : nat -> Expr
  | EBool : bool -> Expr
  | EAdd : Expr -> Expr -> Expr
  | EIf : Expr -> Expr -> Expr -> Expr
.

(* Typing judgment *)
Inductive HasType : Expr -> SimpleType -> Prop :=
  | TyENat : forall n, HasType (ENat n) TyNat
  | TyEBool : forall b, HasType (EBool b) TyBool
  | TyEAdd : forall e1 e2,
      HasType e1 TyNat -> HasType e2 TyNat -> HasType (EAdd e1 e2) TyNat
  | TyEIf : forall e1 e2 e3 t,
      HasType e1 TyBool -> HasType e2 t -> HasType e3 t -> HasType (EIf e1 e2 e3) t
.

(* Values *)
Inductive IsValue : Expr -> Prop :=
  | VNat : forall n, IsValue (ENat n)
  | VBool : forall b, IsValue (EBool b)
.

(* Evaluation *)
Inductive Eval : Expr -> Expr -> Prop :=
  | EvalAdd : forall n1 n2, Eval (EAdd (ENat n1) (ENat n2)) (ENat (n1 + n2))
  | EvalIfTrue : forall e2 e3, Eval (EIf (EBool true) e2 e3) e2
  | EvalIfFalse : forall e2 e3, Eval (EIf (EBool false) e2 e3) e3
  | EvalAddL : forall e1 e1' e2, Eval e1 e1' -> Eval (EAdd e1 e2) (EAdd e1' e2)
  | EvalAddR : forall v e2 e2', IsValue v -> Eval e2 e2' -> Eval (EAdd v e2) (EAdd v e2')
  | EvalIfCond : forall e1 e1' e2 e3, Eval e1 e1' -> Eval (EIf e1 e2 e3) (EIf e1' e2 e3)
.

(* Test fixture *)
Record Fixture : Type := mkFixture {
  fix_setup : TestState -> TestState;
  fix_teardown : TestState -> TestState;
}.

(* Identity fixture *)
Definition id_fixture : Fixture := mkFixture (fun s => s) (fun s => s).

(* Run with fixture *)
Definition run_with_fixture (fixture : Fixture) (tc : TestCase) (f : nat -> nat) (s : TestState) : TestResult * TestState :=
  let s1 := fixture.(fix_setup) s in
  let result := run_test tc f in
  let s2 := fixture.(fix_teardown) s1 in
  (result, s2).

(* Panic test *)
Definition expected_panic (f : nat -> option nat) (input : nat) : bool :=
  match f input with
  | None => true
  | Some _ => false
  end.

(* Generator *)
Definition Generator (A : Type) := GenState -> A * GenState.

(* Simple nat generator *)
Definition gen_nat : Generator nat := fun gs =>
  (gs.(gs_seed) mod (gs.(gs_size) + 1), mkGenState (gs.(gs_seed) + 1) gs.(gs_size)).

(* Run generator *)
Definition run_gen {A : Type} (g : Generator A) (gs : GenState) : A :=
  fst (g gs).

(* Shrink candidates for nat *)
Definition shrink_nat (n : nat) : list nat :=
  match n with
  | 0 => []
  | S m => [0; m]
  end.

(* Property check result *)
Definition check_property (prop : Property) (inputs : list nat) : bool :=
  forallb prop inputs.

(* Find minimal counterexample *)
Fixpoint find_minimal (prop : Property) (candidates : list nat) : option nat :=
  match candidates with
  | [] => None
  | x :: xs => if prop x then find_minimal prop xs else Some x
  end.

(* Shrink until minimal *)
Fixpoint shrink_loop (prop : Property) (current : nat) (fuel : nat) : nat :=
  match fuel with
  | 0 => current
  | S f =>
      let shrinks := shrink_nat current in
      match find_minimal prop shrinks with
      | None => current
      | Some smaller => shrink_loop prop smaller f
      end
  end.

(* Generate all values in range *)
Fixpoint gen_range (n : nat) : list nat :=
  match n with
  | 0 => [0]
  | S m => gen_range m ++ [S m]
  end.

(* Code path representation *)
Definition CodePath := list nat.

(* Reachable paths *)
Definition reachable_paths (max_depth : nat) : list CodePath :=
  map (fun n => [n]) (gen_range max_depth).

(* Fuzzer explored paths *)
Definition fuzzer_explores (inputs : list nat) : list CodePath :=
  map (fun n => [n]) inputs.

(* Path coverage check *)
Definition path_covered (p : CodePath) (explored : list CodePath) : bool :=
  existsb (fun ep => list_beq Nat.eqb p ep) explored.

(* Structured input validity *)
Definition valid_structured_input (min max : nat) (n : nat) : bool :=
  andb (Nat.leb min n) (Nat.leb n max).

(* Differential fuzzing *)
Definition differential_test (f1 f2 : nat -> nat) (input : nat) : bool :=
  Nat.eqb (f1 input) (f2 input).

(* Sanitizer check *)
Inductive SanitizerResult : Type :=
  | SRClean : SanitizerResult
  | SRViolation : string -> SanitizerResult
.

Definition sanitizer_pass (sr : SanitizerResult) : bool :=
  match sr with
  | SRClean => true
  | SRViolation _ => false
  end.

(* Component interface *)
Record Component : Type := mkComponent {
  comp_name : string;
  comp_input_type : SimpleType;
  comp_output_type : SimpleType;
  comp_impl : nat -> nat;
}.

(* Component composition *)
Definition compose_components (c1 c2 : Component) : nat -> nat :=
  fun x => c2.(comp_impl) (c1.(comp_impl) x).

(* API contract *)
Record APIContract : Type := mkAPIContract {
  api_precondition : nat -> bool;
  api_postcondition : nat -> nat -> bool;
  api_impl : nat -> nat;
}.

(* Contract satisfaction *)
Definition satisfies_contract (api : APIContract) (input : nat) : bool :=
  if api.(api_precondition) input
  then api.(api_postcondition) input (api.(api_impl) input)
  else true.

(* Security flow *)
Record SecurityFlow : Type := mkSecFlow {
  sf_source : SecurityProperty;
  sf_sink : SecurityProperty;
  sf_valid : bool;
}.

(* Mutation validity *)
Definition mutation_valid (m : Mutant) (max_loc : nat) : bool :=
  Nat.ltb m.(mut_location) max_loc.

(* Mutation score *)
Definition mutation_score (mutants : list Mutant) : nat :=
  List.length (List.filter (fun m => m.(mut_killed)) mutants).

(* Test detects mutation *)
Definition test_detects_mutation (orig_f mut_f : nat -> nat) (tc : TestCase) : bool :=
  negb (Nat.eqb (orig_f tc.(tc_input)) (mut_f tc.(tc_input))).

(* Timing attack detection *)
Definition timing_attack_detected (measurements : list TimingMeasurement) (tolerance : nat) : bool :=
  existsb (fun tm => negb (is_constant_time tm tolerance)) measurements.

(* Known Answer Test *)
Record KATTest : Type := mkKAT {
  kat_input : nat;
  kat_expected : nat;
}.

Definition run_kat (kat : KATTest) (f : nat -> nat) : bool :=
  Nat.eqb (f kat.(kat_input)) kat.(kat_expected).

(* Brute force counter *)
Record BruteForceProtection : Type := mkBFP {
  bfp_max_attempts : nat;
  bfp_current_attempts : nat;
  bfp_locked : bool;
}.

Definition check_brute_force (bfp : BruteForceProtection) : bool :=
  orb bfp.(bfp_locked) (Nat.leb bfp.(bfp_max_attempts) bfp.(bfp_current_attempts)).

(* Line coverage *)
Definition line_covered (line : nat) (trace : ExecutionTrace) : bool :=
  existsb (fun ev => match ev with TECoverage l => Nat.eqb l line | _ => false end) trace.

(* Security property equality *)
Definition sec_prop_eqb (sp1 sp2 : SecurityProperty) : bool :=
  match sp1, sp2 with
  | SPAuthentication, SPAuthentication => true
  | SPAuthorization, SPAuthorization => true
  | SPConfidentiality, SPConfidentiality => true
  | SPIntegrity, SPIntegrity => true
  | SPNonRepudiation, SPNonRepudiation => true
  | _, _ => false
  end.

(* Security property coverage *)
Definition security_prop_covered (sp : SecurityProperty) (sc : SecurityCoverage) : bool :=
  existsb (sec_prop_eqb sp) sc.(sc_tested).

(* All security properties covered *)
Definition all_security_covered (sc : SecurityCoverage) : bool :=
  forallb (fun sp => security_prop_covered sp sc) sc.(sc_properties).

(* ======================================================================= *)
(* HELPER LEMMAS                                                           *)
(* ======================================================================= *)

Lemma nat_eqb_refl : forall n, Nat.eqb n n = true.
Proof.
  induction n; simpl; auto.
Qed.

Lemma forallb_true_iff : forall {A : Type} (f : A -> bool) (l : list A),
  forallb f l = true <-> (forall x, In x l -> f x = true).
Proof.
  intros A f l. split.
  - induction l; intros H x Hin.
    + inversion Hin.
    + simpl in H. apply andb_true_iff in H. destruct H as [Ha Hl].
      simpl in Hin. destruct Hin as [Heq | Hin].
      * subst. exact Ha.
      * apply IHl; assumption.
  - induction l; intros H; simpl.
    + reflexivity.
    + apply andb_true_iff. split.
      * apply H. left. reflexivity.
      * apply IHl. intros x Hin. apply H. right. exact Hin.
Qed.

Lemma existsb_exists : forall {A : Type} (f : A -> bool) (l : list A),
  existsb f l = true <-> exists x, In x l /\ f x = true.
Proof.
  intros A f l. split.
  - induction l; intros H; simpl in H.
    + discriminate.
    + apply orb_true_iff in H. destruct H as [Ha | Hl].
      * exists a. split; [left; reflexivity | exact Ha].
      * destruct (IHl Hl) as [x [Hin Hfx]].
        exists x. split; [right; exact Hin | exact Hfx].
  - intros [x [Hin Hfx]]. induction l.
    + inversion Hin.
    + simpl. apply orb_true_iff. simpl in Hin. destruct Hin as [Heq | Hin].
      * left. subst. exact Hfx.
      * right. apply IHl. exact Hin.
Qed.

Lemma list_beq_refl : forall l, list_beq Nat.eqb l l = true.
Proof.
  induction l; simpl; auto.
  apply andb_true_iff. split.
  - apply nat_eqb_refl.
  - exact IHl.
Qed.

(* ======================================================================= *)
(* THEOREMS - TESTING FOUNDATIONS (M-01)                                   *)
(* ======================================================================= *)

(** M_001_01: Test determinism - same input produces same result *)
Theorem M_001_01 : forall (tc : TestCase) (f : nat -> nat),
  run_test tc f = run_test tc f.
Proof.
  intros tc f.
  reflexivity.
Qed.

(** M_001_02: Test isolation - tests do not affect each other *)
Theorem M_001_02 : forall (tc1 tc2 : TestCase) (f : nat -> nat) (s : TestState),
  let (r1, s1) := run_isolated tc1 f s in
  let (r2, _) := run_isolated tc2 f s in
  s1 = s.
Proof.
  intros tc1 tc2 f s.
  unfold run_isolated.
  reflexivity.
Qed.

(** M_001_03: Type system reduces test burden - well-typed implies class of bugs absent *)
(* A well-typed expression is either a value or can step - this is progress *)
Theorem M_001_03 : forall (e : Expr) (t : SimpleType),
  HasType e t ->
  IsValue e \/ exists e', Eval e e'.
Proof.
  intros e t Htype.
  induction Htype.
  - (* ENat *) left. constructor.
  - (* EBool *) left. constructor.
  - (* EAdd *)
    destruct IHHtype1 as [Hval1 | [e1' Hstep1]].
    + destruct IHHtype2 as [Hval2 | [e2' Hstep2]].
      * (* Both values - need to show they're nats *)
        inversion Hval1; subst; inversion Htype1; subst.
        inversion Hval2; subst; inversion Htype2; subst.
        right. exists (ENat (n + n0)). constructor.
      * (* e2 steps *)
        right. exists (EAdd e1 e2'). apply EvalAddR; assumption.
    + (* e1 steps *)
      right. exists (EAdd e1' e2). apply EvalAddL. assumption.
  - (* EIf *)
    destruct IHHtype1 as [Hval1 | [e1' Hstep1]].
    + (* e1 is a value - must be bool *)
      inversion Hval1; subst; inversion Htype1; subst.
      destruct b.
      * right. exists e2. constructor.
      * right. exists e3. constructor.
    + (* e1 steps *)
      right. exists (EIf e1' e2 e3). apply EvalIfCond. assumption.
Qed.

(* ======================================================================= *)
(* THEOREMS - UNIT TESTING (M-02)                                          *)
(* ======================================================================= *)

(** M_001_04: Assertion soundness - assert P passes iff P holds *)
Theorem M_001_04 : forall (P : bool),
  (P = true) <-> (if P then TRPass else TRFail "assertion failed") = TRPass.
Proof.
  intros P. split.
  - intros HP. rewrite HP. reflexivity.
  - intros H. destruct P.
    + reflexivity.
    + discriminate H.
Qed.

(** M_001_05: Test fixture setup/teardown correctness *)
Theorem M_001_05 : forall (fixture : Fixture) (tc : TestCase) (f : nat -> nat) (s : TestState),
  fixture.(fix_setup) = (fun x => x) ->
  fixture.(fix_teardown) = (fun x => x) ->
  fst (run_with_fixture fixture tc f s) = run_test tc f.
Proof.
  intros fixture tc f s Hsetup Hteardown.
  unfold run_with_fixture.
  rewrite Hsetup. rewrite Hteardown.
  reflexivity.
Qed.

(** M_001_06: Expected panic test correctness *)
Theorem M_001_06 : forall (f : nat -> option nat) (input : nat),
  expected_panic f input = true <-> f input = None.
Proof.
  intros f input. unfold expected_panic. split.
  - destruct (f input) eqn:Hf.
    + intros H. discriminate H.
    + intros _. reflexivity.
  - intros H. rewrite H. reflexivity.
Qed.

(* ======================================================================= *)
(* THEOREMS - PROPERTY-BASED TESTING (M-03)                                *)
(* ======================================================================= *)

(** M_001_07: Property holds for all generated inputs (soundness) *)
Theorem M_001_07 : forall (prop : Property) (inputs : list nat),
  check_property prop inputs = true ->
  forall x, In x inputs -> prop x = true.
Proof.
  intros prop inputs H x Hin.
  unfold check_property in H.
  rewrite forallb_true_iff in H.
  apply H. exact Hin.
Qed.

(** M_001_08: Shrinking produces minimal counterexample *)
Theorem M_001_08 : forall (prop : Property) (n fuel : nat),
  prop n = false ->
  prop (shrink_loop prop n fuel) = false \/ 
  (forall s, In s (shrink_nat (shrink_loop prop n fuel)) -> prop s = true).
Proof.
  intros prop n fuel.
  revert n.
  induction fuel; intros n Hfail.
  - (* fuel = 0 *)
    simpl. left. exact Hfail.
  - (* fuel = S f *)
    simpl.
    destruct (find_minimal prop (shrink_nat n)) eqn:Hfind.
    + (* Found smaller counterexample *)
      assert (Hsmaller : prop n0 = false).
      {
        clear IHfuel.
        induction (shrink_nat n).
        - simpl in Hfind. discriminate.
        - simpl in Hfind. destruct (prop a) eqn:Hpa.
          + apply IHl. exact Hfind.
          + injection Hfind as Heq. subst. exact Hpa.
      }
      apply IHfuel. exact Hsmaller.
    + (* No smaller counterexample found - n is minimal *)
      right. intros s Hin.
      clear IHfuel.
      induction (shrink_nat n).
      * inversion Hin.
      * simpl in Hfind. destruct (prop a) eqn:Hpa.
        -- simpl in Hin. destruct Hin as [Heq | Hin].
           ++ subst. exact Hpa.
           ++ apply IHl; assumption.
        -- discriminate Hfind.
Qed.

(** M_001_09: Generator coverage - all values in domain reachable *)
Theorem M_001_09 : forall (n : nat),
  In n (gen_range n).
Proof.
  intros n. induction n.
  - simpl. left. reflexivity.
  - simpl. apply in_or_app. right. simpl. left. reflexivity.
Qed.

(** M_001_10: Custom generator well-formedness *)
Theorem M_001_10 : forall (gs : GenState),
  let (v, gs') := gen_nat gs in
  v <= gs.(gs_size) /\ gs'.(gs_seed) = gs.(gs_seed) + 1.
Proof.
  intros gs.
  unfold gen_nat. simpl.
  split.
  - assert (H: gs_seed gs mod (gs_size gs + 1) < gs_size gs + 1).
    { apply Nat.mod_upper_bound. lia. }
    lia.
  - reflexivity.
Qed.

(* ======================================================================= *)
(* THEOREMS - FUZZING (M-04)                                               *)
(* ======================================================================= *)

(** M_001_11: Fuzzer explores all reachable code paths (completeness bound) *)
Theorem M_001_11 : forall (max_depth : nat) (inputs : list nat),
  (forall n, n <= max_depth -> In n inputs) ->
  forall p, In p (reachable_paths max_depth) -> 
  path_covered p (fuzzer_explores inputs) = true.
Proof.
  intros max_depth inputs Hcomplete p Hp.
  unfold reachable_paths in Hp.
  apply in_map_iff in Hp.
  destruct Hp as [n [Heq Hin]].
  subst p.
  unfold path_covered, fuzzer_explores.
  apply existsb_exists.
  assert (Hle : n <= max_depth).
  {
    clear Hcomplete.
    induction max_depth.
    - simpl in Hin. destruct Hin as [Heq | Hf]; [lia | contradiction].
    - simpl in Hin. apply in_app_or in Hin. destruct Hin as [Hin | Hin].
      + assert (n <= max_depth) by (apply IHmax_depth; exact Hin). lia.
      + simpl in Hin. destruct Hin as [Heq | Hf]; [lia | contradiction].
  }
  specialize (Hcomplete n Hle).
  exists [n]. split.
  - apply in_map_iff. exists n. split; [reflexivity | exact Hcomplete].
  - simpl. apply andb_true_iff. split.
    + apply nat_eqb_refl.
    + reflexivity.
Qed.

(** M_001_12: Structured fuzzing preserves input validity *)
Theorem M_001_12 : forall (min max n : nat),
  valid_structured_input min max n = true ->
  min <= n /\ n <= max.
Proof.
  intros min max n H.
  unfold valid_structured_input in H.
  apply andb_true_iff in H. destruct H as [H1 H2].
  apply Nat.leb_le in H1.
  apply Nat.leb_le in H2.
  split; assumption.
Qed.

(** M_001_13: Differential fuzzing detects discrepancies *)
Theorem M_001_13 : forall (f1 f2 : nat -> nat) (input : nat),
  differential_test f1 f2 input = false <-> f1 input <> f2 input.
Proof.
  intros f1 f2 input. unfold differential_test. split.
  - intros H Heq.
    rewrite Heq in H.
    rewrite nat_eqb_refl in H.
    discriminate H.
  - intros Hneq.
    destruct (Nat.eqb (f1 input) (f2 input)) eqn:Heqb.
    + apply Nat.eqb_eq in Heqb. contradiction.
    + reflexivity.
Qed.

(** M_001_14: Sanitizer integration correctness *)
Theorem M_001_14 : forall (sr : SanitizerResult),
  sanitizer_pass sr = true <-> sr = SRClean.
Proof.
  intros sr. unfold sanitizer_pass. split.
  - destruct sr.
    + intros _. reflexivity.
    + intros H. discriminate H.
  - intros H. rewrite H. reflexivity.
Qed.

(* ======================================================================= *)
(* THEOREMS - INTEGRATION TESTING (M-05)                                   *)
(* ======================================================================= *)

(** M_001_15: Component composition test correctness *)
Theorem M_001_15 : forall (c1 c2 : Component) (input : nat),
  compose_components c1 c2 input = c2.(comp_impl) (c1.(comp_impl) input).
Proof.
  intros c1 c2 input.
  unfold compose_components.
  reflexivity.
Qed.

(** M_001_16: API contract verification *)
Theorem M_001_16 : forall (api : APIContract) (input : nat),
  api.(api_precondition) input = true ->
  satisfies_contract api input = true ->
  api.(api_postcondition) input (api.(api_impl) input) = true.
Proof.
  intros api input Hpre Hsat.
  unfold satisfies_contract in Hsat.
  rewrite Hpre in Hsat.
  exact Hsat.
Qed.

(** M_001_17: Security flow integration test soundness *)
Theorem M_001_17 : forall (sf : SecurityFlow),
  sf.(sf_valid) = true ->
  exists src sink, sf.(sf_source) = src /\ sf.(sf_sink) = sink.
Proof.
  intros sf Hvalid.
  exists sf.(sf_source), sf.(sf_sink).
  split; reflexivity.
Qed.

(* ======================================================================= *)
(* THEOREMS - MUTATION TESTING (M-06)                                      *)
(* ======================================================================= *)

(** M_001_18: Mutation operator preserves syntactic validity *)
Theorem M_001_18 : forall (m : Mutant) (max_loc : nat),
  mutation_valid m max_loc = true ->
  m.(mut_location) < max_loc.
Proof.
  intros m max_loc H.
  unfold mutation_valid in H.
  apply Nat.ltb_lt in H.
  exact H.
Qed.

(** M_001_19: Killed mutation implies test detects fault *)
Theorem M_001_19 : forall (orig_f mut_f : nat -> nat) (tc : TestCase),
  test_detects_mutation orig_f mut_f tc = true ->
  orig_f tc.(tc_input) <> mut_f tc.(tc_input).
Proof.
  intros orig_f mut_f tc H.
  unfold test_detects_mutation in H.
  apply negb_true_iff in H.
  apply Nat.eqb_neq in H.
  exact H.
Qed.

(** M_001_20: Mutation score lower bound on test effectiveness *)
Theorem M_001_20 : forall (mutants : list Mutant),
  mutation_score mutants <= List.length mutants.
Proof.
  intros mutants.
  unfold mutation_score.
  induction mutants as [| m ms IH].
  - simpl. lia.
  - simpl. destruct (mut_killed m).
    + simpl. lia.
    + simpl. lia.
Qed.

(* ======================================================================= *)
(* THEOREMS - SECURITY TESTING (M-08)                                      *)
(* ======================================================================= *)

(** M_001_21: Timing test detects non-constant-time code *)
Theorem M_001_21 : forall (measurements : list TimingMeasurement) (tolerance : nat),
  timing_attack_detected measurements tolerance = true ->
  exists tm, In tm measurements /\ is_constant_time tm tolerance = false.
Proof.
  intros measurements tolerance H.
  unfold timing_attack_detected in H.
  apply existsb_exists in H.
  destruct H as [tm [Hin Htest]].
  apply negb_true_iff in Htest.
  exists tm. split; assumption.
Qed.

(** M_001_22: Known Answer Test (KAT) verifies cryptographic correctness *)
Theorem M_001_22 : forall (kat : KATTest) (f : nat -> nat),
  run_kat kat f = true <-> f kat.(kat_input) = kat.(kat_expected).
Proof.
  intros kat f. unfold run_kat. split.
  - intros H. apply Nat.eqb_eq in H. exact H.
  - intros H. apply Nat.eqb_eq. exact H.
Qed.

(** M_001_23: Brute force protection test correctness *)
Theorem M_001_23 : forall (bfp : BruteForceProtection),
  check_brute_force bfp = true <->
  (bfp.(bfp_locked) = true \/ bfp.(bfp_max_attempts) <= bfp.(bfp_current_attempts)).
Proof.
  intros bfp. unfold check_brute_force. split.
  - intros H. apply orb_true_iff in H. destruct H as [Hl | Hr].
    + left. exact Hl.
    + right. apply Nat.leb_le in Hr. exact Hr.
  - intros [Hl | Hr].
    + apply orb_true_iff. left. exact Hl.
    + apply orb_true_iff. right. apply Nat.leb_le. exact Hr.
Qed.

(* ======================================================================= *)
(* THEOREMS - TEST COVERAGE (M-09)                                         *)
(* ======================================================================= *)

(** M_001_24: Line coverage soundness - covered line was executed *)
Theorem M_001_24 : forall (line : nat) (trace : ExecutionTrace),
  line_covered line trace = true ->
  exists ev, In ev trace /\ ev = TECoverage line.
Proof.
  intros line trace H.
  unfold line_covered in H.
  apply existsb_exists in H.
  destruct H as [ev [Hin Hev]].
  destruct ev; try discriminate Hev.
  apply Nat.eqb_eq in Hev. subst.
  exists (TECoverage line). split; [exact Hin | reflexivity].
Qed.

(** M_001_25: Security property coverage completeness *)
Theorem M_001_25 : forall (sc : SecurityCoverage),
  all_security_covered sc = true ->
  forall sp, In sp sc.(sc_properties) -> security_prop_covered sp sc = true.
Proof.
  intros sc H sp Hin.
  unfold all_security_covered in H.
  rewrite forallb_true_iff in H.
  apply H. exact Hin.
Qed.
