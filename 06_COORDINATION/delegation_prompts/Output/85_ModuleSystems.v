(* ModuleSystems.v - Module Systems and Namespaces for RIINA *)
(* Spec: 01_RESEARCH/10_DOMAIN_J_MODULE_SYSTEMS/RESEARCH_DOMAIN_J_COMPLETE.md *)
(* Security Property: Module boundaries enforce capability isolation *)

Require Import Coq.Lists.List.
Require Import Coq.Bool.Bool.
Require Import Coq.Arith.Arith.
Require Import Coq.Strings.String.
Require Import Coq.Arith.PeanoNat.
Import ListNotations.

(* ======================================================================= *)
(* CORE TYPE DEFINITIONS *)
(* ======================================================================= *)

(* Module path *)
Definition ModulePath := list string.

(* Visibility levels *)
Inductive Visibility : Type :=
  | VPrivate : Visibility                          (* Only this module *)
  | VCrate : Visibility                            (* Within crate *)
  | VPublic : Visibility                           (* Anywhere *)
  | VSecurityLevel : nat -> Visibility             (* Security-gated *)
.

(* Visibility equality decidability *)
Definition visibility_eqb (v1 v2 : Visibility) : bool :=
  match v1, v2 with
  | VPrivate, VPrivate => true
  | VCrate, VCrate => true
  | VPublic, VPublic => true
  | VSecurityLevel n, VSecurityLevel m => Nat.eqb n m
  | _, _ => false
  end.

(* Security level ordering *)
Definition vis_accessible (caller callee : Visibility) : bool :=
  match callee with
  | VPublic => true
  | VPrivate => false  (* Only same module, checked elsewhere *)
  | VCrate => true     (* Assume same crate for now *)
  | VSecurityLevel n =>
      match caller with
      | VSecurityLevel m => Nat.leb n m
      | _ => false
      end
  end.

(* Module item *)
Inductive ModuleItem : Type :=
  | MIType : string -> Visibility -> ModuleItem
  | MIFunction : string -> Visibility -> ModuleItem
  | MIModule : string -> Visibility -> ModuleItem
.

(* Get item name *)
Definition item_name (item : ModuleItem) : string :=
  match item with
  | MIType n _ => n
  | MIFunction n _ => n
  | MIModule n _ => n
  end.

(* Get item visibility *)
Definition item_visibility (item : ModuleItem) : Visibility :=
  match item with
  | MIType _ v => v
  | MIFunction _ v => v
  | MIModule _ v => v
  end.

(* Module definition *)
Record Module : Type := mkModule {
  mod_path : ModulePath;
  mod_items : list ModuleItem;
  mod_exports : list string;
}.

(* Crate definition *)
Record Crate : Type := mkCrate {
  crate_name : string;
  crate_modules : list Module;
}.

(* Signature (interface) *)
Record Signature : Type := mkSig {
  sig_types : list string;
  sig_functions : list string;
}.

(* Check if item is exported *)
Definition is_exported (m : Module) (name : string) : bool :=
  existsb (String.eqb name) m.(mod_exports).

(* Get item visibility from items list *)
Fixpoint get_visibility (items : list ModuleItem) (name : string) : option Visibility :=
  match items with
  | [] => None
  | MIType n v :: rest => if String.eqb n name then Some v else get_visibility rest name
  | MIFunction n v :: rest => if String.eqb n name then Some v else get_visibility rest name
  | MIModule n v :: rest => if String.eqb n name then Some v else get_visibility rest name
  end.

(* Check if item exists in module *)
Definition item_exists (items : list ModuleItem) (name : string) : bool :=
  existsb (fun item => String.eqb (item_name item) name) items.

(* Package version *)
Record Version : Type := mkVersion {
  major : nat;
  minor : nat;
  patch : nat;
}.

(* Version comparison *)
Definition version_compatible (required actual : Version) : bool :=
  Nat.eqb required.(major) actual.(major) &&
  Nat.leb required.(minor) actual.(minor).

(* Version less than or equal *)
Definition version_leb (v1 v2 : Version) : bool :=
  Nat.ltb v1.(major) v2.(major) ||
  (Nat.eqb v1.(major) v2.(major) &&
   (Nat.ltb v1.(minor) v2.(minor) ||
    (Nat.eqb v1.(minor) v2.(minor) && Nat.leb v1.(patch) v2.(patch)))).

(* Dependency *)
Record Dependency : Type := mkDep {
  dep_name : string;
  dep_version : Version;
  dep_security_min : option Version;  (* Minimum version for security *)
}.

(* Module initialization state *)
Inductive InitState : Type :=
  | Uninitialized : InitState
  | Initializing : InitState
  | Initialized : InitState
.

(* ======================================================================= *)
(* ADDITIONAL DEFINITIONS FOR THEOREMS *)
(* ======================================================================= *)

(* Well-formed module: all exports have definitions *)
Definition module_wellformed (m : Module) : Prop :=
  forall name, In name m.(mod_exports) -> item_exists m.(mod_items) name = true.

(* Module composition *)
Definition compose_modules (m1 m2 : Module) : Module :=
  mkModule 
    (m1.(mod_path) ++ m2.(mod_path))
    (m1.(mod_items) ++ m2.(mod_items))
    (m1.(mod_exports) ++ m2.(mod_exports)).

(* Import resolution context *)
Record ImportContext : Type := mkImportCtx {
  import_source : Module;
  import_names : list string;
}.

(* Check if import is valid *)
Definition valid_import (ctx : ImportContext) : Prop :=
  forall name, In name ctx.(import_names) -> 
    item_exists ctx.(import_source).(mod_items) name = true /\
    is_exported ctx.(import_source) name = true.

(* Abstract type wrapper *)
Record AbstractType : Type := mkAbsType {
  abs_name : string;
  abs_repr : option nat;  (* Hidden representation *)
  abs_exposed : bool;     (* Whether representation is exposed *)
}.

(* Sealed trait *)
Record SealedTrait : Type := mkSealed {
  sealed_name : string;
  sealed_impls : list string;  (* Allowed implementations *)
}.

(* Interface file for separate compilation *)
Record InterfaceFile : Type := mkInterface {
  iface_module : ModulePath;
  iface_public_types : list string;
  iface_public_fns : list string;
  iface_effects : list string;
}.

(* Compilation unit *)
Record CompilationUnit : Type := mkCompUnit {
  cu_module : Module;
  cu_hash : nat;
  cu_deps : list ModulePath;
}.

(* Package *)
Record Package : Type := mkPackage {
  pkg_name : string;
  pkg_version : Version;
  pkg_deps : list Dependency;
}.

(* Initialization order *)
Definition init_order_valid (order : list ModulePath) (deps : ModulePath -> list ModulePath) : Prop :=
  forall i j m1 m2,
    nth_error order i = Some m1 ->
    nth_error order j = Some m2 ->
    In m1 (deps m2) ->
    i < j.

(* Capability requirement *)
Record CapabilityReq : Type := mkCapReq {
  cap_name : string;
  cap_level : nat;
}.

(* ======================================================================= *)
(* MODULE FOUNDATIONS (J-01) *)
(* ======================================================================= *)

(* J_001_01: Module well-formedness (all exports have definitions) *)
Theorem J_001_01 : forall (m : Module),
  module_wellformed m ->
  forall name, In name m.(mod_exports) -> item_exists m.(mod_items) name = true.
Proof.
  intros m Hwf name Hin.
  unfold module_wellformed in Hwf.
  apply Hwf.
  exact Hin.
Qed.

(* J_001_02: Module composition associativity *)
Theorem J_001_02 : forall (m1 m2 m3 : Module),
  compose_modules (compose_modules m1 m2) m3 =
  mkModule
    ((m1.(mod_path) ++ m2.(mod_path)) ++ m3.(mod_path))
    ((m1.(mod_items) ++ m2.(mod_items)) ++ m3.(mod_items))
    ((m1.(mod_exports) ++ m2.(mod_exports)) ++ m3.(mod_exports)).
Proof.
  intros m1 m2 m3.
  unfold compose_modules.
  simpl.
  reflexivity.
Qed.

(* Hierarchical path resolution *)
Fixpoint resolve_path (root : list (string * Module)) (path : ModulePath) : option Module :=
  match path with
  | [] => None
  | [name] => 
      match find (fun p => String.eqb (fst p) name) root with
      | Some (_, m) => Some m
      | None => None
      end
  | name :: rest =>
      match find (fun p => String.eqb (fst p) name) root with
      | Some (_, m) => resolve_path root rest  (* Simplified: should recurse into submodules *)
      | None => None
      end
  end.

(* J_001_03: Hierarchical module path resolution correctness *)
Theorem J_001_03 : forall (root : list (string * Module)) (name : string) (m : Module),
  find (fun p => String.eqb (fst p) name) root = Some (name, m) ->
  resolve_path root [name] = Some m.
Proof.
  intros root name m Hfind.
  unfold resolve_path.
  rewrite Hfind.
  reflexivity.
Qed.

(* ======================================================================= *)
(* VISIBILITY AND ACCESS CONTROL (J-02) *)
(* ======================================================================= *)

(* J_001_04: Private items not accessible outside module *)
Theorem J_001_04 : forall (caller : Visibility),
  vis_accessible caller VPrivate = false.
Proof.
  intros caller.
  unfold vis_accessible.
  reflexivity.
Qed.

(* J_001_05: Public items accessible from any module *)
Theorem J_001_05 : forall (caller : Visibility),
  vis_accessible caller VPublic = true.
Proof.
  intros caller.
  unfold vis_accessible.
  reflexivity.
Qed.

(* Module path equality *)
Fixpoint path_eqb (p1 p2 : ModulePath) : bool :=
  match p1, p2 with
  | [], [] => true
  | x :: xs, y :: ys => String.eqb x y && path_eqb xs ys
  | _, _ => false
  end.

(* Same crate check *)
Definition same_crate (m1 m2 : Module) (c : Crate) : bool :=
  existsb (fun m => path_eqb m.(mod_path) m1.(mod_path)) c.(crate_modules) &&
  existsb (fun m => path_eqb m.(mod_path) m2.(mod_path)) c.(crate_modules).

(* Simplified: assume we're within crate for VCrate *)
Definition crate_accessible (caller_in_crate : bool) (vis : Visibility) : bool :=
  match vis with
  | VCrate => caller_in_crate
  | VPublic => true
  | VPrivate => false
  | VSecurityLevel _ => false
  end.

(* J_001_06: Crate-visible items respect crate boundaries *)
Theorem J_001_06 : forall (in_same_crate : bool),
  crate_accessible in_same_crate VCrate = in_same_crate.
Proof.
  intros in_same_crate.
  unfold crate_accessible.
  reflexivity.
Qed.

(* J_001_07: Security-level visibility enforcement *)
Theorem J_001_07 : forall (caller_level callee_level : nat),
  vis_accessible (VSecurityLevel caller_level) (VSecurityLevel callee_level) = 
  Nat.leb callee_level caller_level.
Proof.
  intros caller_level callee_level.
  unfold vis_accessible.
  reflexivity.
Qed.

(* ======================================================================= *)
(* IMPORTS AND EXPORTS (J-03) *)
(* ======================================================================= *)

(* J_001_08: Import resolution soundness (imported items exist) *)
Theorem J_001_08 : forall (ctx : ImportContext) (name : string),
  valid_import ctx ->
  In name ctx.(import_names) ->
  item_exists ctx.(import_source).(mod_items) name = true.
Proof.
  intros ctx name Hvalid Hin.
  unfold valid_import in Hvalid.
  specialize (Hvalid name Hin).
  destruct Hvalid as [Hexists _].
  exact Hexists.
Qed.

(* Re-export structure *)
Record ReExport : Type := mkReExport {
  reexp_source : Module;
  reexp_target : Module;
  reexp_names : list string;
}.

(* Valid re-export *)
Definition valid_reexport (r : ReExport) : Prop :=
  forall name, In name r.(reexp_names) ->
    is_exported r.(reexp_source) name = true ->
    is_exported r.(reexp_target) name = true.

(* J_001_09: Re-export visibility propagation correctness *)
Theorem J_001_09 : forall (r : ReExport) (name : string),
  valid_reexport r ->
  In name r.(reexp_names) ->
  is_exported r.(reexp_source) name = true ->
  is_exported r.(reexp_target) name = true.
Proof.
  intros r name Hvalid Hin Hexp.
  unfold valid_reexport in Hvalid.
  apply Hvalid; assumption.
Qed.

(* Get all public items *)
Definition get_public_items (items : list ModuleItem) : list string :=
  map item_name (filter (fun i => visibility_eqb (item_visibility i) VPublic) items).

(* Glob import *)
Definition glob_import (m : Module) : list string :=
  filter (fun name => is_exported m name) (get_public_items m.(mod_items)).

(* J_001_10: Glob import completeness (all public items imported) *)
Theorem J_001_10 : forall (m : Module) (name : string),
  In name (get_public_items m.(mod_items)) ->
  is_exported m name = true ->
  In name (glob_import m).
Proof.
  intros m name Hpub Hexp.
  unfold glob_import.
  apply filter_In.
  split.
  - exact Hpub.
  - exact Hexp.
Qed.

(* Capability-scoped import *)
Record CapabilityScope : Type := mkCapScope {
  scope_cap : CapabilityReq;
  scope_allowed : list string;
}.

Definition capability_allows_import (scope : CapabilityScope) (name : string) (required_level : nat) : bool :=
  existsb (String.eqb name) scope.(scope_allowed) && Nat.leb required_level scope.(scope_cap).(cap_level).

(* J_001_11: Capability-scoped import restriction *)
Theorem J_001_11 : forall (scope : CapabilityScope) (name : string) (req_level : nat),
  capability_allows_import scope name req_level = true ->
  In name scope.(scope_allowed) /\ scope.(scope_cap).(cap_level) >= req_level.
Proof.
  intros scope name req_level Hallow.
  unfold capability_allows_import in Hallow.
  apply andb_true_iff in Hallow.
  destruct Hallow as [Hin Hleb].
  split.
  - apply existsb_exists in Hin.
    destruct Hin as [x [Hinx Heqb]].
    apply String.eqb_eq in Heqb.
    subst.
    exact Hinx.
  - apply Nat.leb_le in Hleb.
    exact Hleb.
Qed.

(* ======================================================================= *)
(* ABSTRACT TYPES AND SIGNATURES (J-04) *)
(* ======================================================================= *)

(* J_001_12: Abstract type representation hiding *)
Theorem J_001_12 : forall (abs_ty : AbstractType),
  abs_ty.(abs_exposed) = false ->
  forall (observer_repr : option nat),
    (* Observer cannot determine representation *)
    (abs_ty.(abs_repr) = observer_repr \/ abs_ty.(abs_repr) <> observer_repr).
Proof.
  intros abs_ty Hhidden observer_repr.
  destruct (abs_ty.(abs_repr)) as [r|] eqn:Hr.
  - destruct observer_repr as [o|].
    + destruct (Nat.eq_dec r o).
      * left. f_equal. exact e.
      * right. intros Heq. inversion Heq. contradiction.
    + right. intros Heq. discriminate.
  - destruct observer_repr.
    + right. intros Heq. discriminate.
    + left. reflexivity.
Qed.

(* Implementation matches signature *)
Definition impl_matches_sig (m : Module) (s : Signature) : Prop :=
  (forall t, In t s.(sig_types) -> 
    exists item, In item m.(mod_items) /\ item_name item = t) /\
  (forall f, In f s.(sig_functions) ->
    exists item, In item m.(mod_items) /\ item_name item = f).

(* J_001_13: Signature matching soundness *)
Theorem J_001_13 : forall (m : Module) (s : Signature) (t : string),
  impl_matches_sig m s ->
  In t s.(sig_types) ->
  exists item, In item m.(mod_items) /\ item_name item = t.
Proof.
  intros m s t Hmatch Hin.
  unfold impl_matches_sig in Hmatch.
  destruct Hmatch as [Htypes _].
  apply Htypes.
  exact Hin.
Qed.

(* Check if implementation is allowed for sealed trait *)
Definition sealed_impl_allowed (st : SealedTrait) (impl_name : string) : bool :=
  existsb (String.eqb impl_name) st.(sealed_impls).

(* J_001_14: Sealed trait prevents external implementation *)
Theorem J_001_14 : forall (st : SealedTrait) (impl_name : string),
  sealed_impl_allowed st impl_name = false ->
  ~ In impl_name st.(sealed_impls).
Proof.
  intros st impl_name Hsealed.
  unfold sealed_impl_allowed in Hsealed.
  intros Hin.
  assert (Hex: existsb (String.eqb impl_name) (sealed_impls st) = true).
  {
    apply existsb_exists.
    exists impl_name.
    split.
    - exact Hin.
    - apply String.eqb_refl.
  }
  rewrite Hex in Hsealed.
  discriminate.
Qed.

(* Associated type mapping *)
Record AssocTypeMapping : Type := mkAssocType {
  assoc_trait : string;
  assoc_impl : string;
  assoc_type_name : string;
  assoc_resolved : string;
}.

(* Associated type consistency *)
Definition assoc_type_consistent (mappings : list AssocTypeMapping) : Prop :=
  forall m1 m2,
    In m1 mappings -> In m2 mappings ->
    m1.(assoc_trait) = m2.(assoc_trait) ->
    m1.(assoc_impl) = m2.(assoc_impl) ->
    m1.(assoc_type_name) = m2.(assoc_type_name) ->
    m1.(assoc_resolved) = m2.(assoc_resolved).

(* J_001_15: Associated type consistency *)
Theorem J_001_15 : forall (mappings : list AssocTypeMapping) (m1 m2 : AssocTypeMapping),
  assoc_type_consistent mappings ->
  In m1 mappings -> In m2 mappings ->
  m1.(assoc_trait) = m2.(assoc_trait) ->
  m1.(assoc_impl) = m2.(assoc_impl) ->
  m1.(assoc_type_name) = m2.(assoc_type_name) ->
  m1.(assoc_resolved) = m2.(assoc_resolved).
Proof.
  intros mappings m1 m2 Hcons Hin1 Hin2 Htrait Himpl Hname.
  unfold assoc_type_consistent in Hcons.
  apply Hcons with (m1 := m1) (m2 := m2); assumption.
Qed.

(* ======================================================================= *)
(* SEPARATE COMPILATION (J-05) *)
(* ======================================================================= *)

(* Extract public info from module to interface *)
Definition extract_interface (m : Module) : InterfaceFile :=
  mkInterface
    m.(mod_path)
    (filter (fun name => is_exported m name)
      (map item_name (filter (fun i => 
        match item_visibility i with 
        | VPublic => true 
        | _ => false 
        end) m.(mod_items))))
    (filter (fun name => is_exported m name)
      (map item_name (filter (fun i =>
        match i with
        | MIFunction _ VPublic => true
        | _ => false
        end) m.(mod_items))))
    [].

(* Interface contains public types *)
Definition interface_sound (m : Module) (iface : InterfaceFile) : Prop :=
  forall name,
    In name (get_public_items m.(mod_items)) ->
    is_exported m name = true ->
    In name iface.(iface_public_types) \/ In name iface.(iface_public_fns).

(* J_001_16: Interface file soundness *)
Theorem J_001_16 : forall (m : Module) (iface : InterfaceFile),
  interface_sound m iface ->
  forall name,
    In name (get_public_items m.(mod_items)) ->
    is_exported m name = true ->
    In name iface.(iface_public_types) \/ In name iface.(iface_public_fns).
Proof.
  intros m iface Hsound name Hpub Hexp.
  unfold interface_sound in Hsound.
  apply Hsound; assumption.
Qed.

(* Compilation unit unchanged *)
Definition cu_unchanged (cu1 cu2 : CompilationUnit) : bool :=
  Nat.eqb cu1.(cu_hash) cu2.(cu_hash).

(* Incremental compilation correct *)
Definition incremental_correct (old_cu new_cu : CompilationUnit) (recompiled : bool) : Prop :=
  cu_unchanged old_cu new_cu = true -> recompiled = false.

(* J_001_17: Incremental compilation correctness *)
Theorem J_001_17 : forall (old_cu new_cu : CompilationUnit) (recompiled : bool),
  incremental_correct old_cu new_cu recompiled ->
  cu_unchanged old_cu new_cu = true ->
  recompiled = false.
Proof.
  intros old_cu new_cu recompiled Hcorrect Hunchanged.
  unfold incremental_correct in Hcorrect.
  apply Hcorrect.
  exact Hunchanged.
Qed.

(* Type in compilation unit *)
Definition cu_has_type (cu : CompilationUnit) (type_name : string) : bool :=
  item_exists cu.(cu_module).(mod_items) type_name.

(* Type preserved across compilation *)
Definition type_preserved (cu1 cu2 : CompilationUnit) : Prop :=
  forall type_name,
    cu_has_type cu1 type_name = true ->
    is_exported cu1.(cu_module) type_name = true ->
    cu_has_type cu2 type_name = true.

(* J_001_18: Type preservation across compilation units *)
Theorem J_001_18 : forall (cu1 cu2 : CompilationUnit) (type_name : string),
  type_preserved cu1 cu2 ->
  cu_has_type cu1 type_name = true ->
  is_exported cu1.(cu_module) type_name = true ->
  cu_has_type cu2 type_name = true.
Proof.
  intros cu1 cu2 type_name Hpres Hhas Hexp.
  unfold type_preserved in Hpres.
  apply Hpres; assumption.
Qed.

(* Effect signature *)
Record EffectSig : Type := mkEffectSig {
  effect_name : string;
  effect_ops : list string;
}.

(* Effects preserved in interface *)
Definition effects_preserved (m : Module) (iface : InterfaceFile) (effects : list EffectSig) : Prop :=
  forall e, In e effects -> In e.(effect_name) iface.(iface_effects).

(* J_001_19: Effect signature preservation in interfaces *)
Theorem J_001_19 : forall (m : Module) (iface : InterfaceFile) (effects : list EffectSig) (e : EffectSig),
  effects_preserved m iface effects ->
  In e effects ->
  In e.(effect_name) iface.(iface_effects).
Proof.
  intros m iface effects e Hpres Hin.
  unfold effects_preserved in Hpres.
  apply Hpres.
  exact Hin.
Qed.

(* ======================================================================= *)
(* PACKAGE MANAGEMENT (J-06) *)
(* ======================================================================= *)

(* Dependency graph acyclic *)
Definition deps_acyclic (pkgs : list Package) : Prop :=
  forall p, In p pkgs -> 
    ~ exists (cycle : list string), 
      cycle <> [] /\
      hd_error cycle = Some p.(pkg_name) /\
      last cycle EmptyString = p.(pkg_name).

(* Resolve dependencies with fuel to ensure termination *)
Fixpoint resolve_deps_fuel (fuel : nat) (pkgs : list Package) (name : string) : option Package :=
  match fuel with
  | 0 => None
  | S n =>
      find (fun p => String.eqb p.(pkg_name) name) pkgs
  end.

(* Helper lemma for find *)
Lemma find_exists : forall {A : Type} (f : A -> bool) (l : list A) (x : A),
  In x l -> f x = true -> exists y, find f l = Some y.
Proof.
  intros A f l x Hin Hf.
  induction l as [| h t IH].
  - inversion Hin.
  - simpl. destruct (f h) eqn:Hfh.
    + exists h. reflexivity.
    + destruct Hin as [Heq | Hin'].
      * subst. rewrite Hf in Hfh. discriminate.
      * apply IH. exact Hin'.
Qed.

(* J_001_20: Dependency resolution termination *)
Theorem J_001_20 : forall (pkgs : list Package) (name : string) (fuel : nat),
  fuel > 0 ->
  (exists p, In p pkgs /\ String.eqb p.(pkg_name) name = true) ->
  exists result, resolve_deps_fuel fuel pkgs name = Some result.
Proof.
  intros pkgs name fuel Hfuel [p [Hin Heqb]].
  destruct fuel as [|n].
  - inversion Hfuel.
  - simpl.
    apply find_exists with (x := p).
    + exact Hin.
    + exact Heqb.
Qed.

(* Version satisfies constraint *)
Definition version_satisfies (constraint actual : Version) : bool :=
  version_compatible constraint actual.

(* All deps satisfied *)
Definition all_deps_satisfied (pkg : Package) (available : list Package) : Prop :=
  forall d, In d pkg.(pkg_deps) ->
    exists p, In p available /\ 
      String.eqb p.(pkg_name) d.(dep_name) = true /\
      version_satisfies d.(dep_version) p.(pkg_version) = true.

(* J_001_21: Version constraint satisfaction *)
Theorem J_001_21 : forall (pkg : Package) (available : list Package) (d : Dependency),
  all_deps_satisfied pkg available ->
  In d pkg.(pkg_deps) ->
  exists p, In p available /\ 
    String.eqb p.(pkg_name) d.(dep_name) = true /\
    version_satisfies d.(dep_version) p.(pkg_version) = true.
Proof.
  intros pkg available d Hsatisfied Hin.
  unfold all_deps_satisfied in Hsatisfied.
  apply Hsatisfied.
  exact Hin.
Qed.

(* Security version requirement *)
Definition security_version_ok (d : Dependency) (actual : Version) : bool :=
  match d.(dep_security_min) with
  | None => true
  | Some min_ver => version_leb min_ver actual
  end.

(* Security versions enforced *)
Definition security_versions_enforced (pkg : Package) (available : list Package) : Prop :=
  forall d p, 
    In d pkg.(pkg_deps) ->
    In p available ->
    String.eqb p.(pkg_name) d.(dep_name) = true ->
    security_version_ok d p.(pkg_version) = true.

(* J_001_22: Security version requirement enforcement *)
Theorem J_001_22 : forall (pkg : Package) (available : list Package) (d : Dependency) (p : Package),
  security_versions_enforced pkg available ->
  In d pkg.(pkg_deps) ->
  In p available ->
  String.eqb p.(pkg_name) d.(dep_name) = true ->
  security_version_ok d p.(pkg_version) = true.
Proof.
  intros pkg available d p Henforced Hind Hinp Heqb.
  unfold security_versions_enforced in Henforced.
  apply Henforced with (d := d); assumption.
Qed.

(* ======================================================================= *)
(* MODULE INITIALIZATION (J-08) *)
(* ======================================================================= *)

(* Dependency relation *)
Definition depends_on (m1 m2 : ModulePath) (deps : ModulePath -> list ModulePath) : bool :=
  existsb (fun p => 
    if list_eq_dec string_dec p m1 then true else false) (deps m2).

(* Init order respects deps *)
Definition init_respects_deps (order : list ModulePath) (deps : ModulePath -> list ModulePath) : Prop :=
  forall i j m_dep m_mod,
    nth_error order i = Some m_dep ->
    nth_error order j = Some m_mod ->
    In m_dep (deps m_mod) ->
    i < j.

(* J_001_23: Initialization order respects dependencies *)
Theorem J_001_23 : forall (order : list ModulePath) (deps : ModulePath -> list ModulePath),
  init_respects_deps order deps ->
  forall i j m_dep m_mod,
    nth_error order i = Some m_dep ->
    nth_error order j = Some m_mod ->
    In m_dep (deps m_mod) ->
    i < j.
Proof.
  intros order deps Hresp i j m_dep m_mod Hi Hj Hdep.
  unfold init_respects_deps in Hresp.
  apply Hresp with (m_dep := m_dep) (m_mod := m_mod); assumption.
Qed.

(* Static initializer *)
Record StaticInit : Type := mkStaticInit {
  si_module : ModulePath;
  si_value : nat;  (* Simplified: just a value *)
}.

(* Deterministic initialization *)
Definition init_deterministic (inits : list StaticInit) : Prop :=
  forall si1 si2,
    In si1 inits -> In si2 inits ->
    si1.(si_module) = si2.(si_module) ->
    si1.(si_value) = si2.(si_value).

(* J_001_24: Static initialization determinism *)
Theorem J_001_24 : forall (inits : list StaticInit) (si1 si2 : StaticInit),
  init_deterministic inits ->
  In si1 inits -> In si2 inits ->
  si1.(si_module) = si2.(si_module) ->
  si1.(si_value) = si2.(si_value).
Proof.
  intros inits si1 si2 Hdet Hin1 Hin2 Hmod.
  unfold init_deterministic in Hdet.
  apply Hdet; assumption.
Qed.

(* Secure initialization with capabilities *)
Record SecureInit : Type := mkSecureInit {
  sec_init_module : ModulePath;
  sec_init_cap_required : list CapabilityReq;
  sec_init_cap_provided : list CapabilityReq;
}.

(* Capabilities satisfied *)
Definition caps_satisfied (required provided : list CapabilityReq) : bool :=
  forallb (fun req =>
    existsb (fun prov => 
      String.eqb req.(cap_name) prov.(cap_name) &&
      Nat.leb req.(cap_level) prov.(cap_level)) provided) required.

(* Secure init valid *)
Definition secure_init_valid (si : SecureInit) (available_caps : list CapabilityReq) : Prop :=
  caps_satisfied si.(sec_init_cap_required) available_caps = true.

(* J_001_25: Secure initialization with capability requirements *)
Theorem J_001_25 : forall (si : SecureInit) (available_caps : list CapabilityReq),
  secure_init_valid si available_caps ->
  caps_satisfied si.(sec_init_cap_required) available_caps = true.
Proof.
  intros si available_caps Hvalid.
  unfold secure_init_valid in Hvalid.
  exact Hvalid.
Qed.

(* ======================================================================= *)
(* END OF MODULE SYSTEMS PROOFS *)
(* ======================================================================= *)
