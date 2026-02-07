(* Copyright (c) 2026 The RIINA Authors. All rights reserved. *)

(** * RIINA Syntax
    
    Core syntax definitions for RIINA.
    
    Reference: RIINA-AST_v1_0_0.md
    
    Mode: ULTRA KIASU | FUCKING PARANOID | ZERO TRUST | ZERO LAZINESS
*)

Require Import Coq.Strings.String.
Require Import Coq.Lists.List.
Require Import Coq.Arith.Arith.
Import ListNotations.

(** ** Identifiers *)

Definition ident := string.
Definition loc := nat.

(** ** Security Levels

    RIINA uses a multi-level lattice for information flow control.
    Matches CTSS v1.0.1 specification (D42-A).

    Lattice structure:
      Public ⊑ Internal ⊑ Session ⊑ User ⊑ System ⊑ Secret

    Product levels are parameterized by product markers (separate hierarchy).
*)

Inductive security_level : Type :=
  | LPublic    : security_level   (* Publicly observable *)
  | LInternal  : security_level   (* Internal use only *)
  | LSession   : security_level   (* Session-scoped *)
  | LUser      : security_level   (* User-level sensitive *)
  | LSystem    : security_level   (* System-level sensitive *)
  | LSecret    : security_level.  (* Maximum secrecy *)

(** Security level numeric encoding for ordering *)
Definition sec_level_num (l : security_level) : nat :=
  match l with
  | LPublic   => 0
  | LInternal => 1
  | LSession  => 2
  | LUser     => 3
  | LSystem   => 4
  | LSecret   => 5
  end.

(** Security level ordering: l1 ⊑ l2 *)
Definition sec_leq (l1 l2 : security_level) : Prop :=
  sec_level_num l1 <= sec_level_num l2.

(** Decidable security level ordering *)
Definition sec_leq_dec (l1 l2 : security_level) : bool :=
  Nat.leb (sec_level_num l1) (sec_level_num l2).

(** Security level join (least upper bound) *)
Definition sec_join (l1 l2 : security_level) : security_level :=
  if Nat.leb (sec_level_num l1) (sec_level_num l2) then l2 else l1.

(** Security level meet (greatest lower bound) *)
Definition sec_meet (l1 l2 : security_level) : security_level :=
  if Nat.leb (sec_level_num l1) (sec_level_num l2) then l1 else l2.

(** Backward compatibility aliases *)
Definition Public := LPublic.
Definition Secret := LSecret.

(** ** Effect Labels

    Effects track observable behaviors of computations.
    Matches CTSS v1.0.1 specification (D40).

    Effect hierarchy (partial order, not total):
    - Pure: No effects
    - IO effects: Read, Write, FileSystem
    - Network effects: Network, NetworkSecure
    - Crypto effects: Crypto, Random
    - System effects: System, Time, Process
    - RIINA product effects: Panel, Zirah, Benteng, Sandi, Menara, Gapura
*)

Inductive effect : Type :=
  (* Base effects *)
  | EffPure       : effect   (* No observable effect *)
  | EffRead       : effect   (* Memory/state read *)
  | EffWrite      : effect   (* Memory/state write *)
  | EffFileSystem : effect   (* File system access *)
  (* Network effects *)
  | EffNetwork    : effect   (* Network I/O *)
  | EffNetSecure  : effect   (* Secure network (TLS) *)
  (* Crypto effects *)
  | EffCrypto     : effect   (* Cryptographic operations *)
  | EffRandom     : effect   (* Random number generation *)
  (* System effects *)
  | EffSystem     : effect   (* System calls *)
  | EffTime       : effect   (* Time/clock access *)
  | EffProcess    : effect   (* Process management *)
  (* RIINA product effects - D40 integration *)
  | EffPanel      : effect   (* Panel UI operations *)
  | EffZirah      : effect   (* Zirah API operations *)
  | EffBenteng    : effect   (* Benteng auth operations *)
  | EffSandi      : effect   (* Sandi crypto operations *)
  | EffMenara     : effect   (* Menara device operations *)
  | EffGapura     : effect.  (* Gapura gateway operations *)

(** Effect category for partial ordering *)
Inductive effect_category : Type :=
  | CatPure
  | CatIO
  | CatNetwork
  | CatCrypto
  | CatSystem
  | CatProduct.

Definition effect_cat (e : effect) : effect_category :=
  match e with
  | EffPure => CatPure
  | EffRead | EffWrite | EffFileSystem => CatIO
  | EffNetwork | EffNetSecure => CatNetwork
  | EffCrypto | EffRandom => CatCrypto
  | EffSystem | EffTime | EffProcess => CatSystem
  | EffPanel | EffZirah | EffBenteng | EffSandi | EffMenara | EffGapura => CatProduct
  end.

(** Effect level within category for ordering *)
Definition effect_level (e : effect) : nat :=
  match e with
  | EffPure => 0
  | EffRead => 1 | EffWrite => 2 | EffFileSystem => 3
  | EffNetwork => 4 | EffNetSecure => 5
  | EffCrypto => 6 | EffRandom => 7
  | EffSystem => 8 | EffTime => 9 | EffProcess => 10
  | EffPanel => 11 | EffZirah => 12 | EffBenteng => 13
  | EffSandi => 14 | EffMenara => 15 | EffGapura => 16
  end.

(** Effect join: max in the hierarchy *)
Definition effect_join (e1 e2 : effect) : effect :=
  if Nat.ltb (effect_level e1) (effect_level e2) then e2 else e1.

(** Pure is identity for effect join *)
Lemma effect_join_pure_l : forall e, effect_join EffPure e = e.
Proof.
  intros e. unfold effect_join. destruct e; simpl; reflexivity.
Qed.

Lemma effect_join_pure_r : forall e, effect_join e EffPure = e.
Proof.
  intros e. unfold effect_join. destruct e; simpl; reflexivity.
Qed.

(** Backward compatibility aliases *)
Definition EffectPure := EffPure.
Definition EffectRead := EffRead.
Definition EffectWrite := EffWrite.
Definition EffectNetwork := EffNetwork.
Definition EffectCrypto := EffCrypto.
Definition EffectSystem := EffSystem.

(** ** Taint Sources

    Taint tracking for untrusted data.
    Matches CTSS v1.0.1 specification (D42-E).
*)

Inductive taint_source : Type :=
  (* Network sources *)
  | TaintNetworkExternal : taint_source  (* External network input *)
  | TaintNetworkInternal : taint_source  (* Internal network input *)
  (* User input sources *)
  | TaintUserInput       : taint_source  (* Direct user input *)
  | TaintFileSystem      : taint_source  (* File system data *)
  | TaintDatabase        : taint_source  (* Database query results *)
  | TaintEnvironment     : taint_source  (* Environment variables *)
  (* RIINA product sources *)
  | TaintGapuraRequest   : taint_source  (* Gapura API request *)
  | TaintZirahEvent      : taint_source  (* Zirah event data *)
  | TaintZirahEndpoint   : taint_source  (* Zirah endpoint data *)
  | TaintBentengBiometric: taint_source  (* Benteng biometric data *)
  | TaintSandiSignature  : taint_source  (* Sandi signature input *)
  | TaintMenaraDevice    : taint_source. (* Menara device data *)

(** Taint source combination *)
Definition taint_combine (t1 t2 : taint_source) : taint_source :=
  (* For now, take the "more external" source *)
  match t1 with
  | TaintNetworkExternal => t1
  | _ => t2
  end.

(** ** Sanitizers

    Sanitization markers for tainted data.
    Matches CTSS v1.0.1 specification (D42-E).
*)

Inductive sanitizer : Type :=
  (* Web sanitizers *)
  | SanHtmlEscape        : sanitizer  (* HTML entity escaping *)
  | SanUrlEncode         : sanitizer  (* URL encoding *)
  | SanJsEscape          : sanitizer  (* JavaScript string escaping *)
  | SanCssEscape         : sanitizer  (* CSS escaping *)
  (* SQL sanitizers *)
  | SanSqlEscape         : sanitizer  (* SQL string escaping *)
  | SanSqlParam          : sanitizer  (* Parameterized query *)
  (* Injection prevention *)
  | SanXssFilter         : sanitizer  (* XSS filtering *)
  | SanPathTraversal     : sanitizer  (* Path traversal check *)
  | SanCommandEscape     : sanitizer  (* Command injection prevention *)
  | SanLdapEscape        : sanitizer  (* LDAP injection prevention *)
  | SanXmlEscape         : sanitizer  (* XML escaping *)
  (* Validation sanitizers *)
  | SanJsonValidation    : sanitizer  (* JSON structure validation *)
  | SanXmlValidation     : sanitizer  (* XML schema validation *)
  | SanEmailValidation   : sanitizer  (* Email format validation *)
  | SanPhoneValidation   : sanitizer  (* Phone format validation *)
  (* Bound sanitizers *)
  | SanLengthBound       : nat -> sanitizer  (* Maximum length check *)
  | SanRangeBound        : nat -> nat -> sanitizer  (* Numeric range check *)
  | SanRegexMatch        : string -> sanitizer  (* Regex pattern match *)
  | SanWhitelist         : list string -> sanitizer  (* Whitelist check *)
  (* Crypto sanitizers *)
  | SanHashVerify        : sanitizer  (* Hash verification *)
  | SanSignatureVerify   : sanitizer  (* Signature verification *)
  | SanMacVerify         : sanitizer  (* MAC verification *)
  (* RIINA product sanitizers *)
  | SanGapuraAuth        : sanitizer  (* Gapura authentication check *)
  | SanZirahSession      : sanitizer  (* Zirah session validation *)
  | SanBentengBiometric  : sanitizer  (* Benteng biometric verification *)
  | SanSandiDecrypt      : sanitizer  (* Sandi decryption check *)
  | SanMenaraAttestation : sanitizer. (* Menara attestation check *)

(** Sanitizer composition *)
Inductive sanitizer_comp : Type :=
  | SanSingle : sanitizer -> sanitizer_comp
  | SanAnd    : sanitizer_comp -> sanitizer_comp -> sanitizer_comp  (* Both required *)
  | SanSeq    : sanitizer_comp -> sanitizer_comp -> sanitizer_comp. (* Sequential application *)

(** ** Capability Kinds

    Capability-based access control.
    Matches CTSS v1.0.1 specification (D42-J).
*)

Inductive capability_kind : Type :=
  (* File capabilities *)
  | CapFileRead    : capability_kind  (* Read file *)
  | CapFileWrite   : capability_kind  (* Write file *)
  | CapFileExecute : capability_kind  (* Execute file *)
  | CapFileDelete  : capability_kind  (* Delete file *)
  (* Network capabilities *)
  | CapNetConnect  : capability_kind  (* Outbound connection *)
  | CapNetListen   : capability_kind  (* Listen for connections *)
  | CapNetBind     : capability_kind  (* Bind to port *)
  (* Process capabilities *)
  | CapProcSpawn   : capability_kind  (* Spawn process *)
  | CapProcSignal  : capability_kind  (* Send signal *)
  (* System capabilities *)
  | CapSysTime     : capability_kind  (* Access system time *)
  | CapSysRandom   : capability_kind  (* Access random *)
  | CapSysEnv      : capability_kind  (* Access environment *)
  (* RIINA product capabilities *)
  | CapRootProduct : capability_kind  (* Root product capability *)
  | CapProductAccess : capability_kind. (* Product-specific access *)

(** Capability with optional constraints *)
Inductive capability : Type :=
  | CapBasic     : capability_kind -> capability
  | CapRevocable : capability -> capability
  | CapTimeBound : capability -> nat -> capability  (* Expires after N seconds *)
  | CapDelegated : capability -> ident -> capability. (* Delegated to principal *)

(** ** Types and Session Types (Mutually Inductive)

    Core type constructors for RIINA.
    Matches CTSS v1.0.1 specification.

    Types and session types are mutually inductive because:
    - Session types contain message types (ty)
    - Types can include channel types (session_type)
*)

Inductive ty : Type :=
  (* Primitive types *)
  | TUnit    : ty
  | TBool    : ty
  | TInt     : ty
  | TString  : ty
  | TBytes   : ty
  (* Function types *)
  | TFn      : ty -> ty -> effect -> ty  (* T1 -[ε]-> T2 *)
  (* Compound types *)
  | TProd    : ty -> ty -> ty            (* T1 × T2 *)
  | TSum     : ty -> ty -> ty            (* T1 + T2 *)
  | TList    : ty -> ty                  (* List[T] *)
  | TOption  : ty -> ty                  (* Option[T] *)
  (* Reference types *)
  | TRef     : ty -> security_level -> ty (* Ref[T]@l *)
  (* Security types - D42 integration *)
  | TSecret  : ty -> ty                  (* Secret[T] - classified data *)
  | TLabeled : ty -> security_level -> ty (* Labeled[T, l] - security label *)
  | TTainted : ty -> taint_source -> ty  (* Tainted[T, src] - tainted data *)
  | TSanitized : ty -> sanitizer -> ty   (* Sanitized[T, san] - sanitized data *)
  | TProof   : ty -> ty                  (* Proof[T] - declassification proof *)
  (* Capability types - D42-J integration *)
  | TCapability : capability_kind -> ty  (* Cap[kind] *)
  | TCapabilityFull : capability -> ty   (* Full capability with constraints *)
  (* Session types - D42-F integration *)
  | TChan    : session_type -> ty        (* Chan[S] - channel with session *)
  | TSecureChan : session_type -> security_level -> ty (* SecureChan[S, l] *)
  (* Constant-time types - for crypto *)
  | TConstantTime : ty -> ty             (* ConstantTime[T] *)
  (* Zeroizing types - secure memory *)
  | TZeroizing : ty -> ty                (* Zeroizing[T] - cleared on drop *)

(** Session types for binary communication protocols *)
with session_type : Type :=
  | SessEnd    : session_type                           (* Session end *)
  | SessSend   : ty -> session_type -> session_type     (* !T.S - send T then continue *)
  | SessRecv   : ty -> session_type -> session_type     (* ?T.S - receive T then continue *)
  | SessSelect : session_type -> session_type -> session_type  (* S1 ⊕ S2 - internal choice *)
  | SessBranch : session_type -> session_type -> session_type  (* S1 & S2 - external choice *)
  | SessRec    : ident -> session_type -> session_type  (* μX.S - recursive session *)
  | SessVar    : ident -> session_type.                 (* X - session variable *)

(** Session duality: dual(S) gives the other endpoint's type *)
Fixpoint session_dual (s : session_type) : session_type :=
  match s with
  | SessEnd => SessEnd
  | SessSend t s' => SessRecv t (session_dual s')
  | SessRecv t s' => SessSend t (session_dual s')
  | SessSelect s1 s2 => SessBranch (session_dual s1) (session_dual s2)
  | SessBranch s1 s2 => SessSelect (session_dual s1) (session_dual s2)
  | SessRec x s' => SessRec x (session_dual s')
  | SessVar x => SessVar x
  end.

(** Backward compatibility: old type names *)
Definition TCapabilityOld (e : effect) : ty :=
  TCapability (match e with
    | EffPure => CapSysRandom  (* placeholder *)
    | EffRead => CapFileRead
    | EffWrite => CapFileWrite
    | EffNetwork => CapNetConnect
    | _ => CapSysRandom
  end).

(** ** Expressions
    
    Core expression forms.
*)

Inductive expr : Type :=
  (* Values *)
  | EUnit   : expr
  | EBool   : bool -> expr
  | EInt    : nat -> expr
  | EString : string -> expr
  | ELoc    : loc -> expr
  | EVar    : ident -> expr
  
  (* Functions *)
  | ELam    : ident -> ty -> expr -> expr    (* λx:T. e *)
  | EApp    : expr -> expr -> expr           (* e1 e2 *)
  
  (* Products *)
  | EPair   : expr -> expr -> expr           (* (e1, e2) *)
  | EFst    : expr -> expr                   (* fst e *)
  | ESnd    : expr -> expr                   (* snd e *)
  
  (* Sums *)
  | EInl    : expr -> ty -> expr             (* inl e : T *)
  | EInr    : expr -> ty -> expr             (* inr e : T *)
  | ECase   : expr -> ident -> expr -> ident -> expr -> expr  (* case e of inl x => e1 | inr y => e2 *)
  
  (* Control *)
  | EIf     : expr -> expr -> expr -> expr   (* if e1 then e2 else e3 *)
  | ELet    : ident -> expr -> expr -> expr  (* let x = e1 in e2 *)
  
  (* Effects *)
  | EPerform : effect -> expr -> expr        (* perform ε e *)
  | EHandle  : expr -> ident -> expr -> expr (* handle e with x => h *)
  
  (* References *)
  | ERef    : expr -> security_level -> expr (* ref e @ l *)
  | EDeref  : expr -> expr                   (* !e *)
  | EAssign : expr -> expr -> expr           (* e1 := e2 *)
  
  (* Security *)
  | EClassify   : expr -> expr               (* classify e *)
  | EDeclassify : expr -> expr -> expr       (* declassify e with proof *)
  | EProve      : expr -> expr               (* prove e *)
  
  (* Capabilities *)
  | ERequire : effect -> expr -> expr        (* require ε in e *)
  | EGrant   : effect -> expr -> expr.       (* grant ε to e *)

(** ** Values
    
    Syntactic values for operational semantics.
*)

Inductive value : expr -> Prop :=
  | VUnit   : value EUnit
  | VBool   : forall b, value (EBool b)
  | VInt    : forall n, value (EInt n)
  | VString : forall s, value (EString s)
  | VLoc    : forall l, value (ELoc l)
  | VLam    : forall x T e, value (ELam x T e)
  | VPair   : forall v1 v2, value v1 -> value v2 -> value (EPair v1 v2)
  | VInl    : forall v T, value v -> value (EInl v T)
  | VInr    : forall v T, value v -> value (EInr v T)
  | VClassify : forall v, value v -> value (EClassify v)
  | VProve  : forall v, value v -> value (EProve v).

(** ** Well-Formedness *)

(** Session types are well-formed *)
Inductive wf_session : session_type -> Prop :=
  | WF_SessEnd : wf_session SessEnd
  | WF_SessSend : forall T S, wf_ty T -> wf_session S -> wf_session (SessSend T S)
  | WF_SessRecv : forall T S, wf_ty T -> wf_session S -> wf_session (SessRecv T S)
  | WF_SessSelect : forall S1 S2, wf_session S1 -> wf_session S2 -> wf_session (SessSelect S1 S2)
  | WF_SessBranch : forall S1 S2, wf_session S1 -> wf_session S2 -> wf_session (SessBranch S1 S2)
  | WF_SessRec : forall x S, wf_session S -> wf_session (SessRec x S)
  | WF_SessVar : forall x, wf_session (SessVar x)

(** Types are well-formed *)
with wf_ty : ty -> Prop :=
  (* Primitive types *)
  | WF_TUnit   : wf_ty TUnit
  | WF_TBool   : wf_ty TBool
  | WF_TInt    : wf_ty TInt
  | WF_TString : wf_ty TString
  | WF_TBytes  : wf_ty TBytes
  (* Function types *)
  | WF_TFn     : forall T1 T2 eff,
                   wf_ty T1 -> wf_ty T2 -> wf_ty (TFn T1 T2 eff)
  (* Compound types *)
  | WF_TProd   : forall T1 T2,
                   wf_ty T1 -> wf_ty T2 -> wf_ty (TProd T1 T2)
  | WF_TSum    : forall T1 T2,
                   wf_ty T1 -> wf_ty T2 -> wf_ty (TSum T1 T2)
  | WF_TList   : forall T,
                   wf_ty T -> wf_ty (TList T)
  | WF_TOption : forall T,
                   wf_ty T -> wf_ty (TOption T)
  (* Reference types *)
  | WF_TRef    : forall T l, wf_ty T -> wf_ty (TRef T l)
  (* Security types *)
  | WF_TSecret : forall T, wf_ty T -> wf_ty (TSecret T)
  | WF_TLabeled : forall T l, wf_ty T -> wf_ty (TLabeled T l)
  | WF_TTainted : forall T src, wf_ty T -> wf_ty (TTainted T src)
  | WF_TSanitized : forall T san, wf_ty T -> wf_ty (TSanitized T san)
  | WF_TProof  : forall T, wf_ty T -> wf_ty (TProof T)
  (* Capability types *)
  | WF_TCapability : forall k, wf_ty (TCapability k)
  | WF_TCapabilityFull : forall cap, wf_ty (TCapabilityFull cap)
  (* Channel types *)
  | WF_TChan : forall S, wf_session S -> wf_ty (TChan S)
  | WF_TSecureChan : forall S l, wf_session S -> wf_ty (TSecureChan S l)
  (* Constant-time and zeroizing types *)
  | WF_TConstantTime : forall T, wf_ty T -> wf_ty (TConstantTime T)
  | WF_TZeroizing : forall T, wf_ty T -> wf_ty (TZeroizing T).

(** ** Substitution
    
    Capture-avoiding substitution.
*)

Fixpoint subst (x : ident) (v : expr) (e : expr) : expr :=
  match e with
  | EUnit => EUnit
  | EBool b => EBool b
  | EInt n => EInt n
  | EString s => EString s
  | ELoc l => ELoc l
  | EVar y => if String.eqb x y then v else EVar y
  | ELam y T body =>
      if String.eqb x y then ELam y T body
      else ELam y T (subst x v body)
  | EApp e1 e2 => EApp (subst x v e1) (subst x v e2)
  | EPair e1 e2 => EPair (subst x v e1) (subst x v e2)
  | EFst e1 => EFst (subst x v e1)
  | ESnd e1 => ESnd (subst x v e1)
  | EInl e1 T => EInl (subst x v e1) T
  | EInr e1 T => EInr (subst x v e1) T
  | ECase e1 y1 e2 y2 e3 =>
      ECase (subst x v e1)
            y1 (if String.eqb x y1 then e2 else subst x v e2)
            y2 (if String.eqb x y2 then e3 else subst x v e3)
  | EIf e1 e2 e3 => EIf (subst x v e1) (subst x v e2) (subst x v e3)
  | ELet y e1 e2 =>
      ELet y (subst x v e1)
           (if String.eqb x y then e2 else subst x v e2)
  | EPerform eff e1 => EPerform eff (subst x v e1)
  | EHandle e1 y h =>
      EHandle (subst x v e1) y
              (if String.eqb x y then h else subst x v h)
  | ERef e1 l => ERef (subst x v e1) l
  | EDeref e1 => EDeref (subst x v e1)
  | EAssign e1 e2 => EAssign (subst x v e1) (subst x v e2)
  | EClassify e1 => EClassify (subst x v e1)
  | EDeclassify e1 e2 => EDeclassify (subst x v e1) (subst x v e2)
  | EProve e1 => EProve (subst x v e1)
  | ERequire eff e1 => ERequire eff (subst x v e1)
  | EGrant eff e1 => EGrant eff (subst x v e1)
  end.

Notation "[ x := v ] e" := (subst x v e) (at level 20).

(** ** Basic Lemmas *)

Definition declass_ok (e1 e2 : expr) : Prop :=
  exists v, value v /\ e1 = EClassify v /\ e2 = EProve (EClassify v).

Lemma value_subst : forall x v1 v2,
  value v1 ->
  value v2 ->
  value ([x := v2] v1).
Proof.
  intros x v1 v2 Hv1 Hv2.
  induction Hv1; simpl.
  - constructor.
  - constructor.
  - constructor.
  - constructor.
  - constructor.
  - destruct (String.eqb x x0) eqn:Heq; apply VLam.
  - constructor; eauto.
  - constructor; eauto.
  - constructor; eauto.
  - constructor; eauto.
  - constructor; eauto.
Qed.

Lemma declass_ok_subst : forall x v e1 e2,
  value v ->
  declass_ok e1 e2 ->
  declass_ok ([x := v] e1) ([x := v] e2).
Proof.
  intros x v e1 e2 Hv Hok.
  destruct Hok as [v0 [Hv0 [He1 He2]]]; subst.
  simpl. exists ([x := v] v0). split.
  - apply value_subst; assumption.
  - split; reflexivity.
Qed.

Lemma value_not_stuck : forall e,
  value e -> e = EUnit \/ (exists b, e = EBool b) \/ (exists n, e = EInt n) \/
             (exists s, e = EString s) \/ (exists x T body, e = ELam x T body) \/
             (exists v1 v2, e = EPair v1 v2) \/
             (exists v T, e = EInl v T) \/ (exists v T, e = EInr v T) \/
             (exists l, e = ELoc l) \/ (exists v, e = EClassify v) \/
             (exists v, e = EProve v).
Proof.
  intros e Hv.
  inversion Hv; subst.
  - left. reflexivity.
  - right. left. exists b. reflexivity.
  - right. right. left. exists n. reflexivity.
  - right. right. right. left. exists s. reflexivity.
  - right. right. right. right. right. right. right. right. left. exists l. reflexivity.
  - right. right. right. right. left. eexists; eexists; eexists; reflexivity.
  - right. right. right. right. right. left. exists v1, v2. reflexivity.
  - right. right. right. right. right. right. left. exists v, T. reflexivity.
  - right. right. right. right. right. right. right. left. exists v, T. reflexivity.
  - right. right. right. right. right. right. right. right. right. left. exists v. reflexivity.
  - right. right. right. right. right. right. right. right. right. right. exists v. reflexivity.
Qed.

(** Note: A lemma about substitution into values requires either:
    1. A 'closed' predicate ensuring values have no free variables, or
    2. A 'free_vars' function to check if x is free in e.

    The naive statement "forall x v e, value e -> [x := v] e = e" is false
    because lambda bodies can contain free variables. We will add the
    correct formulation in Preservation.v when needed for type safety. *)

(** End of Syntax.v *)
