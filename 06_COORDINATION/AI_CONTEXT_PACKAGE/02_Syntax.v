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
