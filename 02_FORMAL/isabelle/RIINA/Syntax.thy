(* Copyright (c) 2026 The RIINA Authors. All rights reserved. *)

(*
 * RIINA Syntax - Isabelle/HOL Port
 *
 * Exact port of 02_FORMAL/coq/foundations/Syntax.v (585 lines, 3 Qed).
 *
 * Reference: RIINA-AST_v1_0_0.md
 *
 * Mode: Comprehensive Verification | Zero Trust
 *
 * Correspondence Table:
 *
 * | Coq Definition     | Isabelle Definition    | Status |
 * |--------------------|------------------------|--------|
 * | ident              | ident                  | OK     |
 * | loc                | loc                    | OK     |
 * | security_level     | security_level         | OK     |
 * | sec_level_num      | sec_level_num          | OK     |
 * | sec_leq            | sec_leq                | OK     |
 * | sec_join           | sec_join               | OK     |
 * | sec_meet           | sec_meet               | OK     |
 * | effect             | effect                 | OK     |
 * | effect_category    | effect_category        | OK     |
 * | effect_cat         | effect_cat             | OK     |
 * | effect_level       | effect_level           | OK     |
 * | effect_join        | effect_join            | OK     |
 * | effect_join_pure_l | effect_join_pure_l     | OK     |
 * | effect_join_pure_r | effect_join_pure_r     | OK     |
 * | taint_source       | taint_source           | OK     |
 * | sanitizer          | sanitizer              | OK     |
 * | capability_kind    | capability_kind        | OK     |
 * | capability         | capability             | OK     |
 * | ty                 | ty                     | OK     |
 * | session_type       | session_type           | OK     |
 * | session_dual       | session_dual           | OK     |
 * | expr               | expr                   | OK     |
 * | value              | value                  | OK     |
 * | wf_ty              | wf_ty                  | OK     |
 * | wf_session         | wf_session             | OK     |
 * | subst              | subst                  | OK     |
 * | value_subst        | value_subst            | OK     |
 * | declass_ok         | declass_ok             | OK     |
 * | declass_ok_subst   | declass_ok_subst       | OK     |
 * | value_not_stuck    | value_not_stuck        | OK     |
 *)

theory Syntax
  imports Main "HOL-Library.Datatype_Records"
begin

section \<open>Identifiers\<close>

(* Identifiers are strings (matches Coq: Definition ident := string) *)
type_synonym ident = string

(* Locations are natural numbers (matches Coq: Definition loc := nat) *)
type_synonym loc = nat


section \<open>Security Levels\<close>

text \<open>
  RIINA uses a multi-level lattice for information flow control.
  Matches CTSS v1.0.1 specification (D42-A).

  Lattice structure:
    Public \<sqsubseteq> Internal \<sqsubseteq> Session \<sqsubseteq> User \<sqsubseteq> System \<sqsubseteq> Secret
\<close>

(* Security levels (matches Coq: Inductive security_level, 6 constructors) *)
datatype security_level =
    LPublic    (* Publicly observable *)
  | LInternal  (* Internal use only *)
  | LSession   (* Session-scoped *)
  | LUser      (* User-level sensitive *)
  | LSystem    (* System-level sensitive *)
  | LSecret    (* Maximum secrecy *)

(* Numeric encoding for ordering (matches Coq: sec_level_num) *)
fun sec_level_num :: "security_level \<Rightarrow> nat" where
  "sec_level_num LPublic   = 0"
| "sec_level_num LInternal = 1"
| "sec_level_num LSession  = 2"
| "sec_level_num LUser     = 3"
| "sec_level_num LSystem   = 4"
| "sec_level_num LSecret   = 5"

(* Security level ordering: l1 \<sqsubseteq> l2 (matches Coq: sec_leq) *)
definition sec_leq :: "security_level \<Rightarrow> security_level \<Rightarrow> bool" where
  "sec_leq l1 l2 \<equiv> sec_level_num l1 \<le> sec_level_num l2"

(* Join (least upper bound) (matches Coq: sec_join) *)
definition sec_join :: "security_level \<Rightarrow> security_level \<Rightarrow> security_level" where
  "sec_join l1 l2 \<equiv> if sec_level_num l1 \<le> sec_level_num l2 then l2 else l1"

(* Meet (greatest lower bound) (matches Coq: sec_meet) *)
definition sec_meet :: "security_level \<Rightarrow> security_level \<Rightarrow> security_level" where
  "sec_meet l1 l2 \<equiv> if sec_level_num l1 \<le> sec_level_num l2 then l1 else l2"


section \<open>Effect Labels\<close>

text \<open>
  Effects track observable behaviors of computations.
  Matches CTSS v1.0.1 specification (D40).
\<close>

(* Effects (matches Coq: Inductive effect, 17 constructors) *)
datatype effect =
  (* Base effects *)
    EffPure        (* No observable effect *)
  | EffRead        (* Memory/state read *)
  | EffWrite       (* Memory/state write *)
  | EffFileSystem  (* File system access *)
  (* Network effects *)
  | EffNetwork     (* Network I/O *)
  | EffNetSecure   (* Secure network (TLS) *)
  (* Crypto effects *)
  | EffCrypto      (* Cryptographic operations *)
  | EffRandom      (* Random number generation *)
  (* System effects *)
  | EffSystem      (* System calls *)
  | EffTime        (* Time/clock access *)
  | EffProcess     (* Process management *)
  (* RIINA product effects *)
  | EffPanel       (* Panel UI operations *)
  | EffZirah       (* Zirah API operations *)
  | EffBenteng     (* Benteng auth operations *)
  | EffSandi       (* Sandi crypto operations *)
  | EffMenara      (* Menara device operations *)
  | EffGapura      (* Gapura gateway operations *)

(* Effect categories (matches Coq: Inductive effect_category, 6 constructors) *)
datatype effect_category =
    CatPure
  | CatIO
  | CatNetwork
  | CatCrypto
  | CatSystem
  | CatProduct

(* Category of an effect (matches Coq: effect_cat) *)
fun effect_cat :: "effect \<Rightarrow> effect_category" where
  "effect_cat EffPure = CatPure"
| "effect_cat EffRead = CatIO"
| "effect_cat EffWrite = CatIO"
| "effect_cat EffFileSystem = CatIO"
| "effect_cat EffNetwork = CatNetwork"
| "effect_cat EffNetSecure = CatNetwork"
| "effect_cat EffCrypto = CatCrypto"
| "effect_cat EffRandom = CatCrypto"
| "effect_cat EffSystem = CatSystem"
| "effect_cat EffTime = CatSystem"
| "effect_cat EffProcess = CatSystem"
| "effect_cat EffPanel = CatProduct"
| "effect_cat EffZirah = CatProduct"
| "effect_cat EffBenteng = CatProduct"
| "effect_cat EffSandi = CatProduct"
| "effect_cat EffMenara = CatProduct"
| "effect_cat EffGapura = CatProduct"

(* Level within category for ordering (matches Coq: effect_level) *)
fun effect_level :: "effect \<Rightarrow> nat" where
  "effect_level EffPure = 0"
| "effect_level EffRead = 1"
| "effect_level EffWrite = 2"
| "effect_level EffFileSystem = 3"
| "effect_level EffNetwork = 4"
| "effect_level EffNetSecure = 5"
| "effect_level EffCrypto = 6"
| "effect_level EffRandom = 7"
| "effect_level EffSystem = 8"
| "effect_level EffTime = 9"
| "effect_level EffProcess = 10"
| "effect_level EffPanel = 11"
| "effect_level EffZirah = 12"
| "effect_level EffBenteng = 13"
| "effect_level EffSandi = 14"
| "effect_level EffMenara = 15"
| "effect_level EffGapura = 16"

(* Effect join: max in hierarchy (matches Coq: effect_join) *)
definition effect_join :: "effect \<Rightarrow> effect \<Rightarrow> effect" where
  "effect_join e1 e2 \<equiv> if effect_level e1 < effect_level e2 then e2 else e1"

(* Pure is identity for effect join (left) (matches Coq: effect_join_pure_l) *)
lemma effect_join_pure_l: "effect_join EffPure e = e"
  by (cases e) (simp_all add: effect_join_def)

(* Pure is identity for effect join (right) (matches Coq: effect_join_pure_r) *)
lemma effect_join_pure_r: "effect_join e EffPure = e"
  by (cases e) (simp_all add: effect_join_def)


section \<open>Taint Sources\<close>

text \<open>
  Taint tracking for untrusted data.
  Matches CTSS v1.0.1 specification (D42-E).
\<close>

(* Taint sources (matches Coq: Inductive taint_source, 12 constructors) *)
datatype taint_source =
  (* Network sources *)
    TaintNetworkExternal  (* External network input *)
  | TaintNetworkInternal  (* Internal network input *)
  (* User input sources *)
  | TaintUserInput        (* Direct user input *)
  | TaintFileSystem       (* File system data *)
  | TaintDatabase         (* Database query results *)
  | TaintEnvironment      (* Environment variables *)
  (* RIINA product sources *)
  | TaintGapuraRequest    (* Gapura API request *)
  | TaintZirahEvent       (* Zirah event data *)
  | TaintZirahEndpoint    (* Zirah endpoint data *)
  | TaintBentengBiometric (* Benteng biometric data *)
  | TaintSandiSignature   (* Sandi signature input *)
  | TaintMenaraDevice     (* Menara device data *)


section \<open>Sanitizers\<close>

text \<open>
  Sanitization markers for tainted data.
  Matches CTSS v1.0.1 specification (D42-E).
\<close>

(* Sanitizers (matches Coq: Inductive sanitizer, 26+ constructors) *)
datatype sanitizer =
  (* Web sanitizers *)
    SanHtmlEscape          (* HTML entity escaping *)
  | SanUrlEncode           (* URL encoding *)
  | SanJsEscape            (* JavaScript string escaping *)
  | SanCssEscape           (* CSS escaping *)
  (* SQL sanitizers *)
  | SanSqlEscape           (* SQL string escaping *)
  | SanSqlParam            (* Parameterized query *)
  (* Injection prevention *)
  | SanXssFilter           (* XSS filtering *)
  | SanPathTraversal       (* Path traversal check *)
  | SanCommandEscape       (* Command injection prevention *)
  | SanLdapEscape          (* LDAP injection prevention *)
  | SanXmlEscape           (* XML escaping *)
  (* Validation sanitizers *)
  | SanJsonValidation      (* JSON structure validation *)
  | SanXmlValidation       (* XML schema validation *)
  | SanEmailValidation     (* Email format validation *)
  | SanPhoneValidation     (* Phone format validation *)
  (* Bound sanitizers *)
  | SanLengthBound nat     (* Maximum length check *)
  | SanRangeBound nat nat  (* Numeric range check *)
  | SanRegexMatch string   (* Regex pattern match *)
  | SanWhitelist "string list"  (* Whitelist check *)
  (* Crypto sanitizers *)
  | SanHashVerify          (* Hash verification *)
  | SanSignatureVerify     (* Signature verification *)
  | SanMacVerify           (* MAC verification *)
  (* RIINA product sanitizers *)
  | SanGapuraAuth          (* Gapura authentication check *)
  | SanZirahSession        (* Zirah session validation *)
  | SanBentengBiometric    (* Benteng biometric verification *)
  | SanSandiDecrypt        (* Sandi decryption check *)
  | SanMenaraAttestation   (* Menara attestation check *)

(* Sanitizer composition (matches Coq: Inductive sanitizer_comp) *)
datatype sanitizer_comp =
    SanSingle sanitizer
  | SanAnd sanitizer_comp sanitizer_comp   (* Both required *)
  | SanSeq sanitizer_comp sanitizer_comp   (* Sequential application *)


section \<open>Capability Kinds\<close>

text \<open>
  Capability-based access control.
  Matches CTSS v1.0.1 specification (D42-J).
\<close>

(* Capability kinds (matches Coq: Inductive capability_kind, 14 constructors) *)
datatype capability_kind =
  (* File capabilities *)
    CapFileRead     (* Read file *)
  | CapFileWrite    (* Write file *)
  | CapFileExecute  (* Execute file *)
  | CapFileDelete   (* Delete file *)
  (* Network capabilities *)
  | CapNetConnect   (* Outbound connection *)
  | CapNetListen    (* Listen for connections *)
  | CapNetBind      (* Bind to port *)
  (* Process capabilities *)
  | CapProcSpawn    (* Spawn process *)
  | CapProcSignal   (* Send signal *)
  (* System capabilities *)
  | CapSysTime      (* Access system time *)
  | CapSysRandom    (* Access random *)
  | CapSysEnv       (* Access environment *)
  (* RIINA product capabilities *)
  | CapRootProduct    (* Root product capability *)
  | CapProductAccess  (* Product-specific access *)

(* Capabilities with constraints (matches Coq: Inductive capability) *)
datatype capability =
    CapBasic capability_kind
  | CapRevocable capability
  | CapTimeBound capability nat    (* Expires after N seconds *)
  | CapDelegated capability ident  (* Delegated to principal *)


section \<open>Types and Session Types\<close>

text \<open>
  Core type constructors for RIINA.
  Matches CTSS v1.0.1 specification.

  Types and session types are mutually inductive because:
  - Session types contain message types (ty)
  - Types can include channel types (session_type)
\<close>

(* Session types and types (mutually inductive) *)
datatype ty =
  (* Primitive types *)
    TUnit
  | TBool
  | TInt
  | TString
  | TBytes
  (* Function types *)
  | TFn ty ty effect                     (* T1 -[\<epsilon>]-> T2 *)
  (* Compound types *)
  | TProd ty ty                          (* T1 \<times> T2 *)
  | TSum ty ty                           (* T1 + T2 *)
  | TList ty                             (* List[T] *)
  | TOption ty                           (* Option[T] *)
  (* Reference types *)
  | TRef ty security_level               (* Ref[T]@l *)
  (* Security types *)
  | TSecret ty                           (* Secret[T] *)
  | TLabeled ty security_level           (* Labeled[T, l] *)
  | TTainted ty taint_source             (* Tainted[T, src] *)
  | TSanitized ty sanitizer              (* Sanitized[T, san] *)
  | TProof ty                            (* Proof[T] *)
  (* Capability types *)
  | TCapability capability_kind          (* Cap[kind] *)
  | TCapabilityFull capability           (* Full capability with constraints *)
  (* Session types *)
  | TChan session_type                   (* Chan[S] *)
  | TSecureChan session_type security_level  (* SecureChan[S, l] *)
  (* Constant-time types *)
  | TConstantTime ty                     (* ConstantTime[T] *)
  (* Zeroizing types *)
  | TZeroizing ty                        (* Zeroizing[T] *)

and session_type =
    SessEnd                                    (* Session end *)
  | SessSend ty session_type                   (* !T.S - send T then continue *)
  | SessRecv ty session_type                   (* ?T.S - receive T then continue *)
  | SessSelect session_type session_type       (* S1 \<oplus> S2 - internal choice *)
  | SessBranch session_type session_type       (* S1 & S2 - external choice *)
  | SessRec ident session_type                 (* \<mu>X.S - recursive session *)
  | SessVar ident                              (* X - session variable *)

(* Session duality (matches Coq: Fixpoint session_dual) *)
fun session_dual :: "session_type \<Rightarrow> session_type" where
  "session_dual SessEnd = SessEnd"
| "session_dual (SessSend t s) = SessRecv t (session_dual s)"
| "session_dual (SessRecv t s) = SessSend t (session_dual s)"
| "session_dual (SessSelect s1 s2) = SessBranch (session_dual s1) (session_dual s2)"
| "session_dual (SessBranch s1 s2) = SessSelect (session_dual s1) (session_dual s2)"
| "session_dual (SessRec x s) = SessRec x (session_dual s)"
| "session_dual (SessVar x) = SessVar x"


section \<open>Expressions\<close>

text \<open>
  Core expression forms.
  (matches Coq: Inductive expr, 27 constructors)
\<close>

datatype expr =
  (* Values *)
    EUnit
  | EBool bool
  | EInt nat
  | EString string
  | ELoc loc
  | EVar ident
  (* Functions *)
  | ELam ident ty expr                            (* \<lambda>x:T. e *)
  | EApp expr expr                                (* e1 e2 *)
  (* Products *)
  | EPair expr expr                               (* (e1, e2) *)
  | EFst expr                                     (* fst e *)
  | ESnd expr                                     (* snd e *)
  (* Sums *)
  | EInl expr ty                                  (* inl e : T *)
  | EInr expr ty                                  (* inr e : T *)
  | ECase expr ident expr ident expr              (* case e of inl x => e1 | inr y => e2 *)
  (* Control *)
  | EIf expr expr expr                            (* if e1 then e2 else e3 *)
  | ELet ident expr expr                          (* let x = e1 in e2 *)
  (* Effects *)
  | EPerform effect expr                          (* perform \<epsilon> e *)
  | EHandle expr ident expr                       (* handle e with x => h *)
  (* References *)
  | ERef expr security_level                      (* ref e @ l *)
  | EDeref expr                                   (* !e *)
  | EAssign expr expr                             (* e1 := e2 *)
  (* Security *)
  | EClassify expr                                (* classify e *)
  | EDeclassify expr expr                         (* declassify e with proof *)
  | EProve expr                                   (* prove e *)
  (* Capabilities *)
  | ERequire effect expr                          (* require \<epsilon> in e *)
  | EGrant effect expr                            (* grant \<epsilon> to e *)


section \<open>Values\<close>

text \<open>
  Syntactic values for operational semantics.
  (matches Coq: Inductive value, 11 constructors)
\<close>

inductive value :: "expr \<Rightarrow> bool" where
  VUnit:   "value EUnit"
| VBool:   "value (EBool b)"
| VInt:    "value (EInt n)"
| VString: "value (EString s)"
| VLoc:    "value (ELoc l)"
| VLam:    "value (ELam x T e)"
| VPair:   "value v1 \<Longrightarrow> value v2 \<Longrightarrow> value (EPair v1 v2)"
| VInl:    "value v \<Longrightarrow> value (EInl v T)"
| VInr:    "value v \<Longrightarrow> value (EInr v T)"
| VClassify: "value v \<Longrightarrow> value (EClassify v)"
| VProve:  "value v \<Longrightarrow> value (EProve v)"


section \<open>Well-Formedness\<close>

text \<open>
  (matches Coq: Inductive wf_ty and wf_session)
\<close>

inductive wf_ty :: "ty \<Rightarrow> bool"
      and wf_session :: "session_type \<Rightarrow> bool" where
  (* Types *)
  WF_TUnit:   "wf_ty TUnit"
| WF_TBool:   "wf_ty TBool"
| WF_TInt:    "wf_ty TInt"
| WF_TString: "wf_ty TString"
| WF_TBytes:  "wf_ty TBytes"
| WF_TFn:     "wf_ty T1 \<Longrightarrow> wf_ty T2 \<Longrightarrow> wf_ty (TFn T1 T2 eff)"
| WF_TProd:   "wf_ty T1 \<Longrightarrow> wf_ty T2 \<Longrightarrow> wf_ty (TProd T1 T2)"
| WF_TSum:    "wf_ty T1 \<Longrightarrow> wf_ty T2 \<Longrightarrow> wf_ty (TSum T1 T2)"
| WF_TList:   "wf_ty T \<Longrightarrow> wf_ty (TList T)"
| WF_TOption: "wf_ty T \<Longrightarrow> wf_ty (TOption T)"
| WF_TRef:    "wf_ty T \<Longrightarrow> wf_ty (TRef T l)"
| WF_TSecret: "wf_ty T \<Longrightarrow> wf_ty (TSecret T)"
| WF_TLabeled: "wf_ty T \<Longrightarrow> wf_ty (TLabeled T l)"
| WF_TTainted: "wf_ty T \<Longrightarrow> wf_ty (TTainted T src)"
| WF_TSanitized: "wf_ty T \<Longrightarrow> wf_ty (TSanitized T san)"
| WF_TProof:  "wf_ty T \<Longrightarrow> wf_ty (TProof T)"
| WF_TCapability: "wf_ty (TCapability k)"
| WF_TCapabilityFull: "wf_ty (TCapabilityFull cap)"
| WF_TChan:   "wf_session S \<Longrightarrow> wf_ty (TChan S)"
| WF_TSecureChan: "wf_session S \<Longrightarrow> wf_ty (TSecureChan S l)"
| WF_TConstantTime: "wf_ty T \<Longrightarrow> wf_ty (TConstantTime T)"
| WF_TZeroizing: "wf_ty T \<Longrightarrow> wf_ty (TZeroizing T)"
  (* Session types *)
| WF_SessEnd: "wf_session SessEnd"
| WF_SessSend: "wf_ty T \<Longrightarrow> wf_session S \<Longrightarrow> wf_session (SessSend T S)"
| WF_SessRecv: "wf_ty T \<Longrightarrow> wf_session S \<Longrightarrow> wf_session (SessRecv T S)"
| WF_SessSelect: "wf_session S1 \<Longrightarrow> wf_session S2 \<Longrightarrow> wf_session (SessSelect S1 S2)"
| WF_SessBranch: "wf_session S1 \<Longrightarrow> wf_session S2 \<Longrightarrow> wf_session (SessBranch S1 S2)"
| WF_SessRec: "wf_session S \<Longrightarrow> wf_session (SessRec x S)"
| WF_SessVar: "wf_session (SessVar x)"


section \<open>Substitution\<close>

text \<open>
  Capture-avoiding substitution.
  (matches Coq: Fixpoint subst)
\<close>

fun subst :: "ident \<Rightarrow> expr \<Rightarrow> expr \<Rightarrow> expr" where
  "subst x v EUnit = EUnit"
| "subst x v (EBool b) = EBool b"
| "subst x v (EInt n) = EInt n"
| "subst x v (EString s) = EString s"
| "subst x v (ELoc l) = ELoc l"
| "subst x v (EVar y) = (if x = y then v else EVar y)"
| "subst x v (ELam y T body) =
     (if x = y then ELam y T body else ELam y T (subst x v body))"
| "subst x v (EApp e1 e2) = EApp (subst x v e1) (subst x v e2)"
| "subst x v (EPair e1 e2) = EPair (subst x v e1) (subst x v e2)"
| "subst x v (EFst e1) = EFst (subst x v e1)"
| "subst x v (ESnd e1) = ESnd (subst x v e1)"
| "subst x v (EInl e1 T) = EInl (subst x v e1) T"
| "subst x v (EInr e1 T) = EInr (subst x v e1) T"
| "subst x v (ECase e1 y1 e2 y2 e3) =
     ECase (subst x v e1)
           y1 (if x = y1 then e2 else subst x v e2)
           y2 (if x = y2 then e3 else subst x v e3)"
| "subst x v (EIf e1 e2 e3) = EIf (subst x v e1) (subst x v e2) (subst x v e3)"
| "subst x v (ELet y e1 e2) =
     ELet y (subst x v e1) (if x = y then e2 else subst x v e2)"
| "subst x v (EPerform eff e1) = EPerform eff (subst x v e1)"
| "subst x v (EHandle e1 y h) =
     EHandle (subst x v e1) y (if x = y then h else subst x v h)"
| "subst x v (ERef e1 l) = ERef (subst x v e1) l"
| "subst x v (EDeref e1) = EDeref (subst x v e1)"
| "subst x v (EAssign e1 e2) = EAssign (subst x v e1) (subst x v e2)"
| "subst x v (EClassify e1) = EClassify (subst x v e1)"
| "subst x v (EDeclassify e1 e2) = EDeclassify (subst x v e1) (subst x v e2)"
| "subst x v (EProve e1) = EProve (subst x v e1)"
| "subst x v (ERequire eff e1) = ERequire eff (subst x v e1)"
| "subst x v (EGrant eff e1) = EGrant eff (subst x v e1)"

notation subst ("\<lbrakk>_ := _\<rbrakk> _" [100, 100, 100] 100)


section \<open>Basic Lemmas\<close>

text \<open>
  Declassification well-formedness (matches Coq: declass_ok)
\<close>

definition declass_ok :: "expr \<Rightarrow> expr \<Rightarrow> bool" where
  "declass_ok e1 e2 \<equiv> \<exists>v. value v \<and> e1 = EClassify v \<and> e2 = EProve (EClassify v)"

text \<open>
  Value preserved under substitution (matches Coq: value_subst)
\<close>

lemma value_subst: "value v1 \<Longrightarrow> value v2 \<Longrightarrow> value (subst x v2 v1)"
proof (induction v1 rule: value.induct)
  case VUnit thus ?case by (simp add: value.VUnit)
next
  case (VBool b) thus ?case by (simp add: value.VBool)
next
  case (VInt n) thus ?case by (simp add: value.VInt)
next
  case (VString s) thus ?case by (simp add: value.VString)
next
  case (VLoc l) thus ?case by (simp add: value.VLoc)
next
  case (VLam x' T e) thus ?case by (cases "x = x'") (simp_all add: value.VLam)
next
  case (VPair v1 v2) thus ?case by (simp add: value.VPair)
next
  case (VInl v T) thus ?case by (simp add: value.VInl)
next
  case (VInr v T) thus ?case by (simp add: value.VInr)
next
  case (VClassify v) thus ?case by (simp add: value.VClassify)
next
  case (VProve v) thus ?case by (simp add: value.VProve)
qed

text \<open>
  Declassification preserved under substitution (matches Coq: declass_ok_subst)
\<close>

lemma declass_ok_subst:
  assumes "value v" and "declass_ok e1 e2"
  shows "declass_ok (subst x v e1) (subst x v e2)"
proof -
  from assms(2) obtain v0 where
    "value v0" "e1 = EClassify v0" "e2 = EProve (EClassify v0)"
    unfolding declass_ok_def by auto
  hence "subst x v e1 = EClassify (subst x v v0)"
    and "subst x v e2 = EProve (EClassify (subst x v v0))"
    by simp_all
  moreover have "value (subst x v v0)"
    using value_subst \<open>value v0\<close> assms(1) by blast
  ultimately show ?thesis
    unfolding declass_ok_def by blast
qed

text \<open>
  Values are not stuck (matches Coq: value_not_stuck)
\<close>

lemma value_not_stuck:
  assumes "value e"
  shows "e = EUnit \<or>
         (\<exists>b. e = EBool b) \<or>
         (\<exists>n. e = EInt n) \<or>
         (\<exists>s. e = EString s) \<or>
         (\<exists>x T body. e = ELam x T body) \<or>
         (\<exists>v1 v2. e = EPair v1 v2) \<or>
         (\<exists>v T. e = EInl v T) \<or>
         (\<exists>v T. e = EInr v T) \<or>
         (\<exists>l. e = ELoc l) \<or>
         (\<exists>v. e = EClassify v) \<or>
         (\<exists>v. e = EProve v)"
  using assms by (cases e rule: value.cases) auto


section \<open>Verification Summary\<close>

text \<open>
  This theory ports Syntax.v (585 lines Coq) to Isabelle/HOL.

  | Coq Lemma         | Isabelle Lemma       | Status   |
  |-------------------|----------------------|----------|
  | effect_join_pure_l| effect_join_pure_l   | Proved   |
  | effect_join_pure_r| effect_join_pure_r   | Proved   |
  | value_subst       | value_subst          | Proved   |
  | declass_ok_subst  | declass_ok_subst     | Proved   |
  | value_not_stuck   | value_not_stuck      | Proved   |

  Total: 5 lemmas ported
\<close>

end
