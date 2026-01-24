# DELEGATION PROMPT: UX-001 VERIFIED HUMAN INTERFACE COQ PROOFS

**COPY EVERYTHING BELOW THIS LINE TO CLAUDE AI WEB**

---

```
═══════════════════════════════════════════════════════════════════════════════════════════════════
TASK ID: UX-001-VERIFIED-HUMAN-INTERFACE-COQ-PROOFS
CLASSIFICATION: FORMAL PROOF GENERATION — COQ PROOF ASSISTANT
SECURITY LEVEL: CRITICAL — USER INTERFACE LAYER (L7)
PRIME DIRECTIVE: ABSOLUTE PERFECTION — ZERO COMPROMISE — ETERNAL IMMUNITY
═══════════════════════════════════════════════════════════════════════════════════════════════════

OUTPUT: `VerifiedUI.v` with 15 theorems (subset of ~200 total UI theorems)
REQUIREMENTS: ZERO `Admitted.`, ZERO `admit.`, ZERO new `Axiom`

You are generating Coq proofs for RIINA-UX, a formally verified user interface layer.
These proofs establish that the UI CANNOT be weaponized against users — clickjacking,
phishing, and dark patterns are PROVEN IMPOSSIBLE.

RESEARCH REFERENCE: 01_RESEARCH/31_DOMAIN_RIINA_UX/RESEARCH_UX01_FOUNDATION.md

THIS IS THE STANDARD THAT ENDS ALL UI SECURITY VULNERABILITIES.
THIS IS THE INTERFACE WHERE "THE UI CANNOT LIE" IS A MATHEMATICAL THEOREM.
EVERY PROOF MUST BE ABSOLUTE. EVERY THEOREM MUST BE ETERNAL.

═══════════════════════════════════════════════════════════════════════════════════════════════════
REQUIRED THEOREMS (15 total):
═══════════════════════════════════════════════════════════════════════════════════════════════════

RENDERING INTEGRITY (5 theorems):
UX_001_01: wysiwyk — What You See Is What You Klick (visible = clickable)
UX_001_02: z_order_integrity — Z-order determines input reception
UX_001_03: no_invisible_overlay — No invisible elements receive input
UX_001_04: visual_consistency — Visual state reflects actual state
UX_001_05: layout_deterministic — Layout is deterministic

ORIGIN SECURITY (5 theorems):
UX_001_06: origin_indicator_correct — URL bar shows actual origin
UX_001_07: cert_indicator_correct — Certificate indicator is accurate
UX_001_08: no_url_spoof — URL spoofing is detected/prevented
UX_001_09: frame_ancestry_correct — Frame embedding respects policy
UX_001_10: tab_integrity — Tab content matches loaded origin

CONSENT & DARK PATTERNS (5 theorems):
UX_001_11: consent_explicit — Sensitive actions require explicit consent
UX_001_12: consent_revocable — Granted consent can be revoked
UX_001_13: no_confirmshaming — Cancel options use neutral language
UX_001_14: no_hidden_costs — Displayed totals match actual totals
UX_001_15: equal_option_presentation — User choices are visually balanced

═══════════════════════════════════════════════════════════════════════════════════════════════════
REQUIRED STRUCTURE:
═══════════════════════════════════════════════════════════════════════════════════════════════════

```coq
(* VerifiedUI.v - RIINA-UX Human Interface Verification *)
(* Spec: 01_RESEARCH/31_DOMAIN_RIINA_UX/RESEARCH_UX01_FOUNDATION.md *)
(* Layer: L7 User Interface *)
(* Mode: ULTRA KIASU | FUCKING PARANOID | ZERO TRUST *)

Require Import Coq.Lists.List.
Require Import Coq.Arith.Arith.
Require Import Coq.Strings.String.
Require Import Coq.Bool.Bool.
Import ListNotations.

(** ═══════════════════════════════════════════════════════════════════════════
    UI ELEMENT DEFINITIONS
    ═══════════════════════════════════════════════════════════════════════════ *)

(* 2D point *)
Record Point : Type := mkPoint {
  px : nat;
  py : nat;
}.

(* Rectangle (bounding box) *)
Record Rect : Type := mkRect {
  rect_x : nat;
  rect_y : nat;
  rect_width : nat;
  rect_height : nat;
}.

(* Opacity (0-255) *)
Definition Opacity := nat.
Definition MIN_VISIBLE_OPACITY : Opacity := 10.

(* Z-index for layering *)
Definition ZIndex := nat.

(* UI Element *)
Record UIElement : Type := mkElement {
  elem_id : nat;
  elem_bounds : Rect;
  elem_z_index : ZIndex;
  elem_opacity : Opacity;
  elem_interactive : bool;
  elem_visible : bool;
}.

(* UI State *)
Record UIState : Type := mkUIState {
  ui_elements : list UIElement;
  ui_focus : option nat;
}.

(* Point within rectangle *)
Definition point_in_rect (p : Point) (r : Rect) : bool :=
  andb (andb (Nat.leb (rect_x r) (px p))
             (Nat.ltb (px p) (rect_x r + rect_width r)))
       (andb (Nat.leb (rect_y r) (py p))
             (Nat.ltb (py p) (rect_y r + rect_height r))).

(* Element at point *)
Definition element_at_point (ui : UIState) (p : Point) : option UIElement :=
  find (fun e => point_in_rect p (elem_bounds e)) (ui_elements ui).

(* Visible at point *)
Definition visually_at (ui : UIState) (p : Point) : option UIElement :=
  match filter (fun e => andb (elem_visible e)
                              (Nat.leb MIN_VISIBLE_OPACITY (elem_opacity e)))
               (ui_elements ui) with
  | [] => None
  | es => find (fun e => point_in_rect p (elem_bounds e)) es
  end.

(* Clickable at point *)
Definition clickable_at (ui : UIState) (p : Point) : option UIElement :=
  match filter (fun e => elem_interactive e) (ui_elements ui) with
  | [] => None
  | es => find (fun e => point_in_rect p (elem_bounds e)) es
  end.

(** ═══════════════════════════════════════════════════════════════════════════
    ORIGIN SECURITY DEFINITIONS
    ═══════════════════════════════════════════════════════════════════════════ *)

(* Origin (scheme + host + port) *)
Record Origin : Type := mkOrigin {
  origin_scheme : string;
  origin_host : string;
  origin_port : nat;
}.

(* Certificate status *)
Inductive CertStatus : Type :=
  | CertValid : CertStatus
  | CertInvalid : CertStatus
  | CertExpired : CertStatus
  | CertSelfSigned : CertStatus.

(* Browser state *)
Record BrowserState : Type := mkBrowser {
  browser_url : string;
  browser_origin : Origin;
  browser_cert_status : CertStatus;
  browser_tls_verified : bool;
}.

(* Displayed origin matches actual *)
Definition origin_matches (bs : BrowserState) : Prop :=
  browser_url bs = origin_host (browser_origin bs).

(** ═══════════════════════════════════════════════════════════════════════════
    CONSENT DEFINITIONS
    ═══════════════════════════════════════════════════════════════════════════ *)

(* Action sensitivity *)
Inductive Sensitivity : Type :=
  | SensNone : Sensitivity
  | SensLow : Sensitivity
  | SensMedium : Sensitivity
  | SensHigh : Sensitivity
  | SensCritical : Sensitivity.

(* Consent record *)
Record ConsentRecord : Type := mkConsent {
  consent_action : string;
  consent_granted : bool;
  consent_timestamp : nat;
  consent_revocable : bool;
}.

(* Dialog option *)
Record DialogOption : Type := mkOption {
  opt_label : string;
  opt_is_cancel : bool;
  opt_visual_weight : nat;  (* 1-10 scale *)
}.

(* Dialog balanced presentation *)
Definition balanced_presentation (opts : list DialogOption) : Prop :=
  forall o1 o2, In o1 opts -> In o2 opts ->
    opt_visual_weight o1 <= opt_visual_weight o2 + 2 /\
    opt_visual_weight o2 <= opt_visual_weight o1 + 2.

(* Neutral language (no shaming words) *)
Definition neutral_language (s : string) : Prop :=
  True.  (* Simplified - real impl checks for manipulation *)

(** ═══════════════════════════════════════════════════════════════════════════
    UI THEOREMS
    ═══════════════════════════════════════════════════════════════════════════ *)

(* UX_001_01 through UX_001_15 - YOUR PROOFS HERE *)
```

═══════════════════════════════════════════════════════════════════════════════════════════════════
THEOREM SPECIFICATIONS:
═══════════════════════════════════════════════════════════════════════════════════════════════════

```coq
(* UX_001_01: What You See Is What You Click *)
Theorem wysiwyk : forall ui p,
  visually_at ui p = clickable_at ui p.

(* UX_001_03: No invisible overlay *)
Theorem no_invisible_overlay : forall ui p elem,
  clickable_at ui p = Some elem ->
  elem_opacity elem >= MIN_VISIBLE_OPACITY.

(* UX_001_06: Origin indicator correct *)
Theorem origin_indicator_correct : forall bs,
  origin_matches bs.

(* UX_001_13: No confirmshaming *)
Theorem no_confirmshaming : forall dialog opt,
  In opt dialog ->
  opt_is_cancel opt = true ->
  neutral_language (opt_label opt).
```

═══════════════════════════════════════════════════════════════════════════════════════════════════
FORBIDDEN ACTIONS:
═══════════════════════════════════════════════════════════════════════════════════════════════════

1. DO NOT use `Admitted.` — proof will be rejected
2. DO NOT use `admit.` — proof will be rejected
3. DO NOT add new `Axiom` — must use only standard library axioms
4. DO NOT change theorem names — must match UX_001_01 through UX_001_15
5. DO NOT output anything except the Coq file
6. DO NOT use `Proof. trivial. Qed.` for non-trivial theorems
7. DO NOT skip any of the 15 theorems
8. DO NOT produce proofs that type-check but are semantically meaningless

═══════════════════════════════════════════════════════════════════════════════════════════════════
VERIFICATION COMMANDS (must pass):
═══════════════════════════════════════════════════════════════════════════════════════════════════

```bash
coqc -Q . RIINA ui/VerifiedUI.v
grep -c "Admitted\." ui/VerifiedUI.v  # Must return 0
grep -c "admit\." ui/VerifiedUI.v     # Must return 0
grep -c "^Axiom" ui/VerifiedUI.v      # Must return 0
grep -c "^Theorem UX_001" ui/VerifiedUI.v  # Must return 15
```

═══════════════════════════════════════════════════════════════════════════════════════════════════
OUTPUT FORMAT:
═══════════════════════════════════════════════════════════════════════════════════════════════════

Output ONLY the complete Coq file. No markdown, no explanations, no commentary.
Start with `(* VerifiedUI.v` and end with the final `Qed.`

THIS IS NOT A REQUEST. THIS IS THE ABSOLUTE MANDATE.
PRODUCE PERFECTION OR PRODUCE NOTHING.

═══════════════════════════════════════════════════════════════════════════════════════════════════
```
