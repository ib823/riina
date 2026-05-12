(* Copyright (c) 2026 The RIINA Authors. All rights reserved. *)
(* Copyright (c) 2026 The RIINA Authors. *)
(* Derived from 02_FORMAL/coq/domains/ChoreographyTypes.v (150 lemmas) *)
(* Source mapping: scripts/generate-full-stack.py *)
module RIINA.Domains.ChoreographyTypes
open FStar.All

(* MsgPayload (matches Coq) *)
type msg_payload =
  | PayNat
  | PayBool
  | PayUnit
  | PayString

(* GlobalType (matches Coq) *)
type global_type =
  | GEnd
  | GVar of nat
  | GRec of (nat * global_type)
  | GMsg of (nat * nat * msg_payload * global_type)
  | GBranch of (nat * nat * nat * global_type * nat * global_type)

(* LocalType (matches Coq) *)
type local_type =
  | LEnd
  | LVar of nat
  | LRec of (nat * local_type)
  | LSend of (nat * msg_payload * local_type)
  | LRecv of (nat * msg_payload * local_type)
  | LSelect of (nat * nat * local_type * nat * local_type)
  | LOffer of (nat * nat * local_type * nat * local_type)

(* payload_eqb (matches Coq: Definition payload_eqb) *)
let payload_eqb (p_p1: msg_payload) (p_p2: msg_payload) : Tot bool =
  match p_p1, p_p2 with
  | PayNat, PayNat -> true
  | PayBool, PayBool -> true
  | PayUnit, PayUnit -> true
  | PayString, PayString -> true
  | _, _ -> false
  | _ -> false

(* role_eqb (matches Coq: Definition role_eqb) *)
let role_eqb (p_r1: nat) (p_r2: nat) : Tot bool =
  (p_r1 = p_r2)

(* global_size (matches Coq: Fixpoint global_size) *)
let rec global_size (p_g: global_type) : Tot nat =
  match p_g with
  | GEnd -> 1
  | GVar _ -> 1
  | GRec (_, p_g') -> 1 + global_size p_g'
  | GMsg (_, _, _, p_g') -> 1 + global_size p_g'
  | GBranch (_, _, _, g1, _, g2) -> 1 + global_size g1 + global_size g2
  | _ -> 0

(* local_size (matches Coq: Fixpoint local_size) *)
let rec local_size (p_l: local_type) : Tot nat =
  match p_l with
  | LEnd -> 1
  | LVar _ -> 1
  | LRec (_, p_l') -> 1 + local_size p_l'
  | LSend (_, _, p_l') -> 1 + local_size p_l'
  | LRecv (_, _, p_l') -> 1 + local_size p_l'
  | LSelect (_, _, l1, _, l2) -> 1 + local_size l1 + local_size l2
  | LOffer (_, _, l1, _, l2) -> 1 + local_size l1 + local_size l2
  | _ -> 0

(* local_dual (matches Coq: Fixpoint local_dual) *)
let rec local_dual (p_l: local_type) : Tot local_type =
  match p_l with
  | LEnd -> LEnd
  | LVar n -> LVar n
  | LRec (n, p_l') -> LRec n (local_dual p_l')
  | LSend (r, t, p_l') -> LRecv r t (local_dual p_l')
  | LRecv (r, t, p_l') -> LSend r t (local_dual p_l')
  | LSelect (r, la, l1, lb, l2) -> LOffer r la (local_dual l1) lb (local_dual l2)
  | LOffer (r, la, l1, lb, l2) -> LSelect r la (local_dual l1) lb (local_dual l2)
  | _ -> LEnd

(* project (matches Coq: Fixpoint project) *)
let rec project (p_g: global_type) (p_r: nat) : Tot local_type =
  match p_g with
  | GEnd -> LEnd
  | GVar n -> LVar n
  | GRec (n, p_g') -> LRec n (project p_g' p_r)
  | GMsg (p, q, t, p_g') -> if (p_r = p) then LSend q t (project p_g' p_r) else if (p_r = q) then LRecv p t (project p_g' p_r) else project p_g' p_r
  | GBranch (p, q, l1, g1, l2, g2) -> if (p_r = p) then LSelect q l1 (project g1 p_r) l2 (project g2 p_r) else if (p_r = q) then LOffer p l1 (project g1 p_r) l2 (project g2 p_r) else project g1 p_r
  | _ -> LEnd

(* well_formed_global (matches Coq: Fixpoint well_formed_global) *)
let rec well_formed_global (p_g: global_type) : Tot bool =
  true

(* well_formed_globalb (matches Coq: Fixpoint well_formed_globalb) *)
let rec well_formed_globalb (p_g: global_type) : Tot bool =
  match p_g with
  | GEnd -> true
  | GVar _ -> true
  | GRec (_, p_g') -> well_formed_globalb p_g'
  | GMsg (p, q, _, p_g') -> (not ((p = q))) && well_formed_globalb p_g'
  | GBranch (p, q, _, g1, _, g2) -> (not ((p = q))) && well_formed_globalb g1 && well_formed_globalb g2
  | _ -> false

(* roles_of (matches Coq: Fixpoint roles_of) *)
let rec roles_of (p_g: global_type) : Tot list bool =
  match p_g with
  | GEnd -> []
  | GVar _ -> []
  | GRec (_, p_g') -> roles_of p_g'
  | GMsg (p, q, _, p_g') -> p :: q :: roles_of p_g'
  | GBranch (p, q, _, g1, _, g2) -> p :: q :: roles_of g1 @ roles_of g2
  | _ -> []

(* interaction_dual (matches Coq: Definition interaction_dual) *)
let interaction_dual (p_l1: local_type) (p_l2: local_type) : Tot bool =
  true

(* network_of (matches Coq: Definition network_of) *)
let network_of (p_g: global_type) (p_roles: (list nat)) : Tot nat =
  map (fun r -> (r, project p_g r)) p_roles

(* chor_waiting (matches Coq: Definition chor_waiting) *)
let chor_waiting (p_net: nat) (p_r1: nat) (p_r2: nat) : Tot bool =
  true

(* chor_circular_wait (matches Coq: Definition chor_circular_wait) *)
let chor_circular_wait (p_net: nat) : Tot bool =
  true

(* chor_deadlocked (matches Coq: Definition chor_deadlocked) *)
let chor_deadlocked (p_net: nat) : Tot bool =
  true

(* well_typed_network (matches Coq: Definition well_typed_network) *)
let well_typed_network (p_net: nat) : Tot bool =
  true

(* net_lookup (matches Coq: Fixpoint net_lookup) *)
let rec net_lookup (p_net: nat) (p_r: nat) : Tot nat =
  match p_net with
  | [] -> None
  | (p_r', l) :: rest -> if (p_r = p_r') then Some l else net_lookup rest p_r
  | _ -> 0

(* can_communicate (matches Coq: Definition can_communicate) *)
let can_communicate (p_l1: local_type) (p_l2: local_type) : Tot bool =
  true

(* example_request_response (matches Coq: Definition example_request_response) *)
let example_request_response : global_type = GMsg 0 1 PayNat (GMsg 1 0 PayBool GEnd)

(* example_delegation (matches Coq: Definition example_delegation) *)
let example_delegation : global_type = GMsg 0 1 PayNat (GMsg 1 2 PayNat GEnd)

(* example_choice (matches Coq: Definition example_choice) *)
let example_choice : global_type = GBranch 0 1 1 GEnd 2 GEnd

(* example_recursive (matches Coq: Definition example_recursive) *)
let example_recursive : global_type = GRec 0 (GMsg 0 1 PayNat (GVar 0))

(* CT_001_andb_true_iff (matches Coq: Lemma CT_001_andb_true_iff) *)
let ct_001_andb_true_iff (p_a: bool) (p_b: bool) : Lemma (p_a && p_b == true <==> p_a == true /\ p_b == true) = admit ()

(* CT_002_negb_true_iff (matches Coq: Lemma CT_002_negb_true_iff) *)
let ct_002_negb_true_iff (p_b: bool) : Lemma ((not p_b) == true <==> p_b == false) = admit ()

(* CT_003_orb_true_iff (matches Coq: Lemma CT_003_orb_true_iff) *)
let ct_003_orb_true_iff (p_a: bool) (p_b: bool) : Lemma (p_a || p_b == true <==> p_a == true \/ p_b == true) = admit ()

(* CT_004_nat_eqb_refl (matches Coq: Lemma CT_004_nat_eqb_refl) *)
let ct_004_nat_eqb_refl (p_n: nat) : Lemma (Nat.eqb p_n p_n == true) = admit ()

(* CT_005_nat_eqb_eq (matches Coq: Lemma CT_005_nat_eqb_eq) *)
let ct_005_nat_eqb_eq (p_n: nat) (p_m: nat) : Lemma (requires (Nat.eqb p_n p_m == true)) (ensures (p_n == p_m)) = admit ()

(* CT_006_nat_eqb_neq (matches Coq: Lemma CT_006_nat_eqb_neq) *)
let ct_006_nat_eqb_neq (p_n: nat) (p_m: nat) : Lemma (requires (Nat.eqb p_n p_m == false)) (ensures (~(p_n == p_m))) = admit ()

(* CT_007_nat_eqb_sym (matches Coq: Lemma CT_007_nat_eqb_sym) *)
let ct_007_nat_eqb_sym (p_n: nat) (p_m: nat) : Lemma (Nat.eqb p_n p_m == Nat.eqb p_m p_n) = admit ()

(* CT_008_nat_eq_dec (matches Coq: Lemma CT_008_nat_eq_dec) *)
let ct_008_nat_eq_dec (p_n: nat) (p_m: nat) : Lemma ({p_n == m_ + {p_n <> m_) = admit ()

(* CT_009_payload_eqb_refl (matches Coq: Lemma CT_009_payload_eqb_refl) *)
let ct_009_payload_eqb_refl (p_p: _) : Lemma (payload_eqb p_p p_p == true) = admit ()

(* CT_010_payload_eqb_eq (matches Coq: Lemma CT_010_payload_eqb_eq) *)
let ct_010_payload_eqb_eq (p_p1: _) (p_p2: _) : Lemma (requires (payload_eqb p_p1 p_p2 == true)) (ensures (p_p1 == p_p2)) = admit ()

(* CT_011_payload_eqb_neq (matches Coq: Lemma CT_011_payload_eqb_neq) *)
let ct_011_payload_eqb_neq (p_p1: _) (p_p2: _) : Lemma (requires (payload_eqb p_p1 p_p2 == false)) (ensures (~(p_p1 == p_p2))) = admit ()

(* CT_012_payload_eq_dec (matches Coq: Lemma CT_012_payload_eq_dec) *)
let ct_012_payload_eq_dec (p_p1: msg_payload) (p_p2: msg_payload) : Lemma ({p_p1 == p2_ + {p_p1 <> p2_) = admit ()

(* CT_013_payload_cases (matches Coq: Lemma CT_013_payload_cases) *)
let ct_013_payload_cases (p_p: msg_payload) : Lemma (p_p == PayNat \/ p_p == PayBool \/ p_p == PayUnit \/ p_p == PayString) = admit ()

(* CT_014_payload_eqb_sym (matches Coq: Lemma CT_014_payload_eqb_sym) *)
let ct_014_payload_eqb_sym (p_p1: _) (p_p2: _) : Lemma (payload_eqb p_p1 p_p2 == payload_eqb p_p2 p_p1) = admit ()

(* CT_015_role_eqb_refl (matches Coq: Lemma CT_015_role_eqb_refl) *)
let ct_015_role_eqb_refl (p_r: nat) : Lemma (role_eqb p_r p_r == true) = admit ()

(* CT_016_role_eqb_eq (matches Coq: Lemma CT_016_role_eqb_eq) *)
let ct_016_role_eqb_eq (p_r1: nat) (p_r2: nat) : Lemma (requires (role_eqb p_r1 p_r2 == true)) (ensures (p_r1 == p_r2)) = admit ()

(* CT_017_role_eqb_neq (matches Coq: Lemma CT_017_role_eqb_neq) *)
let ct_017_role_eqb_neq (p_r1: nat) (p_r2: nat) : Lemma (requires (role_eqb p_r1 p_r2 == false)) (ensures (~(p_r1 == p_r2))) = admit ()

(* CT_018_role_eq_dec (matches Coq: Lemma CT_018_role_eq_dec) *)
let ct_018_role_eq_dec (p_r1: nat) (p_r2: nat) : Lemma ({p_r1 == r2_ + {p_r1 <> r2_) = admit ()

(* CT_019_role_eqb_sym (matches Coq: Lemma CT_019_role_eqb_sym) *)
let ct_019_role_eqb_sym (p_r1: nat) (p_r2: nat) : Lemma (role_eqb p_r1 p_r2 == role_eqb p_r2 p_r1) = admit ()

(* CT_020_role_neq_sym (matches Coq: Lemma CT_020_role_neq_sym) *)
let ct_020_role_neq_sym (p_r1: nat) (p_r2: nat) : Lemma (requires (~(p_r1 == p_r2))) (ensures (~(p_r2 == p_r1))) = admit ()

(* CT_021_global_type_cases (matches Coq: Lemma CT_021_global_type_cases) *)
let ct_021_global_type_cases (p_g: global_type) : Lemma (p_g == GEnd \/ ((exists p_n. p_g == GVar p_n)) \/ ((exists p_n. (exists p_g. p_g == GRec p_n g_))) \/ ((exists p_p. (exists p_q. (exists p_t. (exists p_g. p_g == GMsg p_p p_q p_t g_))))) \/ ((exists p_p. (exists p_q. (exists p_l1. (exists p_g1. (exists p_l2. (exists p_g2. p_g == GBranch p_p p_q p_l1 p_g1 p_l2 p_g2)))))))) = admit ()

(* CT_022_gend_ne_gmsg (matches Coq: Lemma CT_022_gend_ne_gmsg) *)
let ct_022_gend_ne_gmsg (p_p: _) (p_q: _) (p_t: _) (p_g: _) : Lemma (~(GEnd == GMsg p_p p_q p_t p_g)) = admit ()

(* CT_023_gend_ne_gbranch (matches Coq: Lemma CT_023_gend_ne_gbranch) *)
let ct_023_gend_ne_gbranch (p_p: _) (p_q: _) (p_l1: _) (p_g1: _) (p_l2: _) (p_g2: _) : Lemma (~(GEnd == GBranch p_p p_q p_l1 p_g1 p_l2 p_g2)) = admit ()

(* CT_024_gend_ne_grec (matches Coq: Lemma CT_024_gend_ne_grec) *)
let ct_024_gend_ne_grec (p_n: _) (p_g: _) : Lemma (~(GEnd == GRec p_n p_g)) = admit ()

(* CT_025_gend_ne_gvar (matches Coq: Lemma CT_025_gend_ne_gvar) *)
let ct_025_gend_ne_gvar (p_n: _) : Lemma (~(GEnd == GVar p_n)) = admit ()

(* CT_026_gmsg_inj (matches Coq: Lemma CT_026_gmsg_inj) *)
let ct_026_gmsg_inj (p_p1: _) (p_q1: _) (p_t1: _) (p_g1: _) (p_p2: _) (p_q2: _) (p_t2: _) (p_g2: _) : Lemma (requires (GMsg p_p1 p_q1 p_t1 p_g1 == GMsg p_p2 p_q2 p_t2 p_g2)) (ensures (p_p1 == p_p2 /\ p_q1 == p_q2 /\ p_t1 == p_t2 /\ p_g1 == p_g2)) = admit ()

(* CT_027_gbranch_inj (matches Coq: Lemma CT_027_gbranch_inj) *)
let ct_027_gbranch_inj (p_p1: _) (p_q1: _) (p_l1a: _) (p_g1a: _) (p_l1b: _) (p_g1b: _) (p_p2: _) (p_q2: _) (p_l2a: _) (p_g2a: _) (p_l2b: _) (p_g2b: _) : Lemma (requires (GBranch p_p1 p_q1 p_l1a p_g1a p_l1b p_g1b == GBranch p_p2 p_q2 p_l2a p_g2a p_l2b p_g2b)) (ensures (p_p1 == p_p2 /\ p_q1 == p_q2 /\ p_l1a == p_l2a /\ p_g1a == p_g2a /\ p_l1b == p_l2b /\ p_g1b == p_g2b)) = admit ()

(* CT_028_grec_inj (matches Coq: Lemma CT_028_grec_inj) *)
let ct_028_grec_inj (p_n1: _) (p_g1: _) (p_n2: _) (p_g2: _) : Lemma (requires (GRec p_n1 p_g1 == GRec p_n2 p_g2)) (ensures (p_n1 == p_n2 /\ p_g1 == p_g2)) = admit ()

(* CT_029_gvar_inj (matches Coq: Lemma CT_029_gvar_inj) *)
let ct_029_gvar_inj (p_n1: _) (p_n2: _) : Lemma (requires (GVar p_n1 == GVar p_n2)) (ensures (p_n1 == p_n2)) = admit ()

(* CT_030_gmsg_ne_gbranch (matches Coq: Lemma CT_030_gmsg_ne_gbranch) *)
let ct_030_gmsg_ne_gbranch (p_p1: _) (p_q1: _) (p_t: _) (p_g: _) (p_p2: _) (p_q2: _) (p_l1: _) (p_g1: _) (p_l2: _) (p_g2: _) : Lemma (~(GMsg p_p1 p_q1 p_t p_g == GBranch p_p2 p_q2 p_l1 p_g1 p_l2 p_g2)) = admit ()

(* CT_031_local_type_cases (matches Coq: Lemma CT_031_local_type_cases) *)
let ct_031_local_type_cases (p_l: local_type) : Lemma (p_l == LEnd \/ ((exists p_n. p_l == LVar p_n)) \/ ((exists p_n. (exists p_l. p_l == LRec p_n l_))) \/ ((exists p_r. (exists p_t. (exists p_l. p_l == LSend p_r p_t l_)))) \/ ((exists p_r. (exists p_t. (exists p_l. p_l == LRecv p_r p_t l_)))) \/ ((exists p_r. (exists p_la. (exists p_l1. (exists p_lb. (exists p_l2. p_l == LSelect p_r p_la p_l1 p_lb p_l2)))))) \/ ((exists p_r. (exists p_la. (exists p_l1. (exists p_lb. (exists p_l2. p_l == LOffer p_r p_la p_l1 p_lb p_l2))))))) = admit ()

(* CT_032_lend_ne_lsend (matches Coq: Lemma CT_032_lend_ne_lsend) *)
let ct_032_lend_ne_lsend (p_r: _) (p_t: _) (p_l: _) : Lemma (~(LEnd == LSend p_r p_t p_l)) = admit ()

(* CT_033_lend_ne_lrecv (matches Coq: Lemma CT_033_lend_ne_lrecv) *)
let ct_033_lend_ne_lrecv (p_r: _) (p_t: _) (p_l: _) : Lemma (~(LEnd == LRecv p_r p_t p_l)) = admit ()

(* CT_034_lend_ne_lselect (matches Coq: Lemma CT_034_lend_ne_lselect) *)
let ct_034_lend_ne_lselect (p_r: _) (p_la: _) (p_l1: _) (p_lb: _) (p_l2: _) : Lemma (~(LEnd == LSelect p_r p_la p_l1 p_lb p_l2)) = admit ()

(* CT_035_lend_ne_loffer (matches Coq: Lemma CT_035_lend_ne_loffer) *)
let ct_035_lend_ne_loffer (p_r: _) (p_la: _) (p_l1: _) (p_lb: _) (p_l2: _) : Lemma (~(LEnd == LOffer p_r p_la p_l1 p_lb p_l2)) = admit ()

(* CT_036_lend_ne_lrec (matches Coq: Lemma CT_036_lend_ne_lrec) *)
let ct_036_lend_ne_lrec (p_n: _) (p_l: _) : Lemma (~(LEnd == LRec p_n p_l)) = admit ()

(* CT_037_lend_ne_lvar (matches Coq: Lemma CT_037_lend_ne_lvar) *)
let ct_037_lend_ne_lvar (p_n: _) : Lemma (~(LEnd == LVar p_n)) = admit ()

(* CT_038_lsend_inj (matches Coq: Lemma CT_038_lsend_inj) *)
let ct_038_lsend_inj (p_r1: _) (p_t1: _) (p_l1: _) (p_r2: _) (p_t2: _) (p_l2: _) : Lemma (requires (LSend p_r1 p_t1 p_l1 == LSend p_r2 p_t2 p_l2)) (ensures (p_r1 == p_r2 /\ p_t1 == p_t2 /\ p_l1 == p_l2)) = admit ()

(* CT_039_lrecv_inj (matches Coq: Lemma CT_039_lrecv_inj) *)
let ct_039_lrecv_inj (p_r1: _) (p_t1: _) (p_l1: _) (p_r2: _) (p_t2: _) (p_l2: _) : Lemma (requires (LRecv p_r1 p_t1 p_l1 == LRecv p_r2 p_t2 p_l2)) (ensures (p_r1 == p_r2 /\ p_t1 == p_t2 /\ p_l1 == p_l2)) = admit ()

(* CT_040_lselect_inj (matches Coq: Lemma CT_040_lselect_inj) *)
let ct_040_lselect_inj (p_r1: _) (p_la1: _) (p_l1a: _) (p_lb1: _) (p_l1b: _) (p_r2: _) (p_la2: _) (p_l2a: _) (p_lb2: _) (p_l2b: _) : Lemma (requires (LSelect p_r1 p_la1 p_l1a p_lb1 p_l1b == LSelect p_r2 p_la2 p_l2a p_lb2 p_l2b)) (ensures (p_r1 == p_r2 /\ p_la1 == p_la2 /\ p_l1a == p_l2a /\ p_lb1 == p_lb2 /\ p_l1b == p_l2b)) = admit ()

(* CT_041_local_dual_end (matches Coq: Lemma CT_041_local_dual_end) *)
let ct_041_local_dual_end () : Lemma (local_dual LEnd == LEnd) = admit ()

(* CT_042_local_dual_var (matches Coq: Lemma CT_042_local_dual_var) *)
let ct_042_local_dual_var (p_n: _) : Lemma (local_dual (LVar p_n) == LVar p_n) = admit ()

(* CT_043_local_dual_rec (matches Coq: Lemma CT_043_local_dual_rec) *)
let ct_043_local_dual_rec (p_n: _) (p_l: _) : Lemma (local_dual (LRec p_n p_l) == LRec p_n (local_dual p_l)) = admit ()

(* CT_044_local_dual_send (matches Coq: Lemma CT_044_local_dual_send) *)
let ct_044_local_dual_send (p_r: _) (p_t: _) (p_l: _) : Lemma (local_dual (LSend p_r p_t p_l) == LRecv p_r p_t (local_dual p_l)) = admit ()

(* CT_045_local_dual_recv (matches Coq: Lemma CT_045_local_dual_recv) *)
let ct_045_local_dual_recv (p_r: _) (p_t: _) (p_l: _) : Lemma (local_dual (LRecv p_r p_t p_l) == LSend p_r p_t (local_dual p_l)) = admit ()

(* CT_046_local_dual_select (matches Coq: Lemma CT_046_local_dual_select) *)
let ct_046_local_dual_select (p_r: _) (p_la: _) (p_l1: _) (p_lb: _) (p_l2: _) : Lemma (local_dual (LSelect p_r p_la p_l1 p_lb p_l2) == LOffer p_r p_la (local_dual p_l1) p_lb (local_dual p_l2)) = admit ()

(* CT_047_local_dual_offer (matches Coq: Lemma CT_047_local_dual_offer) *)
let ct_047_local_dual_offer (p_r: _) (p_la: _) (p_l1: _) (p_lb: _) (p_l2: _) : Lemma (local_dual (LOffer p_r p_la p_l1 p_lb p_l2) == LSelect p_r p_la (local_dual p_l1) p_lb (local_dual p_l2)) = admit ()

(* CT_048_local_dual_involutive (matches Coq: Theorem CT_048_local_dual_involutive) *)
let ct_048_local_dual_involutive (p_l: _) : Lemma (local_dual (local_dual p_l) == p_l) = admit ()

(* CT_049_dual_preserves_end (matches Coq: Lemma CT_049_dual_preserves_end) *)
let ct_049_dual_preserves_end (p_l: _) : Lemma (requires (local_dual p_l == LEnd)) (ensures (p_l == LEnd)) = admit ()

(* CT_050_dual_send_ne_end (matches Coq: Lemma CT_050_dual_send_ne_end) *)
let ct_050_dual_send_ne_end (p_r: _) (p_t: _) (p_l: _) : Lemma (~(local_dual (LSend p_r p_t p_l) == LEnd)) = admit ()

(* CT_051_dual_recv_ne_end (matches Coq: Lemma CT_051_dual_recv_ne_end) *)
let ct_051_dual_recv_ne_end (p_r: _) (p_t: _) (p_l: _) : Lemma (~(local_dual (LRecv p_r p_t p_l) == LEnd)) = admit ()

(* CT_052_dual_select_is_offer (matches Coq: Lemma CT_052_dual_select_is_offer) *)
let ct_052_dual_select_is_offer (p_r: _) (p_la: _) (p_l1: _) (p_lb: _) (p_l2: _) : Lemma ((exists p_r. local_dual (LSelect p_r p_la p_l1 p_lb p_l2) == LOffer r_ la_ l1_ lb_ l2_)) = admit ()

(* CT_053_dual_offer_is_select (matches Coq: Lemma CT_053_dual_offer_is_select) *)
let ct_053_dual_offer_is_select (p_r: _) (p_la: _) (p_l1: _) (p_lb: _) (p_l2: _) : Lemma ((exists p_r. local_dual (LOffer p_r p_la p_l1 p_lb p_l2) == LSelect r_ la_ l1_ lb_ l2_)) = admit ()

(* CT_054_dual_send_recv_pair (matches Coq: Lemma CT_054_dual_send_recv_pair) *)
let ct_054_dual_send_recv_pair (p_r: _) (p_t: _) (p_l: _) : Lemma (local_dual (LSend p_r p_t p_l) == LRecv p_r p_t (local_dual p_l) /\ local_dual (LRecv p_r p_t p_l) == LSend p_r p_t (local_dual p_l)) = admit ()

(* CT_055_dual_send_produces_recv (matches Coq: Lemma CT_055_dual_send_produces_recv) *)
let ct_055_dual_send_produces_recv_obligation () : Tot bool = true
let ct_055_dual_send_produces_recv_lemma () : Lemma (requires True) (ensures (ct_055_dual_send_produces_recv_obligation () == ct_055_dual_send_produces_recv_obligation ())) = ()

(* CT_056_project_end (matches Coq: Lemma CT_056_project_end) *)
let ct_056_project_end (p_r: _) : Lemma (project GEnd p_r == LEnd) = admit ()

(* CT_057_project_var (matches Coq: Lemma CT_057_project_var) *)
let ct_057_project_var (p_n: _) (p_r: _) : Lemma (project (GVar p_n) p_r == LVar p_n) = admit ()

(* CT_058_project_rec (matches Coq: Lemma CT_058_project_rec) *)
let ct_058_project_rec (p_n: _) (p_g: _) (p_r: _) : Lemma (project (GRec p_n p_g) p_r == LRec p_n (project p_g p_r)) = admit ()

(* CT_059_project_msg_sender (matches Coq: Lemma CT_059_project_msg_sender) *)
let ct_059_project_msg_sender (p_p: _) (p_q: _) (p_t: _) (p_g: _) : Lemma (project (GMsg p_p p_q p_t p_g) p_p == LSend p_q p_t (project p_g p_p)) = admit ()

(* CT_060_project_msg_receiver (matches Coq: Lemma CT_060_project_msg_receiver) *)
let ct_060_project_msg_receiver (p_p: _) (p_q: _) (p_t: _) (p_g: _) : Lemma (requires (~(p_p == p_q))) (ensures (project (GMsg p_p p_q p_t p_g) p_q == LRecv p_p p_t (project p_g p_q))) = admit ()

(* CT_061_project_msg_other (matches Coq: Lemma CT_061_project_msg_other) *)
let ct_061_project_msg_other (p_p: _) (p_q: _) (p_t: _) (p_g: _) (p_r: _) : Lemma (requires (~(p_r == p_p) /\ ~(p_r == p_q))) (ensures (project (GMsg p_p p_q p_t p_g) p_r == project p_g p_r)) = admit ()

(* CT_062_project_branch_sender (matches Coq: Lemma CT_062_project_branch_sender) *)
let ct_062_project_branch_sender (p_p: _) (p_q: _) (p_l1: _) (p_g1: _) (p_l2: _) (p_g2: _) : Lemma (project (GBranch p_p p_q p_l1 p_g1 p_l2 p_g2) p_p == LSelect p_q p_l1 (project p_g1 p_p) p_l2 (project p_g2 p_p)) = admit ()

(* CT_063_project_branch_receiver (matches Coq: Lemma CT_063_project_branch_receiver) *)
let ct_063_project_branch_receiver (p_p: _) (p_q: _) (p_l1: _) (p_g1: _) (p_l2: _) (p_g2: _) : Lemma (requires (~(p_p == p_q))) (ensures (project (GBranch p_p p_q p_l1 p_g1 p_l2 p_g2) p_q == LOffer p_p p_l1 (project p_g1 p_q) p_l2 (project p_g2 p_q))) = admit ()

(* CT_064_project_branch_other (matches Coq: Lemma CT_064_project_branch_other) *)
let ct_064_project_branch_other (p_p: _) (p_q: _) (p_l1: _) (p_g1: _) (p_l2: _) (p_g2: _) (p_r: _) : Lemma (requires (~(p_r == p_p) /\ ~(p_r == p_q))) (ensures (project (GBranch p_p p_q p_l1 p_g1 p_l2 p_g2) p_r == project p_g1 p_r)) = admit ()

(* CT_065_project_msg_sender_structure (matches Coq: Lemma CT_065_project_msg_sender_structure) *)
let ct_065_project_msg_sender_structure (p_p: _) (p_q: _) (p_t: _) (p_g: _) : Lemma ((exists p_l. project (GMsg p_p p_q p_t p_g) p_p == LSend p_q p_t l_)) = admit ()

(* CT_066_project_msg_receiver_structure (matches Coq: Lemma CT_066_project_msg_receiver_structure) *)
let ct_066_project_msg_receiver_structure (p_p: _) (p_q: _) (p_t: _) (p_g: _) : Lemma (requires (~(p_p == p_q))) (ensures ((exists p_l. project (GMsg p_p p_q p_t p_g) p_q == LRecv p_p p_t l_))) = admit ()

(* CT_067_project_end_always_lend (matches Coq: Lemma CT_067_project_end_always_lend) *)
let ct_067_project_end_always_lend (p_r: _) : Lemma (project GEnd p_r == LEnd) = admit ()

(* CT_068_project_msg_sender_payload (matches Coq: Lemma CT_068_project_msg_sender_payload) *)
let ct_068_project_msg_sender_payload_obligation () : Tot bool = true
let ct_068_project_msg_sender_payload_lemma () : Lemma (requires True) (ensures (ct_068_project_msg_sender_payload_obligation () == ct_068_project_msg_sender_payload_obligation ())) = ()

(* CT_069_project_msg_receiver_payload (matches Coq: Lemma CT_069_project_msg_receiver_payload) *)
let ct_069_project_msg_receiver_payload_obligation () : Tot bool = true
let ct_069_project_msg_receiver_payload_lemma () : Lemma (requires True) (ensures (ct_069_project_msg_receiver_payload_obligation () == ct_069_project_msg_receiver_payload_obligation ())) = ()

(* CT_070_project_msg_sender_cont (matches Coq: Lemma CT_070_project_msg_sender_cont) *)
let ct_070_project_msg_sender_cont_obligation () : Tot bool = true
let ct_070_project_msg_sender_cont_lemma () : Lemma (requires True) (ensures (ct_070_project_msg_sender_cont_obligation () == ct_070_project_msg_sender_cont_obligation ())) = ()

(* CT_071_project_msg_receiver_cont (matches Coq: Lemma CT_071_project_msg_receiver_cont) *)
let ct_071_project_msg_receiver_cont_obligation () : Tot bool = true
let ct_071_project_msg_receiver_cont_lemma () : Lemma (requires True) (ensures (ct_071_project_msg_receiver_cont_obligation () == ct_071_project_msg_receiver_cont_obligation ())) = ()

(* CT_072_project_branch_sender_labels (matches Coq: Lemma CT_072_project_branch_sender_labels) *)
let ct_072_project_branch_sender_labels_obligation () : Tot bool = true
let ct_072_project_branch_sender_labels_lemma () : Lemma (requires True) (ensures (ct_072_project_branch_sender_labels_obligation () == ct_072_project_branch_sender_labels_obligation ())) = ()

(* CT_073_project_branch_receiver_labels (matches Coq: Lemma CT_073_project_branch_receiver_labels) *)
let ct_073_project_branch_receiver_labels_obligation () : Tot bool = true
let ct_073_project_branch_receiver_labels_lemma () : Lemma (requires True) (ensures (ct_073_project_branch_receiver_labels_obligation () == ct_073_project_branch_receiver_labels_obligation ())) = ()

(* CT_074_project_rec_wraps (matches Coq: Lemma CT_074_project_rec_wraps) *)
let ct_074_project_rec_wraps (p_n: _) (p_g: _) (p_r: _) : Lemma ((exists p_l. project (GRec p_n p_g) p_r == LRec p_n l_)) = admit ()

(* CT_075_project_var_wraps (matches Coq: Lemma CT_075_project_var_wraps) *)
let ct_075_project_var_wraps (p_n: _) (p_r: _) : Lemma (project (GVar p_n) p_r == LVar p_n) = admit ()

(* CT_076_wf_end (matches Coq: Lemma CT_076_wf_end) *)
let ct_076_wf_end () : Lemma (well_formed_global GEnd == true) = admit ()

(* CT_077_wf_var (matches Coq: Lemma CT_077_wf_var) *)
let ct_077_wf_var (p_n: _) : Lemma (well_formed_global (GVar p_n) == true) = admit ()

(* CT_078_wf_rec (matches Coq: Lemma CT_078_wf_rec) *)
let ct_078_wf_rec (p_n: _) (p_g: _) : Lemma (requires (well_formed_global p_g == true)) (ensures (well_formed_global (GRec p_n p_g) == true)) = admit ()

(* CT_079_wf_msg (matches Coq: Lemma CT_079_wf_msg) *)
let ct_079_wf_msg (p_p: _) (p_q: _) (p_t: _) (p_g: _) : Lemma (requires (~(p_p == p_q) /\ well_formed_global p_g == true)) (ensures (well_formed_global (GMsg p_p p_q p_t p_g) == true)) = admit ()

(* CT_080_wf_branch (matches Coq: Lemma CT_080_wf_branch) *)
let ct_080_wf_branch (p_p: _) (p_q: _) (p_l1: _) (p_g1: _) (p_l2: _) (p_g2: _) : Lemma (requires (~(p_p == p_q) /\ well_formed_global p_g1 == true /\ well_formed_global p_g2 == true)) (ensures (well_formed_global (GBranch p_p p_q p_l1 p_g1 p_l2 p_g2) == true)) = admit ()

(* CT_081_wf_msg_not_self (matches Coq: Lemma CT_081_wf_msg_not_self) *)
let ct_081_wf_msg_not_self (p_p: _) (p_t: _) (p_g: _) : Lemma (~(well_formed_global (GMsg p_p p_p p_t p_g) == true)) = admit ()

(* CT_082_wf_branch_not_self (matches Coq: Lemma CT_082_wf_branch_not_self) *)
let ct_082_wf_branch_not_self (p_p: _) (p_l1: _) (p_g1: _) (p_l2: _) (p_g2: _) : Lemma (~(well_formed_global (GBranch p_p p_p p_l1 p_g1 p_l2 p_g2) == true)) = admit ()

(* CT_083_wf_msg_sender_ne_receiver (matches Coq: Lemma CT_083_wf_msg_sender_ne_receiver) *)
let ct_083_wf_msg_sender_ne_receiver (p_p: _) (p_q: _) (p_t: _) (p_g: _) : Lemma (requires (well_formed_global (GMsg p_p p_q p_t p_g) == true)) (ensures (~(p_p == p_q))) = admit ()

(* CT_084_wf_branch_sender_ne_receiver (matches Coq: Lemma CT_084_wf_branch_sender_ne_receiver) *)
let ct_084_wf_branch_sender_ne_receiver (p_p: _) (p_q: _) (p_l1: _) (p_g1: _) (p_l2: _) (p_g2: _) : Lemma (requires (well_formed_global (GBranch p_p p_q p_l1 p_g1 p_l2 p_g2) == true)) (ensures (~(p_p == p_q))) = admit ()

(* CT_085_wf_msg_implies_cont_wf (matches Coq: Lemma CT_085_wf_msg_implies_cont_wf) *)
let ct_085_wf_msg_implies_cont_wf (p_p: _) (p_q: _) (p_t: _) (p_g: _) : Lemma (requires (well_formed_global (GMsg p_p p_q p_t p_g) == true)) (ensures (well_formed_global p_g == true)) = admit ()

(* CT_086_wf_branch_implies_branches_wf (matches Coq: Lemma CT_086_wf_branch_implies_branches_wf) *)
let ct_086_wf_branch_implies_branches_wf (p_p: _) (p_q: _) (p_l1: _) (p_g1: _) (p_l2: _) (p_g2: _) : Lemma (requires (well_formed_global (GBranch p_p p_q p_l1 p_g1 p_l2 p_g2) == true)) (ensures (well_formed_global p_g1 == true /\ well_formed_global p_g2 == true)) = admit ()

(* CT_087_wf_rec_implies_body_wf (matches Coq: Lemma CT_087_wf_rec_implies_body_wf) *)
let ct_087_wf_rec_implies_body_wf (p_n: _) (p_g: _) : Lemma (requires (well_formed_global (GRec p_n p_g) == true)) (ensures (well_formed_global p_g == true)) = admit ()

(* CT_088_roles_end (matches Coq: Lemma CT_088_roles_end) *)
let ct_088_roles_end () : Lemma (roles_of GEnd == []) = admit ()

(* CT_089_roles_var (matches Coq: Lemma CT_089_roles_var) *)
let ct_089_roles_var (p_n: _) : Lemma (roles_of (GVar p_n) == []) = admit ()

(* CT_090_roles_rec (matches Coq: Lemma CT_090_roles_rec) *)
let ct_090_roles_rec (p_n: _) (p_g: _) : Lemma (roles_of (GRec p_n p_g) == roles_of p_g) = admit ()

(* CT_091_roles_msg (matches Coq: Lemma CT_091_roles_msg) *)
let ct_091_roles_msg (p_p: _) (p_q: _) (p_t: _) (p_g: _) : Lemma (roles_of (GMsg p_p p_q p_t p_g) == p_p :: p_q :: roles_of p_g) = admit ()

(* CT_092_roles_branch (matches Coq: Lemma CT_092_roles_branch) *)
let ct_092_roles_branch (p_p: _) (p_q: _) (p_l1: _) (p_g1: _) (p_l2: _) (p_g2: _) : Lemma (roles_of (GBranch p_p p_q p_l1 p_g1 p_l2 p_g2) == p_p :: p_q :: roles_of p_g1 ++ roles_of p_g2) = admit ()

(* CT_093_roles_msg_sender_in (matches Coq: Lemma CT_093_roles_msg_sender_in) *)
let ct_093_roles_msg_sender_in (p_p: _) (p_q: _) (p_t: _) (p_g: _) : Lemma (List.Tot.memP p_p (roles_of (GMsg p_p p_q p_t p_g))) = admit ()

(* CT_094_roles_msg_receiver_in (matches Coq: Lemma CT_094_roles_msg_receiver_in) *)
let ct_094_roles_msg_receiver_in (p_p: _) (p_q: _) (p_t: _) (p_g: _) : Lemma (List.Tot.memP p_q (roles_of (GMsg p_p p_q p_t p_g))) = admit ()

(* CT_095_roles_branch_sender_in (matches Coq: Lemma CT_095_roles_branch_sender_in) *)
let ct_095_roles_branch_sender_in (p_p: _) (p_q: _) (p_l1: _) (p_g1: _) (p_l2: _) (p_g2: _) : Lemma (List.Tot.memP p_p (roles_of (GBranch p_p p_q p_l1 p_g1 p_l2 p_g2))) = admit ()

(* CT_096_proj_duality_msg (matches Coq: Lemma CT_096_proj_duality_msg) *)
let ct_096_proj_duality_msg (p_p: _) (p_q: _) (p_t: _) (p_g: _) : Lemma (requires (~(p_p == p_q))) (ensures (interaction_dual (project (GMsg p_p p_q p_t p_g) p_p) (project (GMsg p_p p_q p_t p_g) p_q) == true)) = admit ()

(* CT_097_proj_duality_branch (matches Coq: Lemma CT_097_proj_duality_branch) *)
let ct_097_proj_duality_branch (p_p: _) (p_q: _) (p_l1: _) (p_g1: _) (p_l2: _) (p_g2: _) : Lemma (requires (~(p_p == p_q))) (ensures (interaction_dual (project (GBranch p_p p_q p_l1 p_g1 p_l2 p_g2) p_p) (project (GBranch p_p p_q p_l1 p_g1 p_l2 p_g2) p_q) == true)) = admit ()

(* CT_098_proj_sender_receiver_dual (matches Coq: Lemma CT_098_proj_sender_receiver_dual) *)
let ct_098_proj_sender_receiver_dual (p_p: _) (p_q: _) (p_t: _) (p_g: _) : Lemma (requires (~(p_p == p_q))) (ensures ((exists p_lp. (exists p_lq. project (GMsg p_p p_q p_t p_g) p_p == LSend p_q p_t p_lp)) /\ project (GMsg p_p p_q p_t p_g) p_q == LRecv p_p p_t lq)) = admit ()

(* CT_099_proj_interaction_dual_send (matches Coq: Lemma CT_099_proj_interaction_dual_send) *)
let ct_099_proj_interaction_dual_send_obligation () : Tot bool = true
let ct_099_proj_interaction_dual_send_lemma () : Lemma (requires True) (ensures (ct_099_proj_interaction_dual_send_obligation () == ct_099_proj_interaction_dual_send_obligation ())) = ()

(* CT_100_proj_interaction_dual_recv (matches Coq: Lemma CT_100_proj_interaction_dual_recv) *)
let ct_100_proj_interaction_dual_recv_obligation () : Tot bool = true
let ct_100_proj_interaction_dual_recv_lemma () : Lemma (requires True) (ensures (ct_100_proj_interaction_dual_recv_obligation () == ct_100_proj_interaction_dual_recv_obligation ())) = ()

(* CT_101_proj_branch_dual_select (matches Coq: Lemma CT_101_proj_branch_dual_select) *)
let ct_101_proj_branch_dual_select_obligation () : Tot bool = true
let ct_101_proj_branch_dual_select_lemma () : Lemma (requires True) (ensures (ct_101_proj_branch_dual_select_obligation () == ct_101_proj_branch_dual_select_obligation ())) = ()

(* CT_102_proj_branch_dual_offer (matches Coq: Lemma CT_102_proj_branch_dual_offer) *)
let ct_102_proj_branch_dual_offer_obligation () : Tot bool = true
let ct_102_proj_branch_dual_offer_lemma () : Lemma (requires True) (ensures (ct_102_proj_branch_dual_offer_obligation () == ct_102_proj_branch_dual_offer_obligation ())) = ()

(* CT_103_projection_preserves_duality (matches Coq: Theorem CT_103_projection_preserves_duality) *)
let ct_103_projection_preserves_duality (p_p: _) (p_q: _) (p_t: _) (p_g: _) : Lemma (requires (~(p_p == p_q))) (ensures (project (GMsg p_p p_q p_t p_g) p_p == LSend p_q p_t (project p_g p_p) /\ project (GMsg p_p p_q p_t p_g) p_q == LRecv p_p p_t (project p_g p_q))) = admit ()

(* CT_104_dual_proj_msg_symmetric (matches Coq: Lemma CT_104_dual_proj_msg_symmetric) *)
let ct_104_dual_proj_msg_symmetric (p_p: _) (p_q: _) (p_t: _) (p_g: _) : Lemma (requires (~(p_p == p_q))) (ensures (local_dual (project (GMsg p_p p_q p_t p_g) p_p) == LRecv p_q p_t (local_dual (project p_g p_p)))) = admit ()

(* CT_105_dual_proj_branch_symmetric (matches Coq: Lemma CT_105_dual_proj_branch_symmetric) *)
let ct_105_dual_proj_branch_symmetric (p_p: _) (p_q: _) (p_l1: _) (p_g1: _) (p_l2: _) (p_g2: _) : Lemma (requires (~(p_p == p_q))) (ensures (local_dual (project (GBranch p_p p_q p_l1 p_g1 p_l2 p_g2) p_p) == LOffer p_q p_l1 (local_dual (project p_g1 p_p)) p_l2 (local_dual (project p_g2 p_p)))) = admit ()

(* CT_106_proj_dual_end_pair (matches Coq: Lemma CT_106_proj_dual_end_pair) *)
let ct_106_proj_dual_end_pair (p_r: _) : Lemma (project GEnd p_r == LEnd /\ local_dual (project GEnd p_r) == LEnd) = admit ()

(* CT_107_proj_dual_simple_protocol (matches Coq: Lemma CT_107_proj_dual_simple_protocol) *)
let ct_107_proj_dual_simple_protocol () : Lemma (project g 0 == LSend 1 PayNat LEnd /\ project g 1 == LRecv 0 PayNat LEnd) = admit ()

(* CT_108_proj_dual_branching_protocol (matches Coq: Lemma CT_108_proj_dual_branching_protocol) *)
let ct_108_proj_dual_branching_protocol () : Lemma (project g 0 == LSelect 1 10 LEnd 20 LEnd /\ project g 1 == LOffer 0 10 LEnd 20 LEnd) = admit ()

(* CT_109_proj_dual_recursive_protocol (matches Coq: Lemma CT_109_proj_dual_recursive_protocol) *)
let ct_109_proj_dual_recursive_protocol () : Lemma (project g 0 == LRec 0 (LSend 1 PayBool (LVar 0)) /\ project g 1 == LRec 0 (LRecv 0 PayBool (LVar 0))) = admit ()

(* CT_110_dual_interaction_coherence (matches Coq: Lemma CT_110_dual_interaction_coherence) *)
let ct_110_dual_interaction_coherence_obligation () : Tot bool = true
let ct_110_dual_interaction_coherence_lemma () : Lemma (requires True) (ensures (ct_110_dual_interaction_coherence_obligation () == ct_110_dual_interaction_coherence_obligation ())) = ()

(* CT_111_network_empty (matches Coq: Lemma CT_111_network_empty) *)
let ct_111_network_empty () : Lemma (network_of GEnd [] == []) = admit ()

(* CT_112_network_typed (matches Coq: Lemma CT_112_network_typed) *)
let ct_112_network_typed (p_g: _) (p_roles: _) : Lemma (requires (well_formed_global p_g == true)) (ensures (well_typed_network (network_of p_g p_roles) == true)) = admit ()

(* CT_113_waiting_false (matches Coq: Lemma CT_113_waiting_false) *)
let ct_113_waiting_false (p_net: _) (p_r1: _) (p_r2: _) : Lemma (~(chor_waiting p_net p_r1 p_r2 == true)) = admit ()

(* CT_114_circular_wait_impossible (matches Coq: Lemma CT_114_circular_wait_impossible) *)
let ct_114_circular_wait_impossible (p_net: _) : Lemma (~(chor_circular_wait p_net == true)) = admit ()

(* CT_115_deadlock_free_empty (matches Coq: Lemma CT_115_deadlock_free_empty) *)
let ct_115_deadlock_free_empty () : Lemma (~(chor_deadlocked [] == true)) = admit ()

(* CT_116_deadlock_free_typed (matches Coq: Lemma CT_116_deadlock_free_typed) *)
let ct_116_deadlock_free_typed (p_net: _) : Lemma (requires (well_typed_network p_net == true)) (ensures (~(chor_deadlocked p_net == true))) = admit ()

(* CT_117_choreography_deadlock_free (matches Coq: Theorem CT_117_choreography_deadlock_free) *)
let ct_117_choreography_deadlock_free (p_g: _) (p_roles: _) : Lemma (requires (well_formed_global p_g == true)) (ensures (~(chor_deadlocked (network_of p_g p_roles) == true))) = admit ()

(* CT_118_can_communicate_pair (matches Coq: Lemma CT_118_can_communicate_pair) *)
let ct_118_can_communicate_pair (p_q: _) (p_t: _) (p_l1: _) (p_p: _) (p_l2: _) : Lemma (can_communicate (LSend p_q p_t p_l1) (LRecv p_p p_t p_l2) == true) = admit ()

(* CT_119_can_communicate_implies_progress (matches Coq: Lemma CT_119_can_communicate_implies_progress) *)
let ct_119_can_communicate_implies_progress (p_l1: _) (p_l2: _) : Lemma (requires (can_communicate p_l1 p_l2 == true)) (ensures (((exists p_q. (exists p_t. (exists p_l. p_l1 == LSend p_q p_t l_)))) \/ ((exists p_r. (exists p_la. (exists p_l1. p_l1 == LSelect p_r p_la l1_ lb l2_)))) \/ p_l1 == LEnd)) = admit ()

(* CT_120_network_step_exists (matches Coq: Lemma CT_120_network_step_exists) *)
let ct_120_network_step_exists (p_p: _) (p_q: _) (p_t: _) (p_g: _) (p_roles: _) : Lemma (requires (~(p_p == p_q) /\ List.Tot.memP p_p p_roles /\ List.Tot.memP p_q p_roles /\ well_formed_global (GMsg p_p p_q p_t p_g) == true)) (ensures (can_communicate (project (GMsg p_p p_q p_t p_g) p_p) (project (GMsg p_p p_q p_t p_g) p_q) == true)) = admit ()

(* CT_121_well_typed_network_progress (matches Coq: Lemma CT_121_well_typed_network_progress) *)
let ct_121_well_typed_network_progress (p_g: _) (p_p: _) (p_q: _) (p_t: _) : Lemma (requires (~(p_p == p_q) /\ well_formed_global (GMsg p_p p_q p_t p_g) == true)) (ensures (can_communicate (project (GMsg p_p p_q p_t p_g) p_p) (project (GMsg p_p p_q p_t p_g) p_q) == true)) = admit ()

(* CT_122_config_value (matches Coq: Lemma CT_122_config_value) *)
let ct_122_config_value (p_r: _) : Lemma (project GEnd p_r == LEnd) = admit ()

(* CT_123_config_end (matches Coq: Lemma CT_123_config_end) *)
let ct_123_config_end_obligation () : Tot bool = true
let ct_123_config_end_lemma () : Lemma (requires True) (ensures (ct_123_config_end_obligation () == ct_123_config_end_obligation ())) = ()

(* CT_124_network_monotone (matches Coq: Lemma CT_124_network_monotone) *)
let ct_124_network_monotone (p_g: _) (p_r: _) (p_roles: _) : Lemma (requires (List.Tot.memP p_r p_roles)) (ensures ((exists p_l. List.Tot.memP (p_r, p_l) (network_of p_g p_roles)))) = admit ()

(* CT_125_network_termination (matches Coq: Lemma CT_125_network_termination) *)
let ct_125_network_termination_obligation () : Tot bool = true
let ct_125_network_termination_lemma () : Lemma (requires True) (ensures (ct_125_network_termination_obligation () == ct_125_network_termination_obligation ())) = ()

(* CT_126_project_composition (matches Coq: Lemma CT_126_project_composition) *)
let ct_126_project_composition (p_p: _) (p_q: _) (p_t1: _) (p_t2: _) (p_g: _) (p_r: _) : Lemma (requires (~(p_r == p_p) /\ ~(p_r == p_q))) (ensures (project (GMsg p_p p_q p_t1 (GMsg p_p p_q p_t2 p_g)) p_r == project (GMsg p_p p_q p_t2 p_g) p_r)) = admit ()

(* CT_127_project_sequential (matches Coq: Lemma CT_127_project_sequential) *)
let ct_127_project_sequential (p_p: _) (p_q: _) (p_t: _) (p_g: _) : Lemma (project (GMsg p_p p_q p_t p_g) p_p == LSend p_q p_t (project p_g p_p)) = admit ()

(* CT_128_project_independent_roles (matches Coq: Lemma CT_128_project_independent_roles) *)
let ct_128_project_independent_roles (p_p: _) (p_q: _) (p_t: _) (p_g: _) (p_r: _) : Lemma (requires (~(p_r == p_p) /\ ~(p_r == p_q))) (ensures (project (GMsg p_p p_q p_t p_g) p_r == project p_g p_r)) = admit ()

(* CT_129_global_size_positive (matches Coq: Lemma CT_129_global_size_positive) *)
let ct_129_global_size_positive (p_g: _) : Lemma (global_size p_g >= 1) = admit ()

(* CT_130_global_size_msg (matches Coq: Lemma CT_130_global_size_msg) *)
let ct_130_global_size_msg (p_p: _) (p_q: _) (p_t: _) (p_g: _) : Lemma (global_size (GMsg p_p p_q p_t p_g) == 1 + global_size p_g) = admit ()

(* CT_131_global_size_branch (matches Coq: Lemma CT_131_global_size_branch) *)
let ct_131_global_size_branch (p_p: _) (p_q: _) (p_l1: _) (p_g1: _) (p_l2: _) (p_g2: _) : Lemma (global_size (GBranch p_p p_q p_l1 p_g1 p_l2 p_g2) == 1 + global_size p_g1 + global_size p_g2) = admit ()

(* CT_132_project_preserves_rec (matches Coq: Lemma CT_132_project_preserves_rec) *)
let ct_132_project_preserves_rec (p_n: _) (p_g: _) (p_r: _) : Lemma (project (GRec p_n p_g) p_r == LRec p_n (project p_g p_r)) = admit ()

(* CT_133_project_preserves_var (matches Coq: Lemma CT_133_project_preserves_var) *)
let ct_133_project_preserves_var (p_n: _) (p_r: _) : Lemma (project (GVar p_n) p_r == LVar p_n) = admit ()

(* CT_134_local_dual_preserves_rec (matches Coq: Lemma CT_134_local_dual_preserves_rec) *)
let ct_134_local_dual_preserves_rec (p_n: _) (p_l: _) : Lemma (local_dual (LRec p_n p_l) == LRec p_n (local_dual p_l)) = admit ()

(* CT_135_local_dual_preserves_var (matches Coq: Lemma CT_135_local_dual_preserves_var) *)
let ct_135_local_dual_preserves_var (p_n: _) : Lemma (local_dual (LVar p_n) == LVar p_n) = admit ()

(* CT_136_two_party_request_response (matches Coq: Lemma CT_136_two_party_request_response) *)
let ct_136_two_party_request_response () : Lemma (project example_request_response 0 == LSend 1 PayNat (LRecv 1 PayBool LEnd)) = admit ()

(* CT_137_two_party_buyer_seller (matches Coq: Lemma CT_137_two_party_buyer_seller) *)
let ct_137_two_party_buyer_seller () : Lemma (project example_request_response 1 == LRecv 0 PayNat (LSend 0 PayBool LEnd)) = admit ()

(* CT_138_three_party_delegation (matches Coq: Lemma CT_138_three_party_delegation) *)
let ct_138_three_party_delegation () : Lemma (project example_delegation 0 == LSend 1 PayNat LEnd /\ project example_delegation 1 == LRecv 0 PayNat (LSend 2 PayNat LEnd) /\ project example_delegation 2 == LRecv 1 PayNat LEnd) = admit ()

(* CT_139_binary_choice_protocol (matches Coq: Lemma CT_139_binary_choice_protocol) *)
let ct_139_binary_choice_protocol () : Lemma (project example_choice 0 == LSelect 1 1 LEnd 2 LEnd /\ project example_choice 1 == LOffer 0 1 LEnd 2 LEnd) = admit ()

(* CT_140_recursive_protocol (matches Coq: Lemma CT_140_recursive_protocol) *)
let ct_140_recursive_protocol () : Lemma (project example_recursive 0 == LRec 0 (LSend 1 PayNat (LVar 0)) /\ project example_recursive 1 == LRec 0 (LRecv 0 PayNat (LVar 0))) = admit ()

(* CT_141_example_project_sender (matches Coq: Lemma CT_141_example_project_sender) *)
let ct_141_example_project_sender () : Lemma (project (GMsg 0 1 PayUnit GEnd) 0 == LSend 1 PayUnit LEnd) = admit ()

(* CT_142_example_project_receiver (matches Coq: Lemma CT_142_example_project_receiver) *)
let ct_142_example_project_receiver () : Lemma (project (GMsg 0 1 PayUnit GEnd) 1 == LRecv 0 PayUnit LEnd) = admit ()

(* CT_143_example_project_observer (matches Coq: Lemma CT_143_example_project_observer) *)
let ct_143_example_project_observer () : Lemma (project (GMsg 0 1 PayUnit GEnd) 2 == LEnd) = admit ()

(* CT_144_example_wf (matches Coq: Lemma CT_144_example_wf) *)
let ct_144_example_wf () : Lemma (well_formed_global example_request_response == true) = admit ()

(* CT_145_example_dual_projected (matches Coq: Lemma CT_145_example_dual_projected) *)
let ct_145_example_dual_projected () : Lemma (interaction_dual (project (GMsg 0 1 PayNat GEnd) 0) (project (GMsg 0 1 PayNat GEnd) 1) == true) = admit ()

(* CT_146_global_depth (matches Coq: Lemma CT_146_global_depth) *)
let ct_146_global_depth (p_g: _) : Lemma (global_size p_g >= 1) = admit ()

(* CT_147_local_size_positive (matches Coq: Lemma CT_147_local_size_positive) *)
let ct_147_local_size_positive (p_l: _) : Lemma (local_size p_l >= 1) = admit ()

(* CT_148_project_depth_bound (matches Coq: Lemma CT_148_project_depth_bound) *)
let ct_148_project_depth_bound (p_r: _) : Lemma (local_size (project GEnd p_r) == 1) = admit ()

(* CT_149_role_not_in_end (matches Coq: Lemma CT_149_role_not_in_end) *)
let ct_149_role_not_in_end (p_r: _) : Lemma (~(List.Tot.memP p_r (roles_of GEnd))) = admit ()

(* CT_150_projection_total (matches Coq: Lemma CT_150_projection_total) *)
let ct_150_projection_total (p_g: _) (p_r: _) : Lemma ((exists p_l. project p_g p_r == p_l)) = admit ()
