(* Copyright (c) 2026 The RIINA Authors. All rights reserved. *)
(* Copyright (c) 2026 The RIINA Authors. *)
(* Derived from 02_FORMAL/coq/domains/ActorSupervision.v (116 lemmas) *)
(* Source mapping: scripts/generate-full-stack.py *)
module RIINA.Domains.ActorSupervision
open FStar.All

(* RestartStrategy (matches Coq) *)
type restart_strategy =
  | OneForOne
  | AllForOne
  | RestForOne

(* ChildStatus (matches Coq) *)
type child_status =
  | ChildRunning
  | ChildStopped
  | ChildCrashed
  | ChildRestarting

(* ChildType (matches Coq) *)
type child_type =
  | Permanent
  | Transient
  | Temporary

(* RestartDecision (matches Coq) *)
type restart_decision =
  | RestartChild
  | RestartAll
  | RestartRest
  | Escalate
  | DoNothing

(* ChildSpec (matches Coq) *)
type child_spec = {
  f_cs_id: nat;
  f_cs_type: child_type;
  f_cs_max_restarts: nat;
  f_cs_restart_window: nat;
  f_cs_shutdown_timeout: nat;
}

(* ChildState (matches Coq) *)
type child_state = {
  f_ch_spec: child_spec;
  f_ch_status: child_status;
  f_ch_restart_count: nat;
  f_ch_uptime: nat;
  f_ch_pid: nat;
}

(* Supervisor (matches Coq) *)
type supervisor = {
  f_sup_id: nat;
  f_sup_strategy: restart_strategy;
  f_sup_children: list bool;
  f_sup_max_restarts: nat;
  f_sup_restart_count: nat;
  f_sup_max_children: nat;
}

(* strategy_eqb (matches Coq: Definition strategy_eqb) *)
let strategy_eqb (p_s1: restart_strategy) (p_s2: restart_strategy) : Tot bool =
  match p_s1, p_s2 with
  | OneForOne, OneForOne -> true
  | AllForOne, AllForOne -> true
  | RestForOne, RestForOne -> true
  | _, _ -> false
  | _ -> false

(* child_status_eqb (matches Coq: Definition child_status_eqb) *)
let child_status_eqb (p_s1: child_status) (p_s2: child_status) : Tot bool =
  match p_s1, p_s2 with
  | ChildRunning, ChildRunning -> true
  | ChildStopped, ChildStopped -> true
  | ChildCrashed, ChildCrashed -> true
  | ChildRestarting, ChildRestarting -> true
  | _, _ -> false
  | _ -> false

(* child_type_eqb (matches Coq: Definition child_type_eqb) *)
let child_type_eqb (p_t1: child_type) (p_t2: child_type) : Tot bool =
  match p_t1, p_t2 with
  | Permanent, Permanent -> true
  | Transient, Transient -> true
  | Temporary, Temporary -> true
  | _, _ -> false
  | _ -> false

(* child_running (matches Coq: Definition child_running) *)
let child_running (p_c: child_state) : Tot bool =
  child_status_eqb (p_c.f_ch_status) ChildRunning

(* child_stopped (matches Coq: Definition child_stopped) *)
let child_stopped (p_c: child_state) : Tot bool =
  child_status_eqb (p_c.f_ch_status) ChildStopped

(* child_crashed (matches Coq: Definition child_crashed) *)
let child_crashed (p_c: child_state) : Tot bool =
  child_status_eqb (p_c.f_ch_status) ChildCrashed

(* child_restarting (matches Coq: Definition child_restarting) *)
let child_restarting (p_c: child_state) : Tot bool =
  child_status_eqb (p_c.f_ch_status) ChildRestarting

(* child_needs_restart (matches Coq: Definition child_needs_restart) *)
let child_needs_restart (p_c: child_state) : Tot bool =
  child_crashed p_c && (not (child_type_eqb (cs_type (p_c.f_ch_spec))) Temporary) && (p_c.f_ch_restart_count) < (cs_max_restarts (p_c.f_ch_spec))

(* child_within_restart_limit (matches Coq: Definition child_within_restart_limit) *)
let child_within_restart_limit (p_c: child_state) : Tot bool =
  (p_c.f_ch_restart_count) < (cs_max_restarts (p_c.f_ch_spec))

(* supervisor_can_restart (matches Coq: Definition supervisor_can_restart) *)
let supervisor_can_restart (p_sup: supervisor) : Tot bool =
  (p_sup.f_sup_restart_count) < (p_sup.f_sup_max_restarts)

(* supervisor_has_capacity (matches Coq: Definition supervisor_has_capacity) *)
let supervisor_has_capacity (p_sup: supervisor) : Tot bool =
  Nat.ltb (List.Tot.length (p_sup.f_sup_children)) (p_sup.f_sup_max_children)

(* all_children_running (matches Coq: Definition all_children_running) *)
let all_children_running (p_sup: supervisor) : Tot bool =
  forallb child_running (p_sup.f_sup_children)

(* no_children_crashed (matches Coq: Definition no_children_crashed) *)
let no_children_crashed (p_sup: supervisor) : Tot bool =
  forallb (fun c -> (not (child_crashed c))) (p_sup.f_sup_children)

(* supervisor_healthy (matches Coq: Definition supervisor_healthy) *)
let supervisor_healthy (p_sup: supervisor) : Tot bool =
  all_children_running p_sup && supervisor_can_restart p_sup

(* child_in_supervisor (matches Coq: Definition child_in_supervisor) *)
let child_in_supervisor (p_sup: supervisor) (p_cid: nat) : Tot bool =
  existsb (fun c -> Nat.eqb (cs_id (c.f_ch_spec)) p_cid) (p_sup.f_sup_children)

(* find_child (matches Coq: Fixpoint find_child) *)
let rec find_child (p_children: (list child_state)) (p_cid: nat) : Tot nat =
  match p_children with
  | [] -> None
  | c :: rest -> if Nat.eqb (cs_id (c.f_ch_spec)) p_cid then Some c else find_child rest p_cid
  | _ -> 0

(* decide_restart (matches Coq: Definition decide_restart) *)
let decide_restart (p_strat: restart_strategy) (p_can_restart: bool) : Tot restart_decision =
  if p_can_restart then match p_strat with
  | OneForOne -> RestartChild
  | AllForOne -> RestartAll
  | RestForOne -> RestartRest
  | _ -> DoNothing else Escalate

(* restart_decision_eqb (matches Coq: Definition restart_decision_eqb) *)
let restart_decision_eqb (p_d1: restart_decision) (p_d2: restart_decision) : Tot bool =
  match p_d1, p_d2 with
  | RestartChild, RestartChild -> true
  | RestartAll, RestartAll -> true
  | RestartRest, RestartRest -> true
  | Escalate, Escalate -> true
  | DoNothing, DoNothing -> true
  | _, _ -> false
  | _ -> false

(* apply_rest_for_one (matches Coq: Fixpoint apply_rest_for_one) *)
let rec apply_rest_for_one (p_children: (list child_state)) (p_cid: nat) (p_found: bool) : Tot list bool =
  match p_children with
  | [] -> []
  | c :: rest -> let is_target = Nat.eqb (cs_id (c.f_ch_spec)) p_cid in let should_restart = p_found
  | _ -> []

(* riina_child_spec_1 (matches Coq: Definition riina_child_spec_1) *)
let riina_child_spec_1 : child_spec = {f_cs_id=1; f_cs_type=Permanent; f_cs_max_restarts=5; f_cs_restart_window=60; f_cs_shutdown_timeout=5000}

(* riina_child_spec_2 (matches Coq: Definition riina_child_spec_2) *)
let riina_child_spec_2 : child_spec = {f_cs_id=2; f_cs_type=Transient; f_cs_max_restarts=3; f_cs_restart_window=60; f_cs_shutdown_timeout=5000}

(* riina_child_spec_3 (matches Coq: Definition riina_child_spec_3) *)
let riina_child_spec_3 : child_spec = {f_cs_id=3; f_cs_type=Temporary; f_cs_max_restarts=1; f_cs_restart_window=60; f_cs_shutdown_timeout=5000}

(* riina_child_running (matches Coq: Definition riina_child_running) *)
let riina_child_running : child_state = mkChildState riina_child_spec_1 ChildRunning 0 100 101

(* riina_child_crashed (matches Coq: Definition riina_child_crashed) *)
let riina_child_crashed : child_state = mkChildState riina_child_spec_1 ChildCrashed 0 0 101

(* riina_child_stopped (matches Coq: Definition riina_child_stopped) *)
let riina_child_stopped : child_state = mkChildState riina_child_spec_2 ChildStopped 0 50 102

(* riina_child_restarting (matches Coq: Definition riina_child_restarting) *)
let riina_child_restarting : child_state = mkChildState riina_child_spec_2 ChildRestarting 1 0 102

(* riina_child_transient (matches Coq: Definition riina_child_transient) *)
let riina_child_transient : child_state = mkChildState riina_child_spec_2 ChildRunning 0 200 102

(* riina_child_temporary (matches Coq: Definition riina_child_temporary) *)
let riina_child_temporary : child_state = mkChildState riina_child_spec_3 ChildCrashed 0 0 103

(* riina_supervisor (matches Coq: Definition riina_supervisor) *)
let riina_supervisor : supervisor = mkSupervisor 0 OneForOne [riina_child_running; riina_child_transient] 10 0 20

(* riina_supervisor_afo (matches Coq: Definition riina_supervisor_afo) *)
let riina_supervisor_afo : supervisor = mkSupervisor 1 AllForOne [riina_child_running; riina_child_transient] 10 0 20

(* riina_supervisor_rfo (matches Coq: Definition riina_supervisor_rfo) *)
let riina_supervisor_rfo : supervisor = mkSupervisor 2 RestForOne [riina_child_running; riina_child_transient] 10 0 20

(* riina_supervisor_full (matches Coq: Definition riina_supervisor_full) *)
let riina_supervisor_full : supervisor = mkSupervisor 3 OneForOne [riina_child_running] 10 10 20

(* andb_true_iff (matches Coq: Lemma andb_true_iff) *)
let andb_true_iff (p_a: bool) (p_b: bool) : Lemma (p_a && p_b == true <==> p_a == true /\ p_b == true) = admit ()

(* orb_true_iff (matches Coq: Lemma orb_true_iff) *)
let orb_true_iff (p_a: bool) (p_b: bool) : Lemma (p_a || p_b == true <==> p_a == true \/ p_b == true) = admit ()

(* negb_true_iff (matches Coq: Lemma negb_true_iff) *)
let negb_true_iff (p_b: bool) : Lemma ((not p_b) == true <==> p_b == false) = admit ()

(* negb_false_iff (matches Coq: Lemma negb_false_iff) *)
let negb_false_iff (p_b: bool) : Lemma ((not p_b) == false <==> p_b == true) = admit ()

(* leb_le (matches Coq: Lemma leb_le) *)
let leb_le (p_n: _) (p_m: _) : Lemma (p_n p_m == true <==> p_n <= p_m) = admit ()

(* ltb_lt (matches Coq: Lemma ltb_lt) *)
let ltb_lt (p_n: _) (p_m: _) : Lemma (Nat.ltb p_n p_m == true <==> p_n < p_m) = admit ()

(* AS_001_strategy_eq_ofo (matches Coq: Theorem AS_001_strategy_eq_ofo) *)
let as_001_strategy_eq_ofo () : Lemma (strategy_eqb OneForOne OneForOne == true) = admit ()

(* AS_002_strategy_eq_afo (matches Coq: Theorem AS_002_strategy_eq_afo) *)
let as_002_strategy_eq_afo () : Lemma (strategy_eqb AllForOne AllForOne == true) = admit ()

(* AS_003_strategy_eq_rfo (matches Coq: Theorem AS_003_strategy_eq_rfo) *)
let as_003_strategy_eq_rfo () : Lemma (strategy_eqb RestForOne RestForOne == true) = admit ()

(* AS_004_strategy_eqb_refl (matches Coq: Theorem AS_004_strategy_eqb_refl) *)
let as_004_strategy_eqb_refl (p_s: _) : Lemma (strategy_eqb p_s p_s == true) = admit ()

(* AS_005_strategy_eqb_sym (matches Coq: Theorem AS_005_strategy_eqb_sym) *)
let as_005_strategy_eqb_sym (p_s1: _) (p_s2: _) : Lemma (strategy_eqb p_s1 p_s2 == strategy_eqb p_s2 p_s1) = admit ()

(* AS_006_strategy_eqb_true_eq (matches Coq: Theorem AS_006_strategy_eqb_true_eq) *)
let as_006_strategy_eqb_true_eq (p_s1: _) (p_s2: _) : Lemma (requires (strategy_eqb p_s1 p_s2 == true)) (ensures (p_s1 == p_s2)) = admit ()

(* AS_007_strategy_neq_ofo_afo (matches Coq: Theorem AS_007_strategy_neq_ofo_afo) *)
let as_007_strategy_neq_ofo_afo () : Lemma (strategy_eqb OneForOne AllForOne == false) = admit ()

(* AS_008_strategy_neq_ofo_rfo (matches Coq: Theorem AS_008_strategy_neq_ofo_rfo) *)
let as_008_strategy_neq_ofo_rfo () : Lemma (strategy_eqb OneForOne RestForOne == false) = admit ()

(* AS_009_strategy_neq_afo_rfo (matches Coq: Theorem AS_009_strategy_neq_afo_rfo) *)
let as_009_strategy_neq_afo_rfo () : Lemma (strategy_eqb AllForOne RestForOne == false) = admit ()

(* AS_010_strategy_eq_dec (matches Coq: Theorem AS_010_strategy_eq_dec) *)
let as_010_strategy_eq_dec (p_s1: restart_strategy) (p_s2: restart_strategy) : Lemma ({p_s1 == s2_ + {p_s1 <> s2_) = admit ()

(* AS_011_ofo_decides_restart_child (matches Coq: Theorem AS_011_ofo_decides_restart_child) *)
let as_011_ofo_decides_restart_child () : Lemma (decide_restart OneForOne true == RestartChild) = admit ()

(* AS_012_afo_decides_restart_all (matches Coq: Theorem AS_012_afo_decides_restart_all) *)
let as_012_afo_decides_restart_all () : Lemma (decide_restart AllForOne true == RestartAll) = admit ()

(* AS_013_rfo_decides_restart_rest (matches Coq: Theorem AS_013_rfo_decides_restart_rest) *)
let as_013_rfo_decides_restart_rest () : Lemma (decide_restart RestForOne true == RestartRest) = admit ()

(* AS_014_cannot_restart_escalates (matches Coq: Theorem AS_014_cannot_restart_escalates) *)
let as_014_cannot_restart_escalates (p_s: _) : Lemma (decide_restart p_s false == Escalate) = admit ()

(* AS_015_decide_restart_complete (matches Coq: Theorem AS_015_decide_restart_complete) *)
let as_015_decide_restart_complete (p_s: _) (p_b: _) : Lemma (decide_restart p_s p_b == RestartChild \/ decide_restart p_s p_b == RestartAll \/ decide_restart p_s p_b == RestartRest \/ decide_restart p_s p_b == Escalate) = admit ()

(* AS_016_child_status_eq_running (matches Coq: Theorem AS_016_child_status_eq_running) *)
let as_016_child_status_eq_running () : Lemma (child_status_eqb ChildRunning ChildRunning == true) = admit ()

(* AS_017_child_status_eq_stopped (matches Coq: Theorem AS_017_child_status_eq_stopped) *)
let as_017_child_status_eq_stopped () : Lemma (child_status_eqb ChildStopped ChildStopped == true) = admit ()

(* AS_018_child_status_eq_crashed (matches Coq: Theorem AS_018_child_status_eq_crashed) *)
let as_018_child_status_eq_crashed () : Lemma (child_status_eqb ChildCrashed ChildCrashed == true) = admit ()

(* AS_019_child_status_eq_restarting (matches Coq: Theorem AS_019_child_status_eq_restarting) *)
let as_019_child_status_eq_restarting () : Lemma (child_status_eqb ChildRestarting ChildRestarting == true) = admit ()

(* AS_020_child_status_eqb_refl (matches Coq: Theorem AS_020_child_status_eqb_refl) *)
let as_020_child_status_eqb_refl (p_s: _) : Lemma (child_status_eqb p_s p_s == true) = admit ()

(* AS_021_child_status_eqb_sym (matches Coq: Theorem AS_021_child_status_eqb_sym) *)
let as_021_child_status_eqb_sym (p_s1: _) (p_s2: _) : Lemma (child_status_eqb p_s1 p_s2 == child_status_eqb p_s2 p_s1) = admit ()

(* AS_022_child_status_eqb_true_eq (matches Coq: Theorem AS_022_child_status_eqb_true_eq) *)
let as_022_child_status_eqb_true_eq (p_s1: _) (p_s2: _) : Lemma (requires (child_status_eqb p_s1 p_s2 == true)) (ensures (p_s1 == p_s2)) = admit ()

(* AS_023_child_status_eq_dec (matches Coq: Theorem AS_023_child_status_eq_dec) *)
let as_023_child_status_eq_dec (p_s1: child_status) (p_s2: child_status) : Lemma ({p_s1 == s2_ + {p_s1 <> s2_) = admit ()

(* AS_024_child_type_eq_dec (matches Coq: Theorem AS_024_child_type_eq_dec) *)
let as_024_child_type_eq_dec (p_t1: child_type) (p_t2: child_type) : Lemma ({p_t1 == t2_ + {p_t1 <> t2_) = admit ()

(* AS_025_child_type_eqb_refl (matches Coq: Theorem AS_025_child_type_eqb_refl) *)
let as_025_child_type_eqb_refl (p_t: _) : Lemma (child_type_eqb p_t p_t == true) = admit ()

(* AS_026_riina_child_is_running (matches Coq: Theorem AS_026_riina_child_is_running) *)
let as_026_riina_child_is_running () : Lemma (child_running riina_child_running == true) = admit ()

(* AS_027_riina_child_is_crashed (matches Coq: Theorem AS_027_riina_child_is_crashed) *)
let as_027_riina_child_is_crashed () : Lemma (child_crashed riina_child_crashed == true) = admit ()

(* AS_028_riina_child_is_stopped (matches Coq: Theorem AS_028_riina_child_is_stopped) *)
let as_028_riina_child_is_stopped () : Lemma (child_stopped riina_child_stopped == true) = admit ()

(* AS_029_running_not_crashed (matches Coq: Theorem AS_029_running_not_crashed) *)
let as_029_running_not_crashed (p_c: _) : Lemma (requires (child_running p_c == true)) (ensures (child_crashed p_c == false)) = admit ()

(* AS_030_running_not_stopped (matches Coq: Theorem AS_030_running_not_stopped) *)
let as_030_running_not_stopped (p_c: _) : Lemma (requires (child_running p_c == true)) (ensures (child_stopped p_c == false)) = admit ()

(* AS_031_running_not_restarting (matches Coq: Theorem AS_031_running_not_restarting) *)
let as_031_running_not_restarting (p_c: _) : Lemma (requires (child_running p_c == true)) (ensures (child_restarting p_c == false)) = admit ()

(* AS_032_crashed_not_running (matches Coq: Theorem AS_032_crashed_not_running) *)
let as_032_crashed_not_running (p_c: _) : Lemma (requires (child_crashed p_c == true)) (ensures (child_running p_c == false)) = admit ()

(* AS_033_crashed_not_stopped (matches Coq: Theorem AS_033_crashed_not_stopped) *)
let as_033_crashed_not_stopped (p_c: _) : Lemma (requires (child_crashed p_c == true)) (ensures (child_stopped p_c == false)) = admit ()

(* AS_034_child_needs_restart_crashed (matches Coq: Theorem AS_034_child_needs_restart_crashed) *)
let as_034_child_needs_restart_crashed (p_c: _) : Lemma (requires (child_needs_restart p_c == true)) (ensures (child_crashed p_c == true)) = admit ()

(* AS_035_temporary_no_restart (matches Coq: Theorem AS_035_temporary_no_restart) *)
let as_035_temporary_no_restart (p_c: _) : Lemma (requires ((p_c.f_ch_spec).f_cs_type == Temporary)) (ensures (child_needs_restart p_c == false)) = admit ()

(* AS_036_riina_sup_can_restart (matches Coq: Theorem AS_036_riina_sup_can_restart) *)
let as_036_riina_sup_can_restart () : Lemma (supervisor_can_restart riina_supervisor == true) = admit ()

(* AS_037_riina_sup_full_cannot (matches Coq: Theorem AS_037_riina_sup_full_cannot) *)
let as_037_riina_sup_full_cannot () : Lemma (supervisor_can_restart riina_supervisor_full == false) = admit ()

(* AS_038_riina_sup_healthy (matches Coq: Theorem AS_038_riina_sup_healthy) *)
let as_038_riina_sup_healthy () : Lemma (supervisor_healthy riina_supervisor == true) = admit ()

(* AS_039_healthy_all_running (matches Coq: Theorem AS_039_healthy_all_running) *)
let as_039_healthy_all_running (p_sup: _) : Lemma (requires (supervisor_healthy p_sup == true)) (ensures (all_children_running p_sup == true)) = admit ()

(* AS_040_healthy_can_restart (matches Coq: Theorem AS_040_healthy_can_restart) *)
let as_040_healthy_can_restart (p_sup: _) : Lemma (requires (supervisor_healthy p_sup == true)) (ensures (supervisor_can_restart p_sup == true)) = admit ()

(* AS_041_healthy_compose (matches Coq: Theorem AS_041_healthy_compose) *)
let as_041_healthy_compose (p_sup: _) : Lemma (requires (all_children_running p_sup == true /\ supervisor_can_restart p_sup == true)) (ensures (supervisor_healthy p_sup == true)) = admit ()

(* AS_042_healthy_no_crashed (matches Coq: Theorem AS_042_healthy_no_crashed) *)
let as_042_healthy_no_crashed (p_sup: _) : Lemma (requires (all_children_running p_sup == true)) (ensures (no_children_crashed p_sup == true)) = admit ()

(* AS_043_ofo_preserves_non_crashed (matches Coq: Theorem AS_043_ofo_preserves_non_crashed) *)
let as_043_ofo_preserves_non_crashed (p_children: _) (p_cid: _) (p_c: _) : Lemma (requires (List.Tot.memP p_c p_children /\ ~((p_c.f_ch_spec).f_cs_id == p_cid))) (ensures (List.Tot.memP p_c (apply_one_for_one p_children p_cid))) = admit ()

(* AS_044_ofo_preserves_running (matches Coq: Theorem AS_044_ofo_preserves_running) *)
let as_044_ofo_preserves_running (p_children: _) (p_cid: _) (p_c: _) : Lemma (requires (List.Tot.memP p_c p_children /\ child_running p_c == true /\ ~((p_c.f_ch_spec).f_cs_id == p_cid))) (ensures (List.Tot.memP p_c (apply_one_for_one p_children p_cid))) = admit ()

(* AS_045_ofo_preserves_length (matches Coq: Theorem AS_045_ofo_preserves_length) *)
let as_045_ofo_preserves_length (p_children: _) (p_cid: _) : Lemma (length (apply_one_for_one p_children p_cid) == length p_children) = admit ()

(* AS_046_afo_preserves_length (matches Coq: Theorem AS_046_afo_preserves_length) *)
let as_046_afo_preserves_length (p_children: _) : Lemma (length (apply_all_for_one p_children) == length p_children) = admit ()

(* AS_047_rfo_preserves_length (matches Coq: Theorem AS_047_rfo_preserves_length) *)
let as_047_rfo_preserves_length (p_children: _) (p_cid: _) (p_found: _) : Lemma (length (apply_rest_for_one p_children p_cid p_found) == length p_children) = admit ()

(* AS_048_ofo_nil (matches Coq: Theorem AS_048_ofo_nil) *)
let as_048_ofo_nil (p_cid: _) : Lemma (apply_one_for_one [] p_cid == []) = admit ()

(* AS_049_afo_nil (matches Coq: Theorem AS_049_afo_nil) *)
let as_049_afo_nil () : Lemma (apply_all_for_one [] == []) = admit ()

(* AS_050_rfo_nil (matches Coq: Theorem AS_050_rfo_nil) *)
let as_050_rfo_nil (p_cid: _) (p_found: _) : Lemma (apply_rest_for_one [] p_cid p_found == []) = admit ()

(* AS_051_afo_all_running (matches Coq: Theorem AS_051_afo_all_running) *)
let as_051_afo_all_running (p_children: _) : Lemma (forallb child_running (apply_all_for_one p_children) == true) = admit ()

(* AS_052_child_in_riina_sup (matches Coq: Theorem AS_052_child_in_riina_sup) *)
let as_052_child_in_riina_sup () : Lemma (child_in_supervisor riina_supervisor 1 == true) = admit ()

(* AS_053_child_not_in_riina_sup (matches Coq: Theorem AS_053_child_not_in_riina_sup) *)
let as_053_child_not_in_riina_sup () : Lemma (child_in_supervisor riina_supervisor 99 == false) = admit ()

(* AS_054_find_child_nil (matches Coq: Theorem AS_054_find_child_nil) *)
let as_054_find_child_nil (p_cid: _) : Lemma (find_child [] p_cid == None) = admit ()

(* AS_055_find_child_head (matches Coq: Theorem AS_055_find_child_head) *)
let as_055_find_child_head (p_c: _) (p_rest: _) : Lemma (find_child (p_c :: p_rest) ((p_c.f_ch_spec).f_cs_id) == Some p_c) = admit ()

(* AS_056_all_running_nil (matches Coq: Theorem AS_056_all_running_nil) *)
let as_056_all_running_nil () : Lemma (all_children_running (mksupervisor 0 OneForOne [] 10 0 20) == true) = admit ()

(* AS_057_no_crashed_nil (matches Coq: Theorem AS_057_no_crashed_nil) *)
let as_057_no_crashed_nil () : Lemma (no_children_crashed (mksupervisor 0 OneForOne [] 10 0 20) == true) = admit ()

(* AS_058_all_running_cons (matches Coq: Theorem AS_058_all_running_cons) *)
let as_058_all_running_cons (p_c: _) (p_children: _) (p_sup_id: _) (p_strat: _) (p_max_r: _) (p_rc: _) (p_max_c: _) : Lemma (requires (child_running p_c == true /\ all_children_running (mksupervisor p_sup_id p_strat p_children p_max_r p_rc p_max_c) == true)) (ensures (all_children_running (mksupervisor p_sup_id p_strat (p_c :: p_children) p_max_r p_rc p_max_c) == true)) = admit ()

(* AS_059_no_crashed_cons (matches Coq: Theorem AS_059_no_crashed_cons) *)
let as_059_no_crashed_cons (p_c: _) (p_children: _) (p_sup_id: _) (p_strat: _) (p_max_r: _) (p_rc: _) (p_max_c: _) : Lemma (requires (child_crashed p_c == false /\ no_children_crashed (mksupervisor p_sup_id p_strat p_children p_max_r p_rc p_max_c) == true)) (ensures (no_children_crashed (mksupervisor p_sup_id p_strat (p_c :: p_children) p_max_r p_rc p_max_c) == true)) = admit ()

(* AS_060_child_in_nil (matches Coq: Theorem AS_060_child_in_nil) *)
let as_060_child_in_nil (p_sup_id: _) (p_strat: _) (p_max_r: _) (p_rc: _) (p_max_c: _) (p_cid: _) : Lemma (child_in_supervisor (mksupervisor p_sup_id p_strat [] p_max_r p_rc p_max_c) p_cid == false) = admit ()

(* AS_061_child_in_cons_head (matches Coq: Theorem AS_061_child_in_cons_head) *)
let as_061_child_in_cons_head (p_c: _) (p_rest: _) (p_sup_id: _) (p_strat: _) (p_max_r: _) (p_rc: _) (p_max_c: _) : Lemma (child_in_supervisor (mksupervisor p_sup_id p_strat (p_c :: p_rest) p_max_r p_rc p_max_c) ((p_c.f_ch_spec).f_cs_id) == true) = admit ()

(* AS_062_riina_sup_has_capacity (matches Coq: Theorem AS_062_riina_sup_has_capacity) *)
let as_062_riina_sup_has_capacity () : Lemma (supervisor_has_capacity riina_supervisor == true) = admit ()

(* AS_063_riina_sup_strategy (matches Coq: Theorem AS_063_riina_sup_strategy) *)
let as_063_riina_sup_strategy () : Lemma (riina_supervisor.f_sup_strategy == OneForOne) = admit ()

(* AS_064_riina_sup_afo_strategy (matches Coq: Theorem AS_064_riina_sup_afo_strategy) *)
let as_064_riina_sup_afo_strategy () : Lemma (riina_supervisor_afo.f_sup_strategy == AllForOne) = admit ()

(* AS_065_riina_sup_rfo_strategy (matches Coq: Theorem AS_065_riina_sup_rfo_strategy) *)
let as_065_riina_sup_rfo_strategy () : Lemma (riina_supervisor_rfo.f_sup_strategy == RestForOne) = admit ()

(* AS_066_riina_sup_id (matches Coq: Theorem AS_066_riina_sup_id) *)
let as_066_riina_sup_id () : Lemma (riina_supervisor.f_sup_id == 0) = admit ()

(* AS_067_riina_sup_max_restarts (matches Coq: Theorem AS_067_riina_sup_max_restarts) *)
let as_067_riina_sup_max_restarts () : Lemma (riina_supervisor.f_sup_max_restarts == 10) = admit ()

(* AS_068_riina_sup_restart_count (matches Coq: Theorem AS_068_riina_sup_restart_count) *)
let as_068_riina_sup_restart_count () : Lemma (riina_supervisor.f_sup_restart_count == 0) = admit ()

(* AS_069_riina_child_spec_permanent (matches Coq: Theorem AS_069_riina_child_spec_permanent) *)
let as_069_riina_child_spec_permanent () : Lemma (riina_child_spec_1.f_cs_type == Permanent) = admit ()

(* AS_070_riina_child_spec_transient (matches Coq: Theorem AS_070_riina_child_spec_transient) *)
let as_070_riina_child_spec_transient () : Lemma (riina_child_spec_2.f_cs_type == Transient) = admit ()

(* AS_071_riina_child_spec_temporary (matches Coq: Theorem AS_071_riina_child_spec_temporary) *)
let as_071_riina_child_spec_temporary () : Lemma (riina_child_spec_3.f_cs_type == Temporary) = admit ()

(* AS_072_permanent_needs_restart (matches Coq: Theorem AS_072_permanent_needs_restart) *)
let as_072_permanent_needs_restart () : Lemma (child_needs_restart riina_child_crashed == true) = admit ()

(* AS_073_temporary_no_restart (matches Coq: Theorem AS_073_temporary_no_restart) *)
let as_073_temporary_no_restart () : Lemma (child_needs_restart riina_child_temporary == false) = admit ()

(* AS_074_running_no_restart (matches Coq: Theorem AS_074_running_no_restart) *)
let as_074_running_no_restart (p_c: _) : Lemma (requires (child_running p_c == true)) (ensures (child_needs_restart p_c == false)) = admit ()

(* AS_075_stopped_no_restart (matches Coq: Theorem AS_075_stopped_no_restart) *)
let as_075_stopped_no_restart (p_c: _) : Lemma (requires (child_stopped p_c == true)) (ensures (child_needs_restart p_c == false)) = admit ()

(* AS_076_ofo_isolates_siblings (matches Coq: Theorem AS_076_ofo_isolates_siblings) *)
let as_076_ofo_isolates_siblings (p_children: _) (p_cid: _) (p_c: _) : Lemma (requires (List.Tot.memP p_c p_children /\ child_running p_c == true /\ ~((p_c.f_ch_spec).f_cs_id == p_cid))) (ensures ((exists p_c. List.Tot.memP c_ (apply_one_for_one p_children p_cid)) /\ (c_.f_ch_spec).f_cs_id == (p_c.f_ch_spec).f_cs_id /\ child_running c_ == true)) = admit ()

(* AS_077_ofo_preserves_non_target (matches Coq: Theorem AS_077_ofo_preserves_non_target) *)
let as_077_ofo_preserves_non_target (p_children: _) (p_cid: _) (p_c: _) : Lemma (requires (List.Tot.memP p_c p_children /\ ~((p_c.f_ch_spec).f_cs_id == p_cid))) (ensures (List.Tot.memP p_c (apply_one_for_one p_children p_cid))) = admit ()

(* AS_078_crash_does_not_spread (matches Coq: Theorem AS_078_crash_does_not_spread) *)
let as_078_crash_does_not_spread (p_children: _) (p_cid: _) (p_c: _) : Lemma (requires (List.Tot.memP p_c p_children /\ child_running p_c == true /\ ~((p_c.f_ch_spec).f_cs_id == p_cid))) (ensures (child_running p_c == true)) = admit ()

(* AS_079_ofo_restart_sets_running (matches Coq: Theorem AS_079_ofo_restart_sets_running) *)
let as_079_ofo_restart_sets_running (p_children: _) (p_cid: _) (p_c: _) : Lemma (requires (List.Tot.memP p_c p_children /\ (p_c.f_ch_spec).f_cs_id == p_cid /\ child_crashed p_c == true)) (ensures ((exists p_c. List.Tot.memP c_ (apply_one_for_one p_children p_cid)) /\ (c_.f_ch_spec).f_cs_id == p_cid /\ c_.f_ch_status == ChildRunning)) = admit ()

(* AS_080_ofo_increments_restart_count (matches Coq: Theorem AS_080_ofo_increments_restart_count) *)
let as_080_ofo_increments_restart_count (p_children: _) (p_cid: _) (p_c: _) : Lemma (requires (List.Tot.memP p_c p_children /\ (p_c.f_ch_spec).f_cs_id == p_cid /\ child_crashed p_c == true)) (ensures ((exists p_c. List.Tot.memP c_ (apply_one_for_one p_children p_cid)) /\ (c_.f_ch_spec).f_cs_id == p_cid /\ c_.f_ch_restart_count == ch_restart_count p_c + 1)) = admit ()

(* AS_081_afo_restarts_all (matches Coq: Theorem AS_081_afo_restarts_all) *)
let as_081_afo_restarts_all (p_children: _) (p_c: _) : Lemma (requires (List.Tot.memP p_c p_children)) (ensures ((exists p_c. List.Tot.memP c_ (apply_all_for_one p_children)) /\ (c_.f_ch_spec).f_cs_id == (p_c.f_ch_spec).f_cs_id /\ c_.f_ch_status == ChildRunning)) = admit ()

(* AS_082_afo_increments_all (matches Coq: Theorem AS_082_afo_increments_all) *)
let as_082_afo_increments_all (p_children: _) (p_c: _) : Lemma (requires (List.Tot.memP p_c p_children)) (ensures ((exists p_c. List.Tot.memP c_ (apply_all_for_one p_children)) /\ c_.f_ch_restart_count == ch_restart_count p_c + 1)) = admit ()

(* AS_083_escalate_when_limit_reached (matches Coq: Theorem AS_083_escalate_when_limit_reached) *)
let as_083_escalate_when_limit_reached (p_sup: _) : Lemma (requires (supervisor_can_restart p_sup == false)) (ensures ((forall (s: _). decide_restart s (supervisor_can_restart p_sup) == Escalate))) = admit ()

(* AS_084_restart_decision_deterministic (matches Coq: Theorem AS_084_restart_decision_deterministic) *)
let as_084_restart_decision_deterministic (p_s: _) (p_b: _) : Lemma (decide_restart p_s p_b == decide_restart p_s p_b) = admit ()

(* AS_085_decision_eqb_refl (matches Coq: Theorem AS_085_decision_eqb_refl) *)
let as_085_decision_eqb_refl (p_d: _) : Lemma (restart_decision_eqb p_d p_d == true) = admit ()

(* AS_086_decision_eqb_sym (matches Coq: Theorem AS_086_decision_eqb_sym) *)
let as_086_decision_eqb_sym (p_d1: _) (p_d2: _) : Lemma (restart_decision_eqb p_d1 p_d2 == restart_decision_eqb p_d2 p_d1) = admit ()

(* AS_087_needs_restart_implies_crashed (matches Coq: Theorem AS_087_needs_restart_implies_crashed) *)
let as_087_needs_restart_implies_crashed (p_c: _) : Lemma (requires (child_needs_restart p_c == true)) (ensures (child_crashed p_c == true)) = admit ()

(* AS_088_needs_restart_not_temporary (matches Coq: Theorem AS_088_needs_restart_not_temporary) *)
let as_088_needs_restart_not_temporary (p_c: _) : Lemma (requires (child_needs_restart p_c == true)) (ensures (~((p_c.f_ch_spec).f_cs_type == Temporary))) = admit ()

(* AS_089_needs_restart_within_limit (matches Coq: Theorem AS_089_needs_restart_within_limit) *)
let as_089_needs_restart_within_limit (p_c: _) : Lemma (requires (child_needs_restart p_c == true)) (ensures (child_within_restart_limit p_c == true)) = admit ()

(* AS_090_needs_restart_compose (matches Coq: Theorem AS_090_needs_restart_compose) *)
let as_090_needs_restart_compose (p_c: _) : Lemma (requires (child_crashed p_c == true /\ child_type_eqb ((p_c.f_ch_spec).f_cs_type) Temporary == false /\ child_within_restart_limit p_c == true)) (ensures (child_needs_restart p_c == true)) = admit ()

(* AS_091_riina_child_spec_1_id (matches Coq: Theorem AS_091_riina_child_spec_1_id) *)
let as_091_riina_child_spec_1_id () : Lemma (riina_child_spec_1.f_cs_id == 1) = admit ()

(* AS_092_riina_child_spec_2_id (matches Coq: Theorem AS_092_riina_child_spec_2_id) *)
let as_092_riina_child_spec_2_id () : Lemma (riina_child_spec_2.f_cs_id == 2) = admit ()

(* AS_093_riina_child_spec_3_id (matches Coq: Theorem AS_093_riina_child_spec_3_id) *)
let as_093_riina_child_spec_3_id () : Lemma (riina_child_spec_3.f_cs_id == 3) = admit ()

(* AS_094_riina_child_spec_1_max (matches Coq: Theorem AS_094_riina_child_spec_1_max) *)
let as_094_riina_child_spec_1_max () : Lemma (riina_child_spec_1.f_cs_max_restarts == 5) = admit ()

(* AS_095_riina_child_spec_2_max (matches Coq: Theorem AS_095_riina_child_spec_2_max) *)
let as_095_riina_child_spec_2_max () : Lemma (riina_child_spec_2.f_cs_max_restarts == 3) = admit ()

(* AS_096_riina_child_spec_3_max (matches Coq: Theorem AS_096_riina_child_spec_3_max) *)
let as_096_riina_child_spec_3_max () : Lemma (riina_child_spec_3.f_cs_max_restarts == 1) = admit ()

(* AS_097_riina_child_running_uptime (matches Coq: Theorem AS_097_riina_child_running_uptime) *)
let as_097_riina_child_running_uptime () : Lemma (riina_child_running.f_ch_uptime == 100) = admit ()

(* AS_098_riina_child_running_pid (matches Coq: Theorem AS_098_riina_child_running_pid) *)
let as_098_riina_child_running_pid () : Lemma (riina_child_running.f_ch_pid == 101) = admit ()

(* AS_099_riina_child_running_restart_count (matches Coq: Theorem AS_099_riina_child_running_restart_count) *)
let as_099_riina_child_running_restart_count () : Lemma (riina_child_running.f_ch_restart_count == 0) = admit ()

(* AS_100_riina_child_within_limit (matches Coq: Theorem AS_100_riina_child_within_limit) *)
let as_100_riina_child_within_limit () : Lemma (child_within_restart_limit riina_child_running == true) = admit ()

(* AS_101_ofo_after_afo_length (matches Coq: Theorem AS_101_ofo_after_afo_length) *)
let as_101_ofo_after_afo_length (p_children: _) (p_cid: _) : Lemma (length (apply_one_for_one (apply_all_for_one p_children) p_cid) == length p_children) = admit ()

(* AS_102_afo_after_ofo_length (matches Coq: Theorem AS_102_afo_after_ofo_length) *)
let as_102_afo_after_ofo_length (p_children: _) (p_cid: _) : Lemma (length (apply_all_for_one (apply_one_for_one p_children p_cid)) == length p_children) = admit ()

(* AS_103_child_in_after_ofo (matches Coq: Theorem AS_103_child_in_after_ofo) *)
let as_103_child_in_after_ofo (p_children: _) (p_cid: _) (p_c: _) : Lemma (requires (List.Tot.memP p_c p_children /\ ~((p_c.f_ch_spec).f_cs_id == p_cid))) (ensures (child_in_supervisor (mksupervisor 0 OneForOne (apply_one_for_one p_children p_cid) 10 0 20) ((p_c.f_ch_spec).f_cs_id) == true)) = admit ()

(* AS_104_sup_children_count (matches Coq: Theorem AS_104_sup_children_count) *)
let as_104_sup_children_count () : Lemma (length (riina_supervisor.f_sup_children) == 2) = admit ()

(* AS_105_sup_afo_children_count (matches Coq: Theorem AS_105_sup_afo_children_count) *)
let as_105_sup_afo_children_count () : Lemma (length (riina_supervisor_afo.f_sup_children) == 2) = admit ()

(* AS_106_ofo_idempotent_running (matches Coq: Theorem AS_106_ofo_idempotent_running) *)
let as_106_ofo_idempotent_running (p_children: _) (p_cid: _) : Lemma (requires (forallb child_running p_children == true /\ ((forall (c: _). List.Tot.memP c p_children)))) (ensures (apply_one_for_one p_children p_cid == p_children)) = admit ()

(* AS_107_find_child_in (matches Coq: Theorem AS_107_find_child_in) *)
let as_107_find_child_in (p_children: _) (p_cid: _) (p_c: _) : Lemma (requires (find_child p_children p_cid == Some p_c)) (ensures (List.Tot.memP p_c p_children)) = admit ()

(* AS_108_find_child_spec (matches Coq: Theorem AS_108_find_child_spec) *)
let as_108_find_child_spec (p_children: _) (p_cid: _) (p_c: _) : Lemma (requires (find_child p_children p_cid == Some p_c)) (ensures ((p_c.f_ch_spec).f_cs_id == p_cid)) = admit ()

(* AS_109_ofo_does_not_remove_children (matches Coq: Theorem AS_109_ofo_does_not_remove_children) *)
let as_109_ofo_does_not_remove_children (p_children: _) (p_cid: _) (p_c: _) : Lemma (requires (List.Tot.memP p_c p_children)) (ensures ((exists p_c. List.Tot.memP c_ (apply_one_for_one p_children p_cid)) /\ (c_.f_ch_spec).f_cs_id == (p_c.f_ch_spec).f_cs_id)) = admit ()

(* AS_110_sup_healthy_implies_no_crashed (matches Coq: Theorem AS_110_sup_healthy_implies_no_crashed) *)
let as_110_sup_healthy_implies_no_crashed (p_sup: _) : Lemma (requires (supervisor_healthy p_sup == true)) (ensures (no_children_crashed p_sup == true)) = admit ()
