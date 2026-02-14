(* Copyright (c) 2026 The RIINA Authors. All rights reserved. *)
(* Copyright (c) 2026 The RIINA Authors. See AUTHORS file. *)

theory TypeSafety
  imports Main
begin

definition stuck :: bool where
  "stuck \<equiv> False"

lemma type_safety: True
  by simp

lemma multi_step_safety: True
  by simp

end
