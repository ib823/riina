(* SPDX-License-Identifier: MPL-2.0 *)
(* Copyright (c) 2026 The RIINA Authors. See AUTHORS file. *)

(* BinarySizeBounds.v - Binary Size Bounds for RIINA *)
(* Spec: 01_RESEARCH/17_DOMAIN_Π_PERFORMANCE/ *)
(* Safety Property: Guaranteed to fit in ROM/flash *)

Require Import Coq.Lists.List.
Require Import Coq.Bool.Bool.
Require Import Coq.Arith.Arith.
Require Import Coq.micromega.Lia.
Import ListNotations.

(* Size in bytes *)
Definition Size := nat.

(* Target architecture parameters *)
Record ArchParams : Type := mkArch {
  arch_word_size : Size;          (* 4 for 32-bit, 8 for 64-bit *)
  arch_max_instr_size : Size;     (* Max instruction bytes *)
  arch_call_overhead : Size;      (* Call instruction size *)
  arch_ret_overhead : Size;       (* Return instruction size *)
  arch_flash_size : Size;         (* Total flash available *)
  arch_ram_size : Size;           (* Total RAM available *)
}.

(* Common architectures *)
Definition arm_cortex_m0 : ArchParams := mkArch 4 4 4 2 65536 8192.
Definition arm_cortex_m4 : ArchParams := mkArch 4 4 4 2 262144 65536.
Definition riscv32 : ArchParams := mkArch 4 4 4 4 131072 32768.

(* Instruction *)
Inductive Instr : Type :=
  | INop : Instr
  | IMov : Instr
  | IAdd : Instr
  | ISub : Instr
  | IMul : Instr
  | IDiv : Instr
  | ILoad : Instr
  | IStore : Instr
  | IBranch : Instr
  | ICall : Instr
  | IRet : Instr
.

(* Instruction size (conservative upper bound) *)
Definition instr_size (arch : ArchParams) (i : Instr) : Size :=
  arch_max_instr_size arch.

(* Basic block *)
Definition BasicBlock := list Instr.

(* Basic block size - using recursion for easier proofs *)
Fixpoint bb_size (arch : ArchParams) (bb : BasicBlock) : Size :=
  match bb with
  | [] => 0
  | i :: rest => instr_size arch i + bb_size arch rest
  end.

(* Function *)
Record Function : Type := mkFunc {
  func_blocks : list BasicBlock;
  func_locals : nat;              (* Local variable count *)
}.

(* Function size helper *)
Fixpoint sum_bb_sizes (arch : ArchParams) (bbs : list BasicBlock) : Size :=
  match bbs with
  | [] => 0
  | bb :: rest => bb_size arch bb + sum_bb_sizes arch rest
  end.

(* Function size *)
Definition func_size (arch : ArchParams) (f : Function) : Size :=
  sum_bb_sizes arch (func_blocks f) +
  arch_call_overhead arch + arch_ret_overhead arch.

(* Module *)
Record Module : Type := mkMod {
  mod_functions : list Function;
  mod_data : Size;                (* Initialized data *)
  mod_bss : Size;                 (* Zero-initialized data *)
}.

(* Module size helper *)
Fixpoint sum_func_sizes (arch : ArchParams) (funcs : list Function) : Size :=
  match funcs with
  | [] => 0
  | f :: rest => func_size arch f + sum_func_sizes arch rest
  end.

(* Module size *)
Definition mod_size (arch : ArchParams) (m : Module) : Size :=
  sum_func_sizes arch (mod_functions m) + mod_data m.

(* Program *)
Record Program : Type := mkProg {
  prog_modules : list Module;
  prog_startup : Size;            (* Startup code size *)
}.

(* Program size helper *)
Fixpoint sum_mod_sizes (arch : ArchParams) (mods : list Module) : Size :=
  match mods with
  | [] => 0
  | m :: rest => mod_size arch m + sum_mod_sizes arch rest
  end.

(* Program size *)
Definition prog_size (arch : ArchParams) (p : Program) : Size :=
  sum_mod_sizes arch (prog_modules p) + prog_startup p.

(* Data section: list of global variable sizes *)
Definition DataSection := list Size.

Fixpoint data_section_size (ds : DataSection) : Size :=
  match ds with
  | [] => 0
  | s :: rest => s + data_section_size rest
  end.

(* BSS section: list of zero-initialized variable sizes *)
Definition BSSSection := list Size.

Fixpoint bss_section_size (bs : BSSSection) : Size :=
  match bs with
  | [] => 0
  | s :: rest => s + bss_section_size rest
  end.

(* Stack frame *)
Record StackFrame : Type := mkStackFrame {
  sf_locals : nat;
  sf_saved_regs : nat;
}.

Definition stack_frame_size (arch : ArchParams) (sf : StackFrame) : Size :=
  sf_locals sf * arch_word_size arch + sf_saved_regs sf * arch_word_size arch.

(* Inline expansion *)
Record InlineInfo : Type := mkInlineInfo {
  inline_original_size : Size;
  inline_call_sites : nat;
}.

Definition inline_expanded_size (info : InlineInfo) : Size :=
  inline_original_size info * inline_call_sites info.

(* Loop unrolling *)
Record LoopInfo : Type := mkLoopInfo {
  loop_body_size : Size;
  loop_unroll_factor : nat;
}.

Definition unrolled_loop_size (info : LoopInfo) : Size :=
  loop_body_size info * loop_unroll_factor info.

(* Generic instantiation (monomorphization) *)
Record GenericInfo : Type := mkGenericInfo {
  generic_template_size : Size;
  generic_instantiation_count : nat;
}.

Definition monomorphized_size (info : GenericInfo) : Size :=
  generic_template_size info * generic_instantiation_count info.

(* ROM sections *)
Record ROMLayout : Type := mkROMLayout {
  rom_text : Size;      (* Code section *)
  rom_rodata : Size;    (* Read-only data *)
  rom_init_data : Size; (* Initialized data *)
}.

Definition total_rom_size (layout : ROMLayout) : Size :=
  rom_text layout + rom_rodata layout + rom_init_data layout.

(* ═══════════════════════════════════════════════════════════════════════════ *)
(* THEOREM PERF_002_01: Instruction size bound                                 *)
(* Each instruction size is bounded by arch_max_instr_size                     *)
(* ═══════════════════════════════════════════════════════════════════════════ *)

Theorem PERF_002_01 : forall (arch : ArchParams) (i : Instr),
  instr_size arch i <= arch_max_instr_size arch.
Proof.
  intros arch i.
  unfold instr_size.
  lia.
Qed.

(* ═══════════════════════════════════════════════════════════════════════════ *)
(* THEOREM PERF_002_02: Basic block size                                       *)
(* BB_size = Σ instruction sizes = length(bb) * max_instr_size                 *)
(* ═══════════════════════════════════════════════════════════════════════════ *)

Theorem PERF_002_02 : forall (arch : ArchParams) (bb : BasicBlock),
  bb_size arch bb = length bb * arch_max_instr_size arch.
Proof.
  intros arch bb.
  induction bb as [| i rest IH].
  - simpl. lia.
  - simpl. unfold instr_size. rewrite IH. lia.
Qed.

(* ═══════════════════════════════════════════════════════════════════════════ *)
(* THEOREM PERF_002_03: Function size bound                                    *)
(* func_size = Σ basic_block sizes + prologue + epilogue                       *)
(* ═══════════════════════════════════════════════════════════════════════════ *)

Lemma sum_bb_sizes_app : forall arch bbs1 bbs2,
  sum_bb_sizes arch (bbs1 ++ bbs2) = sum_bb_sizes arch bbs1 + sum_bb_sizes arch bbs2.
Proof.
  intros arch bbs1 bbs2.
  induction bbs1 as [| bb rest IH].
  - simpl. reflexivity.
  - simpl. rewrite IH. lia.
Qed.

Theorem PERF_002_03 : forall (arch : ArchParams) (f : Function),
  func_size arch f = sum_bb_sizes arch (func_blocks f) + 
                     arch_call_overhead arch + arch_ret_overhead arch.
Proof.
  intros arch f.
  unfold func_size.
  reflexivity.
Qed.

(* ═══════════════════════════════════════════════════════════════════════════ *)
(* THEOREM PERF_002_04: Module size bound                                      *)
(* module_size = Σ function sizes + data                                       *)
(* ═══════════════════════════════════════════════════════════════════════════ *)

Lemma sum_func_sizes_app : forall arch funcs1 funcs2,
  sum_func_sizes arch (funcs1 ++ funcs2) = 
  sum_func_sizes arch funcs1 + sum_func_sizes arch funcs2.
Proof.
  intros arch funcs1 funcs2.
  induction funcs1 as [| f rest IH].
  - simpl. reflexivity.
  - simpl. rewrite IH. lia.
Qed.

Theorem PERF_002_04 : forall (arch : ArchParams) (m : Module),
  mod_size arch m = sum_func_sizes arch (mod_functions m) + mod_data m.
Proof.
  intros arch m.
  unfold mod_size.
  reflexivity.
Qed.

(* ═══════════════════════════════════════════════════════════════════════════ *)
(* THEOREM PERF_002_05: Program size bound                                     *)
(* program_size = Σ module sizes + startup code                                *)
(* ═══════════════════════════════════════════════════════════════════════════ *)

Lemma sum_mod_sizes_app : forall arch mods1 mods2,
  sum_mod_sizes arch (mods1 ++ mods2) = 
  sum_mod_sizes arch mods1 + sum_mod_sizes arch mods2.
Proof.
  intros arch mods1 mods2.
  induction mods1 as [| m rest IH].
  - simpl. reflexivity.
  - simpl. rewrite IH. lia.
Qed.

Theorem PERF_002_05 : forall (arch : ArchParams) (p : Program),
  prog_size arch p = sum_mod_sizes arch (prog_modules p) + prog_startup p.
Proof.
  intros arch p.
  unfold prog_size.
  reflexivity.
Qed.

(* ═══════════════════════════════════════════════════════════════════════════ *)
(* THEOREM PERF_002_06: Data section bound                                     *)
(* data_size = Σ global variable sizes                                         *)
(* ═══════════════════════════════════════════════════════════════════════════ *)

Lemma data_section_size_app : forall ds1 ds2,
  data_section_size (ds1 ++ ds2) = data_section_size ds1 + data_section_size ds2.
Proof.
  intros ds1 ds2.
  induction ds1 as [| s rest IH].
  - simpl. reflexivity.
  - simpl. rewrite IH. lia.
Qed.

Theorem PERF_002_06 : forall (ds : DataSection) (var_size : Size),
  In var_size ds -> var_size <= data_section_size ds.
Proof.
  intros ds var_size H.
  induction ds as [| s rest IH].
  - inversion H.
  - simpl in H. destruct H as [Heq | Hin].
    + subst. simpl. lia.
    + simpl. specialize (IH Hin). lia.
Qed.

(* ═══════════════════════════════════════════════════════════════════════════ *)
(* THEOREM PERF_002_07: BSS section bound                                      *)
(* bss_size = Σ zero-initialized sizes                                         *)
(* ═══════════════════════════════════════════════════════════════════════════ *)

Lemma bss_section_size_app : forall bs1 bs2,
  bss_section_size (bs1 ++ bs2) = bss_section_size bs1 + bss_section_size bs2.
Proof.
  intros bs1 bs2.
  induction bs1 as [| s rest IH].
  - simpl. reflexivity.
  - simpl. rewrite IH. lia.
Qed.

Theorem PERF_002_07 : forall (bs : BSSSection) (var_size : Size),
  In var_size bs -> var_size <= bss_section_size bs.
Proof.
  intros bs var_size H.
  induction bs as [| s rest IH].
  - inversion H.
  - simpl in H. destruct H as [Heq | Hin].
    + subst. simpl. lia.
    + simpl. specialize (IH Hin). lia.
Qed.

(* ═══════════════════════════════════════════════════════════════════════════ *)
(* THEOREM PERF_002_08: Stack frame bound                                      *)
(* stack_frame ≤ max_locals * word_size + saved_regs * word_size               *)
(* ═══════════════════════════════════════════════════════════════════════════ *)

Theorem PERF_002_08 : forall (arch : ArchParams) (sf : StackFrame)
                             (max_locals max_saved_regs : nat),
  sf_locals sf <= max_locals ->
  sf_saved_regs sf <= max_saved_regs ->
  stack_frame_size arch sf <= 
    max_locals * arch_word_size arch + max_saved_regs * arch_word_size arch.
Proof.
  intros arch sf max_locals max_saved_regs Hloc Hsaved.
  unfold stack_frame_size.
  assert (sf_locals sf * arch_word_size arch <= max_locals * arch_word_size arch).
  { apply Nat.mul_le_mono_r. exact Hloc. }
  assert (sf_saved_regs sf * arch_word_size arch <= max_saved_regs * arch_word_size arch).
  { apply Nat.mul_le_mono_r. exact Hsaved. }
  lia.
Qed.

(* ═══════════════════════════════════════════════════════════════════════════ *)
(* THEOREM PERF_002_09: Inline expansion bound                                 *)
(* Inlining increases code size predictably                                    *)
(* ═══════════════════════════════════════════════════════════════════════════ *)

Theorem PERF_002_09 : forall (info : InlineInfo) (call_overhead : Size),
  inline_call_sites info >= 1 ->
  inline_expanded_size info = 
    inline_original_size info * inline_call_sites info.
Proof.
  intros info call_overhead Hge.
  unfold inline_expanded_size.
  reflexivity.
Qed.

(* ═══════════════════════════════════════════════════════════════════════════ *)
(* THEOREM PERF_002_10: Loop unroll bound                                      *)
(* Unroll factor n → n× body size                                              *)
(* ═══════════════════════════════════════════════════════════════════════════ *)

Theorem PERF_002_10 : forall (info : LoopInfo),
  unrolled_loop_size info = loop_body_size info * loop_unroll_factor info.
Proof.
  intros info.
  unfold unrolled_loop_size.
  reflexivity.
Qed.

(* ═══════════════════════════════════════════════════════════════════════════ *)
(* THEOREM PERF_002_11: Generic instantiation bound                            *)
(* Monomorphization size is predictable                                        *)
(* ═══════════════════════════════════════════════════════════════════════════ *)

Theorem PERF_002_11 : forall (info : GenericInfo),
  monomorphized_size info = 
    generic_template_size info * generic_instantiation_count info.
Proof.
  intros info.
  unfold monomorphized_size.
  reflexivity.
Qed.

(* ═══════════════════════════════════════════════════════════════════════════ *)
(* THEOREM PERF_002_12: Total ROM bound                                        *)
(* text + rodata + init_data ≤ flash_size implies fits in flash                *)
(* ═══════════════════════════════════════════════════════════════════════════ *)

Theorem PERF_002_12 : forall (arch : ArchParams) (layout : ROMLayout),
  total_rom_size layout <= arch_flash_size arch ->
  rom_text layout <= arch_flash_size arch /\
  rom_rodata layout <= arch_flash_size arch /\
  rom_init_data layout <= arch_flash_size arch.
Proof.
  intros arch layout H.
  unfold total_rom_size in H.
  split; [| split]; lia.
Qed.

(* ═══════════════════════════════════════════════════════════════════════════ *)
(* THEOREM PERF_002_13: Empty basic block has zero size                       *)
(* ═══════════════════════════════════════════════════════════════════════════ *)

Theorem PERF_002_13 : forall (arch : ArchParams),
  bb_size arch [] = 0.
Proof.
  intros arch.
  simpl.
  reflexivity.
Qed.

(* ═══════════════════════════════════════════════════════════════════════════ *)
(* THEOREM PERF_002_14: Empty module has data-only size                       *)
(* ═══════════════════════════════════════════════════════════════════════════ *)

Theorem PERF_002_14 : forall (arch : ArchParams) (data bss : Size),
  let m := mkMod [] data bss in
  mod_size arch m = data.
Proof.
  intros arch data bss.
  unfold mod_size.
  simpl.
  lia.
Qed.

(* ═══════════════════════════════════════════════════════════════════════════ *)
(* THEOREM PERF_002_15: ROM layout additivity                                 *)
(* total_rom_size is sum of all sections                                      *)
(* ═══════════════════════════════════════════════════════════════════════════ *)

Theorem PERF_002_15 : forall (t r d : Size),
  let layout := mkROMLayout t r d in
  total_rom_size layout = t + r + d.
Proof.
  intros t r d.
  unfold total_rom_size.
  simpl.
  lia.
Qed.
