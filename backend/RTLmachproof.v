(* *********************************************************************)
(*                                                                     *)
(*              The Compcert verified compiler                         *)
(*                                                                     *)
(*          Xavier Leroy, INRIA Paris-Rocquencourt                     *)
(*                                                                     *)
(*  Copyright Institut National de Recherche en Informatique et en     *)
(*  Automatique.  All rights reserved.  This file is distributed       *)
(*  under the terms of the INRIA Non-Commercial License Agreement.     *)
(*                                                                     *)
(* *********************************************************************)

(** Postorder renumbering of RTL control-flow graphs. *)

Require Import Coqlib Maps.
Require Import AST Linking.
Require Import Values Memory Globalenvs Events Smallstep.
Require Import Op Registers RTL RTLmach.
(*
Definition transf_instr (pc:node)(i: RTL.instruction) : instruction :=
  match i with
  | RTL.Inop s => Inop s
  | RTL.Iop op args res s => Iop op args res s
  | RTL.Iload chunk addr args res s => Iload chunk addr args res s
  | RTL.Istore chunk addr args src s => Istore chunk addr args src s
  | RTL.Icall sg ros args res s => Icall sg ros args res s
  | RTL.Itailcall sg ros args => Itailcall sg ros args
  | RTL.Ibuiltin ef args res s => Ibuiltin ef args res s
  | RTL.Icond cond args s1 s2 => Icond cond args s1 s2
  | RTL.Ijumptable arg tbl => Ijumptable arg tbl
  | RTL.Ireturn or => Ireturn or
  end.

Definition transf_function (f: function) : function :=
  mkfunction
    f.(RTL.fn_sig)
    f.(RTL.fn_params)
    f.(RTL.fn_stacksize)
    (PTree.map transf_instr f.(RTL.fn_code))
    f.(RTL.fn_entrypoint).

Definition transf_fundef (fd: RTL.fundef) : fundef :=
  AST.transf_fundef transf_function fd.
*)
Definition transf_program (p: program) : program := p.


Definition match_prog (p :RTL.program) (tp:program):= p = tp.

Lemma transf_program_match:
  forall p, match_prog p (transf_program p).
Proof.
  intros. reflexivity.
Qed.

Section PRESERVATION.

Variables fn_stack_requirements : ident -> Z.
Variables prog: RTL.program.
Variables tprog: program.
Hypothesis TRANSL: match_prog prog tprog.
Let ge := Genv.globalenv prog.
Let tge := Genv.globalenv tprog.

Lemma prog_eq : prog = tprog.
Proof. auto. Qed.

Lemma genv_eq : ge = tge.
Proof.
  unfold match_prog in TRANSL. unfold ge.
  unfold tge. congruence.
Qed.
(*
Lemma functions_translated:
  forall v f,
  Genv.find_funct ge v = Some f ->
  Genv.find_funct tge v = Some f.
Proof. apply (Genv.find_funct_transf TRANSL). Qed.

Lemma function_ptr_translated:
  forall v f,
  Genv.find_funct_ptr ge v = Some f ->
  Genv.find_funct_ptr tge v = Some (transf_fundef f).
Proof. apply (Genv.find_funct_ptr_transf TRANSL). Qed.

Lemma symbols_preserved:
  forall id,
  Genv.find_symbol tge id = Genv.find_symbol ge id.
Proof. apply (Genv.find_symbol_transf TRANSL). Qed.

Lemma senv_preserved:
  Senv.equiv ge tge.
Proof. apply (Genv.senv_transf TRANSL). Qed.

Lemma sig_preserved:
  forall f, funsig (transf_fundef f) = RTL.funsig f.
Proof.
  destruct f; reflexivity.
Qed.

Lemma find_function_translated:
  forall ros rs fd,
  RTL.find_function ge ros rs = Some fd ->
  find_function tge ros rs = Some (transf_fundef fd).
Proof.
  unfold find_function; unfold RTL.find_function; intros. destruct ros as [r|id].
  eapply functions_translated; eauto.
  rewrite symbols_preserved. destruct (Genv.find_symbol ge id); try congruence.
  eapply function_ptr_translated; eauto.
Qed.
*)
Lemma stage_size_head_le_all : forall s : Mem.stage,
    Mem.size_of_head_frame s <= Mem.size_of_all_frames s.
Proof.
  intros. induction s.
  - simpl. lia.
  - simpl.  generalize (Mem.size_of_all_frames_pos s).
    lia.
Qed.
Lemma stack_size_mach_le_vm : forall stk : Mem.stackadt,
    Mem.stack_size_mach stk <= Mem.stack_size_vm stk.
Proof.
  intros. induction stk.
  - simpl. lia.
  - simpl. generalize (stage_size_head_le_all a).
    lia.
Qed.

Definition match_states (s1 s2:state):  Prop := s1 = s2.

Lemma step_simulation:
  forall S1 t S2, RTL.step fn_stack_requirements ge S1 t S2 ->
  forall S1', match_states S1 S1' ->
  exists S2', step fn_stack_requirements tge S1' t S2' /\ match_states S2 S2'.
Proof.
  intros. inv H0. rewrite <- genv_eq. exists S2.
  inv H; split.
  constructor; auto. reflexivity.
  econstructor; eauto. reflexivity.
  eapply exec_Iload; eauto.  reflexivity.
  eapply exec_Istore; eauto. reflexivity.
  econstructor; eauto. reflexivity.
  econstructor; eauto. reflexivity.
  econstructor; eauto. reflexivity.
  eapply exec_Icond; eauto. reflexivity.
  eapply exec_Ijumptable; eauto. reflexivity.
  eapply exec_Ireturn; eauto. reflexivity.
  econstructor. apply H0.
  apply Mem.record_frame_vm_result in H1 as H2.
  apply Mem.record_frame_vm_size in H1 as H3.
  unfold Mem.record_frame_mach. rewrite H2.
  generalize (stack_size_mach_le_vm (Mem.stack (Mem.support m''))).
  intro.
  assert (Mem.stack_size_mach (Mem.stack (Mem.support m'')) <= Mem.max_stacksize) by lia.
  apply zle_true. auto. reflexivity.
  econstructor; eauto. reflexivity.
  econstructor; eauto. reflexivity.
Qed.

Lemma transl_initial_states:
  forall S, RTL.initial_state fn_stack_requirements prog S ->
  exists R, initial_state fn_stack_requirements tprog R /\ match_states S R.
Proof.
  intros. exists S. split. inv TRANSL.
  inv H. econstructor; eauto. reflexivity.
Qed.

Lemma transl_final_states:
  forall S R r,
  match_states S R -> RTL.final_state S r -> final_state R r.
Proof.
  intros. inv H0. inv H. constructor.
Qed.

Theorem transf_program_correct:
  forward_simulation (RTL.semantics fn_stack_requirements prog)
                     (semantics fn_stack_requirements tprog).
Proof.
  eapply forward_simulation_step.
  inv TRANSL. auto.
  eexact transl_initial_states.
  eexact transl_final_states.
  exact step_simulation.
Qed.

End PRESERVATION.
