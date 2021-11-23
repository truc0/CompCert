Require Import Coqlib Maps.
Require Import AST Linking.
Require Import Values Memory Globalenvs Events Smallstep.
Require Import Op Registers.
Require Import Integers.
Require Import Floats.
Require Import Asm RealAsm RealAsmRegs.

Definition transf_program (p: program) : program := p.

Definition match_prog (p :program) (tp:program):= p = tp.

Lemma transf_program_match:
  forall p, match_prog p (transf_program p).
Proof.
  intros. reflexivity.
Qed.

Section PRESERVATION.

Variables prog: program.
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

Variable instr_size_1 : instruction -> Z.
Variable instr_size_2 : instruction -> Z.

Fixpoint transf_codeofs (c:code) (ofs1 ofs2 : Z) : option Z :=
  if (zeq ofs1 0) then Some ofs2 else
  match c with
    | nil => None
    | i :: il => transf_codeofs il (ofs1 - instr_size_1 i) (ofs2+ instr_size_2 i)
  end.

Inductive match_pc : block -> Z -> Z -> Prop :=
  |match_pc_gen: forall b f ofs1 ofs2,
    Genv.find_funct_ptr ge b = Some (Internal f) ->
    transf_codeofs (fn_code f) ofs1 0 = Some ofs2 ->
    match_pc b ofs1 ofs2.

Inductive match_value: val -> val -> Prop :=
  |match_int :  forall i, match_value (Vint i) (Vint i)
  |match_long: forall i, match_value (Vlong i) (Vlong i)
  |match_float: forall i, match_value (Vfloat i) (Vfloat i)
  |match_single: forall i, match_value (Vsingle i) (Vsingle i)
  |match_ptr1: forall b ofs1 ofs2,
      match_pc b ofs1 ofs2 -> match_value (Vptr b (Ptrofs.repr ofs1)) (Vptr b (Ptrofs.repr ofs2))
  |match_ptr2: forall b o, is_stack b -> match_value (Vptr b o) (Vptr b o)
  |match_undef: match_value Vundef Vundef.

(* Mem.iff memval_inject *)
Inductive match_mem : mem -> mem -> Prop :=
  match_mem_gen: forall m1 m2,
    Mem.support m1 = Mem.support m2 ->
    Mem.mem_access m1 = Mem.mem_access m2 ->
    (*mem_content*)
    match_mem m1 m2.

Inductive match_states: state -> state -> Prop :=
  |match_states_gen: forall rs1 rs2 m1 m2,
      (forall r, r <> PC -> r <> RA -> rs1 r = rs2 r) ->
      match_value (rs1 # PC) (rs2 # PC) ->
      match_value (rs1 # RA) (rs2 # RA) ->
      match_mem m1 m2 ->
      match_states (State rs1 m1) (State rs2 m2).

Lemma step_simulation:
  forall S1 t S2, step instr_size_1 ge S1 t S2 ->
  forall S1', match_states S1 S1' ->
  exists S2', step instr_size_2 tge S1' t S2' /\ match_states S2 S2'.
Proof.
  intros. inv H; inv H0.
  - econstructor; eauto. split.
    econstructor; eauto.
    
    econstructor; eauto.
  - econstructor; eauto. split.
    eapply exec_Iop; eauto. rewrite <- genv_eq.
    eapply eval_operation_memiff; eauto.
    econstructor; eauto.
  - econstructor; eauto. split.
    rewrite <- genv_eq.
    eapply exec_Iload; eauto.
    erewrite <- Mem.loadv_iff; eauto.
    econstructor; eauto.
  - exploit Mem.storev_iff; eauto.
    intros (m2' & H3' & IFF').
    econstructor; eauto. split.
    rewrite <- genv_eq.
    eapply exec_Istore; eauto.
    econstructor; eauto.
    rewrite <- (Mem.support_storev _ _ _ _ _ H3).
    rewrite <- (Mem.support_storev _ _ _ _ _ H3').
    auto.
  - econstructor; eauto. split.
    rewrite <- genv_eq.
    eapply exec_Icall; eauto.
    econstructor; eauto.
    eapply Mem.push_stage_left_iff; eauto.
    simpl. reflexivity.
  - edestruct Mem.free_parallel_iff as [m1' []]; eauto.
    inv H14. erewrite <- Mem.astack_return_frame in H7; eauto.
    erewrite Mem.support_free in H7; eauto. congruence.
    edestruct Mem.return_frame_iff as [m'2 []]; eauto.
    assert ({m'3:mem|Mem.pop_stage m'2= Some m'3}).
      apply Mem.nonempty_pop_stage.
      erewrite <- Mem.astack_return_frame. 2: eauto.
      erewrite Mem.support_free. 2: eauto. congruence.
    destruct X as [m'3 POP].
    apply Mem.astack_pop_stage in POP as STKm2'.
    destruct STKm2' as [hd STKm2'].
    econstructor; eauto. split.
    rewrite <- genv_eq.
    eapply exec_Itailcall; eauto.
    econstructor; eauto.
    eapply Mem.pop_stage_right_iff; eauto.
    erewrite <- Mem.astack_return_frame. 2: eauto.
    erewrite Mem.support_free. 2: eauto. eauto.
    erewrite <- Mem.support_free in H8; eauto.
    erewrite Mem.astack_return_frame in H8; eauto.
    congruence.
  - exploit Mem.push_stage_left_iff; eauto. intro.
    exploit external_call_mem_iff; eauto. intros (m'1 & EXT &IFF').
    econstructor; eauto. split.
    rewrite <- genv_eq.
    econstructor; eauto.
    eapply eval_builtin_args_memiff; eauto.
    econstructor; eauto.
    eapply Mem.pop_stage_left_iff; eauto.
    rewrite <- (external_call_astack _ _ _ _ _ _ _ EXT).
    apply Mem.astack_pop_stage in H4. destruct H4.
    rewrite <- (external_call_astack _ _ _ _ _ _ _ H3) in H0.
    simpl in H0. inv H0. auto.
  - econstructor; eauto. split.
    rewrite <- genv_eq.
    eapply exec_Icond; eauto.
    erewrite <- eval_condition_memiff; eauto.
    econstructor; eauto.
  - econstructor; eauto. split.
    rewrite <- genv_eq.
    eapply exec_Ijumptable; eauto.
    econstructor; eauto.
  - edestruct Mem.free_parallel_iff as [m'1[]]; eauto.
    edestruct Mem.return_frame_iff as [m'2[]]; eauto.
    apply Mem.support_free in H2 as SFREE.
    apply Mem.support_free in H as SFREE'.
    apply Mem.astack_return_frame in H3 as ARET.
    apply Mem.astack_return_frame in H5 as ARET'.
    inv H12. congruence.
    assert ({m'3:mem|Mem.pop_stage m'2= Some m'3}).
      apply Mem.nonempty_pop_stage. congruence.
    destruct X as [m'3 POP].
    econstructor; eauto. split.
    eapply exec_Ireturn; eauto.
    econstructor; eauto.
    eapply Mem.pop_stage_right_iff; eauto.
    rewrite <- ARET. rewrite SFREE. eauto.
    apply Mem.astack_pop_stage in POP. destruct POP. congruence.
  - edestruct Mem.alloc_frame_iff as [m'1 []]; eauto.
    edestruct Mem.alloc_parallel_iff as [m'2 []]; eauto.
    apply Mem.astack_alloc_frame in H1 as SAF.
    apply Mem.astack_alloc_frame in H as SAF'.
    apply Mem.support_alloc in H2 as SAL.
    apply Mem.support_alloc in H4 as SAL'.
    exploit Mem.push_stage_right_iff. apply H5. intro.
    apply Mem.astack_record_frame in H3 as ASTK.
    apply Mem.record_frame_size1 in H3 as SIZE. simpl in SIZE.
    destruct ASTK as (hd' & tl' & ASTKm' & ASTKm''). rewrite ASTKm' in SIZE.
    rewrite SAL in ASTKm'.
    unfold sup_incr in ASTKm'. destr_in ASTKm'. simpl in ASTKm'.
    rewrite <- SAF in ASTKm'.
    rewrite H10 in ASTKm'. inv ASTKm'.
    assert ({m'3:mem|Mem.record_frame (Mem.push_stage m'2) (Memory.mk_frame (fn_stack_requirements id)) = Some m'3}).
      apply Mem.request_record_frame. simpl. congruence.
      simpl. rewrite SAL'. unfold sup_incr. destr. simpl.
      rewrite <- SAF'.
      apply match_stackadt_size in H11. simpl in *.
      generalize (size_of_all_frames_pos hd'). lia.
    destruct X as [m'3 RECORD].
    econstructor; eauto. split.
    econstructor; eauto.
    econstructor; eauto.
    eapply Mem.record_frame_safe_iff; eauto.
    apply Mem.astack_record_frame in RECORD as ASTK.
    destruct ASTK as (hd''&tl''&STKm'1&STKm'2).
    rewrite STKm'2. simpl in STKm'1. inv STKm'1.
    rewrite ASTKm''. econstructor. 2:eauto.
    rewrite SAL'. unfold sup_incr. destr. simpl. rewrite <- SAF'. auto.
  - exploit external_call_mem_iff; eauto.
    intros (m2' & H1'& IFF).
    econstructor; eauto. split.
    rewrite <- genv_eq.
    econstructor; eauto.
    econstructor; eauto.
    rewrite <- (external_call_astack _ _ _ _ _ _ _ H1). eauto.
    rewrite <- (external_call_astack _ _ _ _ _ _ _ H1'). eauto.
  - apply Mem.stack_pop_stage in H1 as H1'. destruct H1'.
    econstructor; eauto. split.
    econstructor; eauto.
    econstructor; eauto.
    eapply Mem.pop_stage_left_iff; eauto.
    apply Mem.astack_pop_stage in H1. destruct H1. rewrite H in H6. inv H6.
    auto.
Qed.

Lemma transf_initial_states:
  forall S1, RTL.initial_state prog S1 ->
  exists S2, initial_state tprog S2 /\ match_states S1 S2.
Proof.
  intros. inv TRANSL. inv H.
  exists (Callstate nil f nil m1 (prog_main tprog)).
  split.
  econstructor; eauto.
  econstructor; eauto.
  eapply Mem.push_stage_left_iff. apply Mem.iff_refl.
  simpl. reflexivity. erewrite Mem.astack_alloc; eauto.
  apply Genv.init_mem_astack in H0. rewrite H0.
  constructor.
Qed.

Lemma transf_final_states:
  forall S1 S2 r, match_states S1 S2 -> RTL.final_state S1 r -> final_state S2 r.
Proof.
  intros. inv H0. inv H. constructor.
Qed.


Theorem transf_program_correct:
  forward_simulation (RTL.semantics fn_stack_requirements prog)
                     (RTLmach.semantics fn_stack_requirements tprog).
Proof.
  eapply forward_simulation_step.
  rewrite prog_eq. auto.
  eexact transf_initial_states.
  eexact transf_final_states.
  exact step_simulation.
Qed.

End PRESERVATION.

Instance TransfRTLmachLink : TransfLink match_prog.
Proof.
  red; intros. destruct (link_linkorder _ _ _ H) as (LO1 & LO2).
  eexists p. split. inv H0. inv H1. auto. reflexivity.
Qed.
