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

Lemma find_function_translated:
  forall ros rs rs' f,
  find_function ge ros rs = Some f ->
  regs_lessdef rs rs' ->
  find_function ge ros rs' = Some f.
Proof.
  intros until f; destruct ros; simpl.
  intros.
  assert (rs'#r = rs#r).
    exploit Genv.find_funct_inv; eauto. intros [b EQ].
    generalize (H0 r). rewrite EQ. intro LD. inv LD. auto.
  rewrite H1. auto.
  destruct (Genv.find_symbol ge i); intros. auto.
  discriminate.
Qed.

Lemma find_function_id_preserved:
  forall ros rs rs' id,
  ros_is_function ge ros rs id ->
  regs_lessdef rs rs' ->
  ros_is_function ge ros rs' id.
Proof.
  unfold ros_is_function. intros.
  destruct ros.
  - destruct H as (b & o & RS & FS).
  specialize (H0 r). rewrite RS in H0; inv H0.
  eexists; eexists; split; eauto.
  - auto.
Qed.

Lemma lessdef_list_refl : forall s,
    Val.lessdef_list s s.
Proof.
  induction s; eauto.
Qed.

Inductive match_stackadt : Mem.stackadt -> Mem.stackadt -> Prop :=
  |match_stackadt_nil : match_stackadt nil nil
  |match_stackadt_cons : forall s1 s2 (t1:Mem.stage) (t1':Mem.stage) (frame:Mem.frame),
     match_stackadt s1 s2 ->
     t1 = frame::t1' ->
     match_stackadt (t1::s1) ((frame::nil)::s2).

Lemma match_stackadt_nonempty : forall s1 s2,
    match_stackadt s1 s2 ->
    s1 = nil <-> s2 = nil.
Proof.
  intros. inv H.
  - reflexivity.
  - split; congruence.
Qed.

Lemma match_stackadt_size : forall s1 s2,
    match_stackadt s1 s2 ->
    Mem.stack_size s2 <= Mem.stack_size s1.
Proof.
  intros. induction H.
  - lia.
  - simpl. rewrite H0. simpl in *.
    generalize (Mem.size_of_all_frames_pos t1').
    lia.
Qed.


Lemma valid_pointer_memiff : forall m1 m2 b ofs,
    Mem.iff m1 m2 -> Mem.valid_pointer m1 b ofs = true <-> Mem.valid_pointer m2 b ofs = true.
Proof. intros. inv H.
       transitivity (Mem.perm m1 b ofs Cur Nonempty).
       apply Mem.valid_pointer_nonempty_perm.
       transitivity (Mem.perm m2 b ofs Cur Nonempty).
       unfold Mem.perm. rewrite access_iff. reflexivity.
       symmetry. apply Mem.valid_pointer_nonempty_perm.
Qed.

Lemma valid_pointer_memiff1 : forall m1 m2 b ofs,
    Mem.iff m1 m2 -> Mem.valid_pointer m1 b ofs = Mem.valid_pointer m2 b ofs.
Proof. intros.
       destruct (Mem.valid_pointer m1 b ofs) eqn:vp1.
       generalize (valid_pointer_memiff _ _ b ofs H). intros.
       apply H0 in vp1. rewrite vp1. auto.
       destruct (Mem.valid_pointer m2 b ofs) eqn:vp2.
       eapply valid_pointer_memiff in vp2; eauto. auto.
Qed.
Lemma eval_cond_memiff:
    forall  (m m0 : mem) (cond : condition) (vl : list val),
      Mem.iff m m0 ->
      eval_condition cond vl m0 =
      eval_condition cond vl m.
Proof.
    intros m m0 cond vl H6.
    unfold eval_condition. destruct cond; auto.
    unfold Val.cmplu_bool. repeat destr.
    repeat (erewrite (valid_pointer_memiff1 m m0 _ _) in Heqb2; eauto). congruence.
    repeat (erewrite (valid_pointer_memiff1 m m0 _ _) in Heqb2; eauto). congruence.
    repeat (erewrite (valid_pointer_memiff1 m m0 _ _) in Heqb2; eauto). congruence.
    repeat (erewrite (valid_pointer_memiff1 m m0 _ _) in Heqb2; eauto). congruence.
    repeat (erewrite (valid_pointer_memiff1 m m0 _ _) in Heqb2; eauto). congruence.
    repeat (erewrite (valid_pointer_memiff1 m m0 _ _) in Heqb2; eauto). congruence.
    repeat (erewrite (valid_pointer_memiff1 m m0 _ _) in Heqb2; eauto). congruence.
    repeat (erewrite (valid_pointer_memiff1 m m0 _ _) in Heqb2; eauto). congruence.
    unfold Val.cmplu_bool. repeat destr.
    repeat (erewrite (valid_pointer_memiff1 m m0 _ _) in Heqb2; eauto). congruence.
    repeat (erewrite (valid_pointer_memiff1 m m0 _ _) in Heqb2; eauto). congruence.
Qed.
Lemma eval_op_memiff:
  forall (sp : val) (m m0 : mem) (op : operation)
    (vl :list val) (v : val) (H3 : eval_operation ge sp op vl m = Some v)
    (H6 : Mem.iff m m0), eval_operation ge sp op vl m0 = Some v.
Proof.
  intros sp m m0 op vl v H3 H6.
  unfold eval_operation in *. destruct op; auto.
  erewrite eval_cond_memiff; eauto.
  repeat destr.
  erewrite eval_cond_memiff; eauto.
Qed.

Lemma eval_builtin_arg_memiff:
  forall sp rs m m0 args vargs,
    eval_builtin_arg ge (fun r: positive => rs # r) sp m args vargs ->
    Mem.iff m m0 ->
    eval_builtin_arg ge (fun r: positive => rs # r) sp m0 args vargs.
Proof.
  intros. induction H; constructor; eauto.
  erewrite <- Mem.loadv_iff; eauto.
  erewrite <- Mem.loadv_iff; eauto.
Qed.

Lemma eval_builtin_args_memiff:
  forall (sp : val) (rs : Regmap.t val) (m m0 : mem) (args : list (builtin_arg reg))
    (vargs : list val) (H3 : eval_builtin_args ge (fun r : positive => rs # r) sp m args vargs)
    (H7 : Mem.iff m m0),
    eval_builtin_args ge (fun r : positive => rs # r) sp m0 args vargs.
Proof.
  intros sp rs m m0 args vargs H3 H7.
  unfold eval_builtin_args in *.
  induction H3; constructor; auto.
  eapply eval_builtin_arg_memiff; eauto.
Qed.

Inductive match_states: RTL.state -> RTL.state -> Prop :=
  | match_regular_states: forall stk f sp pc rs m m',
        Mem.iff m m' ->
        match_stackadt (Mem.stack(Mem.support m)) (Mem.stack(Mem.support m'))->
      match_states (State stk f sp pc rs m)
                   (State stk f sp pc rs m')
  | match_callstates: forall stk f args m sz m' hd tl,
        Mem.iff m m' ->
        Mem.stack(Mem.support m) = hd :: tl ->
        match_stackadt tl (Mem.stack(Mem.support m')) ->
      match_states (Callstate stk f args m sz)
                   (Callstate stk f args m' sz)
  | match_returnstates: forall stk v  m m' hd tl,
        Mem.iff m m' ->
        Mem.stack(Mem.support m) = hd :: tl ->
        match_stackadt tl (Mem.stack(Mem.support m')) ->
      match_states (Returnstate stk v m)
                   (Returnstate stk v m').

Lemma step_simulation:
  forall S1 t S2, RTL.step fn_stack_requirements ge S1 t S2 ->
  forall S1', match_states S1 S1' ->
  exists S2', step fn_stack_requirements tge S1' t S2' /\ match_states S2 S2'.
Proof.
  intros. inv H; inv H0.
  - econstructor; eauto. split.
    econstructor; eauto.
    econstructor; eauto.
  - econstructor; eauto. split.
    eapply exec_Iop; eauto. rewrite <- genv_eq.
    eapply eval_op_memiff; eauto.
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
  - exploit Mem.free_parallel_iff; eauto.
    intros (m2' & H5' & IFF').
    rewrite <- (Mem.support_free _ _ _ _ _ H5) in H13.
    rewrite <- (Mem.support_free _ _ _ _ _ H5') in H13.
    inv H13.  congruence.
    assert ({m3':mem|Mem.pop_stage m2'= Some m3'}).
      apply Mem.nonempty_pop_stage. congruence.
    destruct X as [m3' POP].
    apply Mem.stack_pop_stage in POP as STKm2'.
    destruct STKm2' as [hd STKm2'].
    econstructor; eauto. split.
    rewrite <- genv_eq.
    eapply exec_Itailcall; eauto.
    econstructor; eauto.
    eapply Mem.pop_stage_right_iff; eauto.
    rewrite STKm2' in H0. inv H0. auto.
  - exploit Mem.push_stage_left_iff; eauto. intro.
    exploit external_call_mem_iff; eauto. intros (m'1 & EXT &IFF').
    econstructor; eauto. split.
    rewrite <- genv_eq.
    econstructor; eauto.
    eapply eval_builtin_args_memiff; eauto.
    econstructor; eauto.
    eapply Mem.pop_stage_left_iff; eauto.
    rewrite <- (external_call_mem_stackeq _ _ _ _ _ _ _ EXT).
    apply Mem.stack_pop_stage in H4. destruct H4.
    rewrite <- (external_call_mem_stackeq _ _ _ _ _ _ _ H3) in H0.
    simpl in H0. inv H0. auto.
  - econstructor; eauto. split.
    rewrite <- genv_eq.
    eapply exec_Icond; eauto.
    erewrite eval_cond_memiff; eauto.
    econstructor; eauto.
  - econstructor; eauto. split.
    rewrite <- genv_eq.
    eapply exec_Ijumptable; eauto.
    econstructor; eauto.
  - exploit Mem.free_parallel_iff; eauto.
    intros (m'1 & H2' & IFF).
    rewrite <- (Mem.support_free _ _ _ _ _ H2) in H11.
    rewrite <- (Mem.support_free _ _ _ _ _ H2') in H11.
    inv H11.  congruence.
    assert ({m'2:mem|Mem.pop_stage m'1= Some m'2}).
      apply Mem.nonempty_pop_stage. congruence.
    destruct X as [m'2 POP].
    econstructor; eauto. split.
    eapply exec_Ireturn; eauto.
    econstructor; eauto.
    eapply Mem.pop_stage_right_iff; eauto.
    apply Mem.stack_pop_stage in POP. destruct POP.
    rewrite H5 in H0. inv H0. auto.
  - exploit Mem.alloc_parallel_iff; eauto.
    intros (m'1 & H1' & IFF).
    exploit Mem.push_stage_right_iff. apply IFF. intro.
    apply Mem.stack_record_frame in H2 as STK.
    apply Mem.record_frame_size1 in H2 as SIZE. simpl in SIZE.
    destruct STK as (hd' & tl' & STKm' & STKm'').
    assert ({m'2:mem|Mem.record_frame (Mem.push_stage m'1) (Mem.mk_frame sz) = Some m'2}).
      apply Mem.request_record_frame. simpl. congruence.
      simpl.
      rewrite (Mem.support_alloc _ _ _ _ _ H1'). simpl.
      rewrite (Mem.support_alloc _ _ _ _ _ H1) in SIZE. simpl in SIZE.
      apply match_stackadt_size in H10. rewrite H9 in SIZE. simpl in *.
      generalize (Mem.size_of_all_frames_pos hd). lia.
    destruct X as [m'2 RECORD].
    econstructor; eauto. split.
    econstructor; eauto.
    econstructor; eauto.
    eapply Mem.record_frame_safe_iff; eauto.
    apply Mem.stack_record_frame in RECORD as STK.
    destruct STK as (hd''&tl''&STKm'1&STKm'2).
    rewrite STKm'2. simpl in STKm'1. inv STKm'1.
    rewrite STKm''. econstructor. 2:eauto.
    rewrite (Mem.support_alloc _ _ _ _ _ H1').
    rewrite (Mem.support_alloc _ _ _ _ _ H1) in STKm'.
    simpl in STKm'. rewrite STKm' in H9. inv H9.
    simpl. auto.
  - exploit external_call_mem_iff; eauto.
    intros (m2' & H1'& IFF).
    econstructor; eauto. split.
    rewrite <- genv_eq.
    econstructor; eauto.
    econstructor; eauto.
    rewrite <- (external_call_mem_stackeq _ _ _ _ _ _ _ H1). eauto.
    rewrite <- (external_call_mem_stackeq _ _ _ _ _ _ _ H1'). eauto.
  - apply Mem.stack_pop_stage in H1 as H1'. destruct H1'.
    econstructor; eauto. split.
    econstructor; eauto.
    econstructor; eauto.
    eapply Mem.pop_stage_left_iff; eauto.
    rewrite H in H6. inv H6. auto.
Qed.

Lemma transf_initial_states:
  forall S1, RTL.initial_state fn_stack_requirements prog S1 ->
  exists S2, initial_state fn_stack_requirements tprog S2 /\ match_states S1 S2.
Proof.
  intros. inv TRANSL. inv H.
  exists (Callstate nil f nil m0 (fn_stack_requirements (prog_main tprog))).
  split.
  econstructor; eauto.
  econstructor; eauto.
  eapply Mem.push_stage_left_iff. apply Mem.iff_refl.
  simpl. reflexivity.
  apply Genv.init_mem_stack in H0. rewrite H0.
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

(*

Lemma backward_simulation_step:
  forall S1' t S2', step fn_stack_requirements ge S1' t S2' ->
  forall S1, match_states S1 S1' -> safe (RTL.semantics fn_stack_requirements prog) S1 ->
  exists S2, plus (RTL.step fn_stack_requirements) ge S1 t S2 /\ match_states S2 S2'.
Proof.
  intros. inv H; inv H0.
  - econstructor; eauto. split.
    apply plus_one. econstructor; eauto.
    econstructor; eauto.
  - econstructor; eauto. split.
    apply plus_one. eapply RTL.exec_Iop; eauto.
    eapply eval_op_memiff; eauto.
    econstructor; eauto.
  - econstructor; eauto. split. apply plus_one.
    eapply RTL.exec_Iload; eauto.
    erewrite <- Mem.loadv_iff; eauto.
    econstructor; eauto.
  - exploit Mem.storev_iff; eauto. intros [m0' [STOREV IFF]].
    econstructor; eauto. split. apply plus_one.
    eapply RTL.exec_Istore; eauto.
    econstructor; eauto.
    rewrite <- (Mem.support_storev _ _ _ _ _ H4).
    rewrite <- (Mem.support_storev _ _ _ _ _ STOREV).
    auto.
  - econstructor; eauto. split. apply plus_one.
    eapply RTL.exec_Icall; eauto.
    econstructor; eauto.
    eapply Mem.push_stage_right_iff; eauto.
    reflexivity.
  - exploit Mem.free_parallel_iff; eauto. intros (m0' & H6' & IFF').
    apply Mem.stack_pop_stage in H7 as H7'. destruct H7'.
    inv H14.
    rewrite <- (Mem.support_free _ _ _ _ _ H6) in H8.
    apply Mem.pop_stage_nonempty in H7. rewrite  H8 in H7.
    congruence.
    econstructor; eauto. split. apply plus_one.
    eapply RTL.exec_Itailcall; eauto.
    econstructor. eauto.
    eapply Mem.iff_trans. eapply Mem.iff_comm. eapply Mem.pop_stage_iff; eauto. eauto.
    rewrite (Mem.support_free _ _ _ _ _ H6'). symmetry. eauto.
    rewrite <- (Mem.support_free _ _ _ _ _ H6) in H5.
    rewrite H in H5. inv H5. auto.
  - exploit Mem.push_stage_right_iff; eauto. intros.
    exploit external_call_mem_iff; eauto. intros (m2' & EXTER & IFF').
    assert ({m3':mem|Mem.pop_stage m2' = Some m3'}).
      apply Mem.nonempty_pop_stage.
      rewrite <- (external_call_mem_stackeq _ _ _ _ _ _ _ EXTER).
      simpl. congruence.
    destruct X as [m3' POP].
    econstructor; eauto. split. apply plus_one.
    econstructor; eauto.
    eapply eval_builtin_args_memiff; eauto.
    econstructor; eauto.
    eapply Mem.pop_stage_right_iff; eauto.
    apply external_call_mem_stackeq in EXTER.
    apply Mem.stack_pop_stage in POP. destruct POP.
    rewrite <- EXTER in H0. simpl in H0. inv H0.
    apply external_call_mem_stackeq in H4.
    rewrite <- H4. auto.
  - econstructor; eauto. split. apply plus_one.
    eapply RTL.exec_Icond; eauto.
    erewrite eval_cond_memiff; eauto.
    econstructor; eauto.
  - econstructor; eauto. split. apply plus_one.
    eapply RTL.exec_Ijumptable; eauto.
    econstructor; eauto.
  - exploit Mem.free_parallel_iff; eauto. intros (m1 & H3' & IFF').
    apply Mem.stack_pop_stage in H4 as H4'. destruct H4'.
    rewrite <- (Mem.support_free _ _ _ _ _ H3) in H12.
    rewrite H in H12. inv H12.
    econstructor; eauto. split. apply plus_one.
    eapply RTL.exec_Ireturn; eauto.
    econstructor; eauto.
    eapply Mem.iff_trans. eapply Mem.iff_comm. eapply Mem.pop_stage_iff; eauto. eauto.
    rewrite (Mem.support_free _ _ _ _ _ H3'). eauto.
  - red in H1. generalize (H1 (Callstate s (Internal f) args m0 sz)). intros.
    exploit H. apply star_refl. intros [Sf|Sf].
    + destruct Sf as [r Sf]. inv Sf.
    + destruct Sf as (E & s'' & STEP).
      exists s''. split. apply plus_one. simpl in STEP. unfold ge.
      inv STEP. econstructor. eauto. eauto.
      inv STEP.
      exploit Mem.alloc_parallel_iff; eauto.
      intros (m1 & ALLOC & EXT).
      rewrite H13 in ALLOC. inv ALLOC.
      eapply match_regular_states.
      eapply Mem.record_frame_safe_iff. 2: eauto. 2: eauto.
      eapply Mem.iff_trans. eapply Mem.iff_comm.
      eapply Mem.push_stage_iff. eauto.
      apply Mem.stack_record_frame in H3 as STK.
      destruct STK as (hd'&tl'&STKpm'&STKm'').
      apply Mem.stack_record_frame in H14 as STK.
      destruct STK as (hd''&tl''&STKm1&STKm''0).
      rewrite STKm'',STKm''0.
      rewrite (Mem.support_alloc _ _ _ _ _ H13) in STKm1. simpl in STKm1.
      rewrite STKm1 in H10. inv H10. simpl. simpl in STKpm'.
      inv STKpm'.
      econstructor.
      rewrite (Mem.support_alloc _ _ _ _ _ H2). simpl. auto.
      eauto.
  - exploit external_call_mem_iff; eauto. intros (m1 & H2' & IFF').
    econstructor; eauto. split. apply plus_one.
    econstructor; eauto.
    econstructor; eauto.
    erewrite <- external_call_mem_stackeq; eauto.
    erewrite <- external_call_mem_stackeq; eauto.
  - assert ({m1:mem|Mem.pop_stage m0 = Some m1}).
      apply Mem.nonempty_pop_stage. congruence.
    destruct X as [m1 POP].
    econstructor; eauto. split. apply plus_one.
    econstructor; eauto.
    econstructor; eauto.
    eapply Mem.pop_stage_right_iff; eauto.
    apply Mem.stack_pop_stage in POP.
    destruct POP. rewrite H in H6. inv H6.
    auto.
Qed.

Definition initial_states_exist:
  forall s1, RTL.initial_state fn_stack_requirements prog s1 ->
             exists s2, initial_state fn_stack_requirements prog s2.
Proof.
  intros. inv TRANSL. inv H.
  exists (Callstate nil f nil m0 (fn_stack_requirements (prog_main tprog))).
  econstructor; eauto.
Qed.

Definition match_initial_states:
  forall s1 s2, RTL.initial_state fn_stack_requirements prog s1 ->
                initial_state fn_stack_requirements tprog s2 ->
  exists s1', RTL.initial_state fn_stack_requirements prog s1' /\ match_states s1' s2.
Proof.
  intros. exists s1. split. auto.
  inv H. inv H0.
  rewrite prog_eq in *.    subst ge0. subst ge1.
  rewrite prog_eq in *.
  rewrite H2 in H5. inv H5.
  rewrite H3 in H6. inv H6.
  rewrite H1 in H. inv H.
  eapply match_callstates; eauto.
  eapply Mem.push_stage_iff; eauto.
  simpl. eauto.
  apply Genv.init_mem_stack in H1. rewrite H1.
  constructor.
Qed.

Definition match_final_states:
  forall s1 s2 r,
  match_states s1 s2 -> final_state s2 r -> RTL.final_state s1 r.
Proof.
  intros. inv H0. inv H. constructor.
Qed.

Check safe.
Definition progress:
  forall s1 s2,
  match_states s1 s2 -> safe (RTL.semantics fn_stack_requirements prog) s1 ->
  (exists r, RTL.final_state s2 r) \/
  (exists t, exists s2', (step fn_stack_requirements) tge s2 t s2').
Proof.
  intros. exploit H0. apply star_refl. intros [FIN | [t [S' STEP]]].
  (* 1. Finished. *)
  left. destruct FIN as [r FIN].
  inv FIN. inv H. exists r. constructor.
  right. remember STEP . destruct s.
  - inv H. eexists. eexists. eapply exec_Inop; eauto.
  - inv H. eexists. eexists.
    eapply exec_Iop; eauto.
    rewrite <- genv_eq. unfold ge.
    eapply eval_op_memiff; eauto. apply Mem.iff_comm; auto.
  - inv H. eexists. eexists.
    eapply exec_Iload; eauto.
    rewrite <- genv_eq. unfold ge. eauto.
    erewrite Mem.loadv_iff; eauto.
  - inv H. apply Mem.iff_comm in H8.
    exploit Mem.storev_iff; eauto. intros (m'1 & A & B).
    eexists. eexists.
    eapply exec_Istore; eauto.
    rewrite <- genv_eq. unfold ge. eauto.
  - inv H. eexists. eexists.
    eapply exec_Icall; eauto.
    rewrite <- genv_eq. unfold ge. eauto.
    rewrite <- genv_eq. unfold ge. eauto.
  - inversion H.
    apply Mem.iff_comm in H8.
    exploit Mem.free_parallel_iff; eauto.
    intros (m'1 & A & B).
    exploit star_safe. apply star_one. apply STEP. auto. apply star_refl.
    intros [FIN | [t [S'' STEP']]].
    + destruct FIN as [r' FIN]. inv FIN.
    + remember STEP'. clear Heqs0. inv s0.
      * assert ({m''1:mem|Mem.pop_stage m'1 = Some m''1}).
        apply Mem.nonempty_pop_stage.
        apply Mem.record_frame_nonempty in H18.
        rewrite (Mem.support_free _ _ _ _ _ A).
        rewrite <- (Mem.support_free _ _ _ _ _ e2) in H9.
        apply Mem.support_alloc in H17. rewrite H17 in H18.
        simpl in H18.
        apply match_stackadt_nonempty in H9.
        intro. apply H18. apply H9. auto.
        destruct X as [m''1 POP].
        eexists. eexists.
        eapply exec_Itailcall; eauto.
        rewrite <- genv_eq. unfold ge. eauto.
        rewrite <- genv_eq. unfold ge. eauto.
      * 
        rewrite <- genv_eq. unfold ge. eauto.
  -     rewrite <- genv_eq. unfold ge. eauto.
    
    
  (* 2. Expression step. *)
  assert (exists t, exists S', estep S t S').
    inv H0.
    (* lred *)
    eapply can_estep; eauto. inv H2; auto.
    (* rred *)
    eapply can_estep; eauto. inv H2; auto. inv H1; auto.
    (* callred *)
    eapply can_estep; eauto. inv H2; auto. inv H1; auto.
    (* stuck *)
    exploit (H Stuckstate). apply star_one. left. econstructor; eauto.
    intros [[r F] | [t [S' R]]]. inv F. inv R. inv H0. inv H0.
  destruct H1 as [t' [S'' ESTEP]].
  exists t'; exists S''; left; auto.
  (* 3. Other step. *)
  exists t; exists S'; right; auto.

  intros.

  red in H0. generalize (H0 s1). intros.

    exploit H1. apply star_refl. intros [Sf|Sf].
    + destruct Sf as [r Sf]. inv Sf.
      left. exists r. inv H. constructor.
    + destruct Sf as (E & s'' & STEP).
      right.
      destruct STEP; inv H.
      - eexist. eexist. eapply exec_Inop.
      

End PRESERVATION.



*)
