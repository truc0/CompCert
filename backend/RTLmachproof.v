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
(*
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
*)
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



(*
Lemma valid_pointer_memiff : forall m1 m2 b ofs,
    mem_iff m1 m2 -> Mem.valid_pointer m1 b ofs = true <-> Mem.valid_pointer m2 b ofs = true.
Proof. intros. inv H.
       transitivity (Mem.perm m1 b ofs Cur Nonempty).
       apply Mem.valid_pointer_nonempty_perm.
       transitivity (Mem.perm m2 b ofs Cur Nonempty).
       unfold Mem.perm. rewrite perm_iff0. reflexivity.
       symmetry.        apply Mem.valid_pointer_nonempty_perm.
Qed.

Lemma valid_pointer_memiff1 : forall m1 m2 b ofs,
    mem_iff m1 m2 -> Mem.valid_pointer m1 b ofs = Mem.valid_pointer m2 b ofs.
Proof. intros.
       destruct (Mem.valid_pointer m1 b ofs) eqn:vp1.
       generalize (valid_pointer_memiff _ _ b ofs H). intros.
       apply H0 in vp1. rewrite vp1. auto.
       destruct (Mem.valid_pointer m2 b ofs) eqn:vp2.
       eapply valid_pointer_memiff in vp2; eauto. auto.
Qed.

Lemma eval_cond_memiff:
    forall  (m m0 : mem) (cond : condition) (vl : list val),
      mem_iff m m0 ->
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
    (H6 : mem_iff m m0), eval_operation ge sp op vl m0 = Some v.
Proof.
  intros sp m m0 op vl v H3 H6.
  unfold eval_operation in *. destruct op; auto.
  erewrite eval_cond_memiff; eauto.
  repeat destr.
  erewrite eval_cond_memiff; eauto.
Qed.

Lemma eval_builtin_args_memiff:
  forall (sp : val) (rs : Regmap.t val) (m m0 : mem) (args : list (builtin_arg reg))
    (vargs : list val) (H3 : eval_builtin_args ge (fun r : positive => rs # r) sp m args vargs)
    (H7 : mem_iff m m0),
    eval_builtin_args ge (fun r : positive => rs # r) sp m0 args vargs.
Proof.
  intros sp rs m m0 args vargs H3 H7. Admitted. (*loadv_memiff needed*)

Inductive match_states: RTL.state -> RTL.state -> Prop :=
  | match_regular_states: forall stk f sp pc rs m m',
        mem_iff m' m ->
        match_stackadt (Mem.stack(Mem.support m)) (Mem.stack(Mem.support m'))->
      match_states (State stk f sp pc rs m)
                   (State stk f sp pc rs m')
  | match_callstates: forall stk f args m sz m' hd tl,
        mem_iff m' m ->
        Mem.stack(Mem.support m) = hd :: tl ->
        match_stackadt tl (Mem.stack(Mem.support m')) ->
      match_states (Callstate stk f args m sz)
                   (Callstate stk f args m' sz)
  | match_returnstates: forall stk v  m m' hd tl,
        mem_iff m' m ->
        Mem.stack(Mem.support m) = hd :: tl ->
        match_stackadt tl (Mem.stack(Mem.support m')) ->
      match_states (Returnstate stk v m)
                   (Returnstate stk v m').

Lemma storev_memiff:
  forall (rs : Regmap.t val) (m m0 : mem) (chunk : memory_chunk) (src : reg)
    (a : val) (m' : mem) (H4 : Mem.storev chunk m a rs # src = Some m')
    (H7 : mem_iff m m0),
    exists m'0,
    Mem.storev chunk m0 a rs # src = Some m'0/\mem_iff m' m'0.
Proof.
  intros rs m m0 chunk src a m' H4 H7. Admitted.

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
    eapply loadv_memiff; eauto.
    econstructor; eauto.
  - exploit storev_memiff; eauto. intros [m0' [STOREV IFF]].
    econstructor; eauto. split. apply plus_one.
    eapply RTL.exec_Istore; eauto.
    econstructor; eauto.
    rewrite <- (Mem.support_storev _ _ _ _ _ H4).
    rewrite <- (Mem.support_storev _ _ _ _ _ STOREV).
    auto.
  - econstructor; eauto. split. apply plus_one.
    eapply RTL.exec_Icall; eauto.
    econstructor; eauto. (*push_left*)
    admit. reflexivity.
  - econstructor; eauto. split. apply plus_one.
    eapply RTL.exec_Itailcall; eauto.
    admit. (*free parallel pop_left*)
    econstructor; eauto. admit. admit. admit.
(*
    destruct H7 as [hd H7].
    rewrite <- (Mem.support_free _ _ _ _ _ FREE) in H16.
    rewrite <- (Mem.support_free _ _ _ _ _ H6) in H16.
    rewrite S2 in H16. rewrite H7 in H16. inv H16.
    auto. *)
  - (*push right*)
     econstructor; eauto. split. apply plus_one.
     econstructor; eauto.
*)     
  

Inductive match_stackframes: list stackframe -> list stackframe -> Prop :=
  | match_stackframes_nil:
      match_stackframes nil nil
  | match_stackframes_normal: forall stk stk' res sp pc rs rs' f,
      match_stackframes stk stk' ->
      regs_lessdef rs rs' ->
      match_stackframes
        (Stackframe res f sp pc rs :: stk)
        (Stackframe res f sp pc rs' :: stk').

Inductive match_states: RTL.state -> RTL.state -> Prop :=
  | match_regular_states: forall stk stk' f sp pc rs rs' m m',
        regs_lessdef rs' rs ->
        Mem.extends' m' m ->
        match_stackframes stk' stk ->
        match_stackadt (Mem.stack(Mem.support m)) (Mem.stack(Mem.support m'))->
      match_states (State stk f sp pc rs m)
                   (State stk' f sp pc rs' m')
  | match_callstates: forall stk stk' f args args' m sz m' hd tl,
        Val.lessdef_list args' args->
        Mem.extends' m' m ->
        match_stackframes stk' stk ->
        Mem.stack(Mem.support m) = hd :: tl ->
        match_stackadt tl (Mem.stack(Mem.support m')) ->
      match_states (Callstate stk f args m sz)
                   (Callstate stk' f args' m' sz)
  | match_returnstates: forall stk stk' v v' m m' hd tl,
        Val.lessdef v' v ->
        Mem.extends' m' m ->
        match_stackframes stk' stk ->
        Mem.stack(Mem.support m) = hd :: tl ->
        match_stackadt tl (Mem.stack(Mem.support m')) ->
      match_states (Returnstate stk v m)
                   (Returnstate stk' v' m').


Lemma regs_lessdef_init_regs:
  forall params vl vl',
  Val.lessdef_list vl vl' ->
  regs_lessdef (init_regs vl params) (init_regs vl' params).
Proof.
  induction params; intros.
  simpl. red; intros. rewrite Regmap.gi. constructor.
  simpl. inv H.   red; intros. rewrite Regmap.gi. constructor.
  apply set_reg_lessdef. auto. auto.
Qed.

Lemma backward_simulation_step:
  forall S1' t S2', step fn_stack_requirements ge S1' t S2' ->
  forall S1, match_states S1 S1' -> safe (RTL.semantics fn_stack_requirements prog) S1 ->
  exists S2, plus (RTL.step fn_stack_requirements) ge S1 t S2 /\ match_states S2 S2'.
Proof.
  intros. inv H; inv H0.
  - econstructor; eauto. split.
    apply plus_one. econstructor; eauto.
    econstructor; eauto.
  - assert (Val.lessdef_list (rs##args) (rs0##args)). apply regs_lessdef_regs; auto.
    exploit eval_operation_lessdef; eauto.
    intros [v' [EVAL' VLD]].
    econstructor; eauto. split.
    apply plus_one. eapply RTL.exec_Iop; eauto.
    econstructor; eauto. apply set_reg_lessdef; eauto.
  - assert (Val.lessdef_list (rs##args) (rs0##args)). apply regs_lessdef_regs; auto.
    exploit eval_addressing_lessdef; eauto.
    intros [v' [EVAL' VLD]].
    exploit Mem.loadv_extends'; eauto.
    intros [v'' [LOAD VLD']].
    econstructor; eauto. split. apply plus_one.
    eapply RTL.exec_Iload; eauto.
    econstructor; eauto. intro.
    apply set_reg_lessdef; eauto.
  - assert (Val.lessdef_list (rs##args) (rs0##args)). apply regs_lessdef_regs; auto.
    exploit eval_addressing_lessdef; eauto.
    intros [v' [EVAL' VLD]].
    exploit Mem.storev_extends'; eauto.
    intros [m2' [STORE VLD']].
    econstructor; eauto. split. apply plus_one.
    eapply RTL.exec_Istore; eauto.
    econstructor; eauto.
    rewrite <- (Mem.support_storev _ _ _ _ _ H4).
    rewrite <- (Mem.support_storev _ _ _ _ _ STORE).
    auto.
  - econstructor; eauto. split. apply plus_one.
    eapply RTL.exec_Icall; eauto.
    eapply find_function_id_preserved; eauto.
    eapply find_function_translated; eauto.
    eapply match_callstates; eauto. apply regs_lessdef_regs. auto.
    2: constructor; auto.
    2: constructor; auto.
    {
      inv H12. constructor; simpl; eauto. inv mext_inj.
      constructor; eauto.
    }
  - exploit Mem.free_parallel_extends'; eauto.
    intros [m2' [FREE EXT]].
      destruct (Mem.stack(Mem.support m2')) eqn : S2.
        apply Mem.support_free in FREE. rewrite <- FREE in H16.
        rewrite S2 in H16. inv H16.
        apply Mem.pop_stage_nonempty in H7.
        erewrite Mem.support_free in H7; eauto. congruence.
    econstructor; eauto. split. apply plus_one.
    eapply RTL.exec_Itailcall; eauto.
    eapply find_function_id_preserved; eauto.
    eapply find_function_translated; eauto.
    eapply match_callstates; eauto. apply regs_lessdef_regs. auto.
    eapply Mem.pop_stage_left_extends'; eauto.
    eapply Mem.stack_pop_stage in H7.
    destruct H7 as [hd H7].
    rewrite <- (Mem.support_free _ _ _ _ _ FREE) in H16.
    rewrite <- (Mem.support_free _ _ _ _ _ H6) in H16.
    rewrite S2 in H16. rewrite H7 in H16. inv H16.
    auto.
  - exploit (@eval_builtin_args_lessdef _ ge (fun r => rs#r) (fun r => rs0#r)); eauto.
    intros (vargs' & P & Q).
    assert (Mem.extends' m (Mem.push_stage m0)).
    {
      inv H12. constructor; simpl; eauto. inv mext_inj.
      constructor; eauto.
    }
    exploit external_call_mem_extends'. 2: apply H. all:eauto.
    intros [v' [m'1 [A [B [C D]]]]].
    apply external_call_mem_stackeq in A as A'.
    assert ({m'2:mem|Mem.pop_stage m'1 = Some m'2}).
      apply Mem.nonempty_pop_stage.
      rewrite <- A'. simpl. congruence.
    destruct X as [m'2 POP].
    econstructor; eauto. split. apply plus_one.
    eapply RTL.exec_Ibuiltin; eauto.
    econstructor; eauto. apply set_res_lessdef; auto.
    eapply Mem.pop_stage_right_extends'; eauto.
    erewrite <- (external_call_mem_stackeq _ _ _ _ _ _ _ H4).
    apply Mem.stack_pop_stage in POP. destruct POP as [hd POP].
    rewrite <- A' in POP. simpl in POP. inv POP.
    auto.
  - exists (State stk f sp (if b then ifso else ifnot) rs0 m0); split.
    apply plus_one. eapply RTL.exec_Icond; eauto.
    apply eval_condition_lessdef with (rs##args) m; auto. apply regs_lessdef_regs; auto.
    econstructor; eauto.
  - exists (State stk f sp pc' rs0 m0); split.
    apply plus_one. eapply RTL.exec_Ijumptable; eauto.
    generalize (H9 arg). rewrite H3. intro. inv H. auto.
    econstructor; eauto.
  - exploit Mem.free_parallel_extends'; eauto.
    intros [m2' [FREE EXT]].
    apply Mem.stack_pop_stage in H4 as H4'.
    destruct H4' as [hd H4'].
    rewrite <- (Mem.support_free _ _ _ _ _ H3) in H14.
    rewrite H4' in H14.
    inv H14.
    exists (Returnstate stk0 (regmap_optget or Vundef rs0) m2'); split.
    apply plus_one. eapply RTL.exec_Ireturn; eauto.
    econstructor; eauto.
    destruct or; simpl. apply H9. constructor.
    eapply Mem.pop_stage_left_extends'; eauto.
    rewrite (Mem.support_free _ _ _ _ _ FREE). inv H. reflexivity.
  - red in H1. generalize (H1 (Callstate stk0 (Internal f )args0 m0 sz)). intros.
    exploit H. apply star_refl. intros [Sf|Sf].
    + destruct Sf as [r Sf]. inv Sf.
    + destruct Sf as (E & s'' & STEP).
      exists s''. split. apply plus_one. simpl in STEP. unfold ge.
      inv STEP. econstructor. eauto. eauto.
      inv STEP.
      exploit Mem.alloc_extends'; eauto.
      instantiate (1 := 0). lia.
      instantiate (1 := fn_stacksize f). lia.
      intros (m'1 & ALLOC & EXT).
      rewrite H15 in ALLOC. inv ALLOC.
      eapply match_regular_states.
      apply regs_lessdef_init_regs. auto.
      eapply Mem.push_stage_left_extends' in EXT; eauto.
    exploit Mem.record_frame_safe_extends'; eauto. auto.
    apply Mem.stack_record_frame in H3 as STK1.
    apply Mem.stack_record_frame in H16 as STK2.
    destruct STK2 as (hd2 & tl2 & STKm'1 & STKm''0).
    rewrite (Mem.support_alloc _ _ _ _ _ H15) in STKm'1.
    simpl in STKm'1. rewrite H12 in STKm'1. inv STKm'1.
    rewrite STKm''0.
    destruct STK1 as (hd1 & tl1 & STKpm' & STKm'').
    simpl in STKpm'. inv STKpm'. rewrite  STKm''.
    apply Mem.support_alloc in H2. simpl in H2.
    rewrite H2. simpl.
    inv H13.
    * econstructor. constructor. eauto.
    * econstructor. econstructor. eauto. eauto. eauto.
  -  exploit external_call_mem_extends'; eauto.
    intros [v' [m1 [A [B [C D]]]]].
    econstructor. split.
    apply plus_one. econstructor. eauto.
    econstructor; eauto.
    erewrite <- external_call_mem_stackeq; eauto.
    erewrite <- external_call_mem_stackeq; eauto.
  - assert ({m1:mem|Mem.pop_stage m0 = Some m1}).
      apply Mem.nonempty_pop_stage. congruence.
      destruct X as [m1 POP].
    inv H7.
    econstructor. split. apply plus_one.
    eapply RTL.exec_return; eauto.
    econstructor; eauto. apply set_reg_lessdef; auto.
    eapply Mem.pop_stage_right_extends'; eauto.
    destruct (Mem.stack_pop_stage   _ _ POP).
    rewrite H in H8. inv H8. auto.
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
  eapply Mem.push_stage_right_extends'; eauto. apply Mem.extends'_refl.
  constructor. simpl. reflexivity.
  apply Genv.init_mem_stack in H1. rewrite H1.
  constructor.
Qed.

Definition match_final_states:
  forall s1 s2 r,
  match_states s1 s2 -> final_state s2 r -> RTL.final_state s1 r.
Proof.
  intros. inv H0. inv H. inv H6. inv H3. inv H7.
  constructor.
Qed.
Definition progress:
  forall s1 s2,
  match_states s1 s2 -> safe (RTL.semantics fn_stack_requirements prog) s1 ->
  (exists r, RTL.final_state s2 r) \/
  (exists t, exists s2', (step fn_stack_requirements) tge s2 t s2').
Proof.
  Admitted.

End PRESERVATION.



