Require Import Coqlib Maps.
Require Import AST Linking.
Require Import Values Memory Globalenvs Events Smallstep.
Require Import Op Registers.
Require Import Integers.
Require Import Floats.
Require Import Asm RealAsm RealAsmRegs.

(*
Definition transf_program (p: program) : program := p.

Definition match_prog (p :program) (tp:program):= p = tp.

Lemma transf_program_match:
  forall p, match_prog p (transf_program p).
Proof.
  intros. reflexivity.
Qed.
*)
Section PRESERVATION.

Variables prog: program.
Let ge := Genv.globalenv prog.

(*Lemma prog_eq : prog = tprog.
Proof. auto. Qed.

Lemma genv_eq : ge = tge.
Proof.
  unfold match_prog in TRANSL. unfold ge.
  unfold tge. congruence.
Qed.
*)
Variable instr_size_1 : instruction -> Z.
Variable instr_size_2 : instruction -> Z.

Hypothesis instr_size_1_repr : forall i, 0 <= instr_size_1 i <= Ptrofs.max_unsigned.
Hypothesis instr_size_1_positive :forall i, 0 < instr_size_1 i.
Hypothesis instr_size_2_repr : forall i, 0 <= instr_size_2 i <= Ptrofs.max_unsigned.
Hypothesis instr_size_2_positive :forall i, 0 < instr_size_2 i.

(*
Fixpoint transf_codeofs' (c:code) (ofs1 ofs2 : Z) : Z :=
  if (zeq ofs1 0) then ofs2 else
  match c with
    | nil => 0
    | i :: il => transf_codeofs' il (ofs1 - instr_size_1 i) (ofs2+ instr_size_2 i)
  end.

Definition transf_codeofs (c:code) (ofs : ptrofs) : ptrofs :=
  Ptrofs.repr (transf_codeofs' c (Ptrofs.unsigned ofs) 0 ).
*)

Lemma code_size_positive: forall (is: instruction -> Z) (c:code),
    (forall i, 0 < is i) -> 0 <= code_size is c .
Proof.
  intros. induction c.
  simpl. lia.
  simpl. generalize (H a). lia.
Qed.

Definition match_codeofs (c : code) (ofs1 ofs2 : Z) : Prop :=
    exists a b, c = a ++ b /\
    ofs1 = code_size instr_size_1 a /\
    ofs2 = code_size instr_size_2 a.

Lemma transf_find_instr: forall c ofs1 ofs2 i,
    match_codeofs c ofs1 ofs2 ->
    find_instr instr_size_1 ofs1 c = Some i ->
    find_instr instr_size_2 ofs2 c = Some i.
Proof.
  induction c.
  - intros. inv H. inv H0.
  - intros. inv H.
    destruct H1 as (b & H1 & H2 & H3).
    destruct x.
    + inv H1. inv H. simpl. inv H0. auto.
    + inv H1. simpl. destr.
      generalize (instr_size_2_positive i0).
      generalize (code_size_positive instr_size_2 x instr_size_2_positive). extlia.
      simpl in H0. destr_in H0.
      generalize (instr_size_1_positive i0).
      generalize (code_size_positive instr_size_1 x instr_size_1_positive). extlia.
      eapply IHc; eauto. econstructor.
      exists b. split. eauto. split. lia. lia.
Qed.

Inductive match_pc : block -> Z -> Z -> Prop :=
  |match_pc_gen: forall b f ofs1 ofs2,
    Genv.find_funct_ptr ge b = Some (Internal f) ->
    match_codeofs (fn_code f) ofs1 ofs2 ->
    match_pc b ofs1 ofs2.

Inductive match_value: val -> val -> Prop :=
  |match_int :  forall i, match_value (Vint i) (Vint i)
  |match_long: forall i, match_value (Vlong i) (Vlong i)
  |match_float: forall i, match_value (Vfloat i) (Vfloat i)
  |match_single: forall i, match_value (Vsingle i) (Vsingle i)
  |match_ptr_pc: forall b ofs1 ofs2,
      match_pc b ofs1 ofs2 -> match_value (Vptr b (Ptrofs.repr ofs1)) (Vptr b (Ptrofs.repr ofs2))
  |match_ptr_gdef: forall id, match_value (Vptr (Global id) Ptrofs.zero) (Vptr (Global id) Ptrofs.zero)
  |match_ptr_s : forall b o, is_stack b -> match_value (Vptr b o) (Vptr b o)
  |match_undef: match_value Vundef Vundef.

Inductive match_vallist : list val -> list val -> Prop :=
  match_vallist_nil : match_vallist nil nil
 |match_vallist_cons : forall v1 v2 vl1 vl2,
     match_value v1 v2 ->
     match_vallist vl1 vl2 ->
     match_vallist (v1::vl1) (v2::vl2).

Lemma match_Vnullptr : forall v,
    match_value Vnullptr v -> v = Vnullptr.
Proof.
  intros. unfold Vnullptr in *.
  destruct (Archi.ptr64); inv H; auto.
Qed.

Inductive match_memval : memval -> memval -> Prop :=
  match_memval_byte : forall n : byte, match_memval (Byte n) (Byte n)
| match_memval_frag : forall (v1 v2 : val) (q: quantity) (n:nat),
                      match_value v1 v2 ->
                      match_memval (Fragment v1 q n) (Fragment v2 q n)
| match_memval_undef : match_memval Undef Undef.

(* Mem.iff Mem.mem_inj inject *)
Inductive match_mem : mem -> mem -> Prop :=
  |match_mem_gen: forall m1 m2,
    Mem.support m1 = Mem.support m2 ->
    Mem.mem_access m1 = Mem.mem_access m2 ->
    (*mem_content*)
    (forall (b:block) (ofs:Z) , match_memval
                (ZMap.get ofs (NMap.get _ b (Mem.mem_contents m1)))
                (ZMap.get ofs (NMap.get _ b (Mem.mem_contents m2)))
    ) ->
    match_mem m1 m2.

Definition match_rs (rs1 rs2:regset) : Prop :=
  forall r, match_value (rs1 # r) (rs2 # r).

Inductive match_states: state -> state -> Prop :=
  |match_states_gen: forall rs1 rs2 m1 m2,
      match_rs rs1 rs2 ->
      match_mem m1 m2 ->
      match_states (State rs1 m1) (State rs2 m2).


Lemma eval_builtin_args_match:
  forall rs rs' sp m m' args vargs,
    eval_builtin_args ge rs sp m args vargs ->
    match_rs rs rs' ->
    match_mem m m' ->
    exists vargs',
      eval_builtin_args ge rs' sp m args vargs' /\
      match_vallist vargs vargs'.
Admitted.

Lemma step_simulation:
  forall S1 t S2, step instr_size_1 ge S1 t S2 ->
  forall S1', match_states S1 S1' ->
  exists S2', step instr_size_2 ge S1' t S2' /\ match_states S2 S2'.
Proof.
  intros. inv H; inv H0.
  - admit.
    (*
      econstructor; eauto. split.
      econstructor; eauto.                                                                                *)
  - econstructor; eauto. split.
    generalize (H7 PC). intro H8.
    rewrite H1 in H8. inv H8.
    econstructor. eauto. eauto.
    rewrite Ptrofs.unsigned_repr in H3. rewrite Ptrofs.unsigned_repr.
    eapply transf_find_instr; eauto. inv H0. rewrite H2 in H. inv H. auto.
    admit. admit.



 (* wf? codesize < maxunsigned*)
    exploit eval_builtin_args_match; eauto.
    intros [vargs' [A B]]. apply A.
    admit. (* eval_builtin *)
    admit. (* external_call *)
    admit.
    admit. (*wrong*)
    admit. (*wrong*)
    admit.
  - econstructor; eauto. split.
    eapply exec_step_external.
    rewrite H1 in H7. inv H7. inv H0.
    congruence. auto. auto. eauto.
    rewrite <- H6. admit.
    congruence. congruence.
    rewrite <- H6. congruence. congruence. congruence.
    admit. rewrite <- H6. congruence. congruence. congruence.
    admit. admit. reflexivity.
    admit.

Admitted.

Lemma init_match_mem : forall m,
    Genv.init_mem prog = Some m -> match_mem m m.
Proof.
  Admitted.

Lemma alloc_match_mem : forall m1 m2 lo hi b m1',
   match_mem m1 m2 ->
   Mem.alloc m1 lo hi = (m1', b) ->
   exists m2',
   Mem.alloc m2 lo hi = (m2', b) /\
   match_mem m1' m2'.
Proof.
  intros.
  caseEq (Mem.alloc m2 lo hi). intros.
  exists m. split.
  apply Mem.alloc_result in H0.
  apply Mem.alloc_result in H1. inv H. unfold Mem.nextblock. rewrite H2. auto.
  inv H. constructor; auto.
  + admit.
  + admit.
  + Search Mem.alloc.
    Mem.extends'
  Search Mem.alloc.
Admitted.

 Lemma storev_match_mem:
   forall m1 m2 addr v1 v2 m1',
     match_mem m1 m2 -> match_value v1 v2 ->
     Mem.storev Mptr m1 addr v1 = Some m1' ->
     exists m2',
       Mem.storev Mptr m2 addr v2 = Some m2' /\
         match_mem m1' m2'.
Admitted.

Lemma transf_initial_states:
  forall S1, initial_state prog S1 ->
  exists S2, initial_state prog S2 /\ match_states S1 S2.
Proof.
  intros. exists S1. split. auto. inv H.
  econstructor; eauto.
  unfold rs0. real_simpl_regs.
  apply Genv.genv_vars_eq in H3. rewrite H3.
  eapply match_ptr_gdef.
  unfold rs0. real_simpl_regs. constructor.
  exploit init_match_mem; eauto. intro.
  exploit alloc_match_mem; eauto. intros [m3[ A B]].
  rewrite A in H1. inv H1. unfold Vnullptr in H2.
  destruct (Archi.ptr64).
  exploit storev_match_mem; eauto. econstructor.
  intros [m4 [C D]]. rewrite C in H2. inv H2. auto.
  exploit storev_match_mem; eauto. econstructor.
  intros [m4 [C D]]. rewrite C in H2. inv H2. auto.
Qed.

Lemma transf_final_states:
  forall S1 S2 r, match_states S1 S2 -> final_state S1 r -> final_state S2 r.
Proof.
  intros. inv H0. inv H. constructor.
  rewrite H1 in H5. unfold Vnullptr in *.
  destruct (Archi.ptr64); inv H5; eauto.
  rewrite <- H4. auto. congruence. congruence.
Qed.


Theorem transf_program_correct:
  forward_simulation (semantics instr_size_1 prog)
                     (semantics instr_size_2 prog).
Proof.
  eapply forward_simulation_step.
  reflexivity.
  eexact transf_initial_states.
  eexact transf_final_states.
  exact step_simulation.
Qed.

End PRESERVATION.

