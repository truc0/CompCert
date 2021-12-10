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

(** Constant propagation over RTL.  This is one of the optimizations
  performed at RTL level.  It proceeds by a standard dataflow analysis
  and the corresponding code rewriting. *)

Require Import Coqlib Maps Integers Floats Lattice Kildall.
Require Import AST Linking Builtins.
Require Compopts Machregs.
Require Import Op Registers RTL.
Require Import Liveness ValueDomain ValueAOp ValueAnalysis.
Require Import ConstpropOp.

(** The code transformation builds on the results of the static analysis
  of values from module [ValueAnalysis].  It proceeds instruction by
  instruction.
- Operators whose arguments are all statically known are turned into
  ``load integer constant'', ``load float constant'' or ``load
  symbol address'' operations.  Likewise for loads whose result can
  be statically predicted.
- Operators for which some but not all arguments are known are subject
  to strength reduction (replacement by cheaper operators) and
  similarly for the addressing modes of load and store instructions.
- Cast operators that have no effect (because their arguments are
  already normalized to the destination type) are removed.
- Conditional branches and multi-way branches are statically resolved
  into [Inop] instructions when possible.
- Other instructions are unchanged.

  In addition, we try to jump over conditionals whose condition can
  be statically resolved based on the abstract state "after" the
  instruction that branches to the conditional.  A typical example is:
<<
          1: x := 0 and goto 2
          2: if (x == 0) goto 3 else goto 4
>>
    where other instructions branch into 2 with different abstract values
    for [x].  We transform this code into:
<<
          1: x := 0 and goto 3
          2: if (x == 0) goto 3 else goto 4
>>
*)

Definition transf_ros (ae: AE.t) (ros: reg + ident) : reg + ident :=
  match ros with
  | inl r =>
      match areg ae r with
      | Ptr(Gl symb ofs) => if Ptrofs.eq ofs Ptrofs.zero then inr _ symb else ros
      | _ => ros
      end
  | inr s => ros
  end.

Fixpoint successor_rec (n: nat) (f: function) (ae: AE.t) (pc: node) : node :=
  match n with
  | O => pc
  | S n' =>
      match f.(fn_code)!pc with
      | Some (Inop s) =>
          successor_rec n' f ae s
      | Some (Icond cond args s1 s2) =>
          match resolve_branch (eval_static_condition cond (aregs ae args)) with
          | Some b => successor_rec n' f ae (if b then s1 else s2)
          | None => pc
          end
      | _ => pc
      end
  end.

Definition num_iter := 10%nat.

Definition successor (f: function) (ae: AE.t) (pc: node) : node :=
  successor_rec num_iter f ae pc.

Fixpoint builtin_arg_reduction (ae: AE.t) (a: builtin_arg reg) :=
  match a with
  | BA r =>
      match areg ae r with
      | I n => BA_int n
      | L n => BA_long n
      | F n => if Compopts.generate_float_constants tt then BA_float n else a
      | FS n => if Compopts.generate_float_constants tt then BA_single n else a
      | _ => a
      end
  | BA_splitlong hi lo =>
      match builtin_arg_reduction ae hi, builtin_arg_reduction ae lo with
      | BA_int nhi, BA_int nlo => BA_long (Int64.ofwords nhi nlo)
      | hi', lo' => BA_splitlong hi' lo'
      end
  | BA_addptr a1 a2 =>
      BA_addptr (builtin_arg_reduction ae a1) (builtin_arg_reduction ae a2)
  | _ => a
  end.

Definition builtin_arg_strength_reduction
      (ae: AE.t) (a: builtin_arg reg) (c: builtin_arg_constraint) :=
  let a' := builtin_arg_reduction ae a in
  if builtin_arg_ok a' c then a' else a.

Fixpoint builtin_args_strength_reduction
      (ae: AE.t) (al: list (builtin_arg reg)) (cl: list builtin_arg_constraint) :=
  match al with
  | nil => nil
  | a :: al =>
      builtin_arg_strength_reduction ae a (List.hd OK_default cl)
      :: builtin_args_strength_reduction ae al (List.tl cl)
  end.

(** For debug annotations, add constant values to the original info
    instead of replacing it. *)

Fixpoint debug_strength_reduction (ae: AE.t) (al: list (builtin_arg reg)) :=
  match al with
  | nil => nil
  | a :: al =>
      let a' := builtin_arg_reduction ae a in
      let al' := a :: debug_strength_reduction ae al in
      match a, a' with
      | BA _, (BA_int _ | BA_long _ | BA_float _ | BA_single _) => a' :: al'
      | _, _ => al'
      end
  end.

Definition builtin_strength_reduction
             (ae: AE.t) (ef: external_function) (al: list (builtin_arg reg)) :=
  match ef with
  | EF_debug _ _ _ => debug_strength_reduction ae al
  | _ => builtin_args_strength_reduction ae al (Machregs.builtin_constraints ef)
  end.

(*
Definition transf_builtin
             (ae: AE.t) (am: amem) (rm: romem)
             (ef: external_function)
             (args: list (builtin_arg reg)) (res: builtin_res reg) (s: node) :=
  let dfl := Ibuiltin ef (builtin_strength_reduction ae ef args) res s in
  match ef, res with
  | EF_builtin name sg, BR rd =>
      match lookup_builtin_function name sg with
      | Some bf => 
          match eval_static_builtin_function ae am rm bf args with
          | Some a =>
              match const_for_result a with
              | Some cop => Iop cop nil rd s
              | None => dfl
              end
          | None => dfl
          end
      | None => dfl
      end
  | _, _ => dfl
  end.
*)

Definition transf_instr (f: function) (an: PMap.t VA.t) (rm: romem)
                        (pc: node) (instr: instruction) :=
  match an!!pc with
  | VA.Bot =>
      instr
  | VA.State ae am =>
      match instr with
      | Iop op args res s =>
          let aargs := aregs ae args in
          let a := eval_static_operation op aargs in
          let s' := successor f (AE.set res a ae) s in
          match const_for_result a with
          | Some cop =>
              Iop cop nil res s'
          | None =>
              let (op', args') := op_strength_reduction op args aargs in
              Iop op' args' res s'
          end
      | Iload chunk addr args dst s =>
          let aargs := aregs ae args in
          let a := ValueDomain.loadv chunk rm am (eval_static_addressing addr aargs) in
          match const_for_result a with
          | Some cop =>
              Iop cop nil dst s
          | None =>
              let (addr', args') := addr_strength_reduction addr args aargs in
              Iload chunk addr' args' dst s
          end
      | Istore chunk addr args src s =>
          let aargs := aregs ae args in
          let (addr', args') := addr_strength_reduction addr args aargs in
          Istore chunk addr' args' src s
      | Icall sig ros args res s =>
          Icall sig (transf_ros ae ros) args res s
      | Itailcall sig ros args =>
          Itailcall sig (transf_ros ae ros) args
      | Ibuiltin ef args res s =>
          let dfl := Ibuiltin ef (builtin_strength_reduction ae ef args) res s in
          match ef, res with
          | EF_builtin name sg, BR rd =>
              match lookup_builtin_function name sg with
              | Some bf => 
                  match eval_static_builtin_function ae am rm bf args with
                  | Some a =>
                      match const_for_result a with
                      | Some cop => Iop cop nil rd s
                      | None => dfl
                      end
                 | None => dfl
                 end
             | None => dfl
             end
          | _, _ => dfl
          end
      | Icond cond args s1 s2 =>
          let aargs := aregs ae args in
          match resolve_branch (eval_static_condition cond aargs) with
          | Some b =>
              if b then Inop s1 else Inop s2
          | None =>
              let (cond', args') := cond_strength_reduction cond args aargs in
              Icond cond' args' s1 s2
          end
      | Ijumptable arg tbl =>
          match areg ae arg with
          | I n =>
              match list_nth_z tbl (Int.unsigned n) with
              | Some s => Inop s
              | None => instr
              end
          | _ => instr
          end
      | _ =>
          instr
      end
  end.

Definition transf_function (rm: romem) (f: function) : function :=
  let an := ValueAnalysis.analyze rm f in
  mkfunction
    f.(fn_sig)
    f.(fn_params)
    f.(fn_stacksize)
    (PTree.map (transf_instr f an rm) f.(fn_code))
    f.(fn_entrypoint).

Definition transf_fundef (rm: romem) (fd: fundef) : fundef :=
  AST.transf_fundef (transf_function rm) fd.

Definition transf_program (p: program) : program :=
  let rm := romem_for p in
  transform_program (transf_fundef rm) p.


(** *Abstract Value Alpha Renaming *)

Definition alpha_rename_aptr (a:permutation) (p:aptr) :=
  match p with
  | Gl id ofs => Gl (alpha_rename a id) ofs
  | Glo id => Glo (alpha_rename a id)
  | _ => p
  end.

Program Instance Alpha_aptr: Alpha aptr :=
  { alpha_rename := alpha_rename_aptr }.
Next Obligation.
  destruct p;simpl;auto.
Defined.
Next Obligation.
  destruct p1;auto;simpl;
  erewrite alpha_rename_sym;auto.
Defined.
Next Obligation.
  destruct p1;auto.
Defined.

Global Opaque Alpha_aptr.

Definition alpha_rename_aval (a:permutation) (v:aval) :=
  match v with
  | Uns p n => Uns (alpha_rename a p) n
  | Sgn p n => Sgn (alpha_rename a p) n
  | Ptr p => Ptr (alpha_rename a p)
  | Ifptr p => Ifptr (alpha_rename a p)
  | _ => v
  end.

Program Instance Alpha_aval: Alpha aval :=
  { alpha_rename := alpha_rename_aval }.
Next Obligation.
  destruct p;simpl;auto;
  erewrite alpha_rename_refl;auto.
Defined.
Next Obligation.
  destruct p1;auto;simpl;
  erewrite alpha_rename_sym;auto.
Defined.
Next Obligation.
  destruct p1;auto;simpl;
  erewrite alpha_rename_trans;auto.
Defined.

Global Opaque Alpha_aval.

Definition alpha_rename_acontent (a:permutation) (c:acontent) :=
  match c with
  | ACval chunk v => ACval chunk (alpha_rename a v)
  end.

Program Instance Alpha_acontent: Alpha acontent :=
  { alpha_rename := alpha_rename_acontent }.
Next Obligation.
  destruct p;simpl;auto;
  erewrite alpha_rename_refl;auto.
Defined.
Next Obligation.
  destruct p1;auto;simpl;
  erewrite alpha_rename_sym;auto.
Defined.
Next Obligation.
  destruct p1;auto;simpl;
  erewrite alpha_rename_trans;auto.
Defined.

Global Opaque Alpha_acontent.

Inductive match_option_alpha {A:Type} {ALA:Alpha A} (a:permutation) :option A -> option A -> Prop :=  
| match_none_alpha : match_option_alpha a None None
| match_some_alpha : forall a1 a2, a1 = alpha_rename a a2 ->
                              match_option_alpha a (Some a1) (Some a2).

Definition match_ablock_alpha a b1 b2 :=
  (forall n ,match_option_alpha a (ZTree.get n b1.(ab_contents)) (ZTree.get n b2.(ab_contents)))
  /\ b1.(ab_summary) = alpha_rename a b2.(ab_summary).


Inductive  match_option_ablock_alpha a  :option ablock -> option ablock -> Prop :=
 |match_none_ablock_alpha: match_option_ablock_alpha a None None
 |match_some_ablock_alpha : forall b1 b2,
     match_ablock_alpha a b1 b2 ->
    match_option_ablock_alpha a (Some b1) (Some b2).

Definition  match_romem_alpha a (rm1 rm2: romem) :  Prop :=
  forall pc,
    match_option_ablock_alpha a (rm1 ! pc) (rm2 ! pc).

  
Lemma romem_for_alpha :forall a ctx,
    match_romem_alpha a (romem_for (alpha_rename a ctx)) (romem_for ctx).
  intros.
  Admitted.

Inductive  match_aenv_alpha (a:permutation) : aenv -> aenv -> Prop :=
| match_aenv_Bot_alpha : match_aenv_alpha a AE.Bot AE.Bot
| match_aenv_Top_except_alpha: forall pt1 pt2 pc,
    match_option_alpha a (pt1 ! pc) (pt2 ! pc) ->
    match_aenv_alpha a (AE.Top_except pt1) (AE.Top_except pt2).

Definition match_amem_alpha (a:permutation) am1 am2 : Prop :=
  match_ablock_alpha a am1.(am_stack) am2.(am_stack) /\
  (forall id, match_option_ablock_alpha a (am1.(am_glob) ! id) (am2.(am_glob) ! (alpha_rename a id))) /\
  am1.(am_nonstack) = alpha_rename a am2.(am_nonstack) /\
  am1.(am_top) = alpha_rename a am2.(am_top).


Inductive match_VA_alpha a : VA.t -> VA.t -> Prop :=
| match_Bot_alpha : match_VA_alpha a VA.Bot VA.Bot
| match_State_alpha : forall ae1 ae2 am1 am2, 
    match_aenv_alpha a ae1 ae2 ->
    match_amem_alpha a am1 am2 ->
    match_VA_alpha a (VA.State ae1 am1) (VA.State ae2 am2).


(* Inductive match_option_VA_alpha a : option VA.t -> option VA.t -> Prop := *)
(* | match_none_VA_alpha : match_option_VA_alpha a None None *)
(* | match_some_VA_alpha : forall va1 va2,  *)
(*     match_VA_alpha a va1 va2 -> *)
(*     match_option_VA_alpha a (Some va1) (Some va2). *)

Lemma analyze_alpha: forall f a ctx pc,
    match_VA_alpha a ((analyze (romem_for (alpha_rename a ctx)) (alpha_rename a f))!!pc) ((analyze (romem_for ctx) f)!!pc) .
Admitted.

Lemma match_aenv_alpha_areg : forall a ae1 ae2 r,
        match_aenv_alpha a ae1 ae2 ->
        areg ae1 r =  alpha_rename a (areg ae2 r).
Admitted.


Lemma match_aenv_alpha_aregs : forall a ae1 ae2 l,
        match_aenv_alpha a ae1 ae2 ->
        aregs ae1 l = map (alpha_rename a) (aregs ae2 l).
Admitted.

Lemma eval_static_operation_alpha: forall a op ae1 ae2 l,
    match_aenv_alpha a ae1 ae2 ->
    eval_static_operation (alpha_rename a op) (aregs ae1 l) =
    alpha_rename a (eval_static_operation op (aregs ae2 l)).
Admitted.

Lemma eval_static_addressing_alpha: forall a addr ae1 ae2 l,
    match_aenv_alpha a ae1 ae2 ->
    eval_static_addressing (alpha_rename a addr) (aregs ae1 l) =
    alpha_rename a (eval_static_addressing addr (aregs ae2 l)).
Admitted.

Lemma eval_static_condition_alpha: forall a c ae1 ae2 l,
    match_aenv_alpha a ae1 ae2 ->
    eval_static_condition c (aregs ae1 l) =
    eval_static_condition c (aregs ae2 l).
Admitted.

Lemma const_for_result_alpha: forall a av,
    match_option_alpha a (const_for_result (alpha_rename a av)) (const_for_result av).
  Admitted.

Lemma op_strength_reduction_alpha: forall a o o1 o2 l l1 l2 ae1 ae2,
    match_aenv_alpha a ae1 ae2 ->
    op_strength_reduction (alpha_rename a o) l (aregs ae1 l) = (o1,l1) ->
    op_strength_reduction o l (aregs ae2 l) = (o2,l2) ->
    o1 = alpha_rename a o2 /\ l1 = l2.
Admitted.

Lemma addr_strength_reduction_alpha: forall a addr addr1 addr2 l l1 l2 ae1 ae2,
    match_aenv_alpha a ae1 ae2 ->
    addr_strength_reduction (alpha_rename a addr) l (aregs ae1 l) = (addr1,l1) ->
    addr_strength_reduction addr l (aregs ae2 l) = (addr2,l2) ->
    addr1 = alpha_rename a addr2 /\ l1 = l2.
Admitted.

Lemma builtin_args_strength_reduction_alpha: forall a ae1 ae2 l,
        match_aenv_alpha a ae1 ae2 ->
        forall l1, (builtin_args_strength_reduction ae1 (map (alpha_rename a) l) l1) = (map (alpha_rename a) (builtin_args_strength_reduction ae2 l l1)) .
Admitted.

Lemma cond_strength_reduction_alpha: forall a c ae1 ae2 l,
    match_aenv_alpha a ae1 ae2 ->
    cond_strength_reduction c l (aregs ae1 l) =
    cond_strength_reduction c l (aregs ae2 l).
Admitted.


 Lemma eval_static_builtin_function_alpha: forall a ae1 ae2 am1 am2 rm1 rm2 b l,
            match_aenv_alpha a ae1 ae2 ->
            match_amem_alpha a am1 am2 ->
            match_romem_alpha a rm1 rm2 ->
            match_option_alpha a (eval_static_builtin_function ae1 am1 rm1 b (map (alpha_rename a) l)) (eval_static_builtin_function ae2 am2 rm2 b l).
Admitted.

 Lemma debug_strength_reduction_alpha: forall a ae1 ae2 l,
        match_aenv_alpha a ae1 ae2 ->
        debug_strength_reduction ae1 (map (alpha_rename a) l) =
        map (alpha_rename a) (debug_strength_reduction ae2 l).
 Admitted.
   
 
Lemma AE_set_match_alpha : forall a r v ae1 ae2,
            match_aenv_alpha a ae1 ae2 ->
            match_aenv_alpha a (AE.set r (alpha_rename a v) ae1) (AE.set r v ae2). 
Admitted.

Lemma successor_alpha: forall a f ae1 ae2 pc,
            match_aenv_alpha a ae1 ae2 ->
            successor (alpha_rename a f) ae1 pc = successor f ae2 pc.
Admitted.

Lemma loadv_alpha: forall a chunk rm1 rm2 am1 am2 av1 av2,
        match_romem_alpha a rm1 rm2 ->
        match_amem_alpha a am1 am2 ->
        av1 = alpha_rename a av2 ->
        loadv chunk rm1 am1 av1 = alpha_rename a (loadv chunk rm2 am2 av2).
Admitted.

Lemma transf_instr_alpha_aux :forall f a ctx n i,
    transf_instr (alpha_rename a f)
    (analyze (romem_for (alpha_rename a ctx)) (alpha_rename a f))
    (romem_for (alpha_rename a ctx)) n
    (alpha_rename a i) =
  alpha_rename a
    (transf_instr f (analyze (romem_for ctx) f) 
                  (romem_for ctx) n i).
Proof.
  intros.
  Transparent Alpha_function Alpha_instruction. 
  generalize (analyze_alpha f a ctx).
  intros Match. generalize (Match n). intros Match_n.
  unfold transf_instr.
  destruct i;simpl.
  (* Inop *)
  - inversion Match_n;simpl;auto.
  (* Iop *)
  - inversion Match_n;simpl;auto.
    + generalize (eval_static_operation_alpha a o ae1 ae2 l H1).
      intros M_eval.
      rewrite M_eval.
      generalize (const_for_result_alpha a (eval_static_operation o (aregs ae2 l))). intros.
      inversion H3.
      * destruct (op_strength_reduction (alpha_rename a o) l (aregs ae1 l)) eqn: ?.
        destruct (op_strength_reduction o l (aregs ae2 l)) eqn:?.
        eapply (op_strength_reduction_alpha _ _ _ _ _ _ _ _ _ H1 Heqp) in Heqp0.
        destruct Heqp0. subst.
        generalize (AE_set_match_alpha a r (eval_static_operation o (aregs ae2 l)) ae1 ae2 H1). intros.
        eapply successor_alpha in H4.
        erewrite H4.
        simpl. auto.
      * generalize (AE_set_match_alpha a r (eval_static_operation o (aregs ae2 l)) ae1 ae2 H1). intros.
        eapply successor_alpha in H7.
        erewrite H7.
        simpl. subst. auto.
  - inversion Match_n;simpl;auto.
    generalize (eval_static_addressing_alpha a a0 ae1 ae2 l H1).
    intros.
    generalize (romem_for_alpha a ctx). intros.
    generalize (loadv_alpha _ m _ _ _ _ _ _ H4 H2 H3). intros.
    generalize (const_for_result_alpha a (loadv m (romem_for ctx) am2
                                                (eval_static_addressing a0 (aregs ae2 l)))). intros.
    rewrite H5.                 (* careful *)
    inversion H6.
    + destruct (addr_strength_reduction (alpha_rename a a0) l (aregs ae1 l)) eqn: ?.
      destruct (addr_strength_reduction a0 l (aregs ae2 l)) eqn:?.
      eapply (addr_strength_reduction_alpha _ _ _ _ _ _ _ _ _ H1 Heqp) in Heqp0.
      destruct Heqp0. subst.
      simpl. auto.
    + subst. simpl. auto.
  (* Istore *)
  - inversion Match_n;simpl;auto.
    destruct (addr_strength_reduction (alpha_rename a a0) l (aregs ae1 l)) eqn: ?.
      destruct (addr_strength_reduction a0 l (aregs ae2 l)) eqn:?.
      eapply (addr_strength_reduction_alpha _ _ _ _ _ _ _ _ _ H1 Heqp) in Heqp0.
      destruct Heqp0. subst.
      simpl. auto.
  (* Icall *)
  - inversion Match_n;simpl;auto.
    destruct s0;simpl;auto.
    generalize (match_aenv_alpha_areg a ae1 ae2 r0 H1). intros.
    rewrite H3. destruct (areg ae2 r0);simpl;auto.
    destruct p;simpl;auto.
    simpl.
    Transparent Alpha_aval Alpha_aptr. simpl.
    destruct (Ptrofs.eq ofs Ptrofs.zero);simpl;auto.
  (* Itailcall *)
  - inversion Match_n;simpl;auto.
    destruct s0;simpl;auto.
    generalize (match_aenv_alpha_areg a ae1 ae2 r H1). intros.
    rewrite H3. destruct (areg ae2 r);simpl;auto.
    destruct p;simpl;auto.
    simpl.
    Transparent Alpha_aval Alpha_aptr. simpl.
    destruct (Ptrofs.eq ofs Ptrofs.zero);simpl;auto.
  (* Ibuiltin *)
  - inversion Match_n;simpl;auto.
    generalize (builtin_args_strength_reduction_alpha _ _ _ l H1). intros.   
    destruct e;simpl;auto;try erewrite H3;auto.
    + destruct b;simpl;auto.
      * destruct (lookup_builtin_function name sg);simpl;auto.
        generalize (romem_for_alpha a ctx). intros.
        generalize (eval_static_builtin_function_alpha _ _ _ _ _ _ _ b l H1 H2 H4). intros.
        inversion H5;simpl;auto.
        subst.
        generalize (const_for_result_alpha a a2). intros.
        inversion H8;simpl.
        -- rewrite <- H10;simpl;auto.
        -- rewrite <- H9;subst;auto.
    + erewrite debug_strength_reduction_alpha;auto.
  (* Icond *)
  - inversion Match_n;simpl;auto.
    erewrite (eval_static_condition_alpha _ _ _ _ _ H1).
    destruct (resolve_branch (eval_static_condition c (aregs ae2 l)));simpl;auto.
    destruct b;simpl;auto.
    destruct (cond_strength_reduction c l (aregs ae1 l)) eqn: ?.
    destruct (cond_strength_reduction c l (aregs ae2 l)) eqn:?.
    apply (cond_strength_reduction_alpha _ c _ _ l) in H1;auto.
    rewrite H1 in Heqp. rewrite Heqp in Heqp0. inversion Heqp0.
    simpl. auto.
  (* Ijumptable *)
  - inversion Match_n;simpl;auto.
    generalize (match_aenv_alpha_areg a ae1 ae2 r H1). intros.
    rewrite H3. destruct (areg ae2 r);simpl;auto.
    destruct (list_nth_z l (Int.unsigned n0));simpl;auto.
  (* Ireturn *)
  - inversion Match_n;simpl;auto.
Qed.

Lemma  transf_function_alpha_aux : forall f a ctx n,
    PTree.xmap (transf_instr (alpha_rename a f)
                             (analyze (romem_for (alpha_rename a ctx)) (alpha_rename a f))
                             (romem_for (alpha_rename a ctx)))
               (PTree.map1 (alpha_rename a) (fn_code f)) n =
    PTree.map1 (alpha_rename a)
               (PTree.xmap (transf_instr f (analyze (romem_for ctx) f) (romem_for ctx))
                           (fn_code f) n).
Proof.
  intros. generalize dependent n.
  induction (fn_code f);intros.
  - simpl. auto.
  - simpl.
    destruct o;simpl.
    + f_equal;auto.
      f_equal. apply transf_instr_alpha_aux.
    + f_equal;auto.
Qed.


(* final lemma *)

Lemma transf_function_alpha: forall f a ctx,
    transf_function (romem_for (alpha_rename a ctx)) (alpha_rename a f) =
    alpha_rename a (transf_function (romem_for ctx) f).
Proof.
  Transparent Alpha_prog Alpha_function.
  intros.
  simpl.
  unfold transf_function.
  unfold alpha_rename_function.
  f_equal.
   assert ({|
          fn_sig := fn_sig f;
          fn_params := fn_params f;
          fn_stacksize := fn_stacksize f;
          fn_code := PTree.map1 (alpha_rename a) (fn_code f);
          fn_entrypoint := fn_entrypoint f |} = alpha_rename a f).
  { simpl. unfold alpha_rename_function. auto. }
  rewrite H. clear H. simpl. 
  unfold PTree.map.
  apply transf_function_alpha_aux.
Qed.

Lemma transf_fundef_alpha: forall fd a ctx,
    transf_fundef (romem_for (alpha_rename a ctx)) (alpha_rename a fd) = alpha_rename a (transf_fundef (romem_for ctx) fd).
Proof.
  intros.
  Transparent Alpha_fundef.
  destruct fd;simpl;auto.
  f_equal. apply transf_function_alpha.
Qed.
