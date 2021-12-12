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

(** Elimination of unneeded computations over RTL. *)

Require Import Coqlib Maps Errors Integers Floats Lattice Kildall.
Require Import AST Linking.
Require Import Memory Registers Op RTL.
Require Import ValueDomain ValueAnalysis NeedDomain NeedOp.

(** * Part 1: the static analysis *)

Definition add_need_all (r: reg) (ne: nenv) : nenv :=
  NE.set r All ne.

Definition add_need (r: reg) (nv: nval) (ne: nenv) : nenv :=
  NE.set r (nlub nv (NE.get r ne)) ne.

Fixpoint add_needs_all (rl: list reg) (ne: nenv) : nenv :=
  match rl with
  | nil => ne
  | r1 :: rs => add_need_all r1 (add_needs_all rs ne)
  end.

Fixpoint add_needs (rl: list reg) (nvl: list nval) (ne: nenv) : nenv :=
  match rl, nvl with
  | nil, _ => ne
  | r1 :: rs, nil => add_needs_all rl ne
  | r1 :: rs, nv1 :: nvs => add_need r1 nv1 (add_needs rs nvs ne)
  end.

Definition add_ros_need_all (ros: reg + ident) (ne: nenv) : nenv :=
  match ros with
  | inl r => add_need_all r ne
  | inr s => ne
  end.

Definition add_opt_need_all (or: option reg) (ne: nenv) : nenv :=
  match or with
  | Some r => add_need_all r ne
  | None => ne
  end.

Definition kill (r: reg) (ne: nenv) : nenv := NE.set r Nothing ne.

Definition is_dead (v: nval) :=
  match v with Nothing => true | _ => false end.

Definition is_int_zero (v: nval) :=
  match v with I n => Int.eq n Int.zero | _ => false end.

Fixpoint transfer_builtin_arg (nv: nval) (na: NA.t) (a: builtin_arg reg) : NA.t :=
  let (ne, nm) := na in
  match a with
  | BA r => (add_need r nv ne, nm)
  | BA_int _ | BA_long _ | BA_float _ | BA_single _
  | BA_addrstack _ | BA_addrglobal _ _ => (ne, nm)
  | BA_loadstack chunk ofs => (ne, nmem_add nm (Stk ofs) (size_chunk chunk))
  | BA_loadglobal chunk id ofs => (ne, nmem_add nm (Gl id ofs) (size_chunk chunk))
  | BA_splitlong hi lo =>
      transfer_builtin_arg All (transfer_builtin_arg All na hi) lo
  | BA_addptr hi lo =>
      transfer_builtin_arg All (transfer_builtin_arg All na hi) lo
  end.

Definition transfer_builtin_args (na: NA.t) (al: list (builtin_arg reg)) : NA.t :=
  List.fold_left (transfer_builtin_arg All) al na.

Definition kill_builtin_res (res: builtin_res reg) (ne: NE.t) : NE.t :=
  match res with
  | BR r => kill r ne
  | _    => ne
  end.

Function transfer_builtin (app: VA.t) (ef: external_function)
                          (args: list (builtin_arg reg)) (res: builtin_res reg)
                          (ne: NE.t) (nm: nmem) : NA.t :=
  match ef, args with
  | EF_vload chunk, a1::nil =>
      transfer_builtin_arg All
        (kill_builtin_res res ne,
         nmem_add nm (aaddr_arg app a1) (size_chunk chunk))
        a1
  | EF_vstore chunk, a1::a2::nil =>
      transfer_builtin_arg All
          (transfer_builtin_arg (store_argument chunk)
                                (kill_builtin_res res ne, nm) a2)
          a1
  | EF_memcpy sz al, dst::src::nil =>
      if nmem_contains nm (aaddr_arg app dst) sz then
        transfer_builtin_args
           (kill_builtin_res res ne,
            nmem_add (nmem_remove nm (aaddr_arg app dst) sz) (aaddr_arg app src) sz)
           args
      else (ne, nm)
  | (EF_annot _ _ _ | EF_annot_val _ _ _), _ =>
      transfer_builtin_args (kill_builtin_res res ne, nm) args
  | EF_debug _ _ _, _ =>
      (kill_builtin_res res ne, nm)
  | _, _ =>
      transfer_builtin_args (kill_builtin_res res ne, nmem_all) args
  end.

Definition transfer (f: function) (approx: PMap.t VA.t)
                    (pc: node) (after: NA.t) : NA.t :=
  let (ne, nm) := after in
  match f.(fn_code)!pc with
  | None =>
      NA.bot
  | Some (Inop s) =>
      after
  | Some (Iop op args res s) =>
      let nres := nreg ne res in
      if is_dead nres then after
      else if is_int_zero nres then (kill res ne, nm)
      else (add_needs args (needs_of_operation op nres) (kill res ne), nm)
  | Some (Iload chunk addr args dst s) =>
      let ndst := nreg ne dst in
      if is_dead ndst then after
      else if is_int_zero ndst then (kill dst ne, nm)
      else (add_needs_all args (kill dst ne),
            nmem_add nm (aaddressing approx!!pc addr args) (size_chunk chunk))
  | Some (Istore chunk addr args src s) =>
      let p := aaddressing approx!!pc addr args in
      if nmem_contains nm p (size_chunk chunk)
      then (add_needs_all args (add_need src (store_argument chunk) ne),
            nmem_remove nm p (size_chunk chunk))
      else after
  | Some(Icall sig ros args res s) =>
      (add_needs_all args (add_ros_need_all ros (kill res ne)), nmem_all)
  | Some(Itailcall sig ros args) =>
      (add_needs_all args (add_ros_need_all ros NE.bot),
       nmem_dead_stack f.(fn_stacksize))
  | Some(Ibuiltin ef args res s) =>
      transfer_builtin approx!!pc ef args res ne nm
  | Some(Icond cond args s1 s2) =>
      if peq s1 s2 then after else 
        (add_needs args (needs_of_condition cond) ne, nm)
  | Some(Ijumptable arg tbl) =>
      (add_need_all arg ne, nm)
  | Some(Ireturn optarg) =>
      (add_opt_need_all optarg ne, nmem_dead_stack f.(fn_stacksize))
  end.

Module DS := Backward_Dataflow_Solver(NA)(NodeSetBackward).

Definition analyze (approx: PMap.t VA.t) (f: function): option (PMap.t NA.t) :=
  DS.fixpoint f.(fn_code) successors_instr
              (transfer f approx).

(** * Part 2: the code transformation *)

Definition transf_instr (approx: PMap.t VA.t) (an: PMap.t NA.t)
                        (pc: node) (instr: instruction) :=
  match instr with
  | Iop op args res s =>
      let nres := nreg (fst an!!pc) res in
      if is_dead nres then
        Inop s
      else if is_int_zero nres then
        Iop (Ointconst Int.zero) nil res s
      else if operation_is_redundant op nres then
        match args with
        | arg :: _ => Iop Omove (arg :: nil) res s
        | nil => instr
        end
      else
        instr
  | Iload chunk addr args dst s =>
      let ndst := nreg (fst an!!pc) dst in
      if is_dead ndst then
        Inop s
      else if is_int_zero ndst then
        Iop (Ointconst Int.zero) nil dst s
      else
        instr
  | Istore chunk addr args src s =>
      let p := aaddressing approx!!pc addr args in
      if nmem_contains (snd an!!pc) p (size_chunk chunk)
      then instr
      else Inop s
  | Ibuiltin (EF_memcpy sz al) (dst :: src :: nil) res s =>
      if nmem_contains (snd an!!pc) (aaddr_arg approx!!pc dst) sz
      then instr
      else Inop s
  | Icond cond args s1 s2 =>
      if peq s1 s2 then Inop s1 else instr
  | _ =>
      instr
  end.

Definition transf_function (rm: romem) (f: function) : res function :=
  let approx := ValueAnalysis.analyze rm f in
  match analyze approx f with
  | Some an =>
      OK {| fn_sig := f.(fn_sig);
            fn_params := f.(fn_params);
            fn_stacksize := f.(fn_stacksize);
            fn_code := PTree.map (transf_instr approx an) f.(fn_code);
            fn_entrypoint := f.(fn_entrypoint) |}
  | None =>
      Error (msg "Neededness analysis failed")
  end.

Definition transf_fundef (rm: romem) (fd: fundef) : res fundef :=
  AST.transf_partial_fundef (transf_function rm) fd.

Definition transf_program (p: program) : res program :=
  transform_partial_program (transf_fundef (romem_for p)) p.


Inductive match_nmem_alpha (a:permutation) : nmem -> nmem -> Prop :=
| match_nmem_dead : match_nmem_alpha a NMemDead NMemDead
| match_nmem_used : forall stk1 stk2 gl1 gl2,
    IntvSets.ISet.beq stk1 stk2 = true ->
    (forall id, match_option_alpha a (fun _ intv1 intv2 => IntvSets.ISet.beq intv1 intv2 = true)  (gl1 ! (alpha_rename a id)) (gl2 ! id)) ->
    match_nmem_alpha a (NMem stk1 gl1) (NMem stk2 gl2).


Definition match_NA_alpha (a:permutation) (na1 na2: NA.t) :=
  PTree.beq eq_nval (fst na1) (fst na2) = true /\
  match_nmem_alpha a (snd na2) (snd na2).

Lemma Deadcode_analyze_alpha: forall a f pva1 pva2,
    (forall pc, match_VA_alpha a pva1!!pc pva2!!pc) ->
     match_option_alpha a (fun a pn1 pn2 => forall pc, match_NA_alpha a pn1!!pc pn2!!pc) (analyze pva1 (alpha_rename a f)) (analyze pva2 f).
Admitted.

Lemma is_dead_alpha: forall a pn1 pn2 node r,
      (forall pc : positive, match_NA_alpha a pn1 # pc pn2 # pc) ->
      is_dead (nreg (fst pn1#node) r) = is_dead (nreg (fst pn2#node) r).
Admitted.

Lemma is_int_zero_alpha: forall a pn1 pn2 node r,
      (forall pc : positive, match_NA_alpha a pn1 # pc pn2 # pc) ->
      is_int_zero (nreg (fst pn1#node) r) = is_int_zero (nreg (fst pn2#node) r).
  Admitted.

Lemma operation_is_redundant_alpha: forall a pn1 pn2 node r op,
    (forall pc : positive, match_NA_alpha a pn1 # pc pn2 # pc) ->
    operation_is_redundant (alpha_rename a op) (nreg (fst pn1#node) r) = operation_is_redundant op (nreg (fst pn2#node) r).
Admitted.

Lemma aaddressing_alpha: forall a va1 va2 addr l,
    match_VA_alpha a va1 va2 ->
    aaddressing va1 (alpha_rename a addr) l = alpha_rename a (aaddressing va2 addr l).
Admitted.

Lemma aaddr_arg_alpha: forall a va1 va2 arg,
    match_VA_alpha a va1 va2 ->
    aaddr_arg va1 (alpha_rename a arg) = alpha_rename a (aaddr_arg va2 arg).
Admitted.


Lemma nmem_contains_alpha: forall a pva1 pva2 pn1 pn2 node ap size,
      (forall pc : positive, match_VA_alpha a pva1 # pc pva2 # pc) ->
      (forall pc : positive, match_NA_alpha a pn1 # pc pn2 # pc) ->
      nmem_contains (snd pn1 # node) (alpha_rename a ap) size = nmem_contains (snd pn2#node) ap size.
Admitted.
    

Lemma transf_instr_alpha : forall a pva1 pva2 pn1 pn2 i node,
    (forall pc : positive, match_VA_alpha a pva1 !! pc pva2 !! pc) ->
    (forall pc : positive, match_NA_alpha a pn1 !! pc pn2 !! pc) ->
    transf_instr pva1 pn1 node (alpha_rename a i) =
    alpha_rename a (transf_instr pva2 pn2 node i).
Proof.
  intros.
  Transparent Alpha_instruction.
  destruct i;simpl;auto.
  - generalize (is_dead_alpha _ _ _ node r H0).
    intros. rewrite H1. destruct (is_dead (nreg (fst pn2 # node) r));
    simpl;auto.
    generalize (is_int_zero_alpha _ _ _ node r H0).
    intros. rewrite H2. destruct (is_int_zero (nreg (fst pn2 # node) r));simpl;auto.
    generalize (operation_is_redundant_alpha _ _ _ node r o H0).
    intros. rewrite H3. destruct (operation_is_redundant o (nreg (fst pn2 # node) r));simpl;auto.
    destruct l;simpl;auto.
  - generalize (is_dead_alpha _ _ _ node r H0).
    intros. rewrite H1. destruct (is_dead (nreg (fst pn2 # node) r));
    simpl;auto.
    generalize (is_int_zero_alpha _ _ _ node r H0).
    intros. rewrite H2. destruct (is_int_zero (nreg (fst pn2 # node) r));simpl;auto.
  - eapply aaddressing_alpha in H as ?.
    rewrite H1.
    erewrite nmem_contains_alpha;auto.
    destruct (nmem_contains (snd pn2 # node) (aaddressing pva2 # node a0 l) (size_chunk m));simpl;auto.    
  - destruct s0;simpl;auto.
  - destruct s0;simpl;auto.
  - destruct e;simpl;auto.
    destruct l;simpl;auto.
    destruct l;simpl;auto.
    destruct l;simpl;auto.
    eapply aaddr_arg_alpha in H as ?.
    rewrite H1.
    erewrite nmem_contains_alpha;auto.
    destruct (nmem_contains (snd pn2 # node) (aaddr_arg pva2 # node b0) sz);simpl;auto.
  - destruct (peq n n0);auto.
Qed.


    
Lemma transf_function_alpha_aux : forall a code pva1 pva2 pn1 pn2 node,
    (forall pc, match_VA_alpha a pva1!!pc pva2!!pc) ->
    (forall pc, match_NA_alpha a pn1!!pc pn2!!pc) ->
    PTree.xmap (fun (pc : positive) (instr : instruction) => transf_instr pva1 pn1 pc instr) (PTree.map1 (alpha_rename a) code) node =
          PTree.map1 (alpha_rename a) (PTree.xmap (fun (pc : positive) (instr : instruction) => transf_instr pva2 pn2 pc instr) code node).
Proof.
  intros.
  generalize dependent node.
  induction code;simpl;auto.
  intros. destruct o;simpl.
  - f_equal;auto.
    f_equal.
    apply transf_instr_alpha. auto. auto.
  - f_equal;auto.
Qed.

  
Lemma transf_function_alpha: forall a f f' ctx,
    transf_function (romem_for ctx) f = OK f' ->
    transf_function (romem_for (alpha_rename a ctx)) (alpha_rename a f) = OK (alpha_rename a f').
Proof.
  intros.
  unfold transf_function in *.
  generalize (analyze_alpha f a ctx). intros.
  generalize (Deadcode_analyze_alpha a f _ _ H0). intros.
  inversion H1.
  - rewrite <- H4 in H.
    congruence.
  - rewrite <- H3 in H.
    monadInv H.
    f_equal.
    Transparent Alpha_function.
    simpl. unfold alpha_rename_function. simpl.
    f_equal.
    unfold PTree.map.
    assert ({|
          fn_sig := fn_sig f;
          fn_params := fn_params f;
          fn_stacksize := fn_stacksize f;
          fn_code := PTree.map1 (alpha_rename a) (fn_code f);
          fn_entrypoint := fn_entrypoint f |} = alpha_rename a f). 
    { simpl. unfold alpha_rename_function. auto. }
    simpl in *. rewrite H. clear H.
    inversion H1.
    + simpl in *.
      rewrite <- H5 in H2. congruence.
    + simpl in *. rewrite <- H in H2. rewrite <- H5 in H3.
      inversion H2. inversion H3. subst.
      clear H5 H4 H3 H2 H1 H .
      apply transf_function_alpha_aux. auto. auto.
Qed.

Lemma transf_fundef_alpha : forall a fd fd' ctx,
    transf_fundef (romem_for ctx) fd = OK fd' -> 
    transf_fundef (romem_for (alpha_rename a ctx)) (alpha_rename a fd) = OK (alpha_rename a fd').
Proof.
  unfold transf_fundef.
  unfold transf_partial_fundef.
  intros.
  Transparent Alpha_fundef.
  destruct fd;destruct fd';simpl in *;try congruence;auto.
  monadInv H.
  eapply transf_function_alpha in EQ.
  rewrite EQ. simpl. auto.
  monadInv H.
Qed.

Definition transf_fundef_ctx ctx fd:=
    transf_fundef (romem_for ctx) fd.

Theorem transf_fundef_ctx_alpha: forall fd fd' a ctx,
    transf_fundef_ctx ctx fd = OK fd' ->
    transf_fundef_ctx (alpha_rename a ctx) (alpha_rename a fd) =
    OK (alpha_rename a fd').
Proof.
  intros.
  unfold transf_fundef_ctx in *.
  apply transf_fundef_alpha.
  auto.
Qed.
