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

Require Import Coqlib.
Require Import Maps.
Require Import Postorder.
Require Import RTL.

(** CompCert's dataflow analyses (module [Kildall]) are more precise
  and run faster when the sequence [1, 2, 3, ...]  is a postorder
  enumeration of the nodes of the control-flow graph.  This property
  can be guaranteed when generating the CFG (module [RTLgen]), but
  is, however, invalidated by further RTL optimization passes such as
  [Inlining].

  In this module, we renumber the nodes of RTL control-flow graphs
  to restore the postorder property given above.  In passing,
  we also eliminate CFG nodes that are not reachable from the entry point:
  these nodes are dead code. *)

Section RENUMBER.

Variable pnum: PTree.t positive.   (**r a postorder numbering *)

Definition renum_pc (pc: node) : node :=
  match pnum!pc with
  | Some pc' => pc'
  | None => 1%positive          (**r impossible case, never exercised *)
  end.

Definition renum_instr (i: instruction) : instruction :=
  match i with
  | Inop s => Inop (renum_pc s)
  | Iop op args res s => Iop op args res (renum_pc s)
  | Iload chunk addr args res s => Iload chunk addr args res (renum_pc s)
  | Istore chunk addr args src s => Istore chunk addr args src (renum_pc s)
  | Icall sg ros args res s => Icall sg ros args res (renum_pc s)
  | Itailcall sg ros args => i
  | Ibuiltin ef args res s => Ibuiltin ef args res (renum_pc s)
  | Icond cond args s1 s2 => Icond cond args (renum_pc s1) (renum_pc s2)
  | Ijumptable arg tbl => Ijumptable arg (List.map renum_pc tbl)
  | Ireturn or => i
  end.

Definition renum_node (c': code) (pc: node) (i: instruction) : code :=
  match pnum!pc with
  | None => c'
  | Some pc' => PTree.set pc' (renum_instr i) c'
  end.

Definition renum_cfg (c: code) : code :=
  PTree.fold renum_node c (PTree.empty instruction).

End RENUMBER.

Definition transf_function (f: function) : function :=
  let pnum := postorder (successors_map f) f.(fn_entrypoint) in
  mkfunction
    f.(fn_sig)
    f.(fn_params)
    f.(fn_stacksize)
    (renum_cfg pnum f.(fn_code))
    (renum_pc pnum f.(fn_entrypoint)).

Definition transf_fundef (fd: fundef) : fundef :=
  AST.transf_fundef transf_function fd.

Definition transf_program (p: program) : program :=
  AST.transform_program transf_fundef p.

(** *alpha and transf commute*)
Lemma PTree_map_set {A B:Type}: forall b (k:positive) (v:A) (f:A->B),
    PTree.map1 f (PTree.set k v b) = PTree.set k (f v) (PTree.map1 f b).
Proof.
  induction b.
  - intros. simpl. induction k. 
    + simpl. rewrite IHk. auto.
    + simpl. rewrite IHk. auto.
    + simpl.  auto.
  - intros. simpl. induction k.
    + simpl. rewrite IHb2. auto.
    + simpl. rewrite IHb1. auto.
    + simpl. auto.
Qed.

Lemma renum_instr_alpha_aux: forall permu f i,
    AST.alpha_rename permu (renum_instr f i) =
    renum_instr f (AST.alpha_rename permu i).
Proof.
  Transparent Alpha_instruction.
  induction i;simpl;auto;
    destruct s0;simpl;auto.
Qed.

Lemma renum_cfg_alpha_fold_left_aux: forall permu f fn_code b i,
    PTree.map1 (AST.alpha_rename permu)
               (fold_left (fun (a : code) (p : positive * instruction) =>
                             renum_node f a (fst p) (snd p))
                          (PTree.xelements fn_code i nil) b) =
    fold_left
      (fun (a : code) (p : positive * instruction) =>
         renum_node f a (fst p) (snd p))
      (PTree.xelements (PTree.map1 (AST.alpha_rename permu) fn_code) i
                       nil) (PTree.map1 (AST.alpha_rename permu) b).
Proof.
  induction fn_code. 
  - simpl. auto.
  - simpl.
    destruct o.
    + simpl.
      intros.
      rewrite <- (app_nil_l ((PTree.prev i0, i) :: PTree.xelements fn_code2 i0~1 nil)).
      rewrite <- (app_nil_l ((PTree.prev i0, alpha_rename_instruction permu i)
        :: PTree.xelements
             (PTree.map1 (alpha_rename_instruction permu) fn_code2)
             i0~1 nil)).
      rewrite PTree.xelements_append.
      rewrite PTree.xelements_append.
      rewrite fold_left_app. rewrite fold_left_app.
      set (tf:=(fun (a : code) (p : positive * instruction) =>
                  renum_node f a (fst p) (snd p))).
      simpl.
      erewrite IHfn_code2.
      f_equal.
      unfold tf. simpl.
      unfold renum_node.
      destruct (f ! (PTree.prev i0)).
      * rewrite PTree_map_set. f_equal. 
        apply renum_instr_alpha_aux. (* rename instruction *)
        auto.
      * auto.
    + simpl.
      intros.
      rewrite <- (app_nil_l (PTree.xelements fn_code2 i~1 nil)).
      rewrite <- (app_nil_l  (PTree.xelements
          (PTree.map1 (alpha_rename_instruction permu) fn_code2) i~1
          nil)).
      rewrite PTree.xelements_append.
      rewrite PTree.xelements_append.
      rewrite fold_left_app. rewrite fold_left_app.
      set (tf:=(fun (a : code) (p : positive * instruction) =>
                  renum_node f a (fst p) (snd p))).
      simpl.
      erewrite IHfn_code2.
      f_equal.
      auto.
Qed.


Lemma renum_cfg_alpha_fold_aux : forall permu f fn_code b,
    PTree.map1 (AST.alpha_rename permu)
               (PTree.fold (renum_node f) fn_code b) =
    PTree.fold (renum_node f)
               (PTree.map1 (AST.alpha_rename permu) fn_code)
               (PTree.map1  (AST.alpha_rename permu) b).
Proof.
  intros.
  rewrite PTree.fold_spec.
  rewrite PTree.fold_spec.
  unfold PTree.elements.
  apply renum_cfg_alpha_fold_left_aux.
Qed.  


Lemma renum_cfg_alpha_aux : forall permu f fn_code,
  PTree.map1 (AST.alpha_rename permu) (renum_cfg f fn_code) =
  renum_cfg f (PTree.map1 (AST.alpha_rename permu) fn_code).
Proof.
  unfold renum_cfg. intros.
  apply renum_cfg_alpha_fold_aux.
Qed.  

Lemma alpha_transf_function_commute: forall f permu,
    AST.alpha_rename permu (transf_function f) = transf_function (AST.alpha_rename permu f).
Proof.
  Transparent Alpha_function.
  intros.
  simpl. unfold transf_function.
  destruct f. simpl.
  unfold alpha_rename_function.
  simpl.
  unfold successors_map. simpl.
  assert ((postorder (PTree.map1 successors_instr fn_code) fn_entrypoint) =  (postorder
       (PTree.map1 successors_instr
          (PTree.map1 (AST.alpha_rename permu) fn_code))
       fn_entrypoint)).
    {
      f_equal.
      induction fn_code.
      simpl. auto.
      simpl. rewrite IHfn_code1.
      f_equal.
      destruct o.
      - simpl.
        Transparent Alpha_instruction.
        induction i;simpl;auto;
          destruct s0;simpl;auto.
      - simpl. auto.
      - auto.
    }
  f_equal.
  - rewrite -> H.
    set (f:= (postorder (PTree.map1 successors_instr fn_code) fn_entrypoint)).
    apply renum_cfg_alpha_fold_aux .
    - f_equal. auto.
Qed.
    
Lemma alpha_transf_fundef_commute: forall fd permu,
    AST.alpha_rename permu (transf_fundef fd) = transf_fundef (AST.alpha_rename permu fd).
Proof.
  Transparent AST.Alpha_fundef.
  simpl.
  intros.
  destruct fd.
  simpl.
  f_equal.
  apply alpha_transf_function_commute.
  simpl. auto.
Qed.
