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

(** Recognition of tail calls. *)

Require Import Coqlib Maps AST Registers Op RTL Conventions.

(** An [Icall] instruction that stores its result in register [rreg]
  can be turned into a tail call if:
- its successor is a [Ireturn None] or [Ireturn (Some rreg)] instruction;
- the stack block of the current function is empty: [stacksize = 0].

If the current function had a non-empty stack block, it could be that
the called function accesses it, for instance if a pointer into the
stack block is passed as an argument.  In this case, it would be
semantically incorrect to deallocate the stack block before the call,
as [Itailcall] does.  Therefore, the optimization can only be performed if
the stack block of the current function is empty, in which case it makes
no semantic difference to deallocate it before or after the call.

Another complication is that the [Ireturn] instruction does not, in general,
follow immediately the [Icall] instruction: the RTL code generator
can have inserted moves and no-ops between these instructions.
The general pattern we recognize is therefore:
<<
       r1 <- call(....)
       nop
       r2 <- r1
       r3 <- r2
       return r3
>>
The [is_return] function below recognizes this pattern.
*)

Fixpoint is_return (n: nat) (f: function) (pc: node) (rret: reg)
                   {struct n}: bool :=
  match n with
  | O => false
  | S n' =>
      match f.(fn_code)!pc with
      | Some(Ireturn None) => true
      | Some(Ireturn (Some r)) => Reg.eq r rret
      | Some(Inop s) => is_return n' f s rret
      | Some(Iop op args dst s) =>
          match is_move_operation op args with
          | None => false
          | Some src =>
              if Reg.eq rret src
              then is_return n' f s dst
              else false
          end
      | _ => false
      end
  end.

(** To ensure termination, we bound arbitrarily the number of iterations
of the [is_return] function: we look ahead for a nop/move/return of length
at most [niter] instructions. *)

Definition niter := 5%nat.

(** The code transformation is straightforward: call instructions
  followed by an appropriate nop/move/return sequence become
  tail calls; other instructions are unchanged.

  To ensure that the resulting RTL code is well typed, we
  restrict the transformation to the cases where a tail call is
  allowed by the calling conventions, and where the result signatures
  match. *)

Definition transf_instr (f: function) (pc: node) (instr: instruction) :=
  match instr with
  | Icall sig ros args res s =>
      if is_return niter f s res
      && tailcall_is_possible sig
      && rettype_eq sig.(sig_res) f.(fn_sig).(sig_res)
      then Itailcall sig ros args
      else instr
  | _ => instr
  end.

(** A function is transformed only if its stack block is empty,
    as explained above.  *)

Definition transf_function (f: function) : function :=
  if zeq f.(fn_stacksize) 0
  then RTL.transf_function (transf_instr f) f
  else f.

Definition transf_fundef (fd: fundef) : fundef :=
  AST.transf_fundef transf_function fd.

Definition transf_program (p: program) : program :=
  transform_program transf_fundef p.

(** *static renaming *)

Lemma is_return_alpah: forall a f gas n r,
  is_return gas (alpha_rename a f) n r =
  is_return gas f n r.
Proof.
  Transparent Alpha_instruction Alpha_function Alpha_operation.
  induction gas.
  simpl. auto.
  simpl. intros.
  erewrite PTree.gmap1.
  destruct ((fn_code f) ! n).
  - simpl.
    destruct i;simpl;auto.
    + destruct o;simpl;auto.
      erewrite IHgas.
      auto.
    + destruct s0;simpl;auto.
    + destruct s0;simpl;auto.
  - simpl. auto.
Qed.

Lemma transf_instr_alpha: forall f pc i a,
    transf_instr (alpha_rename a f) pc (alpha_rename a i) = alpha_rename a (transf_instr f pc i).
Proof.
  Transparent Alpha_instruction Alpha_function.
  intros;simpl.
  unfold transf_instr.
  destruct i;auto.
  - 
    cbn [alpha_rename_instruction].
    destruct s0.
    + rewrite is_return_alpah.
      assert ((fn_sig (alpha_rename_function a f)) = (fn_sig f)).
      { simpl. auto. }
      rewrite H.
      destruct (is_return niter f n r && tailcall_is_possible s &&
                rettype_eq (sig_res s) (sig_res (fn_sig f)));auto.
    + rewrite is_return_alpah.
      assert ((fn_sig (alpha_rename_function a f)) = (fn_sig f)).
      { simpl. auto. }
      rewrite H.
      destruct (is_return niter f n r && tailcall_is_possible s &&
                rettype_eq (sig_res s) (sig_res (fn_sig f)));auto.
  - cbn [alpha_rename_instruction].

    destruct s0;auto.
Qed.

Lemma transf_function_ctx_alpha_aux: forall f ctx a p,

PTree.xmap (transf_instr (alpha_rename a ctx))
    (PTree.map1 (alpha_rename_instruction a) (fn_code f)) p =
  PTree.map1 (alpha_rename_instruction a)
             (PTree.xmap (transf_instr ctx) (fn_code f) p).
Proof.
  Transparent Alpha_function Alpha_instruction.
  simpl. intros.
  generalize dependent ctx.
  generalize dependent p.
  induction fn_code;intros;simpl;auto.
  f_equal;auto.
  destruct o;simpl;auto.
  f_equal. eapply transf_instr_alpha.
Qed.

Lemma transf_function_ctx_alpha: forall f ctx a,
    RTL.transf_function (transf_instr (alpha_rename a ctx))
                        (alpha_rename a f) =
    alpha_rename a (RTL.transf_function (transf_instr ctx) f).
Proof.
  Transparent Alpha_instruction Alpha_function.
  unfold RTL.transf_function. simpl.
  unfold alpha_rename_function;simpl.
  intros. f_equal.
  assert ({|
       fn_sig := fn_sig ctx;
       fn_params := fn_params ctx;
       fn_stacksize := fn_stacksize ctx;
       fn_code := PTree.map1 (alpha_rename_instruction a)
                    (fn_code ctx);
       fn_entrypoint := fn_entrypoint ctx |} = alpha_rename a ctx).
  { simpl. unfold alpha_rename_function. auto. }
  rewrite H;clear H.
  apply transf_function_ctx_alpha_aux.
Qed.

Lemma transf_function_alpha: forall f a,
    transf_function (alpha_rename a f) = alpha_rename a (transf_function f).
Proof.
  intros.
  unfold transf_function.
  Transparent Alpha_function Alpha_instruction.
  simpl. destruct (zeq (fn_stacksize f) 0);auto.
  apply transf_function_ctx_alpha.
Qed.  

Lemma transf_fundef_alpha: forall fd a,
    transf_fundef (alpha_rename a fd) = alpha_rename a (transf_fundef fd).
Proof.
  intros.
  Transparent Alpha_fundef.
  simpl.
  destruct fd.
  - simpl. f_equal.
    apply transf_function_alpha.
  - simpl;auto.
Qed.
