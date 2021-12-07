(* *********************************************************************)
(*                                                                     *)
(*              The Compcert verified compiler                         *)
(*                                                                     *)
(*          Xavier Leroy, INRIA Paris-Rocquencourt                     *)
(*                                                                     *)
(*  Copyright Institut National de Recherche en Informatique et en     *)
(*  Automatique.  All rights reserved.  This file is distributed       *)
(*  under the terms of the GNU General Public License as published by  *)
(*  the Free Software Foundation, either version 2 of the License, or  *)
(*  (at your option) any later version.  This file is also distributed *)
(*  under the terms of the INRIA Non-Commercial License Agreement.     *)
(*                                                                     *)
(* *********************************************************************)

(** This file defines a number of data types and operations used in
  the abstract syntax trees of many of the intermediate languages. *)

Require Import String.
Require Import Coqlib Maps Errors Integers Floats.
Require Archi.

Set Implicit Arguments.

(** * Syntactic elements *)

(** Identifiers (names of local variables, of global symbols and functions,
  etc) are represented by the type [positive] of positive integers. *)

Definition ident := positive.

Definition ident_eq := peq.

(** The intermediate languages are weakly typed, using the following types: *)

Inductive typ : Type :=
  | Tint                (**r 32-bit integers or pointers *)
  | Tfloat              (**r 64-bit double-precision floats *)
  | Tlong               (**r 64-bit integers *)
  | Tsingle             (**r 32-bit single-precision floats *)
  | Tany32              (**r any 32-bit value *)
  | Tany64.             (**r any 64-bit value, i.e. any value *)

Lemma typ_eq: forall (t1 t2: typ), {t1=t2} + {t1<>t2}.
Proof. decide equality. Defined.
Global Opaque typ_eq.

Definition list_typ_eq: forall (l1 l2: list typ), {l1=l2} + {l1<>l2}
                     := list_eq_dec typ_eq.

Definition Tptr : typ := if Archi.ptr64 then Tlong else Tint.

Definition typesize (ty: typ) : Z :=
  match ty with
  | Tint => 4
  | Tfloat => 8
  | Tlong => 8
  | Tsingle => 4
  | Tany32 => 4
  | Tany64 => 8
  end.

Lemma typesize_pos: forall ty, typesize ty > 0.
Proof. destruct ty; simpl; lia. Qed.

Lemma typesize_Tptr: typesize Tptr = if Archi.ptr64 then 8 else 4.
Proof. unfold Tptr; destruct Archi.ptr64; auto. Qed.

(** All values of size 32 bits are also of type [Tany32].  All values
  are of type [Tany64].  This corresponds to the following subtyping
  relation over types. *)

Definition subtype (ty1 ty2: typ) : bool :=
  match ty1, ty2 with
  | Tint, Tint => true
  | Tlong, Tlong => true
  | Tfloat, Tfloat => true
  | Tsingle, Tsingle => true
  | (Tint | Tsingle | Tany32), Tany32 => true
  | _, Tany64 => true
  | _, _ => false
  end.

Fixpoint subtype_list (tyl1 tyl2: list typ) : bool :=
  match tyl1, tyl2 with
  | nil, nil => true
  | ty1::tys1, ty2::tys2 => subtype ty1 ty2 && subtype_list tys1 tys2
  | _, _ => false
  end.

(** To describe the values returned by functions, we use the more precise
    types below. *)

Inductive rettype : Type :=
  | Tret (t: typ)                       (**r like type [t] *)
  | Tint8signed                         (**r 8-bit signed integer *)
  | Tint8unsigned                       (**r 8-bit unsigned integer *)
  | Tint16signed                        (**r 16-bit signed integer *)
  | Tint16unsigned                      (**r 16-bit unsigned integer *)
  | Tvoid.                              (**r no value returned *)

Coercion Tret: typ >-> rettype.

Lemma rettype_eq: forall (t1 t2: rettype), {t1=t2} + {t1<>t2}.
Proof. generalize typ_eq; decide equality. Defined.
Global Opaque rettype_eq.

Definition proj_rettype (r: rettype) : typ :=
  match r with
  | Tret t => t
  | Tint8signed | Tint8unsigned | Tint16signed | Tint16unsigned => Tint
  | Tvoid => Tint
  end.

(** Additionally, function definitions and function calls are annotated
  by function signatures indicating:
- the number and types of arguments;
- the type of the returned value;
- additional information on which calling convention to use.

These signatures are used in particular to determine appropriate
calling conventions for the function. *)

Record calling_convention : Type := mkcallconv {
  cc_vararg: option Z;  (**r variable-arity function (+ number of fixed args) *)
  cc_unproto: bool;     (**r old-style unprototyped function *)
  cc_structret: bool    (**r function returning a struct  *)
}.

Definition cc_default :=
  {| cc_vararg := None; cc_unproto := false; cc_structret := false |}.

Definition calling_convention_eq (x y: calling_convention) : {x=y} + {x<>y}.
Proof.
  decide equality; try (apply bool_dec). decide equality; apply Z.eq_dec.
Defined.
Global Opaque calling_convention_eq.

Record signature : Type := mksignature {
  sig_args: list typ;
  sig_res: rettype;
  sig_cc: calling_convention
}.

Definition proj_sig_res (s: signature) : typ := proj_rettype s.(sig_res).

Definition signature_eq: forall (s1 s2: signature), {s1=s2} + {s1<>s2}.
Proof.
  generalize rettype_eq, list_typ_eq, calling_convention_eq; decide equality.
Defined.
Global Opaque signature_eq.

Definition signature_main :=
  {| sig_args := nil; sig_res := Tint; sig_cc := cc_default |}.

(** Memory accesses (load and store instructions) are annotated by
  a ``memory chunk'' indicating the type, size and signedness of the
  chunk of memory being accessed. *)

Inductive memory_chunk : Type :=
  | Mint8signed     (**r 8-bit signed integer *)
  | Mint8unsigned   (**r 8-bit unsigned integer *)
  | Mint16signed    (**r 16-bit signed integer *)
  | Mint16unsigned  (**r 16-bit unsigned integer *)
  | Mint32          (**r 32-bit integer, or pointer *)
  | Mint64          (**r 64-bit integer *)
  | Mfloat32        (**r 32-bit single-precision float *)
  | Mfloat64        (**r 64-bit double-precision float *)
  | Many32          (**r any value that fits in 32 bits *)
  | Many64.         (**r any value *)

Definition chunk_eq: forall (c1 c2: memory_chunk), {c1=c2} + {c1<>c2}.
Proof. decide equality. Defined.
Global Opaque chunk_eq.

Definition Mptr : memory_chunk := if Archi.ptr64 then Mint64 else Mint32.

(** The type (integer/pointer or float) of a chunk. *)

Definition type_of_chunk (c: memory_chunk) : typ :=
  match c with
  | Mint8signed => Tint
  | Mint8unsigned => Tint
  | Mint16signed => Tint
  | Mint16unsigned => Tint
  | Mint32 => Tint
  | Mint64 => Tlong
  | Mfloat32 => Tsingle
  | Mfloat64 => Tfloat
  | Many32 => Tany32
  | Many64 => Tany64
  end.

Lemma type_of_Mptr: type_of_chunk Mptr = Tptr.
Proof. unfold Mptr, Tptr; destruct Archi.ptr64; auto. Qed.

(** Same, as a return type. *)

Definition rettype_of_chunk (c: memory_chunk) : rettype :=
  match c with
  | Mint8signed => Tint8signed
  | Mint8unsigned => Tint8unsigned
  | Mint16signed => Tint16signed
  | Mint16unsigned => Tint16unsigned
  | Mint32 => Tint
  | Mint64 => Tlong
  | Mfloat32 => Tsingle
  | Mfloat64 => Tfloat
  | Many32 => Tany32
  | Many64 => Tany64
  end.

Lemma proj_rettype_of_chunk:
  forall chunk, proj_rettype (rettype_of_chunk chunk) = type_of_chunk chunk.
Proof.
  destruct chunk; auto.
Qed.

(** The chunk that is appropriate to store and reload a value of
  the given type, without losing information. *)

Definition chunk_of_type (ty: typ) :=
  match ty with
  | Tint => Mint32
  | Tfloat => Mfloat64
  | Tlong => Mint64
  | Tsingle => Mfloat32
  | Tany32 => Many32
  | Tany64 => Many64
  end.

Lemma chunk_of_Tptr: chunk_of_type Tptr = Mptr.
Proof. unfold Mptr, Tptr; destruct Archi.ptr64; auto. Qed.

(** Initialization data for global variables. *)

Inductive init_data: Type :=
  | Init_int8: int -> init_data
  | Init_int16: int -> init_data
  | Init_int32: int -> init_data
  | Init_int64: int64 -> init_data
  | Init_float32: float32 -> init_data
  | Init_float64: float -> init_data
  | Init_space: Z -> init_data
  | Init_addrof: ident -> ptrofs -> init_data.  (**r address of symbol + offset *)

Definition init_data_size (i: init_data) : Z :=
  match i with
  | Init_int8 _ => 1
  | Init_int16 _ => 2
  | Init_int32 _ => 4
  | Init_int64 _ => 8
  | Init_float32 _ => 4
  | Init_float64 _ => 8
  | Init_addrof _ _ => if Archi.ptr64 then 8 else 4
  | Init_space n => Z.max n 0
  end.

Fixpoint init_data_list_size (il: list init_data) {struct il} : Z :=
  match il with
  | nil => 0
  | i :: il' => init_data_size i + init_data_list_size il'
  end.

Lemma init_data_size_pos:
  forall i, init_data_size i >= 0.
Proof.
  destruct i; simpl; try extlia. destruct Archi.ptr64; lia.
Qed.

Lemma init_data_list_size_pos:
  forall il, init_data_list_size il >= 0.
Proof.
  induction il; simpl. lia. generalize (init_data_size_pos a); lia.
Qed.

(** Information attached to global variables. *)

Record globvar (V: Type) : Type := mkglobvar {
  gvar_info: V;                    (**r language-dependent info, e.g. a type *)
  gvar_init: list init_data;       (**r initialization data *)
  gvar_readonly: bool;             (**r read-only variable? (const) *)
  gvar_volatile: bool              (**r volatile variable? *)
}.

(** Whole programs consist of:
- a collection of global definitions (name and description);
- a set of public names (the names that are visible outside
  this compilation unit);
- the name of the ``main'' function that serves as entry point in the program.

A global definition is either a global function or a global variable.
The type of function descriptions and that of additional information
for variables vary among the various intermediate languages and are
taken as parameters to the [program] type.  The other parts of whole
programs are common to all languages. *)

Inductive globdef (F V: Type) : Type :=
  | Gfun (f: F)
  | Gvar (v: globvar V).

Arguments Gfun [F V].
Arguments Gvar [F V].

Record program (F V: Type) : Type := mkprogram {
  prog_defs: list (ident * globdef F V);
  prog_public: list ident;
  prog_main: ident
}.


Definition prog_defs_names (F V: Type) (p: program F V) : list ident :=
  List.map fst p.(prog_defs).

(** The "definition map" of a program maps names of globals to their definitions.
  If several definitions have the same name, the one appearing last in [p.(prog_defs)] wins. *)

Definition prog_defmap (F V: Type) (p: program F V) : PTree.t (globdef F V) :=
  PTree_Properties.of_list p.(prog_defs).

Section DEFMAP.

Variables F V: Type.
Variable p: program F V.

Lemma in_prog_defmap:
  forall id g, (prog_defmap p)!id = Some g -> In (id, g) (prog_defs p).
Proof.
  apply PTree_Properties.in_of_list.
Qed.

Lemma prog_defmap_dom:
  forall id, In id (prog_defs_names p) -> exists g, (prog_defmap p)!id = Some g.
Proof.
  apply PTree_Properties.of_list_dom.
Qed.

Lemma prog_defmap_unique:
  forall defs1 id g defs2,
  prog_defs p = defs1 ++ (id, g) :: defs2 ->
  ~In id (map fst defs2) ->
  (prog_defmap p)!id = Some g.
Proof.
  unfold prog_defmap; intros. rewrite H. apply PTree_Properties.of_list_unique; auto.
Qed.

Lemma prog_defmap_norepet:
  forall id g,
  list_norepet (prog_defs_names p) ->
  In (id, g) (prog_defs p) ->
  (prog_defmap p)!id = Some g.
Proof.
  apply PTree_Properties.of_list_norepet.
Qed.

End DEFMAP.

(** * Generic transformations over programs *)

(** We now define a general iterator over programs that applies a given
  code transformation function to all function descriptions and leaves
  the other parts of the program unchanged. *)

Section TRANSF_PROGRAM.

Variable A B V: Type.
Variable transf: A -> B.

Definition transform_program_globdef (idg: ident * globdef A V) : ident * globdef B V :=
  match idg with
  | (id, Gfun f) => (id, Gfun (transf f))
  | (id, Gvar v) => (id, Gvar v)
  end.

Definition transform_program (p: program A V) : program B V :=
  mkprogram
    (List.map transform_program_globdef p.(prog_defs))
    p.(prog_public)
    p.(prog_main).

End TRANSF_PROGRAM.

(** The following is a more general presentation of [transform_program]:
- Global variable information can be transformed, in addition to function
  definitions.
- The transformation functions can fail and return an error message.
- The transformation for function definitions receives a global context
  (derived from the compilation unit being transformed) as additiona
  argument.
- The transformation functions receive the name of the global as
  additional argument. *)

Local Open Scope error_monad_scope.

Section TRANSF_PROGRAM_GEN.

Variables A B V W: Type.
Variable transf_fun: ident -> A -> res B.
Variable transf_var: ident -> V -> res W.

Definition transf_globvar (i: ident) (g: globvar V) : res (globvar W) :=
  do info' <- transf_var i g.(gvar_info);
  OK (mkglobvar info' g.(gvar_init) g.(gvar_readonly) g.(gvar_volatile)).

Fixpoint transf_globdefs (l: list (ident * globdef A V)) : res (list (ident * globdef B W)) :=
  match l with
  | nil => OK nil
  | (id, Gfun f) :: l' =>
    match transf_fun id f with
      | Error msg => Error (MSG "In function " :: CTX id :: MSG ": " :: msg)
      | OK tf =>
        do tl' <- transf_globdefs l'; OK ((id, Gfun tf) :: tl')
    end
  | (id, Gvar v) :: l' =>
    match transf_globvar id v with
      | Error msg => Error (MSG "In variable " :: CTX id :: MSG ": " :: msg)
      | OK tv =>
        do tl' <- transf_globdefs l'; OK ((id, Gvar tv) :: tl')
    end
  end.

Definition transform_partial_program2 (p: program A V) : res (program B W) :=
  do gl' <- transf_globdefs p.(prog_defs);
  OK (mkprogram gl' p.(prog_public) p.(prog_main)).

End TRANSF_PROGRAM_GEN.

(** The following is a special case of [transform_partial_program2],
  where only function definitions are transformed, but not variable definitions. *)

Section TRANSF_PARTIAL_PROGRAM.

Variable A B V: Type.
Variable transf_fun: A -> res B.

Definition transform_partial_program (p: program A V) : res (program B V) :=
  transform_partial_program2 (fun i f => transf_fun f) (fun i v => OK v) p.

End TRANSF_PARTIAL_PROGRAM.

Lemma transform_program_partial_program:
  forall (A B V: Type) (transf_fun: A -> B) (p: program A V),
  transform_partial_program (fun f => OK (transf_fun f)) p = OK (transform_program transf_fun p).
Proof.
  intros. unfold transform_partial_program, transform_partial_program2.
  assert (EQ: forall l,
              transf_globdefs (fun i f => OK (transf_fun f)) (fun i (v: V) => OK v) l =
              OK (List.map (transform_program_globdef transf_fun) l)).
  { induction l as [ | [id g] l]; simpl.
  - auto.
  - destruct g; simpl; rewrite IHl; simpl. auto. destruct v; auto.
  }
  rewrite EQ; simpl. auto.
Qed.


(** * External functions *)

(** For most languages, the functions composing the program are either
  internal functions, defined within the language, or external functions,
  defined outside.  External functions include system calls but also
  compiler built-in functions.  We define a type for external functions
  and associated operations. *)

Inductive external_function : Type :=
  | EF_external (name: string) (sg: signature)
     (** A system call or library function.  Produces an event
         in the trace. *)
  | EF_builtin (name: string) (sg: signature)
     (** A compiler built-in function.  Behaves like an external, but
         can be inlined by the compiler. *)
  | EF_runtime (name: string) (sg: signature)
     (** A function from the run-time library.  Behaves like an
         external, but must not be redefined. *)
  | EF_vload (chunk: memory_chunk)
     (** A volatile read operation.  If the address given as first argument
         points within a volatile global variable, generate an
         event and return the value found in this event.  Otherwise,
         produce no event and behave like a regular memory load. *)
  | EF_vstore (chunk: memory_chunk)
     (** A volatile store operation.   If the address given as first argument
         points within a volatile global variable, generate an event.
         Otherwise, produce no event and behave like a regular memory store. *)
  | EF_malloc
     (** Dynamic memory allocation.  Takes the requested size in bytes
         as argument; returns a pointer to a fresh block of the given size.
         Produces no observable event. *)
  | EF_free
     (** Dynamic memory deallocation.  Takes a pointer to a block
         allocated by an [EF_malloc] external call and frees the
         corresponding block.
         Produces no observable event. *)
  | EF_memcpy (sz: Z) (al: Z)
     (** Block copy, of [sz] bytes, between addresses that are [al]-aligned. *)
  | EF_annot (kind: positive) (text: string) (targs: list typ)
     (** A programmer-supplied annotation.  Takes zero, one or several arguments,
         produces an event carrying the text and the values of these arguments,
         and returns no value. *)
  | EF_annot_val (kind: positive) (text: string) (targ: typ)
     (** Another form of annotation that takes one argument, produces
         an event carrying the text and the value of this argument,
         and returns the value of the argument. *)
  | EF_inline_asm (text: string) (sg: signature) (clobbers: list string)
     (** Inline [asm] statements.  Semantically, treated like an
         annotation with no parameters ([EF_annot text nil]).  To be
         used with caution, as it can invalidate the semantic
         preservation theorem.  Generated only if [-finline-asm] is
         given. *)
  | EF_debug (kind: positive) (text: ident) (targs: list typ).
     (** Transport debugging information from the front-end to the generated
         assembly.  Takes zero, one or several arguments like [EF_annot].
         Unlike [EF_annot], produces no observable event. *)

(** The type signature of an external function. *)

Definition ef_sig (ef: external_function): signature :=
  match ef with
  | EF_external name sg => sg
  | EF_builtin name sg => sg
  | EF_runtime name sg => sg
  | EF_vload chunk => mksignature (Tptr :: nil) (rettype_of_chunk chunk) cc_default
  | EF_vstore chunk => mksignature (Tptr :: type_of_chunk chunk :: nil) Tvoid cc_default
  | EF_malloc => mksignature (Tptr :: nil) Tptr cc_default
  | EF_free => mksignature (Tptr :: nil) Tvoid cc_default
  | EF_memcpy sz al => mksignature (Tptr :: Tptr :: nil) Tvoid cc_default
  | EF_annot kind text targs => mksignature targs Tvoid cc_default
  | EF_annot_val kind text targ => mksignature (targ :: nil) targ cc_default
  | EF_inline_asm text sg clob => sg
  | EF_debug kind text targs => mksignature targs Tvoid cc_default
  end.

(** Whether an external function should be inlined by the compiler. *)

Definition ef_inline (ef: external_function) : bool :=
  match ef with
  | EF_external name sg => false
  | EF_builtin name sg => true
  | EF_runtime name sg => false
  | EF_vload chunk => true
  | EF_vstore chunk => true
  | EF_malloc => false
  | EF_free => false
  | EF_memcpy sz al => true
  | EF_annot kind text targs => true
  | EF_annot_val kind Text rg => true
  | EF_inline_asm text sg clob => true
  | EF_debug kind text targs => true
  end.

(** Whether an external function must reload its arguments. *)

Definition ef_reloads (ef: external_function) : bool :=
  match ef with
  | EF_annot kind text targs => false
  | EF_debug kind text targs => false
  | _ => true
  end.

(** Equality between external functions.  Used in module [Allocation]. *)

Definition external_function_eq: forall (ef1 ef2: external_function), {ef1=ef2} + {ef1<>ef2}.
Proof.
  generalize ident_eq string_dec signature_eq chunk_eq typ_eq list_eq_dec zeq Int.eq_dec; intros.
  decide equality.
Defined.
Global Opaque external_function_eq.

(** Function definitions are the union of internal and external functions. *)

Inductive fundef (F: Type): Type :=
  | Internal: F -> fundef F
  | External: external_function -> fundef F.

Arguments External [F].

Section TRANSF_FUNDEF.

Variable A B: Type.
Variable transf: A -> B.

Definition transf_fundef (fd: fundef A): fundef B :=
  match fd with
  | Internal f => Internal (transf f)
  | External ef => External ef
  end.

End TRANSF_FUNDEF.

Section TRANSF_PARTIAL_FUNDEF.

Variable A B: Type.
Variable transf_partial: A -> res B.

Definition transf_partial_fundef (fd: fundef A): res (fundef B) :=
  match fd with
  | Internal f => do f' <- transf_partial f; OK (Internal f')
  | External ef => OK (External ef)
  end.

End TRANSF_PARTIAL_FUNDEF.

(** * Register pairs *)

Set Contextual Implicit.

(** In some intermediate languages (LTL, Mach), 64-bit integers can be
  split into two 32-bit halves and held in a pair of registers.
  Syntactically, this is captured by the type [rpair] below. *)

Inductive rpair (A: Type) : Type :=
  | One (r: A)
  | Twolong (rhi rlo: A).

Definition typ_rpair (A: Type) (typ_of: A -> typ) (p: rpair A): typ :=
  match p with
  | One r => typ_of r
  | Twolong rhi rlo => Tlong
  end.

Definition map_rpair (A B: Type) (f: A -> B) (p: rpair A): rpair B :=
  match p with
  | One r => One (f r)
  | Twolong rhi rlo => Twolong (f rhi) (f rlo)
  end.

Definition regs_of_rpair (A: Type) (p: rpair A): list A :=
  match p with
  | One r => r :: nil
  | Twolong rhi rlo => rhi :: rlo :: nil
  end.

Fixpoint regs_of_rpairs (A: Type) (l: list (rpair A)): list A :=
  match l with
  | nil => nil
  | p :: l => regs_of_rpair p ++ regs_of_rpairs l
  end.

Lemma in_regs_of_rpairs:
  forall (A: Type) (x: A) p, In x (regs_of_rpair p) -> forall l, In p l -> In x (regs_of_rpairs l).
Proof.
  induction l; simpl; intros. auto. apply in_app. destruct H0; auto. subst a. auto.
Qed.

Lemma in_regs_of_rpairs_inv:
  forall (A: Type) (x: A) l, In x (regs_of_rpairs l) -> exists p, In p l /\ In x (regs_of_rpair p).
Proof.
  induction l; simpl; intros. contradiction.
  rewrite in_app_iff in H; destruct H.
  exists a; auto.
  apply IHl in H. firstorder auto.
Qed.

Definition forall_rpair (A: Type) (P: A -> Prop) (p: rpair A): Prop :=
  match p with
  | One r => P r
  | Twolong rhi rlo => P rhi /\ P rlo
  end.

(** * Arguments and results to builtin functions *)

Inductive builtin_arg (A: Type) : Type :=
  | BA (x: A)
  | BA_int (n: int)
  | BA_long (n: int64)
  | BA_float (f: float)
  | BA_single (f: float32)
  | BA_loadstack (chunk: memory_chunk) (ofs: ptrofs)
  | BA_addrstack (ofs: ptrofs)
  | BA_loadglobal (chunk: memory_chunk) (id: ident) (ofs: ptrofs)
  | BA_addrglobal (id: ident) (ofs: ptrofs)
  | BA_splitlong (hi lo: builtin_arg A)
  | BA_addptr (a1 a2: builtin_arg A).

Inductive builtin_res (A: Type) : Type :=
  | BR (x: A)
  | BR_none
  | BR_splitlong (hi lo: builtin_res A).

Fixpoint globals_of_builtin_arg (A: Type) (a: builtin_arg A) : list ident :=
  match a with
  | BA_loadglobal chunk id ofs => id :: nil
  | BA_addrglobal id ofs => id :: nil
  | BA_splitlong hi lo => globals_of_builtin_arg hi ++ globals_of_builtin_arg lo
  | BA_addptr a1 a2 => globals_of_builtin_arg a1 ++ globals_of_builtin_arg a2
  | _ => nil
  end.

Definition globals_of_builtin_args (A: Type) (al: list (builtin_arg A)) : list ident :=
  List.fold_right (fun a l => globals_of_builtin_arg a ++ l) nil al.

Fixpoint params_of_builtin_arg (A: Type) (a: builtin_arg A) : list A :=
  match a with
  | BA x => x :: nil
  | BA_splitlong hi lo => params_of_builtin_arg hi ++ params_of_builtin_arg lo
  | BA_addptr a1 a2 => params_of_builtin_arg a1 ++ params_of_builtin_arg a2
  | _ => nil
  end.

Definition params_of_builtin_args (A: Type) (al: list (builtin_arg A)) : list A :=
  List.fold_right (fun a l => params_of_builtin_arg a ++ l) nil al.

Fixpoint params_of_builtin_res (A: Type) (a: builtin_res A) : list A :=
  match a with
  | BR x => x :: nil
  | BR_none => nil
  | BR_splitlong hi lo => params_of_builtin_res hi ++ params_of_builtin_res lo
  end.

Fixpoint map_builtin_arg (A B: Type) (f: A -> B) (a: builtin_arg A) : builtin_arg B :=
  match a with
  | BA x => BA (f x)
  | BA_int n => BA_int n
  | BA_long n => BA_long n
  | BA_float n => BA_float n
  | BA_single n => BA_single n
  | BA_loadstack chunk ofs => BA_loadstack chunk ofs
  | BA_addrstack ofs => BA_addrstack ofs
  | BA_loadglobal chunk id ofs => BA_loadglobal chunk id ofs
  | BA_addrglobal id ofs => BA_addrglobal id ofs
  | BA_splitlong hi lo =>
      BA_splitlong (map_builtin_arg f hi) (map_builtin_arg f lo)
  | BA_addptr a1 a2 =>
      BA_addptr (map_builtin_arg f a1) (map_builtin_arg f a2)
  end.

Fixpoint map_builtin_res (A B: Type) (f: A -> B) (a: builtin_res A) : builtin_res B :=
  match a with
  | BR x => BR (f x)
  | BR_none => BR_none
  | BR_splitlong hi lo =>
      BR_splitlong (map_builtin_res f hi) (map_builtin_res f lo)
  end.

(** Which kinds of builtin arguments are supported by which external function. *)

Inductive builtin_arg_constraint : Type :=
  | OK_default
  | OK_const
  | OK_addrstack
  | OK_addressing
  | OK_all.

(** * static variable rename : Alpha renaming *)

Require Import FinFun.
Require Import Fin.

Record permutation :=
  mkpermu{
      permu : ident -> ident;
      finite : exists n, forall x, Plt n x -> permu x = x;
      (* injective : Injective permu; *)
      (* surjective : Surjective permu *)
      bijective : Bijective permu
}.
  
(* rename ident symmetry property *)

Lemma permutation_trans: forall a1 a2, exists a3, forall x y z, a1.(permu) x = y -> a2.(permu) y = z -> a3.(permu) x = z.
Proof.
  intros. destruct a1. destruct a2.
  simpl.
  assert (finite: exists n, forall x, Plt n x -> (fun x => permu1 (permu0 x)) x = x). { destruct finite0. destruct finite1.
   exists (Pos.max x x0). 
   intros.
   apply Pos.max_lub_lt_iff in H1.
   destruct H1.
   apply H in H1. rewrite H1.
   apply H0 in H2. auto. }
                                                                        assert (bij: Bijective (fun x => permu1 (permu0 x))).                     { unfold Bijective in *. 
   destruct bijective0 as [f1 [? ?]]. destruct bijective1 as [f2 [? ?]].
   exists (fun x => f1 (f2 x)). split;intros.
   generalize (H1 (permu0 x)). intros.
   rewrite H3. apply H.
   generalize (H0 (f2 y)). intros. 
   rewrite H3.
   apply H2. }                                                          exists {| permu:= (fun x => permu1 (permu0 x));
      finite:= finite;                                                       bijective := bij |}.                      
  intros.
  simpl.
  rewrite H. auto.
Qed.  

       
(* special permutation: identity function *)

Definition ident_identity := fun (x:ident) => x.

Definition ident_identity_bijective: Bijective ident_identity.
Proof.
  unfold Bijective.
  exists ident_identity.
  auto.
Qed.

Definition ident_identity_finite : exists n, forall x, Plt n x -> ident_identity x = x.
exists 1%positive.
auto.
Qed.

Program Definition identity_permutation :=
  {| permu := ident_identity;
     finite := ident_identity_finite;
     bijective := ident_identity_bijective |}.

Program Definition compose_permutation (a1 a2: permutation):=
  {| permu := fun id => a2.(permu) (a1.(permu) id) |}.
Next Obligation.
  destruct a1. destruct a2.
  simpl.
  destruct finite0. destruct finite1.
  exists (Pos.max x x0). intros.
  apply Pos.max_lub_lt_iff in H1.
  destruct H1.
  apply H in H1. rewrite H1.
  apply H0 in H2. auto.
Defined.
Next Obligation.
  destruct a1. destruct a2.
  simpl.
  unfold Bijective in *. destruct bijective0 as [g0 [? ?]].
  destruct bijective1 as [g1 [? ?]].
  exists (fun id => g0 (g1 id)).
  split.
  intros. generalize (H1 (permu0 x)). intros. 
  rewrite H3. auto.
  intros. generalize (H0 (g1 y)). intros.
  rewrite H3. auto.
Defined.

Definition inverse_permutation (a1 a2:permutation):=
  forall x, a2.(permu) (a1.(permu) x) = x.
Lemma exists_inverse_permutation : forall (a:permutation),
    exists b, inverse_permutation a b.
Admitted.

Lemma inverse_permutation_sym : forall a b,
    inverse_permutation a b -> inverse_permutation b a.
  Admitted.

(* a general lemma for PTree, hard to prove! *)
Lemma Bijective_Injective {A B: Type}: forall (f: A->B), FinFun.Bijective f -> FinFun.Injective f.
Proof.
  unfold FinFun.Bijective. unfold FinFun.Injective.
  intros.
  destruct H as [g [? ?]].
  eapply f_equal in H0.
  erewrite H in H0.  erewrite H in H0.
  auto.
Qed.



Definition support := list ident.

Class Alpha (P: Type) := 
  { alpha_rename : permutation -> P -> P;
    alpha_rename_refl : forall p, alpha_rename identity_permutation p = p;
    alpha_rename_sym: forall p1 p2 a1 a2 , alpha_rename a1 p1 = p2 -> inverse_permutation a1 a2 ->  alpha_rename a2 p2 = p1;
    alpha_rename_trans: forall p1 p2 p3 a1 a2, alpha_rename a1 p1 = p2 -> alpha_rename a2 p2 = p3 -> alpha_rename (compose_permutation a1 a2) p1 = p3
  }.

(* Class Alpha (P : Type) := { *)
(*   alpha_rename : permutation -> P -> P; *)
(*   alpha_equiv : support -> P -> P -> Prop; *)
(*   alpha_equiv_ref : forall p sup, alpha_equiv sup p p; *)
(*   alpha_equiv_sym : forall p1 p2 sup, alpha_equiv sup p1 p2 -> alpha_equiv sup p2 p1; *)
(*   alpha_equiv_trans : forall p1 p2 p3 sup, alpha_equiv sup p1 p2 -> alpha_equiv sup p2 p3 -> alpha_equiv sup p1 p3 *)
(*   }. *)

Definition max_program_ident {F V : Type} (p: program F V):=
  fold_left Pos.max (map fst p.(prog_defs)) 1%positive.

(* Definition alpha_equiv {F V : Type} {AP : Alpha (program F V)} (p1 p1' : program F V) := *)
(*   forall n , Pos.gt n (max_program_ident p1) -> exists (a: alpha_rename n),forall pid, In pid p1.(prog_public) -> a.(permu) pid = pid /\ alpha_prog a p1 = p1'. *)

(* Next Obligation. *)
(*   destruct a. unfold Bijective in *. destruct bijective0 as [g [? ?]]. *)
(*   simpl. *)
(*   assert (fin: exists n, forall x, Plt n x -> g x = x). *)
(*   { destruct finite0. exists x. intros. *)
(*   generalize (e0 x0);intros. *)
(*   generalize (H (g x0)). intros. *)
(*   generalize (H _ H0). intros. *)
(*   generalize (e x0). intros. rewrite H3 in H4. *)
(*   auto. } *)
(*   assert (bij : Bijective g). *)
(*   { unfold Bijective. *)
(*     exists permu0. *)
(*     split;auto. } *)
(*   exists {| permu:= g; finite:= fin; bijective:= bij|}. *)
(*   simpl. auto.   *)
(* Defined. *)

(** *some properties about map *)
Lemma map_alpha_refl {T: Type} {AT: Alpha T} : forall (l:list T),
    map (alpha_rename identity_permutation) l = l.
Proof.
  intros.
  induction l;simpl;auto.
  erewrite alpha_rename_refl.
  f_equal. auto.
Qed.

Lemma map_alpha_sym {T: Type} {AT: Alpha T} : forall (l1 l2:list T) a1 a2,
    map (alpha_rename a1) l1 = l2 ->
    inverse_permutation a1 a2 ->
    map (alpha_rename a2) l2 = l1.
Proof.
  unfold inverse_permutation.
  intros.
  generalize dependent l1.
  induction l2;intros.
  destruct l1;simpl in *;auto.
  inversion H.
  destruct l1;simpl in *;auto.
  inversion H. inversion H.
  f_equal. 
  eapply alpha_rename_sym.
  auto.
  auto.
  rewrite H3.
  eapply IHl2. auto.
Qed.

Lemma map_alpha_trans {T: Type} {AT: Alpha T} : forall (l1 l2 l3:list T) a1 a2,
    map (alpha_rename a1) l1 = l2 ->
    map (alpha_rename a2) l2 = l3 ->
    map (alpha_rename (compose_permutation a1 a2)) l1 = l3.
Proof.
  induction l1.
  destruct l2;destruct l3;simpl;auto.
  intros. inversion H.
  destruct l2;destruct l3;intros;simpl in *;auto;try inversion H.
  inversion H0.
  f_equal.
  eapply alpha_rename_trans;auto.
  rewrite H2. inversion H0;auto.
  eapply IHl1.
  auto. inversion H0.
  rewrite H3. auto.
Qed.

(* rename ident *)
Program Instance Alpha_ident : Alpha ident :={
  alpha_rename := fun (a:permutation) (x :ident) => a.(permu) x }. 

Global Opaque Alpha_ident.

Program Instance Alpha_list_ident : Alpha (list ident) :=
  { alpha_rename := fun (a: permutation) (l: list ident) => map (alpha_rename a) l } .
Next Obligation.
  apply map_id.
Defined.
Next Obligation.
  Transparent Alpha_ident.
 rewrite map_map.
 unfold inverse_permutation in H0. simpl.
 induction p1.
 auto.
 simpl. rewrite IHp1. rewrite (H0 a).
 auto. 
Defined.
Next Obligation.
  induction p1.
  auto.
  simpl. rewrite IHp1.
  auto.
Defined.

Global Opaque Alpha_list_ident.

(* unit renaming *)

Program Instance Alpha_unit : Alpha unit :=
  { alpha_rename := fun a x => x;
  }.

Global Opaque Alpha_unit.


Lemma permutation_bijective : forall a, exists a', forall x y, alpha_rename a x = y -> alpha_rename a' y = x.
Proof.
  unfold alpha_rename.
  Transparent Alpha_ident.
  simpl.
  intros.
  destruct a eqn:Ha.
  simpl in *.
  unfold Bijective in *.
  destruct bijective0 as [permu' [H1 H2]].
  (* permu' is finite *)
  assert (finite: exists n, forall x, Plt n x -> permu' x = x).
  { destruct finite0. 
    exists x.
    intros.
    apply e in H.
    generalize (H1 x0). intro.
    rewrite H in H0.
    auto. }
  (* permu' is bijective *)
  assert (bijective: Bijective permu'). 
  { unfold Bijective. 
    exists permu0.
    split.
    intros.
    generalize (H2 x). intro. auto.
    intros.
    generalize (H1 y). intro. auto. }

  exists {| permu:= permu';
       finite:= finite;
       bijective:= bijective |}.
  simpl. intros.
  rewrite <- H.
  auto.
Qed.


(** *rename buintin argument *)
Fixpoint alpha_rename_builtin_arg {A: Type} (a: permutation) (ba: builtin_arg A) :=
  match ba with
  | BA_loadglobal m id ofs => BA_loadglobal m (alpha_rename a id) ofs
  | BA_addrglobal id ofs => BA_addrglobal (alpha_rename a id) ofs
  | BA_splitlong a1 a2 => BA_splitlong (alpha_rename_builtin_arg a a1) (alpha_rename_builtin_arg a a2)
  | BA_addptr a1 a2 => BA_addptr (alpha_rename_builtin_arg a a1) (alpha_rename_builtin_arg a a2)
  | _ => ba 
  end.

Program Instance Alpha_builtin_arg {A: Type} : Alpha (builtin_arg A) :=
  { alpha_rename := alpha_rename_builtin_arg }.
Next Obligation.
  induction p;simpl;auto;rewrite IHp1;rewrite IHp2;auto.
Defined.
Next Obligation.
  unfold inverse_permutation in H0.
  induction p1;simpl;auto;try rewrite H0;auto.
  1-2 : rewrite IHp1_1;rewrite IHp1_2;auto.
Defined.
Next Obligation.
  induction p1;simpl;auto.
  1-2 : rewrite IHp1_1;rewrite IHp1_2;auto.
Defined.

Global Opaque Alpha_builtin_arg.

(* renaming program, we have Context AF which indicate F has alpha_equiv property *)

(* rename function definition *)
Definition alpha_rename_fundef {F: Type} {AF: Alpha F} (a: permutation) (fd: fundef F):=
  match fd with
  | Internal f => Internal (alpha_rename a f)
  | _ => fd
  end.

Program Instance Alpha_fundef {F: Type} {AF: Alpha F} : Alpha (fundef F) := 
  { alpha_rename := alpha_rename_fundef
  }.                                                               
Next Obligation.
  destruct p;simpl.
  destruct AF.
  unfold alpha_rename in *.
  rewrite (alpha_rename_refl0 f).
  auto. auto.
Defined.
Next Obligation.
  destruct p1;simpl;auto.
  (* internal *)
  destruct AF.
  unfold alpha_rename in *;simpl in *.
  assert (alpha_rename0 a1 f = alpha_rename0 a1 f) by auto.
  generalize (alpha_rename_sym0 f (alpha_rename0 a1 f) _ _ H H0).
  intros. rewrite H1.
  auto.
Defined.
Next Obligation.
  destruct p1;simpl;auto.
  (* internal *)
  destruct AF.
  unfold alpha_rename in *;simpl in *.
  rewrite (alpha_rename_trans0 f (alpha_rename0 a1 f) (alpha_rename0 a2 (alpha_rename0 a1 f)) _ _) by auto.
  auto.
Defined.

Global Opaque Alpha_fundef.
  (* variable renaming *)

Definition alpha_rename_initdata (a: permutation) (i : init_data) :=
  match i with
  | Init_addrof id ofs => Init_addrof (alpha_rename a id) ofs
  | _ => i
  end.

Program Instance Alpha_initdata : Alpha init_data :=
  { alpha_rename := alpha_rename_initdata }.
Next Obligation.
  destruct p;auto.
Defined.
Next Obligation.
  unfold inverse_permutation in H0.
  destruct p1;simpl;auto.
  erewrite H0.
  auto.
Defined.
Next Obligation.
  destruct p1;simpl;auto.
Defined.

Global Opaque Alpha_initdata.

Definition alpha_rename_vardef {V: Type} {AV: Alpha V} (a: permutation) (v: globvar V) :=
  {| gvar_info := alpha_rename a v.(gvar_info);
     gvar_init := map (alpha_rename a) v.(gvar_init);
     gvar_readonly := v.(gvar_readonly);
     gvar_volatile := v.(gvar_volatile) |}.

Program Instance Alpha_vardef {V: Type} {AV: Alpha V} : Alpha (globvar V) :=
  { alpha_rename := alpha_rename_vardef;
  }.
Next Obligation.
  
  unfold alpha_rename_vardef.
  destruct p;simpl.
  erewrite map_alpha_refl.
  destruct AV.
  unfold alpha_rename in *.
  rewrite (alpha_rename_refl0 gvar_info0).
  auto.  
Defined.
Next Obligation.
  unfold alpha_rename_vardef.
  destruct p1;simpl.
  f_equal.   
  destruct AV. 
  unfold alpha_rename in *.
  rename gvar_info0 into f.
  assert (alpha_rename0 a1 f = alpha_rename0 a1 f) by auto.
  generalize (alpha_rename_sym0 f (alpha_rename0 a1 f) _ _ H H0).
  intros. rewrite H1.
  auto.
  eapply map_alpha_sym;auto.
Defined.
Next Obligation.
  unfold alpha_rename_vardef.
  destruct p1;simpl.
  f_equal.
  destruct AV. 
  unfold alpha_rename in *.
  rename gvar_info0 into f.
  rewrite (alpha_rename_trans0 f (alpha_rename0 a1 f) (alpha_rename0 a2 (alpha_rename0 a1 f)) _ _) by auto.
  auto.
  eapply map_alpha_trans;auto.
Defined.

Global Opaque Alpha_vardef.

(* renaming global definition *)

Definition alpha_rename_def {F V: Type} {AF: Alpha F} {AV: Alpha V} (a: permutation) (gd: globdef F V) :=
  match gd with
  | Gfun f => Gfun (alpha_rename a f)
  | Gvar v => Gvar (alpha_rename a v)
  end.

Program Instance Alpha_def {F V: Type} {AF: Alpha F} {AV: Alpha V} : Alpha (globdef F V) := 
 { alpha_rename := alpha_rename_def;
 }.
Next Obligation.
  destruct p;simpl in *;auto;
    unfold alpha_rename_vardef;simpl;
  rewrite alpha_rename_refl;auto.
Defined.
Next Obligation.
  destruct p1;simpl;
  erewrite alpha_rename_sym;auto.
Defined.
Next Obligation.
  destruct p1;simpl;
  erewrite alpha_rename_trans;auto. 
Defined.

Global Opaque Alpha_def.


Definition alpha_rename_prog {F V: Type} {AF: Alpha F} {AV: Alpha V} (a: permutation) (p: program F V) :=
  let idefs := map (fun (d:ident*globdef F V) => (alpha_rename a (fst d), alpha_rename a (snd d))
                   ) p.(prog_defs) in
  {| prog_defs := idefs;
     prog_public := map (alpha_rename a) p.(prog_public);
     prog_main := (alpha_rename a p.(prog_main))
 |}.

Program Instance Alpha_prog (F: Type) (V: Type) {AF: Alpha F} {AV: Alpha V} : Alpha (program F V) :=
  { alpha_rename:= alpha_rename_prog;
  }.
Next Obligation.
  destruct p. unfold alpha_rename_prog.
  simpl.
  induction prog_defs0.
  - simpl. induction prog_public0;auto;simpl.
    + injection IHprog_public0 as H. rewrite H in *.
      unfold ident_identity. auto.
  - induction prog_public0.
    + inversion IHprog_defs0.
      destruct a. simpl. rewrite alpha_rename_refl.
      unfold ident_identity in *. simpl in H0.
      rewrite H0. rewrite H0. auto.
    + inversion IHprog_defs0.
      destruct a. simpl. unfold ident_identity.
      rewrite alpha_rename_refl.
      unfold ident_identity in *. simpl in H0.
      rewrite H0. rewrite H0. rewrite H1. rewrite H1.  auto.
Defined.
Next Obligation.
  destruct p1. unfold alpha_rename_prog.
  simpl. unfold inverse_permutation in H0.
  rewrite H0.
  induction prog_defs0.
  - induction prog_public0;auto;simpl.
    + injection IHprog_public0 as H. rewrite H in *.
       rewrite (H0 _). auto. 
  - induction prog_public0.
    + simpl in *. destruct a. injection IHprog_defs0.
      intros. rewrite H.
      erewrite alpha_rename_sym by auto.
      rewrite H0.
      auto.
    + simpl in *. destruct a.  injection IHprog_defs0.
      intros. rewrite H.
      erewrite alpha_rename_sym by auto.
      rewrite H0.
      rewrite H2. rewrite H0.
      auto. 
Defined.
Next Obligation.
  destruct p1. unfold alpha_rename_prog.
  simpl.
  induction prog_defs0.
  - induction prog_public0;auto;simpl.
    + injection IHprog_public0 as H. rewrite H in *.
      auto.
  - induction prog_public0.
    + simpl in *. destruct a. injection IHprog_defs0.
      intros. rewrite H.
      erewrite alpha_rename_trans by auto.
      auto.
    + simpl in *. destruct a. injection IHprog_defs0.
      intros. rewrite H. rewrite H0.
      erewrite alpha_rename_trans by auto.
      auto.
Defined.


Global Opaque Alpha_prog.



Section ALPHA_EQUIV.
  Context {P: Type} {AP: Alpha P}.
  Context (sup: support).
  Definition alpha_equiv (p1 p2: P) :=
    exists a, (forall x, In x sup -> a.(permu) x = x) /\ alpha_rename a p1 = p2.

  Transparent AP.
  
  Theorem alpha_equiv_refl : forall p,
      alpha_equiv p p.
  Proof.
    unfold alpha_equiv.
    destruct AP.
    simpl in *.
    intros. exists identity_permutation. auto.
  Qed.

  Theorem alpha_equiv_sym : forall p1 p2,
      alpha_equiv p1 p2 -> alpha_equiv p2 p1.
  Proof.
    unfold alpha_equiv.
    intros. destruct H. simpl in *.
    intros.
    destruct x.
    unfold Bijective in *. destruct bijective0 as [g [? ?]].
    assert (fin: exists n, forall x, Plt n x -> g x = x).
    { destruct finite0 as [n ?].
      exists n. intros.
      generalize (e (g x)). apply e1 in H0.
      generalize (e x). intros. rewrite H0 in H1.
      auto. }
    assert (bij: Bijective g).
    { unfold Bijective. exists permu0. split;auto. }
    exists {| permu:= g; finite:= fin; bijective:= bij|}.
    destruct AP. simpl.
    set (a1 := {| permu := g; finite := fin; bijective := bij |}).
    assert (inverse_permutation {|
        permu := permu0;
        finite := finite0;
        bijective := ex_intro
                       (fun g : ident -> ident =>
                        (forall x : ident, g (permu0 x) = x) /\
                        (forall y : ident, permu0 (g y) = y)) g
                       (conj e e0) |} a1).
    { unfold inverse_permutation. simpl.
    auto. }
    split;auto. destruct H.
    intros. apply H in H2.
    unfold inverse_permutation in *.
    generalize (H0 x). intros.
    rewrite H2 in H3. simpl in H3.
    auto.
    eapply alpha_rename_sym0.
    apply H.
    apply H0.
  Qed.

  Theorem alpha_equiv_trans : forall p1 p2 p3,
      alpha_equiv p1 p2 -> alpha_equiv p2 p3 -> alpha_equiv p1 p3.
  Proof.
    unfold alpha_equiv. intros.
    destruct H. destruct H0.
    destruct AP.
    exists (compose_permutation x x0).
    split;auto. intros.
    destruct H. destruct H0.
    unfold compose_permutation. simpl.
    erewrite H.
    erewrite H0.
    auto. auto. auto.
    eapply alpha_rename_trans0.
    apply H. apply H0.
    Qed.
                   
End ALPHA_EQUIV.

(* Section ALPHA_PROPERTY. *)
(* Context {F V: Type} {AF: Alpha F} {AV: Alpha V}. *)
(* Context {AP: Alpha (program F V)}. *)


(* Lemma alpha_sup_exchange: forall p1 p2, alpha_equiv p1.(prog_public) p1 p2 <-> alpha_equiv p2.(prog_public) p1 p2. *)
(*   Transparent Alpha_prog. *)
(*   split;simpl. *)
(*   intros. destruct H as [a [? ?]]. destruct AP. *)
(*   exists a. split;auto. *)
(*   unfold alpha_rename_prog in H0. *)
(*   destruct p1. destruct p2. simpl in *. *)
(*   inversion H0. *)
(*   subst. *)
(*   auto. *)
  
(*   intros. destruct H as [a [? ?]]. *)
(*   exists a. split;auto. *)
(*   unfold alpha_rename_prog in H0. *)
(*   destruct p1. destruct p2. simpl in *. *)
(*   inversion H0. *)
(*   subst. *)
(*   auto. *)
(* Qed. *)

(* Lemma alpha_prog_public: forall p1 p2 sup, alpha_equiv sup p1 p2 -> p1.(prog_public) = p2.(prog_public). *)
(*   Transparent Alpha_prog. *)
(*   simpl. *)
(*   unfold alpha_rename_prog. *)
(*   destruct p1. destruct p2. simpl. *)
(*   intros. destruct H as [? [? ?]]. *)
(*   inversion H0. auto. *)
(* Qed. *)


(* (* (* alpha and link commute *) *) *)
(* (* Class AlphaLink {P: Type} {LP: Linker P} {AP: Alpha P} (get_sup: P -> list ident):= *) *)
(* (*   alpha_link: *) *)
(* (*     forall p1 p2 p1' p2' p p', alpha_equiv (get_sup p1) p1 p1' -> alpha_equiv (get_sup p2) p2 p2' -> link p1 p2 = Some p -> link p1' p2' = Some p' -> alpha_equiv (get_sup p) p p'. *) *)


(* End ALPHA_PROPERTY. *)


(* alpha and tranf commute *)
Class TransfAlpha {S T: Type} {AS: Alpha S} {AT: Alpha T} (transf: S -> T -> Prop) (g1: S -> support) (g2: T -> support) :=
  transf_alpha:
    forall s s' t,
      alpha_equiv (g1 s) s s' ->
      transf s t ->
      exists t', transf s' t' /\ alpha_equiv (g2 t) t t'.


Lemma transform_partial_program_alpha {A B V: Type} {ALA: Alpha A} {ALB: Alpha B} {ALV: Alpha V}:
  forall  (transf_fun: A -> res B) (p p': program A V) (tp tp': program B V) ,
    (forall a b permu, transf_fun a = OK b ->
                  transf_fun (alpha_rename permu a) = OK (alpha_rename permu b)) ->
    alpha_equiv (p.(prog_main) :: p.(prog_public)) p p' ->
    transform_partial_program transf_fun p = OK tp ->
    transform_partial_program transf_fun p' = OK tp' ->
    alpha_equiv (tp.(prog_main) :: tp.(prog_public)) tp tp'.
Proof.
  (* destruct p. destruct p'. destruct tp. destruct tp'. *)
  unfold alpha_equiv.
  unfold transform_partial_program.
  unfold transform_partial_program2.
  intros.
  monadInv H1. monadInv H2. 
  destruct H0 as [a [? ?]].
  exists a. simpl. split.
  - simpl in H0. auto.
  - Transparent Alpha_prog Alpha_def.
    simpl. unfold alpha_rename_prog.
    simpl. f_equal.
    + rewrite <- H1 in *.      
      destruct p.
      simpl in *. clear H1.
      generalize dependent x.
      generalize dependent x0.
      
      induction prog_defs0;intros.
      * simpl in *.
        simpl in EQ0. monadInv EQ0.
        monadInv EQ. simpl. auto.
      * simpl in *.
        destruct a0. simpl in *.        
        destruct g. simpl in *.
        -- destruct (transf_fun f) eqn:TF;try congruence.
           destruct (transf_fun (alpha_rename a f)) eqn:TF';try congruence.
           monadInv EQ. monadInv EQ0.
           simpl. f_equal.
           ++ eapply H in TF.
              rewrite TF' in TF. monadInv TF.
              auto.
           ++ eapply IHprog_defs0.
              auto. auto.           
        -- simpl in *.
           monadInv EQ0.
           monadInv EQ.
           simpl. f_equal.
           eapply IHprog_defs0. auto.
           auto.
    + simpl in H0.
      rewrite <- H1 in *. 
      simpl. auto.
    + rewrite <- H1 in *. 
      simpl. auto.
Qed.

(** *General Properties for PTree *)

(* some general lemma for PTree *)
(* a general lemma for list *)
Lemma in_list_first {A: Type} (Dec: forall (x y : A), {x=y} + {x<>y}):  forall (a:A) l,
    In a l ->
    exists l1 l2, l = l1 ++ a :: l2 /\ ~In a l1.
Proof.
  intros.
  induction l.
  simpl in H. contradiction.
  simpl in H. destruct H.
  exists (@nil A). exists l. simpl. rewrite H. auto.
  destruct (Dec a a0).
  exists (@nil A). exists l. simpl. rewrite e. auto.
  apply IHl in H.
  destruct H as [l1 [l2 [? ?]]].
  exists (a0::l1). exists l2.
  rewrite H. simpl. split. auto.
  red. intros. destruct H1.
  subst;congruence.
  contradiction.
Qed.


Lemma in_list_last {A: Type} (Dec: forall (x y : A), {x=y} + {x<>y}) : forall (a:A) l,
    In a l ->
    exists l1 l2, l = l1 ++ a :: l2 /\ ~In a l2.
Proof.
  intros.
  eapply in_rev in H.
  eapply (in_list_first) in H;auto.
  destruct H as [l1 [l2 [? ?]]].
  exists (rev l2). exists (rev l1).
  eapply rev_eq_app in H.
  rewrite H. simpl.
  rewrite<-app_assoc. simpl.
  split;auto.
  red. intros. apply in_rev in H1. contradiction.
Qed.

Lemma list_app_last {A: Type}: forall (l:list A) n , 
    length l = S n ->
    exists a l1 , l = l1 ++ (a::nil)  /\ length l1 = n. 
Proof.
  intros.
  rewrite <- rev_length in H.
  destruct (rev l) eqn: Rev.
  simpl in H. congruence.
  exists a ,(rev l0).
  simpl in H. inversion H. 
  split. assert (rev (rev l) = rev (a::l0)). f_equal. auto.
  rewrite rev_involutive in H0.
  rewrite H0. simpl. auto.
  apply rev_length.
Qed.

Lemma PTree_fold_last_position_aux {V: Type} : forall n l b k (v:V),
    length l = n ->
    b ! k = None ->
    (fold_left (fun (m : PTree.t V) (k_v : PTree.elt * V) =>
                  PTree.set (fst k_v) (snd k_v) m) 
               l b) ! k = Some v ->
    exists l1 l2, l = l1 ++ (k,v) :: l2 /\ ~ In k (map fst l2). 
Proof.
  induction n.
  - simpl. intros.
    rewrite length_zero_iff_nil in H. subst.
    simpl in *. rewrite H0 in H1. inversion H1.
  - intros.
    apply list_app_last in H.
    destruct H as [a [l1 [? ?]]].
    subst. erewrite  fold_left_app in H1.
    simpl in H1.
    destruct a. simpl in *.
    (* discuss whether a equal to (k,v) *)
    destruct (Pos.eq_dec e k).
    + subst. erewrite PTree.gss in H1.
      inversion H1. exists l1, nil.
      simpl. auto.
    + erewrite PTree.gso in H1;auto.
      eapply IHn in H1.
      destruct H1 as [l2 [l3 [? ?]]].
      subst.
      exists l2,(l3 ++ (e,v0)::nil).
      rewrite <- app_assoc. split;auto.
      red. intros. apply H1.
      rewrite map_app in H.
      eapply in_app in H.
      destruct H. auto. simpl in H. destruct H;auto.
      congruence. contradiction.
      auto.
      auto.
Qed.

Lemma PTree_of_list_last_position {V: Type} : forall l k (v:V),
    (PTree_Properties.of_list l) ! k = Some v ->
    exists l1 l2, l = l1 ++ (k,v) :: l2 /\ ~ In k (map fst l2).
Proof.
  unfold PTree_Properties.of_list.
  intros.
  eapply PTree_fold_last_position_aux.
  auto.
  apply PTree.gempty.
  auto.
Qed.




Lemma PTree_of_list_map {V: Type} : forall (f: positive -> positive) (g: V -> V) (l:list (positive * V)) k (v: V),
    (FinFun.Bijective f) ->
    (PTree_Properties.of_list l) ! k = Some v ->
    (PTree_Properties.of_list
       (map (fun (ele:(positive*V)) =>  (f (fst ele), g (snd ele))) l)) ! (f k) = Some (g v).
Proof.
  intros.
  induction l.
  - unfold PTree_Properties.of_list in *.
    simpl in *.
    erewrite PTree.gempty in H0.
    inversion H0.
  - intros.
    (* key idea : discuss whether a in l or not, because of_list take the last occurence *)
    destruct (in_dec Pos.eq_dec k (map fst l)).
    + apply PTree_of_list_last_position in H0.
      destruct H0 as [l1 [l2 [? ?]]].
      destruct l1.
      * rewrite H0. simpl in *.
        rewrite <- (app_nil_l ((f k, g v)
      :: map (fun ele : positive * V => (f (fst ele), g (snd ele)))
           l2)).
        eapply PTree_Properties.of_list_unique.
        erewrite map_map. simpl.
        (* f is Bijective *)
        unfold FinFun.Bijective in H. destruct H as [f1 [? ?]].
        red. intros. eapply (in_map f1) in H3.
        erewrite H in H3. erewrite map_map in H3.
        apply H1. erewrite <- map_id. (* use map_id to solve lta conversion *)
        erewrite map_map. clear H0 IHl H1.
        induction l2.
        simpl in H3. auto.
        simpl in *. destruct H3.
        left. erewrite H in H0. auto.
        right. apply IHl2. auto.
      * simpl in H0. injection H0. intros;subst.
        clear H0. rewrite app_comm_cons.
        rewrite map_app. simpl.
        rewrite app_comm_cons.
        eapply PTree_Properties.of_list_unique.
        erewrite map_map. simpl.
        unfold FinFun.Bijective in H. destruct H as [f1 [? ?]].
        red. intros. eapply (in_map f1) in H2.
        erewrite H in H2. erewrite map_map in H2.
        apply H1. erewrite <- map_id. (* use map_id to solve lta conversion *)
        erewrite map_map. clear IHl H1 i.
        induction l2.
        simpl in H2. auto.
        simpl in *. destruct H2.
        left. erewrite H in H1. auto.
        right. apply IHl2. auto.
    + eapply PTree_Properties.in_of_list in H0. simpl in H0.
      destruct H0.
      * subst.
        assert (~ In (f k) (map f (map fst l))).
        { erewrite map_map.
          red.
          erewrite in_map_iff.
          intros. destruct H0 as [x [? ?]].
          apply Bijective_Injective in H. unfold FinFun.Injective in H.
          eapply H in H0.
          apply (in_map fst) in H1. rewrite H0 in H1. auto.
        }
        simpl. rewrite <- (app_nil_l ((f k, g v) :: map (fun ele : positive * V => (f (fst ele), g (snd ele))) l)).
        eapply PTree_Properties.of_list_unique.
        erewrite map_map. erewrite map_map in H0.
        simpl. auto.       
      * apply (in_map fst) in H0.
        simpl in H0. contradiction.
Qed.

        
(* a more general lemma, need to be moved to AST.v *)
Lemma rename_program_remain_gd {F V: Type} {AF: Alpha F} {AV: Alpha V}: forall (p:AST.program F V) id gd a,
    (prog_defmap p) ! id = Some gd ->
    (prog_defmap (alpha_rename a p)) ! (alpha_rename a id) = Some (alpha_rename a gd).
Proof.
  unfold prog_defmap.
  Transparent Alpha_prog.
  destruct p. simpl in *.
  intros. eapply PTree_of_list_map.
  destruct a. simpl. auto.
  auto.
Qed.
