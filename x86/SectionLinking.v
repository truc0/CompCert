(* *******************  *)
(* Author: Jinhua Wu    *)
(* Date:   Sep 16, 2019 *)
(* Last updated: Feb 1, 2022 by Jinhua Wu *)
(* *******************  *)

(** * Linking sections of same type *)

Require Import Coqlib Integers AST Maps.
Require Import Asm.
Require Import Errors.
Require Import Memtype.
Require Import RelocProgram.
Require Import SymbolString.
Import ListNotations.

Set Implicit Arguments.

Local Open Scope error_monad_scope.
Local Open Scope Z_scope.

(** merge sections *)

Definition link_section (sec1 sec2: section) : res (ident * section) :=
  match sec1, sec2 with
  | sec_text c1, sec_text c2 =>
    let id := create_section_ident tt in
    OK (id, sec_text (c1 ++ c2))
  | sec_data d1, sec_data d2 =>
    let id := create_section_ident tt in
    OK (id, sec_data (d1 ++ d2))
  | sec_rodata d1, sec_rodata d2 =>
    let id := create_section_ident tt in
    OK (id, sec_rodata (d1 ++ d2))
  | sec_bytes b1, sec_bytes b2 =>
    let id := create_section_ident tt in
    OK (id, sec_bytes (b1 ++ b2))
  | _, _ => Error (msg "link sections of different type")
  end.

Definition transl_sectable (id1 id2: ident) (sec1 sec2: section) (sectbl: sectable) : res (ident * sectable) :=
  do idsec <- link_section sec1 sec2;
  let (id, sec) := idsec in
  let tbl1 := PTree.remove id1 sectbl in
  let tbl2 := PTree.remove id2 tbl1 in
  OK (id, PTree.set id sec tbl2).


Definition transl_relocentry (ofs:Z) (e:relocentry) :=
  Build_relocentry (e.(reloc_offset) + ofs) e.(reloc_type) e.(reloc_symb) e.(reloc_addend).  

Definition link_reloctable (ofs: Z) (rel1 rel2: reloctable) : reloctable :=
  let rel2' := map (transl_relocentry ofs) rel2 in
  rel1++rel2'.

Section WITH_NEW_SYMB.
  Variable e1 e2 : symbentry.
  Variable new_symb: ident.

Definition transl_relocmap (id1 id2 : ident) (reloc_map : reloctable_map) :=
  match  reloc_map ! id1, reloc_map ! id2 with
  | Some tbl1, Some tbl2 =>
    let ofs := e1.(symbentry_size) in
    let tbl := link_reloctable ofs tbl1 tbl2 in
    PTree.set new_symb tbl reloc_map
  | None, Some tbl2 =>
    let ofs := e1.(symbentry_size) in
    let tbl := link_reloctable ofs [] tbl2 in
    PTree.set new_symb tbl reloc_map
  | _, _ => reloc_map
  end.

Definition transl_symbtbl (id1 id2 :ident) (symbtbl: symbtable) : symbtable :=
    let e2' := Build_symbentry e2.(symbentry_bind) e2.(symbentry_type) e1.(symbentry_size) (secindex_normal new_symb) e2.(symbentry_size) in
    let e1' := Build_symbentry e1.(symbentry_bind) e1.(symbentry_type) e1.(symbentry_value) (secindex_normal new_symb) e1.(symbentry_size) in
    let e := Build_symbentry e1.(symbentry_bind) e1.(symbentry_type) 0 (secindex_normal new_symb) (e1.(symbentry_size) + e2.(symbentry_size)) in
    let tbl1 := PTree.set id1 e1' symbtbl in
    let tbl2 := PTree.set id2 e2' tbl1 in
    PTree.set new_symb e tbl2.
  
