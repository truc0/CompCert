(* *******************  *)
(* Author: Yuting Wang  *)
(* Date:   Oct 16, 2019 *)
(* *******************  *)

(** * Check if the definition is a local or global one *)

(* open Printf *)
open Camlcoq
open C2C
open AST

(* https://caml.inria.fr/pub/old_caml_site/FAQ/FAQ_EXPERT-eng.html#strings *)
let explode s =
  let rec exp i l =
    if i < 0 then l else exp (i - 1) (s.[i] :: l) in
  exp (String.length s - 1) []

let is_def_builtin (id: ident) : bool =
  try
    let name = Hashtbl.find string_of_atom id in
    let ename = explode name in
    (List.mem_assoc ename Builtins0.standard_builtin_table) || (List.mem_assoc ename Builtins1.platform_builtin_table)
  with
  | Not_found ->
    try    (* workaround for different ocaml versions *)
      let name = Hashtbl.find string_of_atom id in
      let ename = explode name in
      List.mem_assoc ename Builtins1.platform_builtin_table
    with
    | Not_found ->
       false

let is_def_string_literal (id: ident) : bool =
  let lit_sec = [Sections.for_stringlit()] in
  try 
    let a = Hashtbl.find decl_atom id in
    a.a_sections = lit_sec
  with
  | Not_found ->
     false

let is_def_static (id: ident) : bool =
  atom_is_static id
