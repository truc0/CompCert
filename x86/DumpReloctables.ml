open Camlcoq
open RelocProgram
(* open Errors *)  (* update: to avoid conflict in newer ocaml versions *)

let dump_reloctype rt =
  match rt with
  | Coq_reloc_abs  -> "abs"
  | Coq_reloc_rel  -> "rel"
  | Coq_reloc_null -> "null"

let dump_relocentry re =
  Format.printf "[ofs = %d, type = %s, symb = %d, addend = %d\n"
    (Z.to_int (re.reloc_offset))
    (dump_reloctype (re.reloc_type))
    (N.to_int (re.reloc_symb))
    (Z.to_int (re.reloc_addend))
    (* update: extraction no longer produces record projection constants *)

let dump_reloctable rtbl =
  List.iter dump_relocentry rtbl

let dump_reloctables rmap =
  Format.printf "RELOC CODE:\n"; dump_reloctable (rmap.reloctable_code);
  Format.printf "RELOC DATA:\n"; dump_reloctable (rmap.reloctable_data);
  (* let nil : Errors.errmsg = [] in *)
  Errors.Error []
