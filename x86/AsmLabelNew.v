(* ******************** *)
(* Author: Zhenguo Yin  *)
(* Date:   Aug 30, 2020 *)
(* ******************** *)

Require Import Coqlib Integers AST Maps.
Require Import UserAsm.
Require Import Errors.

(** Set Current Function *)
Parameter set_current_function : function -> res unit.
(** Generate New Lable *)
Parameter new_label : unit -> label.
