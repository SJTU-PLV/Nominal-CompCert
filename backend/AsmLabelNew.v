Require Import Coqlib Integers AST Maps.
Require Import Asm.
Require Import Errors.

(** Set Current Function *)
Parameter set_current_function : function -> res unit.
(** Generate New Lable *)
Parameter new_label : unit -> label.
