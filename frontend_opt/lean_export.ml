open Mtyped
module Nt = Normalty.Frontend
open Item
open Sugar
open To_prop

let lean_layout_ty = function
  | Nt.Ty_bool -> "Bool"
  | Nt.Ty_int -> "Int"
  | Nt.Ty_unit -> "Unit"
  | Nt.Ty_constructor (name, _) -> name
  | ty ->
      _die_with [%here]
        (spf "lean_layout_ty: unsupported type '%s'" (Nt.layout ty))

let leansetting =
  {
    sym_true = "True";
    sym_false = "False";
    sym_and = " ∧ ";
    sym_or = " ∨ ";
    sym_not = "¬";
    sym_implies = "→";
    sym_iff = "↔";
    sym_forall = "∀ ";
    sym_exists = "∃ ";
    layout_typedid = (fun x -> spf "(%s : %s)" x.x (lean_layout_ty x.ty));
    layout_mp = (function "==" -> "=" | x -> x);
  }

let layout_prop_to_lean = layout_prop_ leansetting

let layout_item_to_lean = function
  | MAxiom { name; prop } ->
      spf "@[grind]\ntheorem %s : %s := by grind" name
        (layout_prop_to_lean prop)
  | _ -> _die_with [%here] "not implemented"
