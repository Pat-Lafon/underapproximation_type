open Item
open Sugar
open To_prop

let coqsetting =
  {
    sym_true = "True";
    sym_false = "False";
    sym_and = " /\\ ";
    sym_or = " \\/ ";
    sym_not = "~";
    sym_implies = "->";
    sym_iff = "<->";
    sym_forall = "forall ";
    sym_exists = "exists ";
    layout_typedid = (fun x -> x.x);
    layout_mp = (function "==" -> "=" | x -> x);
  }

let layout_prop_to_coq = layout_prop_ coqsetting

let layout_item_to_coq = function
  | MAxiom { name; prop } ->
      spf "Lemma %s : %s. Proof. Qed. Hint Resolve %s: core." name
        (layout_prop_to_coq prop) name
  | _ -> _die_with [%here] "not implemented"
