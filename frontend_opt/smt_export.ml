module Nt = Normalty.Frontend
open Prop
open To_lit
open Sugar
open Zzdatatype.Datatype

let smt_layout_ty = function
  | Nt.Ty_bool -> "Bool"
  | Nt.Ty_int -> "Int"
  | Nt.Ty_constructor _ -> "Int"
  | _ -> _die_with [%here] "unimp"

let rec layout_to_smtlib2 = function
  | Lit lit -> layout_typed_lit_to_smtlib2 lit
  | Implies (p1, p2) ->
      spf "(=> %s %s)" (layout_to_smtlib2 p1) (layout_to_smtlib2 p2)
  | And [ p ] -> layout_to_smtlib2 p
  | Or [ p ] -> layout_to_smtlib2 p
  | And ps -> spf "(and %s)" @@ List.split_by " " layout_to_smtlib2 ps
  | Or ps -> spf "(or %s)" @@ List.split_by " " layout_to_smtlib2 ps
  | Not p -> spf "(not %s)" (layout_to_smtlib2 p)
  | Iff (p1, p2) ->
      spf "(= %s %s)" (layout_to_smtlib2 p1) (layout_to_smtlib2 p2)
  | Ite _ -> _die_with [%here] "unimp"
  | Forall { qv; body } ->
      spf "(forall ((%s %s)) %s)" qv.x (smt_layout_ty qv.ty)
        (layout_to_smtlib2 body)
  | Exists { qv; body } ->
      spf "(exists ((%s %s)) %s)" qv.x (smt_layout_ty qv.ty)
        (layout_to_smtlib2 body)
