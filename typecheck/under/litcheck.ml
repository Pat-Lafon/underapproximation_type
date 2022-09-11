open Languages

(* open Abstraction *)
(* open Sugar *)

let lit_to_prop_lit (ty, x) =
  let open UL in
  let open Autov.Prop in
  match x with
  | ConstB b -> ACbool b
  | ConstI i -> ACint i
  | Var id -> AVar { ty; x = id }
