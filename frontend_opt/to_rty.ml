open Ocaml5_parser
open Parsetree
open Pprintast
open Mtyped

(* open Mutils *)
open Zzdatatype.Datatype
module Nt = Normalty.Frontend
open Constant
open Lit
open Prop
open Cty
open Rty
open To_cty
open To_id
open Sugar

let rec layout_rty = function
  | RtyBase { ou; cty } -> (
      match ou_to_qt ou with
      | Normalty.Connective.Fa -> spf "{%s}" (layout_cty cty)
      | Normalty.Connective.Ex -> spf "[%s]" (layout_cty cty))
  | RtyBaseArr { argcty; arg; retty } -> (
      match arg with
      | "_" -> spf "{%s} → %s" (layout_cty argcty) (layout_rty retty)
      | _ -> spf "(%s:{%s}) → %s" arg (layout_cty argcty) (layout_rty retty))
  | RtyArrArr { argrty; retty } ->
      spf "%s → %s" (layout_rty argrty) (layout_rty retty)
  | RtyTuple ts -> spf "(%s)" @@ List.split_by_comma layout_rty ts
  | RtyPolyType { pt; rty } ->
      spf "%s%s.%s" (Nt.qt_pretty_layout Fa) pt (layout_rty rty)
  | RtyPolyPred { pred; rty } ->
      spf "%s(%s: %s).%s" (Nt.qt_pretty_layout Fa) pred.x (Nt.layout_nt pred.ty)
        (layout_rty rty)

let get_ou expr =
  match expr.pexp_attributes with
  | l when List.exists (fun x -> String.equal x.attr_name.txt "over") l -> Over
  | _ -> Under

let _monad = "M"

let mk_top_overcty nty =
  let phi = Lit (AC (B true)) #: Nt.Ty_bool in
  Cty { nty; phi }

let mk_return_rty retty =
  RtyBaseArr
    { argcty = mk_top_overcty Nt.Ty_unit; arg = "_unit"; retty }

let rec rty_of_expr expr =
  match expr.pexp_desc with
  | Pexp_constraint _ ->
      let cty = cty_of_expr expr in
      RtyBase { ou = get_ou expr; cty }
  | Pexp_fun (_, rtyexpr, pattern, body) -> (
      let retty = rty_of_expr body in
      let arg = id_of_pattern pattern in
      match rtyexpr with
      | None -> _die_with [%here] "die"
      | Some rtyexpr -> (
          match rty_of_expr rtyexpr with
          | RtyBase { cty; _ } -> RtyBaseArr { argcty = cty; arg; retty }
          | RtyTuple _ -> _die_with [%here] "die"
          | argrty -> RtyArrArr { argrty; retty }))
  | Pexp_let (_, [ vb ], body) -> (
      let retty = rty_of_expr body in
      let arg = id_of_pattern vb.pvb_pat in
      match rty_of_expr vb.pvb_expr with
      | RtyBase { cty; _ } -> RtyBaseArr { argcty = cty; arg; retty }
      | RtyTuple _ -> _die_with [%here] "die"
      | argrty -> RtyArrArr { argrty; retty })
  | Pexp_tuple es -> RtyTuple (List.map rty_of_expr es)
  | Pexp_construct (c, Some expr) when String.equal _monad (longid_to_id c) ->
      mk_return_rty (rty_of_expr expr)
  | _ ->
      _die_with [%here]
        (spf "wrong refinement type: %s" (string_of_expression expr))
