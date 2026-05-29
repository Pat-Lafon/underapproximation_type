open Ocaml5_parser
open Parsetree
open Pprintast
open Mtyped
open Mutils
open Zzdatatype.Datatype
module Nt = Normalty.Frontend
open Cty
open Lit
open Prop
open To_constant
open To_prop
open Sugar

let pprint_phi (phi : 't prop) =
  let res =
    let* lit = prop_force_typed_lit_opt phi in
    let* args = typed_lit_force_aappop_opt (lit, "==") in
    match args with
    | [ a; b ] ->
        let* v = typed_lit_force_avar_opt a in
        let* c = typed_lit_force_ac_opt b in
        if String.equal v.x default_v then Some c else None
    | _ -> None
  in
  match res with None -> layout_prop phi | Some c -> layout_constant c

let pprint = function
  | Cty { nty; phi } ->
      spf "%s:%s | %s" default_v (Nt.layout nty) (pprint_phi phi)

let layout_cty = pprint

let get_self ct =
  match ct.ptyp_desc with
  | Ptyp_extension (name, PTyp ty) -> name.txt #: (Nt.core_type_to_t ty)
  | _ ->
      let () = Printf.printf "\nct: %s\n" (layout_ct ct) in
      _die [%here]

let vars_phi_of_expr expr =
  let rec aux expr =
    match expr.pexp_desc with
    | Pexp_constraint (e', ct) ->
        (* let () = Printf.printf "\nct: %s\n" (layout_ct ct) in *)
        (* let () = *)
        (*   Printf.printf "\ne': %s\n" (string_of_expression e') *)
        (* in *)
        let v = get_self ct in
        let vs, phi = aux e' in
        (v :: vs, phi)
    | _ -> ([], prop_of_expr expr)
  in
  let vs, prop = aux expr in
  (List.rev vs, prop)

let cty_of_expr expr =
  match vars_phi_of_expr expr with
  | [ { x; ty } ], phi when String.equal x default_v -> Cty { nty = ty; phi }
  | _ -> _die_with [%here] (string_of_expression expr)
