open Ocaml5_parser
open Parsetree
open Sugar
open Mutils
open Mtyped
module Nt = Normalty.Frontend
(* open Syntax.NTyped *)

let typed_id_to_pattern id =
  let pat = string_to_pattern id.x in
  match id.ty with
  | Nt.Ty_unknown -> pat
  | ty -> typed_to_pattern (pat, Nt.t_to_core_type ty)

let typed_ids_to_pattern ids =
  tuple_to_pattern (List.map typed_id_to_pattern ids)

let longid_to_id c =
  match Longident.flatten c.Location.txt with
  | [] -> _die_with [%here] "die"
  | [ c ] -> c
  | _ -> _die_with [%here] "un-imp"

let id_to_longid x =
  match Longident.unflatten [ x ] with
  | Some x -> Location.mknoloc x
  | None -> _die_with [%here] "die"

let id_of_pattern pattern =
  match pattern.ppat_desc with
  | Ppat_var ident -> ident.txt
  | Ppat_any -> "_"
  | Ppat_construct (name, None) -> longid_to_id name
  | _ -> _die_with [%here] "die"
