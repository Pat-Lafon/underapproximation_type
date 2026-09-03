open Zutils
open OcamlParser
open Oparse
open Mutils
open Prop
open Parsetree
open Zdatatype
open Ast
open Sugar
open To_cty

let rec layout_rty = function
  | RtyBase { ou; cty } -> layout_ou_bracket ou @@ layout_cty cty
  | RtyArr { argrty; arg; retty } ->
      let argrty = layout_rty_bracket argrty in
      let arr = "→" in
      if List.exists (String.equal arg) @@ fv_rty_id retty then
        spf "%s:%s %s %s" arg argrty arr (layout_rty retty)
      else spf "%s %s %s" argrty arr (layout_rty retty)
  | RtyPolyType { pt; rty } ->
      spf "%s%s.%s" (Nt.qt_pretty_layout Fa) pt (layout_rty rty)
  | RtyPolyPred { pred; rty } ->
      spf "%s(%s: %s).%s" (Nt.qt_pretty_layout Fa) pred.x (Nt.layout_nt pred.ty)
        (layout_rty rty)

and layout_rty_bracket rty =
  match rty with
  | RtyBase _ -> layout_rty rty
  | _ -> spf "(%s)" (layout_rty rty)

let get_ou expr =
  match expr.pexp_attributes with
  | l when List.exists (fun x -> String.equal x.attr_name.txt "over") l -> Over
  | _ -> Under

let mk_ou_attr ou =
  let txt = match ou with Over -> "over" | Under -> "under" in
  {
    attr_name = Location.mknoloc txt;
    attr_payload = PStr [];
    attr_loc = Location.none;
  }

let base_type_name = Nt._constructor_ty_0 "baseType"
let _monad = "M"

let rec rty_of_expr expr =
  match expr.pexp_desc with
  | Pexp_constraint _ -> RtyBase { ou = get_ou expr; cty = cty_of_expr expr }
  | Pexp_fun (Asttypes.Nolabel, None, pattern, body) ->
      let param = To_raw_term.typed_id_of_pattern pattern in
      if Nt.equal_nt base_type_name param.ty then
        RtyPolyType { pt = param.x; rty = rty_of_expr body }
      else RtyPolyPred { pred = param; rty = rty_of_expr body }
  | Pexp_fun (Asttypes.Optional _, None, pattern, body) ->
      let param = To_raw_term.typed_id_of_pattern pattern in
      let retty = rty_of_expr body in
      let argrty = mk_top_overrty param.ty in
      RtyArr { argrty; arg = param.x; retty }
  | Pexp_fun (_, Some rtyexpr, pattern, body) ->
      let retty = rty_of_expr body in
      let arg = id_of_pattern pattern in
      (* let arr_type = get_arr_type rtyexpr in *)
      let argrty = rty_of_expr rtyexpr in
      RtyArr { argrty; arg; retty }
  | Pexp_let (_, [ vb ], body) ->
      let retty = rty_of_expr body in
      let arg = id_of_pattern vb.pvb_pat in
      (* let arr_type = get_arr_type vb.pvb_expr in *)
      let argrty = rty_of_expr vb.pvb_expr in
      RtyArr { argrty; arg; retty }
  | Pexp_construct (c, Some expr) when String.equal _monad (longid_to_id c) ->
      mk_return_rty (rty_of_expr expr)
  | _ ->
      _failatwith [%here]
        (spf "wrong refinement type: %s" (string_of_expression expr))

let rty_of_expr expr =
  let rty = rty_of_expr expr in
  check_syntactically_wf_rty rty;
  rty

(* Inverse of [rty_of_expr]: the re-parseable source form (versus [layout_rty]'s
   [\[v:ty | phi\]] display form) that a committed [.abd] file is read back from. *)
let rec rty_to_expr = function
  | RtyBase { ou; cty } ->
      let e = cty_to_expr cty in
      { e with pexp_attributes = mk_ou_attr ou :: e.pexp_attributes }
  | RtyArr { argrty; arg; retty } ->
      desc_to_ocamlexpr
      @@ Pexp_fun
           ( Asttypes.Nolabel,
             Some (rty_to_expr argrty),
             string_to_pattern arg,
             rty_to_expr retty )
  | RtyPolyType { pt; rty } ->
      mklam
        (typed_to_pattern
           (string_to_pattern pt, Nt.t_to_core_type base_type_name))
        (rty_to_expr rty)
  | RtyPolyPred { pred; rty } ->
      mklam
        (typed_to_pattern (string_to_pattern pred.x, Nt.t_to_core_type pred.ty))
        (rty_to_expr rty)

let layout_rty_source rty = string_of_expression (rty_to_expr rty)
let rty_of_source str = rty_of_expr (parse_expression str)

(* [prop_to_expr] renders n-ary [And]/[Or] as binary OCaml [&&]/[||] and drops
   singleton [And \[p\]], so a parsed-back prop is flattened where the inferred
   one may nest; [smart_and]/[smart_or] put both into the same flat form so
   [equal_rty] compares a round-tripped [.abd] against fresh abduction. *)
let rec normalize_rty = function
  | RtyBase { ou; cty = { nty; phi } } ->
      let rec flatten = function
        | Lit _ as p -> p
        | Implies (a, b) -> Implies (flatten a, flatten b)
        | Ite (a, b, c) -> Ite (flatten a, flatten b, flatten c)
        | Not p -> Not (flatten p)
        | And es -> smart_and (List.map flatten es)
        | Or es -> smart_or (List.map flatten es)
        | Iff (a, b) -> Iff (flatten a, flatten b)
        | Forall { qv; body } -> Forall { qv; body = flatten body }
        | Exists { qv; body } -> Exists { qv; body = flatten body }
      in
      RtyBase { ou; cty = { nty; phi = flatten phi } }
  | RtyArr { argrty; arg; retty } ->
      RtyArr { argrty = normalize_rty argrty; arg; retty = normalize_rty retty }
  | RtyPolyType { pt; rty } -> RtyPolyType { pt; rty = normalize_rty rty }
  | RtyPolyPred { pred; rty } -> RtyPolyPred { pred; rty = normalize_rty rty }

let%test_module "abd rty source round-trip" =
  (module struct
    (* The renderers read the global zutils config; seed it before round-tripping. *)
    let () = ZUtilsConfig.set ZUtilsConfig.default
    let eq = equal_rty (fun _ _ -> true)

    (* rty_to_expr then rty_of_expr recovers the same coverage type, so a
       committed [.abd] read back by [check_or_write_abduction_file] matches. *)
    let%test "existential base coverage type round-trips" =
      let src =
        "(((is_nil v) && (fun (((n)[@exists]) : int) -> (len v n) && (n <= \
         s))) : [%v : ilist]) [@under]"
      in
      let r = rty_of_source src in
      eq (normalize_rty r) (normalize_rty (rty_of_source (layout_rty_source r)))

    (* [normalize_rty] must erase the nesting/singleton difference between an
       inferred n-ary [And] and the binary [And] a round-trip produces. *)
    let%test "nested and singleton And normalize to the flat form" =
      let base phi =
        RtyBase
          { ou = Under; cty = { nty = Nt.Ty_constructor ("ilist", []); phi } }
      in
      let pred name = Lit (AAppOp (name#:Nt.bool_ty, []))#:Nt.bool_ty in
      let a, b, c = (pred "a", pred "b", pred "c") in
      eq
        (normalize_rty (base (And [ a; And [ b; c ] ])))
        (normalize_rty (base (And [ a; b; c ])))
      && eq
           (normalize_rty (base (And [ And [ a ]; b ])))
           (normalize_rty (base (And [ a; b ])))
  end)
