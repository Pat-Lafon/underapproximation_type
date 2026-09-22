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
  Ast_helper.Attr.mk
    (Location.mknoloc (match ou with Over -> "over" | Under -> "under"))
    (PStr [])

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

(* Inverse of [rty_of_expr]; [layout_rty] renders the display form. *)
let rec rty_to_expr = function
  | RtyBase { ou; cty } ->
      let e = cty_to_expr cty in
      { e with pexp_attributes = mk_ou_attr ou :: e.pexp_attributes }
  | RtyArr { argrty; arg; retty } ->
      desc_to_ocamlexpr
      @@ Pexp_let
           ( Asttypes.Nonrecursive,
             [ mk_vb (string_to_pattern arg, rty_to_expr argrty) ],
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

let%test_module "abd rty source round-trip" =
  (module struct
    (* The renderers read the global zutils config; seed it before round-tripping. *)
    let () =
      ZUtilsConfig.set (Result.get_ok (ZUtilsConfig.of_yojson (`Assoc [])))

    let eq = equal_rty Nt.equal_nt
    let normalize rty = rty_of_source (layout_rty_source rty)

    let%test "existential base coverage type round-trips" =
      let src =
        "(((is_nil v) && (fun (((n)[@exists]) : int) -> (len v n) && (n <= \
         s))) : [%v : ilist]) [@under]"
      in
      let r = rty_of_source src in
      eq r (rty_of_source (layout_rty_source r))

    let int_over = rty_of_source "(true : [%v: int]) [@over]"
    let int_under = rty_of_source "(v >= 0 : [%v: int]) [@under]"

    let%test "arrow round-trips" =
      let r = RtyArr { argrty = int_over; arg = "a"; retty = int_under } in
      eq r (normalize r)

    let%test "nested arrows round-trip" =
      let r =
        RtyArr
          {
            argrty = int_over;
            arg = "a";
            retty = RtyArr { argrty = int_over; arg = "b"; retty = int_under };
          }
      in
      eq r (normalize r)

    (* [M e] has no inverse: it parses to the [RtyArr] the renderer emits, whose
       unit argument [mk_return_rty] fills with [Prop.mk_true]. *)
    let%test "monadic return round-trips as an arrow" =
      let r = rty_of_source "M ((v >= 0 : [%v: int]) [@under])" in
      eq r (normalize r)

    (* An optional-label argument is the other source form for an arrow. *)
    let%test "optional-label argument round-trips" =
      let r = rty_of_source "fun ?(a : int) -> (v >= 0 : [%v: int]) [@under]" in
      eq r (normalize r)

    let%test "poly type round-trips" =
      let r = RtyPolyType { pt = "a"; rty = int_under } in
      eq r (normalize r)

    let%test "poly pred round-trips" =
      let r =
        RtyPolyPred
          { pred = "p"#:(Nt.mk_arr Nt.int_ty Nt.bool_ty); rty = int_under }
      in
      eq r (normalize r)

    let%test "nested and singleton And normalize to one form" =
      let base phi =
        RtyBase
          { ou = Under; cty = { nty = Nt.Ty_constructor ("ilist", []); phi } }
      in
      let pred name = Lit (AAppOp (name#:Nt.bool_ty, []))#:Nt.bool_ty in
      let a, b, c = (pred "a", pred "b", pred "c") in
      eq
        (normalize (base (And [ a; And [ b; c ] ])))
        (normalize (base (And [ a; b; c ])))
      && eq
           (normalize (base (And [ And [ a ]; b ])))
           (normalize (base (And [ a; b ])))
  end)
