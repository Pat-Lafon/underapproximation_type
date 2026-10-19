open Zutils
open Prop
open Sugar
open Ast

type rec_def = {
  fname : string;
  params : (Nt.t, string) typed list;
  body : (Nt.t, Nt.t raw_term) typed;
}

let registry : rec_def list ref = ref []
let impl_name base = base ^ "_impl"
let z3_ctor_name = String.lowercase_ascii

let rec peel_lams acc (t : (Nt.t, Nt.t raw_term) typed) =
  match t.x with
  | Lam { lamarg; lambody } -> peel_lams (lamarg :: acc) lambody
  | _ -> (List.rev acc, t)

let register_items items =
  List.iter
    (function
      | MFuncImpRaw { name; body; _ } ->
          if List.exists (fun d -> String.equal d.fname name.x) !registry then
            _die_with [%here] (spf "duplicate method-predicate %s" name.x);
          let params, core = peel_lams [] body in
          if List.exists (fun p -> String.equal p.x "res") params then
            _die_with [%here]
              (spf
                 "measure %s: parameter \"res\" collides with the wrapper's \
                  result"
                 name.x);
          registry := !registry @ [ { fname = name.x; params; body = core } ]
      | _ -> ())
    items

let to_impl_calls body =
  List.fold_left
    (fun acc d ->
      typed_subst_raw_term d.fname
        (fun v -> Var { v with x = impl_name v.x })
        acc)
    body !registry

(* SMT-LIB rejects a bare [c']; [|c'|] is the same name, quoted. *)
let sym s = if String.contains s '\'' then spf "|%s|" s else s
let paren l = spf "(%s)" (String.concat " " l)
let app head = function [] -> head | args -> paren (head :: args)
let sort ty = Z3.Sort.to_string (Z3aux.tp_to_sort (Prover.get_prover ()).ctx ty)

let primop = function
  | "==" -> "="
  | "!=" -> "distinct"
  | "&&" -> "and"
  | "||" -> "or"
  | ("+" | "-" | "*" | ">" | ">=" | "<" | "<=" | "not" | "mod") as p -> p
  | p -> _die_with [%here] (spf "unsupported primop %s" p)

let rec smt_term (t : (Nt.t, Nt.t raw_term) typed) =
  match t.x with
  | Const (I n) when n < 0 -> paren [ "-"; string_of_int (-n) ]
  | Const (I n) -> string_of_int n
  | Const (B b) -> string_of_bool b
  | Var x -> sym x.x
  | Ifte (c, tb, eb) -> app "ite" (List.map smt_term [ c; tb; eb ])
  | Let { if_rec = false; rhs; lhs = [ x ]; letbody } ->
      paren
        [ "let"; paren [ paren [ sym x.x; smt_term rhs ] ]; smt_term letbody ]
  | AppOp ({ x = PrimOp p; _ }, args) -> app (primop p) (List.map smt_term args)
  | AppOp ({ x = DtConstructor c; _ }, args) ->
      app (sym (z3_ctor_name c)) (List.map smt_term args)
  | App ({ x = Var fn; _ }, args) -> app (sym fn.x) (List.map smt_term args)
  | Match { matched; match_cases } ->
      let arm (Matchcase { constructor; args; exp }) =
        paren
          [
            app
              (sym (z3_ctor_name constructor.x))
              (List.map (fun a -> sym a.x) args);
            smt_term exp;
          ]
      in
      paren [ "match"; smt_term matched; paren (List.map arm match_cases) ]
  | _ -> _die_with [%here] "unsupported term in measure body"

let smt_datatype (d : Z3decls.datatype_decl) =
  let field (f : Z3decls.field_spec) = paren [ sym f.fname; sort f.ftype ] in
  let ctor (c : Z3decls.ctor_spec) =
    paren (sym c.cname :: List.map field c.fields)
  in
  paren
    [
      "declare-datatypes";
      paren [ paren [ sym d.dt_name; "0" ] ];
      paren [ paren (List.map ctor d.ctors) ];
    ]

(* [define-fun-rec] even where nothing recurses: z3 inlines a [define-fun] and solves a
   different query. *)
let define name params ret body =
  paren
    [
      "define-fun-rec";
      sym name;
      paren (List.map (fun p -> paren [ sym p.x; sort p.ty ]) params);
      ret;
      body;
    ]

let smt_def (d : rec_def) =
  let call =
    app (sym (impl_name d.fname)) (List.map (fun p -> sym p.x) d.params)
  in
  [
    define (impl_name d.fname) d.params (sort d.body.ty)
      (smt_term (to_impl_calls d.body));
    define d.fname
      (d.params @ [ "res"#:d.body.ty ])
      "Bool"
      (paren [ "="; call; "res" ]);
  ]

let render_smtlib () =
  List.map smt_datatype (Z3decls.registered_decls ())
  @ List.concat_map smt_def !registry
  |> String.concat "\n"
  |> fun s -> s ^ "\n"

let measures_text = lazy (render_smtlib ())

let build_functional_query prop =
  let query = Propencoding.to_z3 (Prover.get_prover ()).ctx prop in
  spf "%s(assert %s)\n" (Lazy.force measures_text) (Z3.Expr.to_string query)
