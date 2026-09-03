open Zutils
open Prop
open Sugar

(* Datatype-rendering helpers shared by the Lean and Coq export twins
   ([lean_export.ml] / [coq_export.ml]). *)

let wildcards (c : Z3decls.ctor_spec) =
  String.concat "" (List.map (fun _ -> " _") c.fields)

let binder_of (f : Z3decls.field_spec) = String.sub f.fname 0 1

let ctor_has_field (f : Z3decls.field_spec) (c : Z3decls.ctor_spec) =
  List.exists (fun (g : Z3decls.field_spec) -> g.fname = f.fname) c.fields

let accessor_binders (f : Z3decls.field_spec) (c : Z3decls.ctor_spec) =
  List.map
    (fun (g : Z3decls.field_spec) ->
      if g.fname = f.fname then binder_of f else "_")
    c.fields
  |> String.concat " "

(* One [Inductive]/[inductive] constructor line, e.g. [  | Cons (head : Z) (tail : ilist)];
   [layout_ty]/[ctor] supply the per-target type and constructor rendering. *)
let ctor_line ~layout_ty ~ctor (c : Z3decls.ctor_spec) =
  let flds =
    List.map
      (fun (f : Z3decls.field_spec) ->
        spf " (%s : %s)" f.fname (layout_ty f.ftype))
      c.fields
    |> String.concat ""
  in
  spf "  | %s%s" (ctor c.cname) flds

let accessor_fields (d : Z3decls.datatype_decl) : Z3decls.field_spec list =
  List.concat_map (fun (c : Z3decls.ctor_spec) -> c.fields) d.ctors

open Ast

let reindent ~first n s =
  let pad = String.make n ' ' in
  String.split_on_char '\n' s
  |> List.mapi (fun i l -> if i = 0 && not first then l else pad ^ l)
  |> String.concat "\n"

let indent n s = reindent ~first:true n s

(* Splices a multi-line child after an inline prefix (e.g. a wrapped atom) so its
   continuation lines clear the prefix and Lean's layout still parses. *)
let indent_continuation n s = reindent ~first:false n s

let render_def ~kw ~stmt_end ~layout_typedid ~name ~params ~retty ~body =
  let ps =
    match params with
    | [] -> ""
    | _ -> " " ^ String.concat " " (List.map layout_typedid params)
  in
  spf "%s %s%s : %s :=\n%s%s" kw name ps retty (indent 2 body) stmt_end

let render_const = function
  | I n when n < 0 ->
      (* parenthesize: bare [-1] parses as subtraction in operand position *)
      spf "(%d)" n
  | I n -> string_of_int n
  | B true -> "true"
  | B false -> "false"
  | U -> _die_with [%here] "render_const: unit unsupported in rec-def body"
  | C _ -> _die_with [%here] "render_const: char unsupported in rec-def body"
  | S _ -> _die_with [%here] "render_const: string unsupported in rec-def body"
  | F _ -> _die_with [%here] "render_const: float unsupported in rec-def body"

(* Shared measure-body renderer for both export twins; only leaf tokens differ, in
   [term_setting]. The layout targets Lean's significant indentation; Gallina is
   whitespace-insensitive, so the Lean-valid layout is also valid Coq. *)
type term_setting = {
  ctor_ref : string -> string;
      (* constructor name to its reference token: Coq [Cons], Lean [.Cons] *)
  primop : string -> string;
  not_ : string -> string;
  eq : string -> string -> string -> Nt.t -> string;
      (* operator ([==]/[!=]), atomized operands, operand type *)
  match_end : string;
  let_sep : string;
}

let rec render_rt_ (st : term_setting) (t : (Nt.t, Nt.t raw_term) typed) :
    string =
  match t.x with
  | Const c -> render_const c
  | Var x -> x.x
  | Ifte (c, tb, eb) ->
      let tb = render_rt_ st tb and eb = render_rt_ st eb in
      if String.contains tb '\n' || String.contains eb '\n' then
        spf "if %s then\n%s\nelse\n%s" (render_rt_ st c) (indent 2 tb)
          (indent 2 eb)
      else spf "if %s then %s else %s" (render_rt_ st c) tb eb
  | Let { if_rec = false; lhs = [ x ]; rhs; letbody } ->
      let rhs = render_rt_ st rhs in
      let binding =
        if String.contains rhs '\n' then spf "let %s :=\n%s" x.x (indent 2 rhs)
        else spf "let %s := %s" x.x rhs
      in
      spf "%s%s\n%s" binding st.let_sep (render_rt_ st letbody)
  | AppOp (op, args) -> render_appop_ st op args
  | App (f, args) -> render_app_ st f args
  | Match { matched; match_cases } -> render_match_ st matched match_cases
  | Let _ ->
      _die_with [%here]
        "render_rt: only single-binder non-recursive let supported"
  | Lam _ -> _die_with [%here] "render_rt: Lam should be peeled before the body"
  | Err -> _die_with [%here] "render_rt: Err unsupported in rec-def body"
  | Tuple _ -> _die_with [%here] "render_rt: Tuple unsupported in rec-def body"
  | Record _ ->
      _die_with [%here] "render_rt: Record unsupported in rec-def body"
  | Field _ -> _die_with [%here] "render_rt: Field unsupported in rec-def body"

and render_atom_ (st : term_setting) (t : (Nt.t, Nt.t raw_term) typed) : string
    =
  match t.x with
  | Var _ | Const _ -> render_rt_ st t
  | _ -> spf "(%s)" (indent_continuation 1 (render_rt_ st t))

and render_appop_ (st : term_setting) (op : (Nt.t, op) typed)
    (args : (Nt.t, Nt.t raw_term) typed list) : string =
  match (op.x, args) with
  | PrimOp "not", [ a ] -> st.not_ (render_atom_ st a)
  | PrimOp (("==" | "!=") as p), [ a; b ] ->
      st.eq p (render_atom_ st a) (render_atom_ st b) a.ty
  | PrimOp (("&&" | "||") as p), (_ :: _ :: _ as xs) ->
      String.concat (spf " %s " (st.primop p)) (List.map (render_atom_ st) xs)
  | PrimOp p, [ a; b ] ->
      spf "%s %s %s" (render_atom_ st a) (st.primop p) (render_atom_ st b)
  | PrimOp p, _ ->
      _die_with [%here] (spf "render_appop: primop %s with unexpected arity" p)
  | DtConstructor c, [] -> st.ctor_ref c
  | DtConstructor c, _ ->
      spf "%s %s" (st.ctor_ref c)
        (String.concat " " (List.map (render_atom_ st) args))

and render_app_ (st : term_setting) (f : (Nt.t, Nt.t raw_term) typed)
    (args : (Nt.t, Nt.t raw_term) typed list) : string =
  match f.x with
  | Var fn ->
      if args = [] then fn.x
      else
        spf "%s %s" fn.x (String.concat " " (List.map (render_atom_ st) args))
  | _ ->
      _die_with [%here]
        "render_app: higher-order application unsupported in rec-def body"

and render_match_ (st : term_setting) (matched : (Nt.t, Nt.t raw_term) typed)
    (cases : Nt.t raw_match_case list) : string =
  let arm (Matchcase { constructor; args; exp }) =
    let pat =
      match List.map (fun a -> a.x) args with
      | [] -> st.ctor_ref constructor.x
      | binders ->
          spf "%s %s" (st.ctor_ref constructor.x) (String.concat " " binders)
    in
    let body = render_rt_ st exp in
    if String.contains body '\n' then spf "| %s =>\n%s" pat (indent 4 body)
    else spf "| %s => %s" pat body
  in
  match cases with
  | [] -> _die_with [%here] "render_match: empty match"
  | _ ->
      spf "match %s with\n%s%s" (render_rt_ st matched)
        (List.map arm cases |> String.concat "\n")
        st.match_end
