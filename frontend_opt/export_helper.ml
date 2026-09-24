open Zutils
open Prop
open Sugar
open Ast
open Measure

(* What distinguishes the Lean and Coq export twins: leaf tokens and statement
   templates. The layout targets Lean's significant indentation; Gallina is
   whitespace-insensitive, so the Lean-valid layout is also valid Coq. *)
type setting = {
  ctor_ref : string -> string;
      (* constructor name to its reference token: Coq [Cons], Lean [.Cons] *)
  primop : string -> string;
  not_ : string -> string;
  eq : string -> string -> string -> Nt.t -> string;
      (* operator ([==]/[!=]), atomized operands, operand type *)
  match_end : string;
  let_sep : string;
  layout_ty : Nt.t -> string;
  option_ty : string -> string;
  some_ : string;
  none_ : string;
  inductive : Z3decls.datatype_decl -> string list -> string;
      (* the datatype and its rendered constructor lines *)
  match_def :
    Z3decls.datatype_decl -> name:string -> ret:string -> string list -> string;
      (* a function by match on the datatype, from its rendered arms *)
  dt_extra : Z3decls.datatype_decl -> string list;
      (* definitions between the inductive and its recognizers *)
}

let ctor_name (cname : string) = String.capitalize_ascii cname

(* Lowercase, to match the relational predicate names the axioms reference. *)
let recognizer_name (c : Z3decls.ctor_spec) =
  "is_" ^ String.lowercase_ascii c.cname

let apply head args = String.concat " " (head :: args)

(* One constructor line, e.g. [  | Cons (head : Z) (tail : ilist)]. *)
let ctor_line (st : setting) (c : Z3decls.ctor_spec) =
  let flds =
    List.map
      (fun (f : Z3decls.field_spec) ->
        spf " (%s : %s)" f.fname (st.layout_ty f.ftype))
      c.fields
    |> String.concat ""
  in
  spf "  | %s%s" (ctor_name c.cname) flds

let accessor_fields (d : Z3decls.datatype_decl) : Z3decls.field_spec list =
  List.concat_map (fun (c : Z3decls.ctor_spec) -> c.fields) d.ctors

(* A match arm on [c], its fields bound by [binder]. *)
let ctor_arm (st : setting) (c : Z3decls.ctor_spec) binder rhs =
  spf "  | %s => %s"
    (apply (st.ctor_ref c.cname) (List.map binder c.fields))
    rhs

let render_recognizer (st : setting) (d : Z3decls.datatype_decl)
    (target : Z3decls.ctor_spec) : string =
  st.match_def d ~name:(recognizer_name target) ~ret:(st.layout_ty Nt.bool_ty)
    (List.map
       (fun (c : Z3decls.ctor_spec) ->
         ctor_arm st c (fun _ -> "_") (string_of_bool (c.cname = target.cname)))
       d.ctors)

let render_accessor (st : setting) (d : Z3decls.datatype_decl)
    (f : Z3decls.field_spec) : string =
  let x = String.sub f.fname 0 1 in
  let binds (g : Z3decls.field_spec) = g.fname = f.fname in
  st.match_def d ~name:f.fname
    ~ret:(st.option_ty (st.layout_ty f.ftype))
    (List.map
       (fun (c : Z3decls.ctor_spec) ->
         ctor_arm st c
           (fun g -> if binds g then x else "_")
           (if List.exists binds c.fields then spf "%s %s" st.some_ x
            else st.none_))
       d.ctors)

let render_datatype_decl (st : setting) (d : Z3decls.datatype_decl) : string =
  let inductive = st.inductive d (List.map (ctor_line st) d.ctors) in
  String.concat "\n\n"
    ((inductive :: st.dt_extra d)
    @ List.map (render_recognizer st d) d.ctors
    @ List.map (render_accessor st d) (accessor_fields d))

let render_datatype_decls (st : setting) () : string =
  Z3decls.registered_decls ()
  |> List.map (render_datatype_decl st)
  |> String.concat "\n\n"

let reindent ~first n s =
  let pad = String.make n ' ' in
  String.split_on_char '\n' s
  |> List.mapi (fun i l -> if i = 0 && not first then l else pad ^ l)
  |> String.concat "\n"

let indent n s = reindent ~first:true n s

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
  | U | C _ | S _ | F _ ->
      _die_with [%here] "render_const: only int and bool in rec-def body"

let rec render_rt_ (st : setting) (t : (Nt.t, Nt.t raw_term) typed) : string =
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
  | Err | Tuple _ | Record _ | Field _ ->
      _die_with [%here]
        "render_rt: Err/Tuple/Record/Field unsupported in rec-def body"

and render_atom_ (st : setting) (t : (Nt.t, Nt.t raw_term) typed) : string =
  match t.x with
  | Var _ | Const _ -> render_rt_ st t
  (* Continuation lines clear the opening paren so Lean's layout still parses. *)
  | _ -> spf "(%s)" (reindent ~first:false 1 (render_rt_ st t))

and render_appop_ (st : setting) (op : (Nt.t, op) typed)
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
  | DtConstructor c, _ ->
      apply (st.ctor_ref c) (List.map (render_atom_ st) args)

and render_app_ (st : setting) (f : (Nt.t, Nt.t raw_term) typed)
    (args : (Nt.t, Nt.t raw_term) typed list) : string =
  match f.x with
  | Var fn -> apply fn.x (List.map (render_atom_ st) args)
  | _ ->
      _die_with [%here]
        "render_app: higher-order application unsupported in rec-def body"

and render_match_ (st : setting) (matched : (Nt.t, Nt.t raw_term) typed)
    (cases : Nt.t raw_match_case list) : string =
  let arm (Matchcase { constructor; args; exp }) =
    let pat =
      apply (st.ctor_ref constructor.x) (List.map (fun a -> a.x) args)
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

let render_all (render_measure : rec_def -> string) () : string =
  all_defs () |> List.map render_measure |> String.concat "\n\n"

(* One impl definition then its wrapper, per measure in source order. *)
let render_impl_wrapper ~impl ~wrapper : unit -> string =
  render_all (fun (d : rec_def) -> impl d ^ "\n\n" ^ wrapper d)

(* A measure's relational wrapper, definitionally [impl args = res]: the same
   impl+wrapper pair [Recdef_z3.register_all_for_ctx] derives for Z3. *)
let render_wrapper ~render_def (d : rec_def) : string =
  let call = apply (impl_name d.fname) (List.map (fun p -> p.x) d.params) in
  render_def ~name:d.fname
    ~params:(d.params @ [ "res"#:d.body.ty ])
    ~retty:"Prop" ~body:(spf "%s = res" call)
