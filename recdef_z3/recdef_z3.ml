open Zutils
open Ast
open Prop
open Sugar
open Measure

let dt_decl (dt_name : string) =
  match Prop.Z3decls.find_decl dt_name with
  | Some d -> d
  | None -> _die_with [%here] (spf "no datatype %s in registry" dt_name)

let func_of zenv dt_name f =
  match Prop.Z3decls.z3_data_type_func_lookup zenv dt_name f with
  | Some fd -> fd
  | None -> _die_with [%here] (spf "datatype %s has no function %s" dt_name f)

let resolve_cases dt_name (decl : Prop.Z3decls.datatype_decl) cases =
  let resolve (Matchcase { constructor; args; exp }) =
    let cname = String.lowercase_ascii constructor.x in
    match
      List.find_opt
        (fun c -> String.equal c.Prop.Z3decls.cname cname)
        decl.ctors
    with
    | None -> _die_with [%here] (spf "%s has no constructor %s" dt_name cname)
    | Some c ->
        if List.length c.Prop.Z3decls.fields <> List.length args then
          _die_with [%here] (spf "arity mismatch for constructor %s" cname);
        (c, args, exp)
  in
  let resolved = List.map resolve cases in
  let case_ctors =
    List.sort_uniq String.compare
      (List.map (fun (c, _, _) -> c.Prop.Z3decls.cname) resolved)
  in
  if List.length case_ctors <> List.length resolved then
    _die_with [%here] (spf "duplicate constructor in match on %s" dt_name);
  if List.length case_ctors <> List.length decl.ctors then
    _die_with [%here]
      (spf "non-exhaustive match on %s: %d distinct cases for %d constructors"
         dt_name (List.length case_ctors) (List.length decl.ctors));
  resolved

let rec encode (zenv : Prop.Z3decls.z3_env) env
    (t : (Nt.t, Nt.t raw_term) typed) : Z3.Expr.expr =
  let ctx = zenv.ctx in
  match t.x with
  | Const (I n) -> Prop.Z3aux.int_to_z3 ctx n
  | Const (B b) -> Prop.Z3aux.bool_to_z3 ctx b
  | Const _ -> _die_with [%here] "unsupported constant in rec-def body"
  | Var x -> (
      match List.assoc_opt x.x env with
      | Some e -> e
      | None ->
          _die_with [%here]
            (spf
               "unbound variable %s (a nullary call must appear as an [App], \
                not a bare [Var])"
               x.x))
  | Ifte (c, tb, eb) ->
      Z3.Boolean.mk_ite ctx (encode zenv env c) (encode zenv env tb)
        (encode zenv env eb)
  | Let { if_rec = false; rhs; lhs = [ x ]; letbody } ->
      encode zenv ((x.x, encode zenv env rhs) :: env) letbody
  | Let _ ->
      _die_with [%here]
        "only non-recursive single-binding let supported in rec-def body"
  | AppOp (op, args) -> encode_op zenv env op args t.ty
  | App (f, args) -> encode_app zenv env f args
  | Match { matched; match_cases } -> encode_match zenv env matched match_cases
  | _ -> _die_with [%here] "unsupported raw_term form in rec-def body"

and encode_op (zenv : Prop.Z3decls.z3_env) env (op : (Nt.t, op) typed) args
    retty =
  let ctx = zenv.ctx in
  let a = List.map (encode zenv env) args in
  match (op.x, a) with
  | PrimOp "+", l -> Z3.Arithmetic.mk_add ctx l
  | PrimOp "-", [ x; y ] -> Z3.Arithmetic.mk_sub ctx [ x; y ]
  | PrimOp "*", l -> Z3.Arithmetic.mk_mul ctx l
  | PrimOp ">", [ x; y ] -> Z3.Arithmetic.mk_gt ctx x y
  | PrimOp ">=", [ x; y ] -> Z3.Arithmetic.mk_ge ctx x y
  | PrimOp "<", [ x; y ] -> Z3.Arithmetic.mk_lt ctx x y
  | PrimOp "<=", [ x; y ] -> Z3.Arithmetic.mk_le ctx x y
  | PrimOp "==", [ x; y ] -> Z3.Boolean.mk_eq ctx x y
  | PrimOp "!=", [ x; y ] -> Z3.Boolean.mk_not ctx (Z3.Boolean.mk_eq ctx x y)
  | PrimOp "&&", l -> Z3.Boolean.mk_and ctx l
  | PrimOp "||", l -> Z3.Boolean.mk_or ctx l
  | PrimOp "not", [ x ] -> Z3.Boolean.mk_not ctx x
  | PrimOp "mod", [ x; y ] -> Z3.Arithmetic.Integer.mk_mod ctx x y
  | PrimOp p, _ -> _die_with [%here] (spf "unsupported primop %s" p)
  | DtConstructor c, _ ->
      let dt_name = Nt.layout retty in
      Z3.FuncDecl.apply (func_of zenv dt_name (String.lowercase_ascii c)) a

and encode_app (zenv : Prop.Z3decls.z3_env) env
    (f : (Nt.t, Nt.t raw_term) typed) args =
  match f.x with
  | Var fn -> (
      match Prop.Z3decls.rec_func_lookup zenv fn.x with
      | Some fd -> Z3.FuncDecl.apply fd (List.map (encode zenv env) args)
      | None ->
          _die_with [%here]
            (spf "rec-def body calls unregistered function %s" fn.x))
  | _ ->
      _die_with [%here] "higher-order application unsupported in rec-def body"

and encode_match (zenv : Prop.Z3decls.z3_env) env
    (matched : (Nt.t, Nt.t raw_term) typed) cases =
  let ctx = zenv.ctx in
  let m = encode zenv env matched in
  let dt_name = Nt.layout matched.ty in
  let dt_func f = func_of zenv dt_name f in
  let resolved = resolve_cases dt_name (dt_decl dt_name) cases in
  let encode_case (c, args, exp) =
    let env =
      List.map2
        (fun field arg ->
          (arg.x, Z3.FuncDecl.apply (dt_func field.Prop.Z3decls.fname) [ m ]))
        c.Prop.Z3decls.fields args
      @ env
    in
    encode zenv env exp
  in
  let rec build = function
    | [] -> _die_with [%here] "empty match"
    (* No guard on the last case: [resolve_cases] made the cases a bijection with the ctors. *)
    | [ rc ] -> encode_case rc
    | ((c, _, _) as rc) :: rest ->
        Z3.Boolean.mk_ite ctx
          (Z3.FuncDecl.apply (dt_func ("is_" ^ c.Prop.Z3decls.cname)) [ m ])
          (encode_case rc) (build rest)
  in
  build resolved

(* One forward pass suffices because [all_defs] is in source order: each callee's decl precedes
   its use. *)
let register_all_for_ctx (zenv : Prop.Z3decls.z3_env) : unit =
  let ctx = zenv.ctx in
  let bool_sort = Prop.Z3aux.tp_to_sort zenv Nt.bool_ty in
  (* [make_body] is deferred past [register_rec_func] so a self-call finds the fd in [rec_func_map];
     and since [mk_func_decl] can't attach a body, even the non-recursive wrapper uses [add_rec_def]. *)
  let define_rec name argsorts retsort argexprs make_body =
    let fd = Z3.FuncDecl.mk_rec_func_decl_s ctx name argsorts retsort in
    Prop.Z3decls.register_rec_func zenv name fd;
    Z3.FuncDecl.add_rec_def ctx fd argexprs (make_body ());
    fd
  in
  let register_def (d : rec_def) =
    let argsorts =
      List.map (fun p -> Prop.Z3aux.tp_to_sort zenv p.ty) d.params
    in
    let retsort = Prop.Z3aux.tp_to_sort zenv d.body.ty in
    let env =
      List.map2
        (fun p s -> (p.x, Z3.Expr.mk_const_s ctx p.x s))
        d.params argsorts
    in
    let argexprs = List.map snd env in
    let impl_fd =
      define_rec (impl_name d.fname) argsorts retsort argexprs (fun () ->
          encode zenv env (to_impl_calls d.body))
    in
    let res = Z3.Expr.mk_const_s ctx "res" retsort in
    ignore
      (define_rec d.fname (argsorts @ [ retsort ]) bool_sort (argexprs @ [ res ])
         (fun () ->
           Z3.Boolean.mk_eq ctx (Z3.FuncDecl.apply impl_fd argexprs) res))
  in
  List.iter register_def (all_defs ())

(* Encode [prop] against a fresh local ctx (method predicates as [define-fun-rec]s) to race
   the prover's axiom encoding. [None] if the query has an uninterpreted app. *)
let build_functional_query (prop : Nt.t prop) : string option =
  let func_ctx = Z3.mk_context [] in
  let zenv = Prop.Z3aux.mk_env func_ctx in
  register_all_for_ctx zenv;
  let query = Prop.Propencoding.to_z3 zenv prop in
  if Prop.Z3aux.has_uninterpreted_app query then None
  else Some (Prop.Prover.serialize zenv [ query ])
