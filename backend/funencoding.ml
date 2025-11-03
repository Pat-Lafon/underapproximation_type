open Mtyped
open Litencoding

let rec term_to_z3 ctx (term : ('t, 't Term.term) typed) : Z3.Expr.expr =
  let open Term in
  let open Lit in
  let open Frontend_opt.To_lit in
  match term.x with
  | CVal _ -> Litencoding.typed_lit_to_z3 ctx (term_to_lit term)
  | CLetE { lhs = { ty = Nt.T.Ty_arrow _; _ }; _ } ->
      failwith "term_to_z3:CLetE:unimplemented"
  | CLetE { lhs; rhs; body } ->
      let to_expr = term_to_z3 ctx rhs in
      let body_expr = term_to_z3 ctx body in
      let from_expr = Litencoding.typed_lit_to_z3 ctx (AVar lhs)#:lhs.ty in
      Printf.printf "let %s = %s in %s\n"
        (Z3.Expr.to_string from_expr)
        (Z3.Expr.to_string to_expr)
        (Z3.Expr.to_string body_expr);
      let res = Z3.Expr.substitute_one body_expr from_expr to_expr in

      Printf.printf "let %s = %s in %s -> %s\n"
        (Z3.Expr.to_string from_expr)
        (Z3.Expr.to_string to_expr)
        (Z3.Expr.to_string body_expr)
        (Z3.Expr.to_string res);
      res
  | CApp { appf; apparg } ->
      if Nt.T.destruct_arr_tp appf.ty |> fst |> fun l -> List.length l == 1 then
        let f = value_to_lit appf in
        let v = value_to_lit apparg in
        match f.x with
        | AVar fv ->
            Litencoding.typed_lit_to_z3 ctx (AAppOp (fv, [ v ]))#:term.ty
        | _ -> failwith "term_to_z3:CApp::unimplemented"
      else failwith "term_to_z3:CApp:TooManyArgs"
  | CAppOp { op; appopargs } ->
      let args = List.map value_to_lit appopargs in
      Litencoding.typed_lit_to_z3 ctx
        (AAppOp (op#->Op.op_name_for_typectx, args))#:term.ty
  | CMatch { matched = { ty = Nt.T.Ty_bool; x = cond }; match_cases } ->
      assert (List.length match_cases = 2);
      let true_case =
        List.find_map
          (fun (CMatchcase { constructor; args; exp }) ->
            assert (args = []);
            print_endline constructor.x;
            match constructor.x with
            | "True" -> Some (term_to_z3 ctx exp)
            | _ -> None)
          match_cases
        |> Option.get
      in
      let false_case =
        List.find_map
          (fun (CMatchcase { constructor; args; exp }) ->
            assert (args = []);
            print_endline constructor.x;
            match constructor.x with
            | "False" -> Some (term_to_z3 ctx exp)
            | _ -> None)
          match_cases
        |> Option.get
      in

      Z3.Boolean.mk_ite ctx
        (value_to_lit cond#:Nt.T.Ty_bool |> Litencoding.typed_lit_to_z3 ctx)
        true_case false_case
  | _ -> failwith "term_to_z3:unimplmented"

let rec raw_term_to_z3 ctx (raw_term : (Nt.t, Nt.t Raw_term.raw_term) typed) :
    Z3.Expr.expr =
  let open Raw_term in
  let open Frontend_opt.To_lit in
  let open Lit in
  match raw_term.x with
  | Var _ | Const _ ->
      Litencoding.typed_lit_to_z3 ctx raw_term#->raw_term_to_lit
  | Lam _ ->
      (*       let lamarg = __force_typed __FILE__ __LINE__ lamarg in
      let lambody = raw_term_to_z3 (add_to_right ctx lamarg) lambody in
      let ty = Nt.construct_arr_tp ([ lamarg.ty ], lambody.ty) in
      Z3.FuncDecl.apply
        (Z3.FuncDecl.mk_func_decl_s ctx "lambda" [ ty ] ty)
        [ lambody ] *)
      failwith "raw_term_to_z3:Lam:unimplemented"
  | App ({ x = Var fv; _ }, appargs) ->
      let args = List.map (fun a -> a#->raw_term_to_lit) appargs in
      Litencoding.typed_lit_to_z3 ctx (AAppOp (fv, args))#:raw_term.ty
  | Ite (cond, t, f) ->
      let cond = raw_term_to_z3 ctx cond in
      let t = raw_term_to_z3 ctx t in
      let f = raw_term_to_z3 ctx f in

      Z3.Boolean.mk_ite ctx cond t f
  | AppOp (op, args) ->
      let args = List.map (fun a -> a#->raw_term_to_lit) args in
      Litencoding.typed_lit_to_z3 ctx
        (AAppOp (op#->Op.op_name_for_typectx, args))#:raw_term.ty
  | Let _ -> failwith "raw_term_to_z3:Let:unimplemented"
  | _ -> failwith "raw_term_to_z3:unimplemented"

let z3_create_rec_func ctx name (args : (Nt.t, string) Mtyped.typed list) ret
    body =
  let arg_tys = List.map (fun x -> Z3aux.tp_to_sort ctx x.ty) args in

  List.iter (fun a -> Printf.printf "%s -> " (Z3.Sort.to_string a)) arg_tys;

  let ret_ty = Z3aux.tp_to_sort ctx ret in

  Printf.printf "%s\n" (Z3.Sort.to_string ret_ty);

  let rec_func = Z3.FuncDecl.mk_rec_func_decl_s ctx name arg_tys ret_ty in

  let func_args =
    List.map (fun a -> Z3aux.tpedvar_to_z3 ctx (a.ty, a.x)) args
  in

  let body = raw_term_to_z3 ctx body in

  Z3.FuncDecl.add_rec_def ctx rec_func func_args body;

  let res = { func = rec_func } in

  Hashtbl.add rec_func_map name res;

  res
