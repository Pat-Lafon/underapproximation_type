module NL = Languages.NormalAnormal
module UL = Languages.UnderAnormal
module NT = Languages.Normalty
module UT = Languages.Underty
module Op = Languages.Op
module P = Autov.Prop
open Zzdatatype.Datatype
open Abstraction
open Sugar
open UT

type ctx = Qtypectx.ctx
(* type 'a bodytyped = { ty : UT.bodyt; x : string } *)

let layout_judge = Frontend.Typectx.pretty_layout_under_judge Trans.nan_to_term

let lit_to_prop_lit (ty, x) =
  let open UL in
  match x with
  | ConstB b -> P.(ACbool b)
  | ConstI i -> P.(ACint i)
  | Var id -> P.(AVar { ty; x = id })

let erase_check file line (underfty, normalty) =
  (* let () = *)
  (*   Printf.printf "|_ %s _| ~> %s = %s\n" *)
  (*     (Frontend.Undertype.layout underfty) *)
  (*     (Frontend.Type.layout @@ UT.erase underfty) *)
  (*     (Frontend.Type.layout normalty) *)
  (* in *)
  let _ = _check_equality file line NT.eq (UT.erase underfty) normalty in
  ()

let erase_check_mk_id file line id underfty =
  (* let () = *)
  (*   Printf.printf "|_ %s _| ~> %s = %s\n" *)
  (*     (Frontend.Undertype.layout underfty) *)
  (*     (Frontend.Type.layout @@ UT.erase underfty) *)
  (*     (Frontend.Type.layout id.NL.ty) *)
  (* in *)
  let _ = _check_equality file line NT.eq (UT.erase underfty.k) id.NL.ty in
  UL.{ ty = underfty; x = id.x }

let subtyping_check = Undersub.subtyping_check

let close_qv_by_ctx_diff (ctx, UL.{ ty; x }) ctx' =
  UL.{ ty = Qtypectx.close_qv_by_diff ctx ctx' ty; x }

let rec id_type_infer (ctx : ctx) (id : NL.id NL.typed) : UL.id UL.typed =
  let open UT in
  let ty =
    try without_qv (Typectx.get_ty ctx.k id.x)
    with _ -> Prim.get_primitive_under_ty (External id.x)
  in
  (* let ty = *)
  (*   UT.( *)
  (*     match ty with *)
  (*     | UnderTy_base { basename; normalty; prop } -> *)
  (*         UnderTy_base *)
  (*           { *)
  (*             basename = id.x; *)
  (*             normalty; *)
  (*             prop = P.subst_id prop basename id.x; *)
  (*           } *)
  (*     | _ -> ty) *)
  (* in *)
  erase_check_mk_id __FILE__ __LINE__ id ty

and id_type_check (ctx : ctx) (id : NL.id NL.typed) (ty : UT.t) : NL.id UL.typed
    =
  let id = id_type_infer ctx id in
  let () = subtyping_check __FILE__ __LINE__ ctx id.UL.ty ty in
  id

and lit_type_infer (ctx : ctx) (lit : NL.smt_lit NL.typed) : UL.smt_lit UL.typed
    =
  let open NL in
  let open UT in
  match lit.x with
  | ConstI n ->
      {
        ty =
          without_qv
          @@ make_basic "_nu" NT.Ty_int (fun nu ->
                 P.(Lit (AOp2 ("==", AVar nu, ACint n))));
        x = ConstI n;
      }
  | ConstB true ->
      {
        ty = without_qv @@ make_basic "_nu" NT.Ty_int (fun nu -> Lit (AVar nu));
        x = ConstB true;
      }
  | ConstB false ->
      {
        ty =
          without_qv
          @@ make_basic "_nu" NT.Ty_int (fun nu -> Not (Lit (AVar nu)));
        x = ConstB true;
      }
  | Var id ->
      let id = id_type_infer ctx { ty = lit.ty; x = id } in
      UL.{ ty = id.ty; x = Var id.x }

and value_type_infer (ctx : ctx) (a : NL.value NL.typed) : UL.value UL.typed =
  let aty = a.ty in
  match a.x with
  | NL.Lit lit ->
      let lit = lit_type_infer ctx { ty = aty; x = lit } in
      UL.{ ty = lit.ty; x = Lit lit.x }
  | NL.Lam (_, _) ->
      (* NOTE: Can we infer a type of the lambda function without the argment type? *)
      _failatwith __FILE__ __LINE__ "cannot infer under arrow type"
  | NL.Fix _ -> _failatwith __FILE__ __LINE__ "unimp"

and value_type_check (ctx_ori : ctx) (a : NL.value NL.typed) (ty : UT.t) :
    UL.value UL.typed =
  let open UT in
  let ty, ctx = unify_qv_to ty ctx_ori in
  let result =
    match (a.NL.x, ty) with
    | NL.Lit _, _ ->
        let x = value_type_infer ctx a in
        let () = subtyping_check __FILE__ __LINE__ ctx x.ty (without_qv ty) in
        x
    | NL.Lam (id, body), UnderTy_arrow { argname; argty; retty } ->
        let () = erase_check __FILE__ __LINE__ (argty, id.ty) in
        let retty = UT.subst_id retty argname id.x in
        let ctx' = Qtypectx.add_to_right ctx (argty, id.x) in
        let body = term_type_check ctx' body (without_qv retty) in
        {
          ty =
            map_qv
              (fun retty -> UnderTy_arrow { argname; argty; retty })
              body.ty;
          x = Lam ({ ty = without_qv @@ argty; x = id.x }, body);
        }
    | NL.Fix (f, body), ty ->
        let () = erase_check __FILE__ __LINE__ (ty, f.ty) in
        let ctx' = Qtypectx.add_to_right ctx (ty, f.x) in
        let body = value_type_check ctx' body (without_qv ty) in
        { ty = body.ty; x = Fix ({ ty = without_qv ty; x = f.x }, body) }
    | _, _ -> _failatwith __FILE__ __LINE__ ""
  in
  close_qv_by_ctx_diff (ctx, result) ctx_ori

and handle_lettu ctx (tu, args, body) target_type =
  let open UL in
  let args = List.map (lit_type_infer ctx) args in
  let tu =
    erase_check_mk_id __FILE__ __LINE__ tu
      (UT.t_to_tuple_t (List.map (fun x -> x.ty) args))
  in
  let retqtf, tuty, ctx = unify_qv_to tu.ty ctx in
  let ctx' = Qtypectx.add_to_right ctx (tuty, tu.x) in
  let body =
    match target_type with
    | None -> term_type_infer ctx' body
    | Some ty -> term_type_check ctx' body ty
  in
  (* TODO: sanity check before hide depedent vars *)
  UL.
    {
      ty = retqtf @@ hide_vars_in_ctx ctx' [ tu.x ] body.ty;
      x = LetTu { tu; args; body };
    }

and handle_letdetu ctx (tu, args, body) target_type =
  let open UL in
  let open UT in
  let tu = id_type_infer ctx tu in
  let argsty =
    match distruct_tuple_t_opt tu.ty with
    | Some ts -> ts
    | _ -> _failatwith __FILE__ __LINE__ ""
  in
  let args =
    List.map (fun (x, ty) -> erase_check_mk_id __FILE__ __LINE__ x ty)
    @@ List.combine args argsty
  in
  let retqtfs, ctx' =
    List.fold_right
      (fun x (retqtf, ctx) ->
        let f, xty, ctx = unify_qv_to x.UL.ty ctx in
        let ctx = Qtypectx.add_to_right ctx (xty, x.x) in
        ((fun x -> f @@ retqtf x), ctx))
      args
      ((fun x -> x), ctx)
  in
  let body =
    match target_type with
    | None -> term_type_infer ctx' body
    | Some ty -> term_type_check ctx' body ty
  in
  (* TODO: sanity check before hide depedent vars *)
  let ty =
    retqtfs @@ hide_vars_in_ctx ctx' (List.map (fun x -> x.UL.x) args) body.ty
  in
  UL.{ ty; x = LetDeTu { tu; args; body } }

and handle_letapp ctx (ret, fty, args, body) self =
  let open UL in
  let args = List.map (lit_type_infer ctx) args in
  let argsty, retty = UT.destruct_arrow_tp fty in
  let _ =
    List.fold_left
      (fun ctx (arg, (ty, id)) ->
        let () = subtyping_check __FILE__ __LINE__ ctx arg.ty (without_qv ty) in
        let ctx' = Qtypectx.add_to_right ctx (ty, id) in
        ctx')
      ctx
    @@ List.combine args argsty
  in
  (* let fty' = UT.arrow_args_rename (List.map (fun x -> x.NL.x) args) f.ty in *)
  let ret = erase_check_mk_id __FILE__ __LINE__ ret (without_qv retty) in
  (* let retqtfs, ctx' = *)
  (*   List.fold_right *)
  (*     (fun x (retqtf, ctx) -> *)
  (*       let f, xty, ctx = unify_qv_to x.UL.ty ctx in *)
  (*       let ctx = Qtypectx.add_to_right ctx (xty, x.x) in *)
  (*       ((fun x -> f @@ retqtf x), ctx)) *)
  (*     args *)
  (*     ((fun x -> x), ctx) *)
  (* in *)
  let litbindings =
    List.map
      (fun arg -> lit_to_prop_lit (NT.to_smtty @@ UT.erase arg.ty, arg.x))
      args
  in
  let ret =
    {
      ty =
        List.fold_left
          (fun ret ((_, x), lit) -> UT.instantiate_vars (x, lit) ret)
          ret.ty
        @@ List.combine argsty litbindings;
      x = ret.x;
    }
  in
  let ctx' = Qtypectx.add_to_right ctx (ret.ty, ret.x) in
  let body = self ctx' body in
  (* TODO: sanity check before hide depedent vars *)
  (UT.hide_quantify_variable_in_ty ret.x ret.ty body.ty, (ret, args, body))

and handle_letval ctx (lhs, rhs, body) self =
  let open UL in
  let rhs = value_type_infer ctx rhs in
  let lhs = erase_check_mk_id __FILE__ __LINE__ lhs rhs.ty in
  let ctx' = Qtypectx.add_to_right ctx (lhs.ty, lhs.x) in
  let body = self ctx' body in
  (* TODO: sanity check before hide depedent vars *)
  {
    ty = UT.hide_quantify_variable_in_ty lhs.x lhs.ty body.ty;
    x = LetVal { lhs; rhs; body };
  }

and term_type_infer (ctx : ctx) (a : NL.term NL.typed) : UL.term UL.typed =
  let open NL in
  match a.x with
  | V v ->
      let v = value_type_infer ctx { ty = a.ty; x = v } in
      { ty = v.ty; x = V v.x }
  | LetTu { tu; args; body } ->
      handle_lettu ctx (tu, args, body) term_type_infer
  | LetDeTu { tu; args; body } ->
      handle_letdetu ctx (tu, args, body) term_type_infer
  | LetOp { ret; op; args; body } ->
      let argsty = List.map (fun x -> x.ty) args in
      let opty =
        Prim.get_primitive_under_ty
          (Op.PrimOp (op, NT.construct_arrow_tp (argsty, ret.ty)))
      in
      (* TODO: fix *)
      let opty = opty.t in
      let ty, (ret, args, body) =
        handle_letapp ctx (ret, opty, args, body) term_type_infer
      in
      { ty; x = LetOp { ret; op; args; body } }
  | LetApp { ret; f; args; body } ->
      let f = id_type_infer ctx f in
      let ty, (ret, args, body) =
        handle_letapp ctx (ret, f.ty, args, body) term_type_infer
      in
      { ty; x = LetApp { ret; f; args; body } }
  | LetVal { lhs; rhs; body } ->
      handle_letval ctx (lhs, rhs, body) term_type_infer
  | Ite { cond; e_t; e_f } ->
      let cond = id_type_infer ctx cond in
      let true_branch_prop x =
        Autov.(Prop.(Lit (AVar { ty = Smtty.Bool; x })))
      in
      let false_branch_prop x =
        Autov.(Prop.(Not (Lit (AVar { ty = Smtty.Bool; x }))))
      in
      let true_branch_ctx =
        Qtypectx.add_to_right ctx
          ( UT.base_type_add_conjunction_with_selfname true_branch_prop cond.ty,
            cond.x )
      in
      let false_branch_ctx =
        Qtypectx.add_to_right ctx
          ( UT.base_type_add_conjunction_with_selfname false_branch_prop cond.ty,
            cond.x )
      in
      let e_t = term_type_infer true_branch_ctx e_t in
      let e_f = term_type_infer false_branch_ctx e_f in
      let tys =
        [
          UT.base_type_add_conjunction (true_branch_prop cond.x) e_t.ty;
          UT.base_type_add_conjunction (false_branch_prop cond.x) e_f.ty;
        ]
      in
      let () =
        List.iter
          (fun ty ->
            Printf.printf "case ty: %s\n" @@ Frontend.Undertype.pretty_layout ty)
          tys
      in
      let ty = UT.disjunct_list tys in
      let () =
        Printf.printf "merged case ty: %s\n"
        @@ Frontend.Undertype.pretty_layout ty
      in
      (* NOTE: underappproximate here *)
      { ty; x = Ite { cond; e_t; e_f } }
  | Match { matched; cases } ->
      let matched = id_type_infer ctx matched in
      let handle_case { constructor; args; exp } =
        let rev_constructor_nt =
          let argsty, retty = NT.destruct_arrow_tp constructor.ty in
          match argsty with
          | [] -> retty
          | _ -> NT.(Ty_arrow (retty, Ty_tuple argsty))
        in
        let constructor_ty =
          Prim.get_primitive_rev_under_ty
            Op.(PrimOp (Dt constructor.x, rev_constructor_nt))
        in
        (* TODO: fix *)
        let constructor = UL.{ ty = constructor_ty.t; x = constructor.x } in
        let retty, args =
          let open UT in
          (* TODO: fix *)
          match constructor_ty.t with
          | UnderTy_base _ -> (constructor_ty.t, [])
          | UnderTy_arrow { argty; retty = UnderTy_tuple ts; argname } ->
              let ts = List.map (fun t -> UT.subst_id t argname matched.x) ts in
              let tsargs = _safe_combine __FILE__ __LINE__ ts args in
              let args =
                List.map
                  (fun (t, id) ->
                    match t with
                    | UnderTy_base { basename; normalty; prop } ->
                        ( UnderTy_base
                            {
                              basename = id;
                              normalty;
                              prop = P.subst_id prop basename id;
                            },
                          id )
                    | _ -> _failatwith __FILE__ __LINE__ "wrong rev under prim")
                  tsargs
              in
              (argty, args)
          | _ -> _failatwith __FILE__ __LINE__ "wrong rev under prim"
        in
        let branch_prop id =
          let basename, prop = UT.base_type_extract_prop retty in
          P.subst_id prop basename id
        in
        let ctx' =
          Qtypectx.add_to_rights ctx
          @@ UT.
               ( base_type_add_conjunction_with_selfname branch_prop matched.ty,
                 matched.x )
             :: args
        in
        let exp = term_type_infer ctx' exp in
        let casety =
          UT.base_type_add_conjunction (branch_prop matched.x) exp.ty
        in
        (casety, UL.{ constructor; args = List.map snd args; exp })
      in
      let tys, cases = List.split @@ List.map handle_case cases in
      let () =
        List.iter
          (fun ty ->
            Printf.printf "case ty: %s\n" @@ Frontend.Undertype.pretty_layout ty)
          tys
      in
      let ty = UT.disjunct_list tys in
      let () =
        Printf.printf "merged case ty: %s\n"
        @@ Frontend.Undertype.pretty_layout ty
      in
      { ty; x = Match { matched; cases } }

and term_type_check (ctx : ctx) (x : NL.term NL.typed) (ty : UT.t) :
    UL.term UL.typed =
  let () = Printf.printf "%s\n" (layout_judge ctx (x, ty)) in
  let () = erase_check __FILE__ __LINE__ (ty, x.ty) in
  let self ctx e = term_type_check ctx e ty in
  let open NL in
  match (x.x, ty) with
  | V v, _ ->
      let v = value_type_check ctx { ty = x.ty; x = v } ty in
      { ty = v.ty; x = V v.x }
  | LetTu { tu; args; body }, _ -> handle_lettu ctx (tu, args, body) self
  | LetDeTu { tu; args; body }, _ -> handle_letdetu ctx (tu, args, body) self
  | LetApp { ret; f; args; body }, _ ->
      let f = id_type_infer ctx f in
      let ty, (ret, args, body) =
        handle_letapp ctx (ret, f.ty, args, body) self
      in
      { ty; x = LetApp { ret; f; args; body } }
  | LetOp { ret; op; args; body }, _ ->
      let argsty = List.map (fun x -> x.ty) args in
      let opty =
        Prim.get_primitive_under_ty
          (Op.PrimOp (op, NT.construct_arrow_tp (argsty, ret.ty)))
      in
      (* TODO: fix *)
      let opty = opty.t in
      let ty', (ret, args, body) =
        handle_letapp ctx (ret, opty, args, body) self
      in
      (* let _ = *)
      (*   Printf.printf "ret = _:%s\n" @@ Frontend.Undertype.pretty_layout ty' *)
      (* in *)
      { ty = ty'; x = LetOp { ret; op; args; body } }
  | LetVal { lhs; rhs; body }, _ -> handle_letval ctx (lhs, rhs, body) self
  | Ite _, _ | Match _, _ ->
      let x = term_type_infer ctx x in
      let () = subtyping_check __FILE__ __LINE__ ctx x.ty ty in
      (* NOTE: underappproximate here *)
      { ty; x = x.x }

let type_check x ty = term_type_check [] x ty

module SNA = Languages.StrucNA
module SOA = Languages.StrucOA

let struc_check l r =
  let open SNA in
  List.iter
    (fun (name', ty) ->
      match List.find_opt (fun { name; _ } -> String.equal name name') l with
      | None -> _failatwith __FILE__ __LINE__ "does not provide source code"
      | Some { body; _ } ->
          let _ = type_check body ty in
          ())
    r