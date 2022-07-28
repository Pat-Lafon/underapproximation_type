module NL = Languages.NormalAnormal
module OL = Languages.OverAnormal
module NT = Languages.Normalty
module OT = Languages.Overty
open Zzdatatype.Datatype
open Abstraction
open Sugar

let layout_judge = Frontend.Typectx.pretty_layout_over_judge Trans.nan_to_term

let erase_check file line (overfty, normalty) =
  (* let () = *)
  (*   Printf.printf "|_ %s _| = %s\n" *)
  (*     (Frontend.Overtype.layout overfty) *)
  (*     (Frontend.Type.layout @@ OT.erase overfty) *)
  (* in *)
  let _ = _check_equality file line NT.eq (OT.erase overfty) normalty in
  ()

let erase_check_mk_id file line id overfty =
  (* let () = *)
  (*   Printf.printf "|_ %s _| = %s\n" *)
  (*     (Frontend.Overtype.layout overfty) *)
  (*     (Frontend.Type.layout @@ OT.erase overfty) *)
  (* in *)
  let _ = _check_equality file line NT.eq (OT.erase overfty) id.NL.ty in
  OL.{ ty = overfty; x = id.x }

let hide_depedent_var ctx name ty =
  match List.rev ctx with
  | (name', argty) :: _ when String.equal name name' ->
      OT.forall_quantify_variable_in_ty name argty ty
  | _ -> _failatwith __FILE__ __LINE__ "not a well founded ctx, naming error"

let const_type_infer v =
  let open Value in
  match v with
  | U -> _failatwith __FILE__ __LINE__ ""
  | I n ->
      OT.(
        make_basic "_nu" NT.Ty_int (fun nu ->
            P.(Lit (AOp2 ("==", AVar nu, ACint n)))))
  | B true -> OT.(make_basic "_nu" NT.Ty_int (fun nu -> Lit (AVar nu)))
  | B false -> OT.(make_basic "_nu" NT.Ty_int (fun nu -> Not (Lit (AVar nu))))
  | _ -> _failatwith __FILE__ __LINE__ ""

let rec id_type_infer (ctx : OT.t Typectx.t) (id : NL.id NL.typed) :
    NL.id OL.typed =
  let ty =
    try Prim.get_primitive_over_ty id.x
    with _ ->
      let ty = Typectx.get_ty ctx id.x in
      let ty =
        OT.(
          match ty with
          | OverTy_base { basename; normalty; prop } ->
              OverTy_base
                {
                  basename = id.x;
                  normalty;
                  prop = P.subst_id prop basename id.x;
                }
          | _ -> ty)
      in
      ty
  in
  erase_check_mk_id __FILE__ __LINE__ id ty

and id_type_check (ctx : OT.t Typectx.t) (id : NL.id NL.typed) (ty : OT.t) :
    NL.id OL.typed =
  let id = id_type_infer ctx id in
  let () = Oversub.subtyping_check ctx id.OL.ty ty in
  id

and value_type_infer (ctx : OT.t Typectx.t) (a : NL.value NL.typed) :
    OL.value OL.typed =
  let open NL in
  match a.x with
  | Const v -> OL.{ ty = const_type_infer v; x = Const v }
  | Var x ->
      let x = id_type_infer ctx { ty = a.ty; x } in
      OL.{ ty = x.ty; x = Var x.x }
  | Lam (_, _) ->
      (* NOTE: Can we infer a type of the lambda function without the argment type? *)
      _failatwith __FILE__ __LINE__ "cannot infer over arrow type"
  | Fix _ -> _failatwith __FILE__ __LINE__ "unimp"

and value_type_check (ctx : OT.t Typectx.t) (a : NL.value NL.typed) (ty : OT.t)
    : OL.value OL.typed =
  let open NL in
  match (a.x, ty) with
  | Const _, _ | Var _, _ ->
      let x = value_type_infer ctx a in
      let () = Oversub.subtyping_check ctx x.ty ty in
      x
  | Lam (id, body), OT.(OverTy_arrow { argname; argty; retty }) ->
      let () = erase_check __FILE__ __LINE__ (argty, id.ty) in
      let retty = OT.subst_id retty argname id.x in
      let ctx' = Typectx.overlap ctx (argty, id.x) in
      let body = term_type_check ctx' body retty in
      { ty; x = Lam ({ ty = argty; x = id.x }, body) }
  | Fix (f, body), ty ->
      let () = erase_check __FILE__ __LINE__ (ty, f.ty) in
      let ctx' = Typectx.overlap ctx (ty, f.x) in
      let body = value_type_check ctx' body ty in
      { ty; x = Fix ({ ty; x = f.x }, body) }
  | _, _ -> _failatwith __FILE__ __LINE__ ""

and handle_lettu ctx (tu, args, body) self =
  let open OL in
  let args = List.map (id_type_infer ctx) args in
  let tuty = OT.OverTy_tuple (List.map (fun x -> x.ty) args) in
  let tu = erase_check_mk_id __FILE__ __LINE__ tu tuty in
  let tu = { x = tu.x; ty = tuty } in
  let ctx' = Typectx.overlap ctx (tu.ty, tu.x) in
  let body = self ctx' body in
  (* TODO: sanity check before hide depedent vars *)
  {
    ty = OT.forall_quantify_variable_in_ty tu.x tu.ty body.ty;
    x = LetTu { tu; args; body };
  }

and handle_letdetu ctx (tu, args, body) self =
  let open OL in
  let tu = id_type_infer ctx tu in
  let argsty =
    match tu.ty with
    | OT.OverTy_tuple ts -> ts
    | _ -> _failatwith __FILE__ __LINE__ ""
  in
  let args =
    List.map (fun (x, ty) -> erase_check_mk_id __FILE__ __LINE__ x ty)
    @@ List.combine args argsty
  in
  let ctx' =
    List.fold_left
      (fun ctx' id ->
        let ctx' = Typectx.overlap ctx' (id.ty, id.x) in
        ctx')
      ctx args
  in
  let body = self ctx' body in
  (* TODO: sanity check before hide depedent vars *)
  let ty =
    List.fold_right
      (fun id ty -> OT.forall_quantify_variable_in_ty id.x id.ty ty)
      args body.ty
  in
  { ty; x = LetDeTu { tu; args; body } }

and handle_letapp ctx (ret, f, args, body) self =
  let open OL in
  let f = id_type_infer ctx f in
  let fty' = OT.arrow_args_rename (List.map (fun x -> x.NL.x) args) f.ty in
  let argsty, retty = OT.destruct_arrow_tp fty' in
  let args =
    List.map (fun ((argty, _), arg) -> id_type_check ctx arg argty)
    @@ List.combine argsty args
  in
  let ret = erase_check_mk_id __FILE__ __LINE__ ret retty in
  let ctx' = Typectx.overlap ctx (ret.ty, ret.x) in
  let body = self ctx' body in
  (* TODO: sanity check before hide depedent vars *)
  {
    ty = OT.forall_quantify_variable_in_ty ret.x ret.ty body.ty;
    x = LetApp { ret; f; args; body };
  }

and handle_letval ctx (lhs, rhs, body) self =
  let open OL in
  let rhs = value_type_infer ctx rhs in
  let lhs = erase_check_mk_id __FILE__ __LINE__ lhs rhs.ty in
  let ctx' = Typectx.overlap ctx (lhs.ty, lhs.x) in
  let body = self ctx' body in
  (* TODO: sanity check before hide depedent vars *)
  {
    ty = OT.forall_quantify_variable_in_ty lhs.x lhs.ty body.ty;
    x = LetVal { lhs; rhs; body };
  }

and term_type_infer (ctx : OT.t Typectx.t) (a : NL.term NL.typed) :
    OL.term OL.typed =
  let open NL in
  match a.x with
  | V v ->
      let v = value_type_infer ctx { ty = a.ty; x = v } in
      { ty = v.ty; x = V v.x }
  | LetTu { tu; args; body } ->
      handle_lettu ctx (tu, args, body) term_type_infer
  | LetDeTu { tu; args; body } ->
      handle_letdetu ctx (tu, args, body) term_type_infer
  | LetApp { ret; f; args; body } ->
      handle_letapp ctx (ret, f, args, body) term_type_infer
  | LetVal { lhs; rhs; body } ->
      handle_letval ctx (lhs, rhs, body) term_type_infer
  | Ite (_, _, _) -> _failatwith __FILE__ __LINE__ "should not infer ite"
  | Match (_, _) -> _failatwith __FILE__ __LINE__ "should not infer match"

and term_type_check (ctx : OT.t Typectx.t) (x : NL.term NL.typed) (ty : OT.t) :
    OL.term OL.typed =
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
      handle_letapp ctx (ret, f, args, body) self
  | LetVal { lhs; rhs; body }, _ -> handle_letval ctx (lhs, rhs, body) self
  | Ite (id, e1, e2), _ ->
      let id = id_type_infer ctx id in
      let true_branch_prop x =
        Autov.(Prop.(Lit (AVar { ty = Smtty.Bool; x })))
      in
      let false_branch_prop x =
        Autov.(Prop.(Not (Lit (AVar { ty = Smtty.Bool; x }))))
      in
      let true_branch_ctx =
        Typectx.overlap ctx
          (OT.base_type_add_conjunction true_branch_prop id.ty, id.x)
      in
      let false_branch_ctx =
        Typectx.overlap ctx
          (OT.base_type_add_conjunction false_branch_prop id.ty, id.x)
      in
      let e1 = term_type_check true_branch_ctx e1 ty in
      let e2 = term_type_check false_branch_ctx e2 ty in
      (* NOTE: overappproximate here *)
      { ty; x = Ite (id, e1, e2) }
  | Match (id, cases), _ ->
      let id = id_type_infer ctx id in
      let handle_case { constructor; args; exp } =
        let constructor_ty = Prim.get_primitive_over_ty constructor in
        let constructor_ty = OT.arrow_args_rename args constructor_ty in
        let args, retty = OT.destruct_arrow_tp constructor_ty in
        let retty_prop id =
          OT.(
            match retty with
            | OverTy_base { basename; prop; _ } -> P.subst_id prop basename id
            | _ -> _failatwith __FILE__ __LINE__ "bad constructor type")
        in
        let ctx' =
          Typectx.overlaps ctx @@ args
          @ [ (OT.base_type_add_conjunction retty_prop id.ty, id.x) ]
        in
        let exp = term_type_check ctx' exp ty in
        OL.{ constructor; args = List.map snd args; exp }
      in
      let cases = List.map handle_case cases in
      (* NOTE: overappproximate here *)
      { ty; x = Match (id, cases) }

(* let x = term_type_infer ctx x in *)
(* let () = Oversub.subtyping_check ctx x.ty ty in *)
(* (\* NOTE: overappproximate here *\) *)
(* { ty; x = x.x } *)

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
