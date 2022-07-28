module NL = Languages.NormalAnormal
module OL = Languages.OverAnormal
module NT = Languages.Normalty
module OT = Languages.Overty
open Zzdatatype.Datatype
open Sugar

let layout_subtyping = Frontend.Typectx.pretty_layout_over_subtyping

let subtyping_to_query ctx typeself (prop1, prop2) =
  let fv1 = Autov.prop_fv prop1 in
  let fv2 = Autov.prop_fv prop2 in
  let fv = fv1 @ fv2 in
  let ctx =
    List.filter_map
      (fun (x, ty) ->
        OT.(
          match ty with
          | OverTy_base { basename; prop; _ } ->
              let prop = P.subst_id prop basename x in
              Some (x, prop)
          | _ -> None))
      ctx
  in
  let () =
    List.iter
      (fun name ->
        if
          String.equal typeself name
          || List.exists (fun (x, _) -> String.equal name x) ctx
        then ()
        else _failatwith __FILE__ __LINE__ @@ "type context is not well founded")
      fv
  in
  let pre = List.map snd ctx in
  (pre @ [ prop1 ], prop2)

let subtyping_check (ctx : OT.t Typectx.t) (t1 : OT.t) (t2 : OT.t) =
  let open OT in
  let rec aux ctx (t1, t2) =
    let () = Printf.printf "Subtype: \n%s\n" @@ layout_subtyping ctx (t1, t2) in
    match (t1, t2) with
    | ( OverTy_base { basename = name1; prop = prop1; _ },
        OverTy_base { basename = name2; prop = prop2; _ } ) ->
        let typeself, prop1, prop2 =
          match (Typectx.in_ctx ctx name1, Typectx.in_ctx ctx name2) with
          | true, true ->
              ( _check_equality __FILE__ __LINE__ String.equal name1 name2,
                prop1,
                prop2 )
          | false, true -> (name2, P.subst_id prop1 name1 name2, prop2)
          | _, _ -> (name1, prop1, P.subst_id prop2 name2 name1)
        in
        let pres, res = subtyping_to_query ctx typeself (prop1, prop2) in
        if Autov.check_implies_multi_pre pres res then ()
        else failwith "Subtyping check: rejected by the verifier"
    | OverTy_tuple ts1, OverTy_tuple ts2 ->
        List.iter (aux ctx) @@ List.combine ts1 ts2
    | ( OverTy_arrow { argname = x1; argty = t11; retty = t12 },
        OverTy_arrow { argname = x2; argty = t21; retty = t22 } ) ->
        let t22 = subst_id t22 x2 x1 in
        let () = aux ctx (t21, t11) in
        let () = aux ctx (t12, t22) in
        ()
    | _, _ -> _failatwith __FILE__ __LINE__ "die: under subtype"
  in
  aux ctx (t1, t2)
