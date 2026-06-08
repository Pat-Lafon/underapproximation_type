open Language
open Zutils
open Sugar
open Auxtyping
open Inference
open Feature

type t = Nt.t

let abductive_infer_subtyping_query ~(features : t lit list)
    ~(verifier : t prop -> bool) ~(sanity_check : t prop -> bool) =
  match Cegis.cegis features verifier sanity_check with
  | None -> _failatwith [%here] "end"
  | Some res -> res

let abductive_infer_cty (uctx : Termcheck.uctx) cty1 cty2 =
  let vars =
    List.filter_map
      (fun x ->
        match x.ty with
        | RtyBase { ou = Over; _ } -> Some x.x #: (erase_rty x.ty)
        | _ -> None)
      (Typectx.ctx_to_list uctx.rctx.rty_ctx)
  in
  let v = default_v #: cty1.nty in
  let vars = v :: vars in
  let features = mk_features (Feature.get_template ()) vars in
  let verifier prop =
    let phi = smart_or [ prop; cty1.phi ] in
    let cty1' = { nty = cty1.nty; phi } in
    let res = sub_cty Under uctx.rctx cty1' cty2 in
    let () =
      Myconfig._log_queries @@ fun _ ->
      Pp.printf "@{<bold>@{<orange>Verifier:@} %b@}\n" res
    in
    res
  in
  let sanity_check phi =
    let cty1' = { nty = cty1.nty; phi } in
    let res = non_emptiness_cty uctx.rctx cty1' in
    let () =
      Myconfig._log_queries @@ fun _ ->
      Pp.printf "@{<bold>@{<orange>Sanity_check:@} %b@}\n" res
    in
    res
  in
  let phi' = abductive_infer_subtyping_query ~features ~verifier ~sanity_check in
  { nty = cty2.nty; phi = smart_add_to phi' cty2.phi }

let abductive_infer_rty uctx rty1 rty2 =
  match (rty1, rty2) with
  | RtyBase { ou = Under; cty = cty1 }, RtyBase { ou = Under; cty = cty2 } ->
      let cty = abductive_infer_cty uctx cty1 cty2 in
      RtyBase { ou = Under; cty }
  | _, _ -> _failatwith [%here] "unimp"
