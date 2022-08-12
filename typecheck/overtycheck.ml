module T = Autov.Smtty
module NT = Languages.Normalty
open Languages.Overty
open Sugar

let infer_id ctx name =
  let open Autov.Prop in
  match Typectx.get_opt ctx name.x with
  | None -> failwith "free variable in refinement type"
  | Some ty -> { ty; x = name.x }

let rec infer_lit ctx lit =
  let open Autov.Prop in
  match lit with
  | AVar id -> AVar (infer_id ctx id)
  | ACint _ | ACbool _ -> lit
  | AOp2 (mp, a, b) ->
      let a = infer_lit ctx a in
      let b = infer_lit ctx b in
      if T.eq (lit_get_ty a, T.Int) && T.eq (lit_get_ty b, T.Int) && is_op mp
      then AOp2 (mp, a, b)
      else _failatwith __FILE__ __LINE__ ""

let infer_prop ctx t =
  let open Autov.Prop in
  let rec aux ctx t =
    match t with
    | Lit lit -> Lit (infer_lit ctx lit)
    | Implies (e1, e2) -> Implies (aux ctx e1, aux ctx e2)
    | Ite (e1, e2, e3) -> Ite (aux ctx e1, aux ctx e2, aux ctx e3)
    | Not e -> Not (aux ctx e)
    | And es -> And (List.map (aux ctx) es)
    | Or es -> Or (List.map (aux ctx) es)
    | Iff (e1, e2) -> Iff (aux ctx e1, aux ctx e2)
    | MethodPred (mp, args) -> MethodPred (mp, List.map (infer_lit ctx) args)
    | Forall (u, e) ->
        let ctx = Typectx.add_to_right ctx (u.ty, u.x) in
        Forall (u, aux ctx e)
    | Exists (u, e) ->
        let ctx = Typectx.add_to_right ctx (u.ty, u.x) in
        Exists (u, aux ctx e)
  in
  aux ctx t

let infer t =
  let rec aux ctx = function
    | OverTy_base { basename; normalty; prop } ->
        let ctx = Typectx.add_to_right ctx (NT.to_smtty normalty, basename) in
        OverTy_base { basename; normalty; prop = infer_prop ctx prop }
    | OverTy_arrow { argname; argty; retty } ->
        let argty = aux ctx argty in
        let ctx =
          Typectx.add_to_right ctx (NT.to_smtty @@ erase argty, argname)
        in
        OverTy_arrow { argname; argty; retty = aux ctx retty }
    | OverTy_tuple ts -> OverTy_tuple (List.map (aux ctx) ts)
  in
  aux Typectx.empty t