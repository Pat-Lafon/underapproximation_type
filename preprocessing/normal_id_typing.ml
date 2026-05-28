open Language
open Sugar

type t = Nt.t

let _unify file line t1 t2 =
  match (t1, t2) with
  | _, Nt.Ty_unknown -> t1
  | Nt.Ty_unknown, _ -> t2
  | t1, t2 -> Nt._type_unify file line t1 t2

let bi_typed_id_infer (ctx : t ctx) (x : (t, string) typed) :
    (t, string) typed =
  let ctx_ty = match get_opt ctx x.x with Some t -> t | None -> Nt.Ty_unknown in
  let ty = _unify __FILE__ __LINE__ ctx_ty x.ty in
  match ty with
  | Nt.Ty_unknown ->
      let () =
        Printf.printf "(%s: %s) =? %s\n" x.x (Nt.layout ctx_ty) (Nt.layout x.ty)
      in
      _die_with [%here] ("die: can't unify " ^ x.x)
  | _ -> { ty; x = x.x }

let bi_typed_id_check (ctx : t ctx) (x : (t, string) typed) (ty : t) :
    (t, string) typed =
  let x = bi_typed_id_infer ctx x in
  let ty = Nt._type_unify __FILE__ __LINE__ x.ty ty in
  { ty; x = x.x }
