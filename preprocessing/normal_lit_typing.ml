open Language
open Normal_id_typing
open Normal_constant_typing
open Sugar

type t = Nt.t

let rec bi_typed_lit_check (ctx : t ctx) (lit : (t, t lit) typed)
    (ty : t) : (t, t lit) typed =
  match (lit.x, ty) with
  | AC _, _ | AVar _, _ ->
      let lit = bi_typed_lit_infer ctx lit in
      let _ = Nt._type_unify __FILE__ __LINE__ lit.ty ty in
      lit.x #: ty
  | ATu l, Nt.Ty_tuple tys ->
      let l =
        try
          List.map (fun (x, ty) -> bi_typed_lit_check ctx x ty)
          @@ _safe_combine __FILE__ __LINE__ l tys
        with Failure msg ->
          Printf.eprintf "ERROR [tuple_lit_check_safe_combine]: %s\n" msg;
          raise (Failure msg)
      in
      (ATu l) #: ty
  | AProj _, _ -> _die_with [%here] "unimp"
  | AAppOp (mp, args), _ ->
      let mp = bi_typed_id_infer ctx mp in
      let args' = List.map (bi_typed_lit_infer ctx) args in
      let mp_ty =
        try
          Nt._type_unify __FILE__ __LINE__ mp.ty
            (Nt.construct_arr_tp (List.map _get_ty args', ty))
        with Failure msg ->
          Printf.eprintf "ERROR [appop_check_type_unify]: mp.x=%s, %s\n" mp.x msg;
          raise (Failure msg)
      in
      let mp = mp.x #: mp_ty in
      let argsty, _ = Nt.destruct_arr_tp mp_ty in
      let args =
        try
          List.map (fun (x, ty) -> bi_typed_lit_check ctx x ty)
          @@ _safe_combine __FILE__ __LINE__ args argsty
        with Failure msg ->
          Printf.eprintf "ERROR [appop_check_safe_combine]: mp.x=%s, %s\n" mp.x msg;
          raise (Failure msg)
      in
      (AAppOp (mp, args)) #: ty
  | _, _ -> _die_with [%here] "lit type error"

and bi_typed_lit_infer (ctx : t ctx) (lit : (t, t lit) typed) :
    (t, t lit) typed =
  match lit.x with
  | AVar id ->
      let id =
        match id.ty with
        | Nt.Ty_unknown -> bi_typed_id_infer ctx id
        | ty ->
            let _ = failwith "endsd" in
            id.x #: ty
      in
      (AVar id) #: id.ty
  | AC c -> (
      match lit.ty with
      | Nt.Ty_unknown -> (AC c) #: (infer_constant c)
      | ty -> (AC c) #: ty)
  | ATu l ->
      let l = List.map (bi_typed_lit_infer ctx) l in
      let ty = Nt.mk_tuple (List.map _get_ty l) in
      (ATu l) #: ty
  | AProj _ -> _die_with [%here] "unimp"
  | AAppOp (mp, args) ->
      let mp = bi_typed_id_infer ctx mp in
      let args' = List.map (bi_typed_lit_infer ctx) args in
      let mp_ty =
        try
          Nt._type_unify __FILE__ __LINE__ mp.ty
            (Nt.construct_arr_tp (List.map _get_ty args', Ty_unknown))
        with Failure msg ->
          Printf.eprintf "ERROR [appop_infer_type_unify]: mp.x=%s, %s\n" mp.x msg;
          raise (Failure msg)
      in
      let mp = mp.x #: mp_ty in
      let argsty, retty = Nt.destruct_arr_tp mp_ty in
      let args =
        try
          List.map (fun (x, ty) -> bi_typed_lit_check ctx x ty)
          @@ _safe_combine __FILE__ __LINE__ args argsty
        with Failure msg ->
          Printf.eprintf "ERROR [appop_infer_safe_combine]: mp.x=%s, %s\n" mp.x msg;
          raise (Failure msg)
      in
      (AAppOp (mp, args)) #: retty
