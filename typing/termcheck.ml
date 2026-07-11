open Language
open Zutils
open Common

let term_type_check (bctx : built_in_ctx) (rctx : rctx) body rty =
  try Bidirect.term_type_check bctx rctx (body, rty)
  with RecArgCheckFailure -> None

let term_type_infer (bctx : built_in_ctx) (rctx : rctx) body =
  try Bidirect.term_type_infer bctx rctx body with RecArgCheckFailure -> None

let value_type_infer (bctx : built_in_ctx) (rctx : rctx) v =
  Bidirect.value_type_infer bctx rctx v

let _mk_rec_arg_phi name typed_args =
  let open Prop in
  let arr_ty =
    Nt.construct_arr_tp (List.map (fun a -> a.ty) typed_args, Nt.bool_ty)
  in
  let op = name#:arr_ty in
  lit_to_prop (AAppOp (op, List.map tvar_to_lit typed_args))

let apply_rec_arg1 (fixarg : (Nt.t, string) typed) : Nt.t cty =
  { nty = fixarg.ty; phi = mk_self_wf_dec fixarg }

let apply_rec_arg2 (arg : (Nt.t, string) typed) (arg' : (Nt.t, string) typed)
    (arg1 : (Nt.t, string) typed) : Nt.t cty =
  let nty = arg1.ty in
  let phi = _mk_rec_arg_phi "rec_arg2" [ arg; arg'; arg1; default_v#:nty ] in
  { nty; phi }
