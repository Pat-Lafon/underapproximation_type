open Language
open Zutils
open Common

type uctx = { bctx : built_in_ctx; rctx : rctx }

let add_to_rights (uctx : uctx) (vars : (Nt.t rty, string) typed list) : uctx =
  { uctx with rctx = Rctx.add_vars uctx.rctx vars }

let term_type_check (uctx : uctx) body rty =
  Bidirect.term_type_check uctx.bctx uctx.rctx (body, rty)

let term_type_infer (uctx : uctx) body =
  Bidirect.term_type_infer uctx.bctx uctx.rctx body

let value_type_infer (uctx : uctx) v =
  Bidirect.value_type_infer uctx.bctx uctx.rctx v

exception RecArgCheckFailure

let _cur_rec_func_name : (string * Nt.t cty * Nt.t) option ref = ref None

let init_cur_rec_func_name v = _cur_rec_func_name := Some v
let get_cur_rec_func_name () = !_cur_rec_func_name

let _mk_rec_arg_phi name typed_args =
  let open Prop in
  let arr_ty =
    Nt.construct_arr_tp (List.map (fun a -> a.ty) typed_args, Nt.bool_ty)
  in
  let op = name #: arr_ty in
  lit_to_prop (AAppOp (op, List.map tvar_to_lit typed_args))

let apply_rec_arg1 (fixarg : (Nt.t, string) typed) : Nt.t cty =
  { nty = fixarg.ty; phi = mk_self_wf_dec fixarg }

let apply_rec_arg2 (arg : (Nt.t, string) typed) (arg' : (Nt.t, string) typed)
    (arg1 : (Nt.t, string) typed) : Nt.t cty =
  let nty = arg1.ty in
  let phi =
    _mk_rec_arg_phi "rec_arg2" [ arg; arg'; arg1; default_v #: nty ]
  in
  { nty; phi }

let term_type_infer_with_rec_check uctx body =
  try term_type_infer uctx body with RecArgCheckFailure -> None
