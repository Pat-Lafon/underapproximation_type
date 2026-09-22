open Language
open Common

let term_type_check (bctx : built_in_ctx) (rctx : rctx) body rty =
  try Bidirect.term_type_check bctx rctx (body, rty)
  with RecArgCheckFailure -> None

let term_type_infer (bctx : built_in_ctx) (rctx : rctx) body =
  try Bidirect.term_type_infer bctx rctx body with RecArgCheckFailure -> None

let value_type_infer (bctx : built_in_ctx) (rctx : rctx) v =
  Bidirect.value_type_infer bctx rctx v
