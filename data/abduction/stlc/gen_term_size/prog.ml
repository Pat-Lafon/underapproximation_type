val nonderter_dec : int -> int
val gen_type : unit -> stlc_ty
val gen_const : unit -> stlc_term
val vars_with_type : stlc_ty -> stlc_tyctx -> stlc_term
val gen_term_no_app : stlc_ty -> stlc_tyctx -> stlc_term

let[@library] nonderter_dec =
  let a = (v > 0 : [%v: int]) [@over] in
  (v == a - 1 : [%v: int]) [@under]

let[@library] gen_type =
  let s = (true : [%v: unit]) [@over] in
  (true : [%v: stlc_ty]) [@under]

let[@library] gen_const =
  let a = (true : [%v: unit]) [@over] in
  (is_const v : [%v: stlc_term]) [@under]

let[@library] vars_with_type =
  let tau = (true : [%v: stlc_ty]) [@over] in
  let gamma = (true : [%v: stlc_tyctx]) [@over] in
  (typing gamma v tau && is_var v : [%v: stlc_term]) [@under]

let[@library] gen_term_no_app =
  let tau = (true : [%v: stlc_ty]) [@over] in
  let gamma = (true : [%v: stlc_tyctx]) [@over] in
  (typing gamma v tau && num_app v 0 : [%v: stlc_term]) [@under]

let rec gen_term_size (dec : int) (num : int) (tau : stlc_ty)
    (gamma : stlc_tyctx) : stlc_term =
  if num == 0 then gen_term_no_app tau gamma
  else if bool_gen () then vars_with_type tau gamma
  else if bool_gen () then
    let (arg_tau : stlc_ty) = gen_type () in
    let (num_func : int) = int_range_inex 0 num in
    let (num_arg : int) = int_range_inex 0 (num - num_func) in
    let (dec_dec : int) = nonderter_dec dec in
    let (func : stlc_term) =
      gen_term_size dec_dec num_func (Stlc_ty_arr (arg_tau, tau)) gamma
    in
    let (arg : stlc_term) = gen_term_size dec_dec num_arg arg_tau gamma in
    Stlc_app (func, arg)
  else
    match tau with
    | Stlc_ty_nat -> Err
    | Stlc_ty_arr (tau1, tau2) ->
        let (dec_dec1 : int) = nonderter_dec dec in
        let (body : stlc_term) =
          gen_term_size dec_dec1 num tau2 (Stlc_tyctx_cons (tau1, gamma))
        in
        Stlc_abs (tau1, body)

let[@assert] gen_term_size =
  let dec = (v >= 0 : [%v: int]) [@over] in
  let num = (v >= 0 : [%v: int]) [@over] in
  let tau = (dec_pair v dec num : [%v: stlc_ty]) [@over] in
  let gamma = (true : [%v: stlc_tyctx]) [@over] in
  (typing gamma v tau && num_app v num : [%v: stlc_term]) [@under]
