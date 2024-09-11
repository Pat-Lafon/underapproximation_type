(* val get_num_arr : stlc_ty -> int
val gen_type : unit -> stlc_ty
val vars_with_type : stlc_tyctx -> stlc_ty -> stlc_term
val gen_term_no_app : stlc_tyctx -> stlc_ty -> stlc_term *)

let rec gen_term_size (num_arr_tau : int) (num : int) (gamma : stlc_tyctx)
    (tau : stlc_ty) : stlc_term =
  if sizecheck num then gen_term_no_app gamma tau
  else if bool_gen () then Err
  else
    match tau with
    | Stlc_ty_nat -> Err
    | Stlc_ty_arr (tau1, tau2) ->
        let (num_arr_tau2 : int) = get_num_arr tau2 in
        let (body : stlc_term) =
          gen_term_size num_arr_tau2 num (Stlc_tyctx_cons (tau1, gamma)) tau2
        in
        Stlc_abs (tau1, body)

let[@assert] gen_term_size =
  let num_arr_tau = (v >= 0 : [%v: int]) [@over] in
  let num = (v >= 0 : [%v: int]) [@over] in
  let gamma = (true : [%v: stlc_tyctx]) [@over] in
  let tau = (num_arr v num_arr_tau : [%v: stlc_ty]) [@over] in
  (typing gamma v tau && num_app v num : [%v: stlc_term]) [@under]
