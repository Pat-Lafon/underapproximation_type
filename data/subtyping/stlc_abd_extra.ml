let[@assert] rty1 =
  let num_arr_tau = (v >= 0 : [%v: int]) [@over] in
  let num = (v >= 0 : [%v: int]) [@over] in
  let gamma = (true : [%v: stlc_tyctx]) [@over] in
  let tau = (num_arr v num_arr_tau : [%v: stlc_ty]) [@over] in
  ((* (num == 0 && typing gamma v tau && num_app v num)
   (* && num_arr_tau == 0 *)
   (* || (num == 0 && not (num_arr_tau == 0)) *)
   || *) num > 0 && fun ((x_1 [@exists]) : bool) ->
      ( x_1 && fun ((arg_tau [@exists]) : stlc_ty) ((b_0 [@exists]) : int) ->
        0 <= b_0 && b_0 == num
        && fun ((num_app_func [@exists]) : int) ->
        0 <= num_app_func && num_app_func < b_0
        && fun ((func_ty [@exists]) : stlc_ty) ->
        stlc_ty_arr1 func_ty arg_tau
        && stlc_ty_arr2 func_ty tau
        && fun ((num_arr_func_ty [@exists]) : int) ->
        num_arr func_ty num_arr_func_ty && fun ((num_arr_1 [@exists]) : int) ->
        num_arr_1 >= 0
        && num_arr_1 == num_arr_func_ty
        && fun ((num_1 [@exists]) : int) ->
        num_1 >= 0 && num_arr_1 >= 0
        && (num_arr_1 < num_arr_tau || num_1 < num)
        && num_1 == num_app_func
        && fun ((x_7 [@exists]) : stlc_ty) ->
        stlc_ty_arr1 x_7 arg_tau && stlc_ty_arr2 x_7 tau
        && fun ((tau_0 [@exists]) : stlc_ty) ->
        num_arr tau_0 num_arr_1 && tau_0 == x_7
        && fun ((func [@exists]) : stlc_term) ->
        typing gamma func tau_0 && num_app func num_1
        && fun ((num_arr_arg_ty [@exists]) : int) ->
        num_arr arg_tau num_arr_arg_ty && fun ((num_arr_2 [@exists]) : int) ->
        num_arr_2 >= 0
        && num_arr_2 == num_arr_arg_ty
        && fun ((num_2 [@exists]) : int) ->
        num_2 >= 0 && num_arr_2 >= 0
        && (num_arr_2 < num_arr_tau || num_2 < num)
        && num_2 == num - num_app_func - 1
        && fun ((tau_1 [@exists]) : stlc_ty) ->
        num_arr tau_1 num_arr_2 && tau_1 == arg_tau
        && fun ((arg [@exists]) : stlc_term) ->
        typing gamma arg tau_1 && num_app arg num_2 && stlc_app1 v func
        && stlc_app2 v arg )
      || (not x_1)
         && fun ((tau1 [@exists]) : stlc_ty) ((tau2 [@exists]) : stlc_ty) ->
         stlc_ty_arr1 tau tau1 && stlc_ty_arr2 tau tau2
         && fun ((num_arr_tau2 [@exists]) : int) ->
         num_arr tau2 num_arr_tau2 && fun ((num_arr_3 [@exists]) : int) ->
         num_arr_3 >= 0 && num_arr_3 == num_arr_tau2
         && fun ((num_3 [@exists]) : int) ->
         num_3 >= 0 && num_arr_3 >= 0
         && (num_arr_3 < num_arr_tau || num_3 < num)
         && num_3 == num
         && fun ((x_13 [@exists]) : stlc_tyctx) ->
         stlc_tyctx_hd x_13 tau1 && stlc_tyctx_tl x_13 gamma
         && fun ((tau_2 [@exists]) : stlc_ty) ->
         num_arr tau_2 num_arr_3 && tau_2 == tau2
         && fun ((body [@exists]) : stlc_term) ->
         typing x_13 body tau_2 && num_app body num_3 && stlc_abs_ty v tau1
         && stlc_abs_body v body
   (* ((num == 0) && (num_arr_tau == 0)) || ((num == 0) && not (num_arr_tau == 0)) || (
      ∃x_0, (((x_0) <=> (num == 0)) && (not (x_0) <=> (num > 0)) && not (x_0) && (
         ∃x_1, (((x_1) && (
            ∃arg_tau, (∃b_0, ((0 <= b_0) && (b_0 == num) && (
               ∃num_app_func, ((0 <= num_app_func) && (num_app_func < b_0) && (∃func_ty, ((stlc_ty_arr1 func_ty arg_tau) && (stlc_ty_arr2 func_ty tau) && (∃num_arr_func_ty, ((num_arr func_ty num_arr_func_ty) && (∃num_arr_1, ((num_arr_1 >= 0) && (num_arr_1 == num_arr_func_ty) && (∃num_1, ((num_1 >= 0) && (num_arr_1 >= 0) && ((num_arr_1 < num_arr_tau) || (num_1 < num)) && (num_1 == num_app_func) && (∃x_7, ((stlc_ty_arr1 x_7 arg_tau) && (stlc_ty_arr2 x_7 tau) && (∃tau_0, ((num_arr tau_0 num_arr_1) && (tau_0 == x_7) && (∃func, ((typing gamma func tau_0) && (num_app func num_1) && (∃num_arr_arg_ty, ((num_arr arg_tau num_arr_arg_ty) && (∃num_arr_2, ((num_arr_2 >= 0) && (num_arr_2 == num_arr_arg_ty) && (∃num_2, ((num_2 >= 0) && (num_arr_2 >= 0) && ((num_arr_2 < num_arr_tau) || (num_2 < num)) && (num_2 == ((num - num_app_func) - 1)) && (∃tau_1, ((num_arr tau_1 num_arr_2) && (tau_1 == arg_tau) && (∃arg, ((typing gamma arg tau_1) && (num_app arg num_2) && (stlc_app1 v func) && (stlc_app2 v arg))))))))))))))))))))))))))))))) || (not (x_1) && (∃tau1, (∃tau2, ((stlc_ty_arr1 tau tau1) && (stlc_ty_arr2 tau tau2) && (∃num_arr_tau2, ((num_arr tau2 num_arr_tau2) && (∃num_arr_3, ((num_arr_3 >= 0) && (num_arr_3 == num_arr_tau2) && (∃num_3, ((num_3 >= 0) && (num_arr_3 >= 0) && ((num_arr_3 < num_arr_tau) || (num_3 < num)) && (num_3 == num) && (∃x_13, ((stlc_tyctx_hd x_13 tau1) && (stlc_tyctx_tl x_13 gamma) && (∃tau_2, ((num_arr tau_2 num_arr_3) && (tau_2 == tau2) && (∃body, ((typing x_13 body tau_2) && (num_app body num_3) && (stlc_abs_ty v tau1) && (stlc_abs_body v body))))))))))))))))))))) *)
    : [%v: stlc_term])
    [@under]

let[@assert] rty2 =
  let num_arr_tau = (v >= 0 : [%v: int]) [@over] in
  let num = (v >= 0 : [%v: int]) [@over] in
  let gamma = (true : [%v: stlc_tyctx]) [@over] in
  let tau = (num_arr v num_arr_tau : [%v: stlc_ty]) [@over] in
  (typing gamma v tau && num_app v num : [%v: stlc_term]) [@under]
