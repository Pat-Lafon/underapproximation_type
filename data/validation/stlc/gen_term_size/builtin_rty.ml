let[@library] get_num_arr =
  let s = (true : [%v: stlc_ty]) [@over] in
  (num_arr s v : [%v: int]) [@under]

let[@library] gen_type =
  let s = (true : [%v: unit]) [@over] in
  (true : [%v: stlc_ty]) [@under]

(* let[@library] vars_with_type =
  let gamma = (true : [%v: stlc_tyctx]) [@over] in
  let tau = (true : [%v: stlc_ty]) [@over] in
  (typing gamma v tau && is_var v : [%v: stlc_term]) [@under]
 *)
let[@library] gen_term_no_app =
  let gamma = (true : [%v: stlc_tyctx]) [@over] in
  let tau = (true : [%v: stlc_ty]) [@over] in
  (typing gamma v tau && num_app v 0 : [%v: stlc_term]) [@under]

(* let[@library] ( == ) =
     let a = (true : [%v: int]) [@over] in
     let b = (true : [%v: int]) [@over] in
     (iff v (a == b) : [%v: bool]) [@under]

   let[@library] ( != ) =
     let a = (true : [%v: int]) [@over] in
     let b = (true : [%v: int]) [@over] in
     (iff v (a != b) : [%v: bool]) [@under] *)

(* let[@library] ( < ) =
     let a = (true : [%v: int]) [@over] in
     let b = (true : [%v: int]) [@over] in
     (iff v (a < b) : [%v: bool]) [@under]

   let[@library] ( > ) =
     let a = (true : [%v: int]) [@over] in
     let b = (true : [%v: int]) [@over] in
     (iff v (a > b) : [%v: bool]) [@under] *)

(* let[@library] ( <= ) =
     let a = (true : [%v: int]) [@over] in
     let b = (true : [%v: int]) [@over] in
     (iff v (a <= b) : [%v: bool]) [@under]

   let[@library] ( >= ) =
     let a = (true : [%v: int]) [@over] in
     let b = (true : [%v: int]) [@over] in
     (iff v (a >= b) : [%v: bool]) [@under] *)

let[@library] ( - ) =
  let a = (true : [%v: int]) [@over] in
  let b = (true : [%v: int]) [@over] in
  (v == a - b : [%v: int]) [@under]

(* let[@library] TT = (true : [%v: unit]) [@under] *)
let[@library] True = (v : [%v: bool]) [@under]
let[@library] False = (not v : [%v: bool]) [@under]

(* STLC *)

let[@library] Stlc_ty_nat = (stlc_ty_nat v : [%v: stlc_ty]) [@under]

let[@library] Stlc_ty_arr =
  let t1 = (true : [%v: stlc_ty]) [@over] in
  let t2 = (true : [%v: stlc_ty]) [@over] in
  (stlc_ty_arr1 v t1 && stlc_ty_arr2 v t2 : [%v: stlc_ty]) [@under]

(* let[@library] Stlc_const =
   let n = (true : [%v: int]) [@over] in
   (stlc_const v n : [%v: stlc_term]) [@under] *)

(* let[@library] Stlc_id =
   let n = (true : [%v: int]) [@over] in
   (stlc_id v n : [%v: stlc_term]) [@under] *)

let[@library] Stlc_app =
  let t1 = (true : [%v: stlc_term]) [@over] in
  let t2 = (true : [%v: stlc_term]) [@over] in
  (stlc_app1 v t1 && stlc_app2 v t2 : [%v: stlc_term]) [@under]

let[@library] Stlc_abs =
  let ty = (true : [%v: stlc_ty]) [@over] in
  let body = (true : [%v: stlc_term]) [@over] in
  (stlc_abs_ty v ty && stlc_abs_body v body : [%v: stlc_term]) [@under]

(* let[@library] Stlc_tyctx_nil = (stlc_tyctx_emp v : [%v: stlc_tyctx]) [@under] *)

let[@library] Stlc_tyctx_cons =
  let ty = (true : [%v: stlc_ty]) [@over] in
  let ctx = (true : [%v: stlc_tyctx]) [@over] in
  (stlc_tyctx_hd v ty && stlc_tyctx_tl v ctx : [%v: stlc_tyctx]) [@under]

(* the built-in random generators *)

(* let[@library] int_range =
   let a = (true : [%v: int]) [@over] in
   let b = (1 + a < v : [%v: int]) [@over] in
   (a < v && v < b : [%v: int]) [@under] *)

let[@library] bool_gen =
  let _ = (true : [%v: unit]) [@over] in
  (true : [%v: bool]) [@under]

let[@library] hidden_stlc_term_gen =
  let _ = (true : [%v: unit]) [@over] in
  (true : [%v: stlc_term]) [@under]

let[@library] sizecheck =
  let x = (true : [%v: int]) [@over] in
  (iff v (x == 0) && iff (not v) (x > 0) : [%v: bool]) [@under]

let[@library] int_range_inex =
  let a = (true : [%v: int]) [@over] in
  let b = (a <= v : [%v: int]) [@over] in
  (a <= v && v < b : [%v: int]) [@under]

(* let[@library] dummy = (true : [%v: unit]) [@under] *)
