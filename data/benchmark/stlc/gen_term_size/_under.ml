external method_predicates : t = "size" "dec_pair" "size_app" "typing"

let[@library] nonderter_dec =
  let a = (v > 0 : [%v: int]) [@over] in
  (0 <= v && v < a : [%v: int]) [@under]

let[@library] gen_type_size =
  let s = (v >= 0 : [%v: int]) [@over] in
  (size v s : [%v: stlc_ty]) [@under]

let[@library] gen_const =
  let a = (true : [%v: unit]) [@over] in
  (is_const v : [%v: stlc_term]) [@under]

let[@library] or_var_in_typectx =
  let a = (true : [%v: stlc_term]) [@over] in
  let tau = (true : [%v: stlc_ty]) [@over] in
  let gamma = (true : [%v: stlc_tyctx]) [@over] in
  ((implies (typing gamma a tau) (typing gamma v tau)
   && implies (no_app a) (no_app v)
   && implies (no_app a) (no_app v)
   && fun (u : [%forall: int]) -> implies (size_app a u) (size_app a v))
   || typing_var gamma v tau
    : [%v: stlc_term])
    [@under]

let[@library] gen_term_no_app =
  let size_of_tau = (v >= 0 : [%v: int]) [@over] in
  let tau = (size v size_of_tau : [%v: stlc_ty]) [@over] in
  let gamma = (true : [%v: stlc_tyctx]) [@over] in
  (typing gamma v tau && no_app v : [%v: stlc_term]) [@under]

let gen_term_size =
  let dec = (v >= 0 : [%v: int]) [@over] in
  let num_app = (v >= 0 : [%v: int]) [@over] in
  let tau = (dec_pair dec num_app v : [%v: stlc_ty]) [@over] in
  let gamma = (true : [%v: stlc_tyctx]) [@over] in
  (typing gamma v tau && size_app v num_app : [%v: stlc_term]) [@under]
