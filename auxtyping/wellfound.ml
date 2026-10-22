open Language
open Zutils

let mk_self_wf_dec x =
  let open Prop in
  let v = tvar_to_lit default_v#:x.ty in
  if Nt.equal_nt x.ty Nt.int_ty then
    And [ Cmp (Lt, v, tvar_to_lit x); Cmp (Ge, v, (AC (I 0))#:Nt.int_ty) ]
  else
    let lt = "decreasing"#:Nt.(construct_arr_tp ([ x.ty; x.ty ], bool_ty)) in
    lit_to_prop (AAppOp (lt, [ v; tvar_to_lit x ]))
