open Language
open Sugar
open Zzdatatype.Datatype
open Normal_prop_typing
open Normal_rty_typing
open Normal_term_typing

type t = Nt.t

let constructor_declaration_mk_ (retty, { constr_name; args }) =
  let argsty = Constructor_declaration.get_arg_types args in
  constr_name#:(Nt.construct_arr_tp (argsty, retty))

let item_mk_ctx (e : t item) =
  match e with
  | MTyDecl { type_name; type_params; type_decl = Decl_constructors cs } ->
      let retty =
        Nt.Ty_constructor
          (type_name, List.map (fun x -> Nt.Ty_var x) type_params)
      in
      List.map (fun c -> constructor_declaration_mk_ (retty, c)) cs
  | MTyDecl { type_decl = Decl_record _; _ } -> []
  | MValDecl x -> [ x ]
  | MMethodPred mp -> [ mp ]
  | MAxiom _ -> []
  | MRty _ -> []
  | MFuncImpRaw _ | MFuncImp _ -> _die_with [%here] "not predefine"

let item_erase (e : 'a item) =
  match e with
  | MRty { name; rty; _ } -> MValDecl name#:(erase_rty rty)
  | _ -> e

let item_check ctx (e : t item) : t ctx * t item =
  match e with
  | MTyDecl { type_name; type_params; type_decl = Decl_constructors cs } ->
      let res =
        MTyDecl { type_name; type_params; type_decl = Decl_constructors cs }
      in
      let retty =
        Nt.Ty_constructor
          (type_name, List.map (fun x -> Nt.Ty_var x) type_params)
      in
      let xs =
        List.map (fun c -> constructor_declaration_mk_ (retty, c)) cs
      in
      (add_to_rights ctx xs, res)
  | MTyDecl ({ type_decl = Decl_record _; _ } as d) -> (ctx, MTyDecl d)
  | MValDecl x ->
      let res = MValDecl x in
      (add_to_right ctx x, res)
  | MMethodPred x ->
      let res = MMethodPred x in
      (add_to_right ctx x, res)
  | MAxiom { name; prop } ->
      (ctx, MAxiom { name; prop = bi_typed_prop_check ctx prop })
  | MRty { is_assumption; name; rty } ->
      (ctx, MRty { is_assumption; name; rty = bi_typed_rty_check ctx rty })
  | MFuncImpRaw { name; if_rec = false; body } ->
      let body = bi_typed_term_infer ctx body in
      let name = name.x#:body.ty in
      (add_to_right ctx name, MFuncImpRaw { name; if_rec = false; body })
  | MFuncImpRaw { name; if_rec = true; body } ->
      let name_ty = Raw_term.__get_lam_term_ty __FILE__ __LINE__ body.x in
      let name = name.x#:name_ty in
      let ctx' = add_to_right ctx name in
      let body = bi_typed_term_check ctx' body name.ty in
      (ctx', MFuncImpRaw { name; if_rec = true; body })
  | MFuncImp _ -> _die_with [%here] "die"

let struct_mk_ctx ctx l =
  add_to_rights ctx @@ List.concat @@ List.map item_mk_ctx l

let struct_check (ctx : Nt.t Typectx.ctx) l =
  List.fold_left
    (fun (ctx, res) e ->
      let ctx, e = item_check ctx e in
      (ctx, res @ [ e ]))
    (ctx, []) l
