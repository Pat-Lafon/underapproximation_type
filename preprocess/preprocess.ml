include Basic_typing
include Normalization
open Language
open Zutils

let parse file =
  ocaml_structure_to_items
  @@ OcamlParser.Oparse.parse_imp_from_file ~sourcefile:file

let multi_parse files = List.concat_map parse files

(* Populate [Dtencoding.decl_registry]; [Prover._mk_prover] reads it at Z3 ctx creation.
   Skip non-uninterp names ([bool]/[option]/[int]/...) — handled by existing
   [smt_tp_to_sort] arms. Reject [CtorTuple] because synthesized positional
   accessors (e.g. [cons_0]) wouldn't match the axiom op names ([head]/[tail])
   that subtyping queries emit. *)
let collect_dt_decls items =
  let module D = Prop.Dtencoding in
  let ctor_of_decl type_name { constr_name; args } =
    let fields =
      match args with
      | CtorTuple [] -> []
      | CtorRecord xs ->
          List.map (fun x -> D.{ fname = x.x; ftype = x.ty }) xs
      | CtorTuple (_ :: _) ->
          Sugar._die_with [%here]
            (Printf.sprintf
               "Dtencoding: positional constructor `%s` in type `%s` is not \
                supported; use record syntax `{ field : type; ... }`"
               constr_name type_name)
    in
    D.{ cname = String.lowercase_ascii constr_name; fields }
  in
  let dt_decl_of_item = function
    | MTyDecl { type_name; type_decl = Decl_constructors decls; _ } ->
        if Nt.(is_uninterp (to_smtty (Ty_constructor (type_name, [])))) then
          let ctors = List.map (ctor_of_decl type_name) decls in
          Some D.{ dt_name = type_name; ctors }
        else None (* builtin smtty name like [unit]/[bool] — handled by [smt_tp_to_sort] *)
    | MTyDecl { type_decl = Decl_record _; _ } -> None (* record type, not a sum ADT *)
    | MValDecl _ | MMethodPred _ | MAxiom _ | MFuncImpRaw _ | MFuncImp _
    | MRty _ | MLocalRty _ ->
        None (* non-type items *)
  in
  List.iter D.register_decl (List.filter_map dt_decl_of_item items)

let predefined_files =
  [ "basic_typing.ml"; "refinement_typing.ml"; "wf_decreasing_axioms.ml" ]

let resolve_files (prim_path : MyconfigAst.preload_path) : string list =
  match
    ( prim_path.data_type_decls,
      prim_path.normal_typing,
      prim_path.coverage_typing,
      prim_path.axioms )
  with
  | Some dt, Some nt, Some ct, Some ax -> [ dt; nt; ct; ax ]
  | None, None, None, None ->
      List.map (spf "%s/%s" prim_path.predefined_path) predefined_files
  | _ ->
      failwith
        "prim_path: per-test fields (data_type_decls, normal_typing, \
         coverage_typing, axioms) must be all present or all absent; mixed \
         shapes are not supported"

let load_ctxs () =
  match !_ctxs with
  | Some ctxs -> ctxs
  | None ->
      let prim_path = Myconfig.get_prim_path () in
      let files = resolve_files prim_path in
      let items = multi_parse files in
      let () = collect_dt_decls items in
      let alias = Type_alias.item_mk_type_alias_ctx items in
      let items = Type_alias.item_inline alias items in
      let basic_ctx, items = struct_check builtin_basic_ctx items in
      let builtin_ctx =
        Typectx.add_to_rights (struct_mk_rty_ctx items) builtin_rty_ctx
      in
      let axioms = struct_mk_axiom_ctx items in
      let bctx = { builtin_ctx; cur_axiom_names = [] } in
      let bctx = axiom_add_to_rights bctx axioms in
      let res = (alias, basic_ctx, bctx) in
      _ctxs := Some res;
      res

let load_basic_ctx () =
  let _, basic_ctx, _ = load_ctxs () in
  basic_ctx

let load_bctx () =
  let _, _, bctx = load_ctxs () in
  bctx

let load_alias () =
  let alias, _, _ = load_ctxs () in
  alias

let preprocess source_files =
  let items = multi_parse source_files in
  let items' = Type_alias.item_inline (load_alias ()) items in
  let alias = Type_alias.item_mk_type_alias_ctx items' in
  let items' = Type_alias.item_inline alias items' in
  (* let () = Pp.printf "@{<bold>result:@}\n%s\n" (layout_structure items) in *)
  (* let () = Pp.printf "@{<bold>result:@}\n%s\n" (layout_structure items') in *)
  let _, code = struct_check (load_basic_ctx ()) items' in
  let code = Type_alias.item_inline alias code in
  let code = Type_alias.item_inline (load_alias ()) code in
  let () =
    TypecheckerLog.preprocess (fun _ ->
        Pp.printf "@{<bold>result:@}\n%s\n" (layout_structure code))
  in
  (* let () = *)
  (*   Pp.printf "@{<bold>alias:@}\n%s\n" (Type_alias.layout_alias (load_alias ())) *)
  (* in *)
  (* let () = _die [%here] in *)
  normalize_structure code
