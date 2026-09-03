include Basic_typing
include Normalization
open Language
open Zutils

let parse file =
  ocaml_structure_to_items
  @@ OcamlParser.Oparse.parse_imp_from_file ~sourcefile:file

let multi_parse files = List.concat_map parse files

let builtin_basic_ctx =
  let ctor dt name =
    constructor_declaration_mk_ (dt, { constr_name = name; args = CtorTuple [] })
  in
  Typectx.add_to_rights Typectx.emp
    [ ctor Nt.bool_ty "True"; ctor Nt.bool_ty "False"; ctor Nt.unit_ty "TT" ]

let builtin_rty_ctx =
  let under nty phi = RtyBase { ou = Under; cty = { nty; phi } } in
  let v_holds = Prop.lit_to_prop (Prop.AVar default_v#:Nt.bool_ty) in
  [
    "TT"#:(under Nt.unit_ty Prop.mk_true);
    "True"#:(under Nt.bool_ty v_holds);
    "False"#:(under Nt.bool_ty (Prop.Not v_holds));
  ]

let _ctxs = ref None

(* Registers eligible ADTs into [Z3decls.decl_registry] so they get a structured Z3 sort
   rather than an uninterpreted one. *)
let collect_dt_decls items =
  let module D = Prop.Z3decls in
  let ctor_of_decl { constr_name; args } =
    match args with
    | CtorTuple [] ->
        Some D.{ cname = String.lowercase_ascii constr_name; fields = [] }
    | CtorRecord xs ->
        Some
          D.
            {
              cname = String.lowercase_ascii constr_name;
              fields = List.map (fun x -> { fname = x.x; ftype = x.ty }) xs;
            }
    | CtorTuple (_ :: _) -> None (* positional ctor: type not encodable *)
  in
  let dt_decl_of_item = function
    | MTyDecl { type_name; type_decl = Decl_constructors decls; _ } ->
        if Nt.(is_uninterp (to_smtty (Ty_constructor (type_name, [])))) then
          let ctors = List.map ctor_of_decl decls in
          if List.exists Option.is_none ctors then (
            TypecheckerLog.preprocess (fun () ->
                Printf.printf
                  "collect_dt_decls: skipping `%s` from datatype encoding \
                   (positional constructor; falls back to uninterpreted sort)\n"
                  type_name);
            None)
          else
            Some D.{ dt_name = type_name; ctors = List.filter_map Fun.id ctors }
        else None
          (* builtin smtty name like [unit]/[bool] — handled by [smt_tp_to_sort] *)
    | MTyDecl { type_decl = Decl_record _; _ } -> None
    | MValDecl _ | MMethodPred _ | MAxiom _ | MFuncImpRaw _ | MFuncImp _
    | MRty _ | MLocalRty _ ->
        None
  in
  let decls = List.filter_map dt_decl_of_item items in
  List.iter D.register_decl decls;
  decls

let assert_monomorphic loc kind name = function
  | [] -> ()
  | tvars ->
      _failatwith loc
        (Printf.sprintf "polymorphic %s `%s` not supported (type variables: %s)"
           kind name (String.concat ", " tvars))

(* An encodable datatype's constructor/recognizer/accessor predicate names are fixed by
   [Z3decls], so their normal-type signatures are derived here rather than restated in each
   benchmark's [normal_typing.ml]. *)
let derive_dt_method_preds (decls : Prop.Z3decls.datatype_decl list) :
    Nt.t item list =
  let module D = Prop.Z3decls in
  let val_decl name args ret =
    let ty = Nt.construct_arr_tp (args, ret) in
    assert_monomorphic [%here] "datatype predicate" name
      (Nt.gather_type_vars ty);
    MValDecl name#:ty
  in
  List.concat_map
    (fun (d : D.datatype_decl) ->
      let dt_ty = Nt.Ty_constructor (d.dt_name, []) in
      List.concat_map
        (fun (c : D.ctor_spec) ->
          let field_tys =
            List.map (fun (f : D.field_spec) -> f.ftype) c.fields
          in
          let ctor = val_decl c.cname field_tys dt_ty in
          let recognizer = val_decl ("is_" ^ c.cname) [ dt_ty ] Nt.bool_ty in
          let accessors =
            List.map
              (fun (f : D.field_spec) -> val_decl f.fname [ dt_ty ] f.ftype)
              c.fields
          in
          ctor :: recognizer :: accessors)
        d.ctors)
    decls

let resolve_files (prim_path : TypecheckerConfig.prim_path) : string list =
  [
    prim_path.data_type_decls;
    prim_path.normal_typing;
    prim_path.coverage_typing;
    prim_path.axioms;
  ]

let relational_of_functional (ty : Nt.t) : Nt.t =
  let args, ret = Nt.destruct_arr_tp ty in
  Nt.construct_arr_tp (args @ [ ret ], Nt.bool_ty)

let check_measure_body ctx (name, if_rec, body) =
  let tvars, t = Nt.lift_poly_tp body.ty in
  assert_monomorphic [%here] "measure" name.x tvars;
  let body = raw_term_type_check ctx [] body.x#:t in
  MFuncImpRaw { name; if_rec; body = body.x#:t }

(* Each measure takes two signatures off [base_ctx], in two contexts: a *functional* sig to check
   its own body (a recursive [depth l] then types as its result, not a partial app), and a
   *relational* sig for the specs — the predicate form they reference, replacing the relational
   [val]s a [program] benchmark omits. *)
let struct_check_program items =
  let defs, measures, specs =
    List.fold_right
      (fun item (defs, measures, specs) ->
        match item with
        | MTyDecl _ | MValDecl _ | MMethodPred _ ->
            (item :: defs, measures, specs)
        | MFuncImpRaw { name; if_rec; body } ->
            (defs, (name, if_rec, body) :: measures, specs)
        | MFuncImp _ ->
            _failatwith [%here]
              "struct_check_program: normalized measure (MFuncImp) in typing \
               context"
        | MAxiom _ | MRty _ | MLocalRty _ -> (defs, measures, item :: specs))
      items ([], [], [])
  in
  let base_ctx, typed_defs = struct_check builtin_basic_ctx defs in
  let measure_names = List.map (fun (name, _, _) -> name) measures in
  let functional_ctx = Typectx.add_to_rights base_ctx measure_names in
  let typed_measures = List.map (check_measure_body functional_ctx) measures in
  let relational_sigs =
    List.map
      (fun name -> name.x#:(relational_of_functional name.ty))
      measure_names
  in
  let global_pre = Typectx.add_to_rights base_ctx relational_sigs in
  let global_ctx, typed_specs = struct_check global_pre specs in
  (global_ctx, typed_defs @ typed_measures @ typed_specs)

let load_ctxs () =
  match !_ctxs with
  | Some ctxs -> ctxs
  | None ->
      let prim_path = (TypecheckerConfig.get ()).prim_path in
      let files = resolve_files prim_path in
      let items = multi_parse files in
      let dt_decls = collect_dt_decls items in
      let items = derive_dt_method_preds dt_decls @ items in
      let alias = Type_alias.item_mk_type_alias_ctx items in
      let items = Type_alias.item_inline alias items in
      let basic_ctx, items = struct_check_program items in
      (* After [struct_check_program] so the measure bodies carry types. *)
      let () = Measure.register_items items in
      let () =
        match ZUtilsConfig.get_smt_encoding () with
        | ZUtilsConfig.Both
          when not
                 (List.exists
                    (function
                      | MFuncImpRaw { if_rec = true; _ } -> true | _ -> false)
                    items) ->
            _failatwith [%here]
              "zutils.smt_encoding [\"Both\"] requires at least one recursive \
               measure in the typing context"
        | ZUtilsConfig.Axiom | ZUtilsConfig.Both -> ()
      in
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
  let _, code = struct_check (load_basic_ctx ()) items' in
  let code = Type_alias.item_inline (load_alias () @ alias) code in
  let () =
    TypecheckerLog.preprocess (fun _ ->
        Pp.printf "@{<bold>result:@}\n%s\n" (layout_structure code))
  in
  normalize_structure code
