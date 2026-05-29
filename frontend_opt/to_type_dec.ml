open Ocaml5_parser
open Parsetree
open Item
open Constructor_declaration
open Mtyped
module Type = Normalty.Frontend
open Sugar

let constructor_declaration_of_ocaml { pcd_name; pcd_args; _ } =
  match pcd_args with
  | Pcstr_tuple cts ->
      let args =
        List.mapi (fun i ct ->
            let ty = Type.core_type_to_t ct in
            { x = Printf.sprintf "field_%d" i; ty })
          cts
      in
      { Constructor_declaration.constr_name = pcd_name.txt; args = Tuple args }
  | Pcstr_record fields ->
      let args =
        List.map (fun { pld_name; pld_type; _ } ->
            let ty = Type.core_type_to_t pld_type in
            { x = pld_name.txt; ty })
          fields
      in
      { Constructor_declaration.constr_name = pcd_name.txt; args = Record args }

let constructor_declaration_to_ocaml { constr_name; args } =
  let pcd_args =
    match args with
    | Record arg_list ->
        let pld_fields =
          List.map (fun { x = name; ty } ->
              {
                pld_name = Location.mknoloc name;
                pld_type = Type.t_to_core_type ty;
                pld_loc = Location.none;
                pld_mutable = Asttypes.Immutable;
                pld_attributes = [];
              })
            arg_list
        in
        Pcstr_record pld_fields
    | Tuple arg_list -> 
        Pcstr_tuple (List.map (fun { ty; _ } -> Type.t_to_core_type ty) arg_list)
  in
  {
    pcd_name = Location.mknoloc constr_name;
    pcd_vars = [];
    pcd_args;
    pcd_res = None;
    pcd_loc = Location.none;
    pcd_attributes = [];
  }

let label_declaration_of_ocaml ld =
  ld.pld_name.txt #: (Type.core_type_to_t ld.pld_type)

let label_declaration_to_ocaml x =
  {
    pld_name = Location.mknoloc x.x;
    pld_mutable = Asttypes.Immutable;
    pld_type = Type.t_to_core_type x.ty;
    pld_loc = Location.none;
    pld_attributes = [];
  }

let of_ocamltypedec { ptype_name; ptype_params; ptype_kind; ptype_manifest; _ }
    =
  let type_params =
    List.map
      (fun (ct, (_, _)) ->
        match Type.core_type_to_t ct with
        | Type.T.Ty_var name -> name
        | _ -> _die_with [%here] "die")
      ptype_params
  in
  let mk type_decl =
    MTyDecl { type_name = ptype_name.txt; type_params; type_decl }
  in
  match (ptype_kind, ptype_manifest) with
  | Ptype_variant cds, None ->
      mk (Decl_constructors (List.map constructor_declaration_of_ocaml cds))
  | Ptype_record lds, None ->
      mk (Decl_record (List.map label_declaration_of_ocaml lds))
  | _ -> failwith "unimp complex type decl"

let to_ocamltypedec = function
  | MTyDecl { type_name; type_params; type_decl } ->
      let ptype_kind =
        match type_decl with
        | Decl_constructors cds ->
            Ptype_variant (List.map constructor_declaration_to_ocaml cds)
        | Decl_record l ->
            Ptype_record (List.map label_declaration_to_ocaml l)
      in
      {
        ptype_name = Location.mknoloc type_name;
        ptype_params =
          List.map
            (fun t ->
              ( Type.t_to_core_type (Type.T.Ty_var t),
                (Asttypes.NoVariance, Asttypes.NoInjectivity) ))
            type_params;
        ptype_cstrs = [];
        ptype_kind;
        ptype_manifest = None;
        ptype_attributes = [];
        ptype_loc = Location.none;
        ptype_private = Asttypes.Public;
      }
  | _ -> _die_with [%here] "die"

let layout_ocaml es =
  let _ = Format.flush_str_formatter () in
  Pprintast.structure Format.str_formatter
  @@ List.map
       (fun e ->
         {
           pstr_desc = Pstr_type (Asttypes.Recursive, [ e ]);
           pstr_loc = Location.none;
         })
       es;
  Format.flush_str_formatter ()

let layout_type_dec e = layout_ocaml [ to_ocamltypedec e ]
