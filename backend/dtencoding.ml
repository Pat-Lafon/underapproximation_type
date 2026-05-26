type z3_data_type = {
  sort : Z3.Sort.sort;
  constructors : (string * Z3.FuncDecl.func_decl) list;
  recognizers : (string * Z3.FuncDecl.func_decl) list;
  accessors : (string * Z3.FuncDecl.func_decl) list;
}

(* TODO: index NT.t instead of string? *)
let datatype_map : (string, z3_data_type) Hashtbl.t = Hashtbl.create 5

let z3_data_type_get (s : string) : z3_data_type option =
  Hashtbl.find_opt datatype_map s

let register_data_type (name : string) (dt : z3_data_type) : unit =
  Hashtbl.add datatype_map name dt

let z3_data_type_func_get (dt : z3_data_type) (f : string) :
    Z3.FuncDecl.func_decl option =
  List.find_opt (fun (name, _) -> name = f) dt.constructors
  |> Core.Option.first_some
       (List.find_opt (fun (name, _) -> name = f) dt.recognizers)
  |> Core.Option.first_some
       (List.find_opt (fun (name, _) -> name = f) dt.accessors)
  |> Option.map snd

let z3_data_type_check (s : string) : bool = z3_data_type_get s <> None

let z3_data_type_func_check (s : string) (f : string) : bool =
  z3_data_type_get s
  |> Option.map (fun dt -> z3_data_type_func_get dt f) <> None

let z3_data_type_layout { sort; constructors; recognizers; accessors } =
  List.fold_left
    (fun acc (name_str, decl) ->
      let decl_str = Z3.FuncDecl.to_string decl in
      Printf.sprintf "%s\n%s: %s" acc name_str decl_str)
    (Printf.sprintf "datatype %s" (Z3.Sort.to_string sort))
    (constructors @ recognizers @ accessors)

type case = string * (string * Z3.Sort.sort option) list

let create_constructor ctx case =
  let name, args = case in
  let symbols, types =
    List.map (fun (s, t) -> (Z3.Symbol.mk_string ctx s, t)) args |> List.split
  in
  let zeros = List.map (fun _ -> 0) types in
  let recognizer =
    Z3.Symbol.mk_string ctx ("is_" ^ String.uncapitalize_ascii name)
  in
  Z3.Datatype.mk_constructor_s ctx name recognizer symbols types zeros

let create_data_type ctx name cases =
  let init_constructors = List.map (create_constructor ctx) cases in
  let sort = Z3.Datatype.mk_sort_s ctx name init_constructors in
  let dt_constructors = Z3.Datatype.get_constructors sort in
  let constructor_names = List.map fst cases in
  let constructors = List.combine constructor_names dt_constructors in
  let recognizers =
    List.combine
      (List.map (fun c -> "is_" ^ String.uncapitalize_ascii c) constructor_names)
      (Z3.Datatype.get_recognizers sort)
  in
  let accessors =
    List.combine cases (Z3.Datatype.get_accessors sort)
    |> List.map (fun (a, b) -> List.combine (snd a |> List.map fst) b)
    |> List.flatten
  in
  { sort; constructors; recognizers; accessors }

