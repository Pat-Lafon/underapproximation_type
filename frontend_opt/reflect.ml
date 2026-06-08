type reflected_type = {
  type_name : string;
  type_params : string list;
  type_decls : Ast.constructor_declaration list;
}

let reflect_func_set : (string, unit) Hashtbl.t = Hashtbl.create 10
let reflect_func_mem s = Hashtbl.mem reflect_func_set s

let reflect_type_set : (string, reflected_type) Hashtbl.t = Hashtbl.create 10
let reflect_type_mem s = Hashtbl.mem reflect_type_set s
let get_reflect_type s = Hashtbl.find_opt reflect_type_set s

let get_all_reflected_types () =
  Hashtbl.fold (fun _ v acc -> v :: acc) reflect_type_set []

let add_reflect_func name = Hashtbl.add reflect_func_set name ()

let add_reflect_type name type_params type_decls =
  Hashtbl.add reflect_type_set name { type_name = name; type_params; type_decls }
