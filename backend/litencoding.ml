open Z3
open Z3aux
open Language
open Sugar

type z3_rec_func = { func : Z3.FuncDecl.func_decl }

(* TODO: Will we want both rec and non-rec here? *)
let rec_func_map : (string, z3_rec_func) Hashtbl.t = Hashtbl.create 5

let constant_to_z3 ctx c =
  let open Constant in
  match c with
  | U | Tu _ | Dt _ ->
      _failatwith __FILE__ __LINE__ "unimp complex constant encoding"
  | B b -> bool_to_z3 ctx b
  | I i -> int_to_z3 ctx i

let rec typed_lit_to_z3 ctx lit =
  Printf.printf "typed_lit_to_z3: %s\n"
    (lit.x |> Lit.sexp_of_lit Nt.sexp_of_t |> Sexplib.Sexp.to_string);

  match lit.x with
  | ATu _ | AProj _ -> _failatwith __FILE__ __LINE__ "die"
  | AC c -> constant_to_z3 ctx c
  | AVar x -> tpedvar_to_z3 ctx (x.ty, x.x)
  | AAppOp (op, args) -> (
      let args = List.map (typed_lit_to_z3 ctx) args in
      match (op.x, args) with
      | "==", [ a; b ] -> Boolean.mk_eq ctx a b
      | "!=", [ a; b ] -> Boolean.mk_not ctx @@ Boolean.mk_eq ctx a b
      | "<=", [ a; b ] -> Arithmetic.mk_le ctx a b
      | ">=", [ a; b ] -> Arithmetic.mk_ge ctx a b
      | "<", [ a; b ] -> Arithmetic.mk_lt ctx a b
      | ">", [ a; b ] -> Arithmetic.mk_gt ctx a b
      | "+", [ a; b ] -> Arithmetic.mk_add ctx [ a; b ]
      | "-", [ a; b ] -> Arithmetic.mk_sub ctx [ a; b ]
      | "mod", [ a; b ] -> Arithmetic.Integer.mk_mod ctx a b
      | "*", [ a; b ] -> Arithmetic.mk_mul ctx [ a; b ]
      | "/", [ a; b ] -> Arithmetic.mk_div ctx a b
      | "ite", [ a; b; c ] -> Boolean.mk_ite ctx a b c
      | opname, args ->
          let func =
            match
              (* Assume op.ty is an arrow type*)
              let fst_arg = op.ty |> Nt.get_argty |> Nt.layout in
              Option.bind (Dtencoding.z3_data_type_get fst_arg) (fun x ->
                  Dtencoding.z3_data_type_func_get x opname)
            with
            | Some f -> f
            | None -> (
                match Hashtbl.find_opt rec_func_map opname with
                | Some f -> f.func
                | None ->
                    let argsty, retty = Nt.destruct_arr_tp op.ty in
                    z3func ctx opname argsty retty)
          in

          Printf.printf "%s: %s\n" op.x (op.ty |> Nt.layout);
          Printf.printf "%s\n" (lit.ty |> Nt.layout);
          print_endline "================";
          List.iter
            (fun arg -> Printf.printf "%s\n" (arg |> Expr.to_string))
            args;
          print_endline "================";

          Z3.FuncDecl.apply func args)
