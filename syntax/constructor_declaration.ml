module NT = Normalty.Ntyped
open Sexplib.Std
open Mtyped

type arg_spec =
  | Tuple of (NT.t, string) typed list  (* Positional: field_0, field_1, ... *)
  | Record of (NT.t, string) typed list (* Named: actual field names *)
[@@deriving sexp]

type constructor_declaration = {
  constr_name : string;
  args : arg_spec;
}
[@@deriving sexp]

(* Extract argument types from an arg_spec *)
let get_arg_types (spec : arg_spec) : NT.t list =
  match spec with
  | Tuple args | Record args -> List.map (fun { ty; _ } -> ty) args

(* Extract argument list (names and types) from an arg_spec *)
let get_args (spec : arg_spec) : (NT.t, string) typed list =
  match spec with
  | Tuple args | Record args -> args
