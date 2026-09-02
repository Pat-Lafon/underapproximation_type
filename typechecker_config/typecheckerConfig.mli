type prim_path = {
  data_type_decls : string;
  normal_typing : string;
  coverage_typing : string;
  axioms : string;
}

type t = {
  prim_path : prim_path;
  log_tags : string list;
  lean_preamble : string option;
  coq_preamble : string option;
  emit_backend : string option;
}

(* Populates the zutils + typechecker sections. *)
val bootstrap : Yojson.Safe.t -> unit
val get : unit -> t
val get_log_tags : unit -> string list
val get_lean_preamble_path : unit -> string option
val get_coq_preamble_path : unit -> string option
val get_emit_backend : unit -> [ `Lean | `Coq ]
