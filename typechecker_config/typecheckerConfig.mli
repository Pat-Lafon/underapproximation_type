(* The "typechecker" meta-config section. [set]/[of_meta_config] are deliberately
   not exposed: the section is never populated without zutils, so [bootstrap] is
   the only entry point — it sets both. See typecheckerConfig.ml. *)
type prim_path = {
  data_type_decls : string;
  normal_typing : string;
  coverage_typing : string;
  axioms : string;
}

type t = {
  prim_path : prim_path;
  lean_preamble : string option;
  coq_preamble : string option;
  emit_backend : string option;
}

(* Populate the zutils + typechecker sections together from a parsed meta-config
   root. *)
val bootstrap : Yojson.Safe.t -> unit
val get : unit -> t
val get_lean_preamble_path : unit -> string option
val get_coq_preamble_path : unit -> string option
val get_emit_backend : unit -> [ `Lean | `Coq ]
