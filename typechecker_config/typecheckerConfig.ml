(* The "typechecker" meta-config section: which files to load for type checking.
   Set/get is the shared ConfigSection protocol. [data_type_decls] carries the datatype
   [type] decl (and, for benchmarks with a functional encoding, the [let rec] measures
   inline). *)
type prim_path = {
  data_type_decls : string;
  normal_typing : string;
  coverage_typing : string;
  axioms : string;
}
[@@deriving of_yojson { strict = true }]

(* [lean_preamble]/[coq_preamble] each name a header file (imports / [set_option]s
   for Lean, [Require Import] / [Open Scope] for Coq) prepended to the generated
   preamble for that backend. *)
type t = {
  prim_path : prim_path;
  lean_preamble : string option; [@default None]
  coq_preamble : string option; [@default None]
  emit_backend : string option; [@default None]
}
[@@deriving of_yojson { strict = true }]

include ConfigSection.Make (struct
  type nonrec t = t

  let name = "typechecker"
  let of_yojson = of_yojson
end)

(* Sets zutils too: typechecking always needs both sections, and the .mli hides
   [set]/[of_meta_config] so this is the only way in — a caller can't set one and
   forget the other. *)
let bootstrap root =
  ZUtilsConfig.set (ZUtilsConfig.of_meta_config root);
  set (of_meta_config root)

let get_lean_preamble_path () = (get ()).lean_preamble
let get_coq_preamble_path () = (get ()).coq_preamble

(* Which backend the on-failure subtyping query emitter targets. Absent field → Lean;
   an unrecognized value fails loudly rather than silently picking a default. *)
let get_emit_backend () =
  match (get ()).emit_backend with
  | None | Some "lean" -> `Lean
  | Some "coq" -> `Coq
  | Some other ->
      failwith
        (Printf.sprintf "unknown emit_backend %S (expected \"lean\" or \"coq\")"
           other)
