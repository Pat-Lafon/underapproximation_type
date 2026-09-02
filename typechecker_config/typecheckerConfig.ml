type prim_path = {
  data_type_decls : string;
  normal_typing : string;
  coverage_typing : string;
  axioms : string;
}
[@@deriving of_yojson { strict = true }]

type t = {
  prim_path : prim_path;
  log_tags : string list; [@default []]
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

(* Typechecking reads the zutils section too, so the pair is set together. *)
let bootstrap root =
  ZUtilsConfig.set (ZUtilsConfig.of_meta_config root);
  set (of_meta_config root)

let get_log_tags () = (get ()).log_tags
let get_lean_preamble_path () = (get ()).lean_preamble
let get_coq_preamble_path () = (get ()).coq_preamble

let get_emit_backend () =
  match (get ()).emit_backend with
  | None | Some "lean" -> `Lean
  | Some "coq" -> `Coq
  | Some other ->
      failwith
        (Printf.sprintf "unknown emit_backend %S (expected \"lean\" or \"coq\")"
           other)
