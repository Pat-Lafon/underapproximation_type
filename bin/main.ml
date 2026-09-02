open Core
open Language
open Zutils

let regular_file =
  Command.Arg_type.create (fun filename ->
      match Sys_unix.is_file filename with
      | `Yes -> filename
      | `No -> failwith "Not a regular file"
      | `Unknown -> failwith "Could not determine if this was a regular file")

let print_source_code source_file () =
  let code = Preprocess.preprocess [ source_file ] in
  let _ = Pp.printf "%s\n" (layout_structure code) in
  ()

let subtype_check source_file () =
  let code = Preprocess.preprocess [ source_file ] in
  let _, rty1 = get_rty_by_name code "rty1" in
  let _, rty2 = get_rty_by_name code "rty2" in
  let _ =
    pprint_subtyping
      (fun () -> Typectx.pprint_ctx layout_rty Typectx.emp)
      (rty1, rty2) ()
  in
  let _ = Preprocess.load_bctx () in
  let () = Statistic.create_query_stat "subtyping" in
  let res =
    Auxtyping.sub_rty (Typing.Rctx.emp "subtyping" [] []) (rty1, rty2)
  in
  Pp.printf "@{<bold>Result: %b@}\n" res;
  Stdlib.exit (if res then 0 else 1)

let nonempty_check source_file () =
  let code = Preprocess.preprocess [ source_file ] in
  let _, rty = get_rty_by_name code "rty" in
  let _ = Preprocess.load_bctx () in
  let () = Statistic.create_query_stat "nonempty" in
  let rctx = Typing.Rctx.emp "nonempty" [] [] in
  let res = Auxtyping.non_emptiness_spec rctx rty in
  Pp.printf "@{<bold>Result: %b@}\n" res;
  Stdlib.exit (if res then 0 else 1)

let type_check source_file () =
  let code = Preprocess.preprocess [ source_file ] in
  let () = Pp.printf "@{<bold>result:@} %s\n" (layout_structure code) in
  let bctx = Preprocess.load_bctx () in
  let results = Typing.struc_check bctx code in
  let failed = List.filter results ~f:(fun (_, ok) -> not ok) in
  let () =
    List.iter failed ~f:(fun (name, _) ->
        Pp.printf "@{<bold>FAILED:@} %s\n" name)
  in
  let ok = List.is_empty failed in
  Pp.printf "@{<bold>Result: %b@}\n" ok;
  Stdlib.exit (if ok then 0 else 1)

(* [load_bctx] is called for its side effect: it registers every axiom into the prover. *)
let loaded_axioms () =
  let _ = Preprocess.load_bctx () in
  Prop.Prover.all_axioms ()

let export_axioms_lean oc =
  Auxtyping.Emit.emit_axiom_preamble
    (Auxtyping.Emit.pieces `Lean)
    oc (loaded_axioms ())

let export_axioms_coq oc =
  Auxtyping.Emit.emit_axiom_preamble
    (Auxtyping.Emit.pieces `Coq)
    oc (loaded_axioms ())

let one_param_file message f =
  let cmd =
    Command.basic ~summary:message
      Command.Let_syntax.(
        let%map_open config_file =
          flag "config"
            (optional_with_default "meta-config.json" regular_file)
            ~doc:"config file path"
        and source_file = anon ("source_code_file" %: regular_file) in
        let root = Yojson.Safe.from_file config_file in
        TypecheckerConfig.bootstrap root;
        f source_file)
  in
  (message, cmd)

let config_only message f =
  let cmd =
    Command.basic ~summary:message
      Command.Let_syntax.(
        let%map_open config_file =
          flag "config"
            (optional_with_default "meta-config.json" regular_file)
            ~doc:"config file path"
        and output_file =
          flag "output" (required string)
            ~doc:"file path for the rendered axioms"
        in
        fun () ->
          let root = Yojson.Safe.from_file config_file in
          TypecheckerConfig.bootstrap root;
          Out_channel.with_file output_file ~f)
  in
  (message, cmd)

let commands =
  Command.group ~summary:"Poirot"
    [
      one_param_file "print-source-code" print_source_code;
      one_param_file "subtype-check" subtype_check;
      one_param_file "nonempty-check" nonempty_check;
      one_param_file "type-check" type_check;
      config_only "export-axioms-lean" export_axioms_lean;
      config_only "export-axioms-coq" export_axioms_coq;
    ]

let () = Command_unix.run commands
