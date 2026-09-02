open Zdatatype
open Language

(* When inline tests run, cwd is the test stanza's build dir (e.g.
   [.../underapproximation_type/test/fast]). The two [dirname]s strip [test/fast]
   to land on the project root, which [run_test] chdir's to. *)
let project_root = Filename.dirname (Filename.dirname (Sys.getcwd ()))

let load source_file =
  Statistic.clear ();
  Sys.chdir project_root;
  let cfg_root = Yojson.Safe.from_file "test/meta-config.json" in
  TypecheckerConfig.bootstrap cfg_root;
  Preprocess.preprocess [ source_file ]

let run_test source_file =
  let code = load source_file in
  let results = Typing.struc_check (Preprocess.load_bctx ()) code in
  let passed =
    List.filter_map (fun (n, ok) -> if ok then Some n else None) results
  in
  let failed =
    List.filter_map (fun (n, ok) -> if ok then None else Some n) results
  in
  Printf.printf "passing: %s\n" (List.split_by_comma Fun.id passed);
  Printf.printf "failing: %s\n" (List.split_by_comma Fun.id failed)

let run_emptiness_test source_file =
  let code = load source_file in
  let _, rty = get_rty_by_name code "rty" in
  let _ = Preprocess.load_bctx () in
  Statistic.create_query_stat "nonempty";
  let rctx = Typing.Rctx.emp "nonempty" [] [] in
  Printf.printf "nonempty: %b\n" (Auxtyping.non_emptiness_spec rctx rty)
