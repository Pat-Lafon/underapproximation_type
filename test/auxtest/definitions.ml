open Zdatatype

(* When inline tests run, cwd is the test stanza's build dir (e.g.
   [.../underapproximation_type/test/fast]). The two [dirname]s strip [test/fast]
   to land on the project root, which [run_test] chdir's to. *)
let project_root = Filename.dirname (Filename.dirname (Sys.getcwd ()))

let run_test source_file =
  Statistic.clear ();
  Sys.chdir project_root;
  let cfg_root = Yojson.Safe.from_file "test/meta-config.json" in
  TypecheckerConfig.bootstrap cfg_root;
  let code = Preprocess.preprocess [ source_file ] in
  let results = Typing.struc_check (Preprocess.load_bctx ()) code in
  let passed =
    List.filter_map (fun (n, ok) -> if ok then Some n else None) results
  in
  let failed =
    List.filter_map (fun (n, ok) -> if ok then None else Some n) results
  in
  Printf.printf "passing: %s\n" (List.split_by_comma Fun.id passed);
  Printf.printf "failing: %s\n" (List.split_by_comma Fun.id failed)
