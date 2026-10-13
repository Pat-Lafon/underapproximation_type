open Zdatatype
open Auxtest

(* [run_test] reads [test/meta-config.json], and the loaded context is cached
   per process, so this suite bootstraps [data/adt]'s prim path itself. *)
let%expect_test "adt/sizedlist" =
  Sys.chdir project_root;
  TypecheckerConfig.bootstrap
    (Yojson.Safe.from_file "test/adt/meta-config.json");
  let code = Preprocess.preprocess [ "data/adt/sizedlist.ml" ] in
  let _, passed, failed = Typing.struc_check (Preprocess.load_bctx ()) code in
  Printf.printf "passing: %s\n" (List.split_by_comma Fun.id passed);
  Printf.printf "failing: %s\n" (List.split_by_comma Fun.id failed);
  [%expect
    {|
    passing: sizedlist_gen
    failing:
    |}]
