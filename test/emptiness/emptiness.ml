open Auxtest

let%expect_test "nonempty_int" =
  run_emptiness_test "test/data/emptiness/nonempty_int.ml";
  [%expect {| nonempty: true |}]

let%expect_test "empty_int" =
  run_emptiness_test "test/data/emptiness/empty_int.ml";
  [%expect {| nonempty: false |}]
