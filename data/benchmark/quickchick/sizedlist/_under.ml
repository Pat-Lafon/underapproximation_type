external method_predicates : t = "len" "<="

(* See https://v2.ocaml.org/manual/attributes.html for [@x : y] *)
(* and https://ocaml.org/docs/metaprogramming#preprocessors for [%x : y] *)
let sized_list_gen =
  let s = (0 <= v : [%v: int]) [@over] in
  (fun (u : [%forall: int]) -> implies (len v u) (0 <= u && u <= s)
    : [%v: int list])
    [@under]
