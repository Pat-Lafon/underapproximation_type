external method_predicates : t = "rng" "mem" "sorted" "<="

let[@assert] set_gen =
  let d = (0 <= v : [%v: int]) [@over] in
  let lo = (true : [%v: int]) [@over] in
  let hi = (v == lo + d : [%v: int]) [@over] in
  (fun (u : int) -> implies (mem v u) (lo < u && u < hi) && sorted v && rng v d
    : [%v: int set])
    [@under]
