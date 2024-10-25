let[@assert] rty1 =
  let d = (0 <= v : [%v: int]) [@over] in
  let lo = (true : [%v: int]) [@over] in
  let hi = (lo < v : [%v: int]) [@over] in
  (leaf v && d == 0
   && (fun (u : int) -> (tree_mem v u) #==> (lo < u && u < hi))
   && bst v
   && fun ((n [@exists]) : int) -> depth v n && n <= d
    : [%v: int tree])
    [@under]

let[@assert] rty2 =
  let d = (0 <= v : [%v: int]) [@over] in
  let lo = (true : [%v: int]) [@over] in
  let hi = (lo < v : [%v: int]) [@over] in
  (leaf v && d == 0 : [%v: int tree]) [@under]
