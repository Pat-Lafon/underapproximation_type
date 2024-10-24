let rec size_bst_gen (d : int) (lo : int) (hi : int) : int tree =
  if sizecheck d then Leaf
  else if bool_gen () then Err
  else if (incr lo) < hi then
    let (x : int) = int_range lo hi in
    let (lt : int tree) = size_bst_gen (subs d) lo x in
    let (rt : int tree) = size_bst_gen (subs d) x hi in
    Node (x, lt, rt)
  else Exn

let[@assert] size_bst_gen =
  let d = (0 <= v : [%v: int]) [@over] in
  let lo = (true : [%v: int]) [@over] in
  let hi = (lo < v : [%v: int]) [@over] in
  ((fun (u : int) -> (tree_mem v u) #==> (lo < u && u < hi))
   && bst v
   && fun ((n [@exists]) : int) -> depth v n && n <= d
    : [%v: int tree])
    [@under]
