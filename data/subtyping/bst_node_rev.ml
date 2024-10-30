let[@assert] rty1 =
  let d = (0 <= v : [%v: int]) [@over] in
  let lo = (true : [%v: int]) [@over] in
  let hi = (lo < v : [%v: int]) [@over] in
  (fun ((lt [@exists]) : int tree) ((rt [@exists]) : int tree)
       ((d_2 [@exists]) : int) ((x [@exists]) : int) ->
     d > 0
     && lo + 1 < hi
     && lo < x && x < hi
     && 0 <= d - 1
     && (fun (u : int) -> (tree_mem lt u) #==> (lo < u && u < x))
     && bst lt (* && not (leaf lt) *)
     && (fun ((n [@exists]) : int) -> depth lt n && n <= d - 1 (* && n > 0 *))
     && (fun (u : int) -> (tree_mem rt u) #==> (x < u && u < hi))
     && bst rt
     (* && (not (leaf rt)) *)
     && (fun ((n [@exists]) : int) -> depth rt n && n <= d - 1)
     (* && n > 0 *)
     && root v x
     && lch v lt && rch v rt
    : [%v: int tree])
    [@under]

let[@assert] rty2 =
  let d = (0 <= v : [%v: int]) [@over] in
  let lo = (true : [%v: int]) [@over] in
  let hi = (lo < v : [%v: int]) [@over] in
  (d > 0
   && (fun (u : int) -> (tree_mem v u) #==> (lo < u && u < hi))
   && bst v
   && (not (leaf v))
   && fun ((n [@exists]) : int) -> depth v n && n <= d
    : [%v: int tree])
    [@under]
