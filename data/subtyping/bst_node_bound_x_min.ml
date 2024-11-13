let[@assert] rty1 =
  let d = (0 <= v : [%v: int]) [@over] in
  let lo = (true : [%v: int]) [@over] in
  let hi = (lo < v : [%v: int]) [@over] in
  (fun ((lt [@exists]) : int tree) ((rt [@exists]) : int tree)
       ((x [@exists]) : int) ->
     d > 0
     && lo + 1 < hi
     && lo < x && x < hi
     && ((not (leaf lt)) #==> (lower_bound lt lo))
     && ((not (leaf lt)) #==> (upper_bound lt x))
     && bst lt && x < hi && bst rt
     && ((not (leaf rt)) #==> (lower_bound rt x))
     && ((not (leaf rt)) #==> (upper_bound rt hi))
     && root v x && lch v lt && rch v rt
    : [%v: int tree])
    [@under]

let[@assert] rty2 =
  let d = (0 <= v : [%v: int]) [@over] in
  let lo = (true : [%v: int]) [@over] in
  let hi = (lo < v : [%v: int]) [@over] in
  (d > 0
   && ((not (leaf v)) #==> (lower_bound v lo))
   && ((not (leaf v)) #==> (upper_bound v hi))
   && bst v
   && not (leaf v)
   && fun ((n [@exists]) : int) -> depth v n && n <= d
    : [%v: int tree])
    [@under]
