let[@assert] rty1 =
  let d = ((0 <= v : [%v: int]) [@over]) in
  let lo = ((true : [%v: int]) [@over]) in
  let hi = ((lo < v : [%v: int]) [@over]) in
  ((fun ((lt [@exists]) : int tree)
      ((rt [@exists]) : int tree)
      ((d_1 [@exists]) : int)
      ((d_2 [@exists]) : int)
      ((x [@exists]) : int)
    ->
      d > 0
      && lo + 1 < hi
      && lo < x && x < hi
      && 0 <= d - 1
      && d - 1 >= 0
      && bst lt
      && (fun ((n [@exists]) : int) -> depth lt n && n <= d - 1)
      && 0 <= d_2 && d_2 >= 0 && d_2 < d
      && d_2 == d - 1
      && x < hi && bst rt
      && (fun ((n [@exists]) : int) -> depth rt n && n <= d_2)
      && root v x && lch v lt && rch v rt
    : [%v: int tree])
    [@under])

let[@assert] rty2 =
  let d = ((0 <= v : [%v: int]) [@over]) in
  let lo = ((true : [%v: int]) [@over]) in
  let hi = ((lo < v : [%v: int]) [@over]) in
  ((d > 0
    && ((not (leaf v))#==>(lower_bound v lo))
    && ((not (leaf v))#==>(upper_bound v hi))
    && bst v
    && (not (leaf v))
    && fun ((n [@exists]) : int) -> depth v n && n <= d
    : [%v: int tree])
    [@under])
