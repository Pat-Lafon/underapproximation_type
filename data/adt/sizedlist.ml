let rec sizedlist_gen (s : int) : ilist =
  if s <= 0 then Nil
  else if bool_gen () then Nil
  else Cons (int_gen (), sizedlist_gen (s - 1))

let[@assert] sizedlist_gen =
  let s = ((0 <= v : [%v: int]) [@over]) in
  ((fun ((n [@exists]) : int) -> len v n && n <= s : [%v: ilist]) [@under])
