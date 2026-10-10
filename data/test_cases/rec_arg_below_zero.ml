let rec below_zero_gen (x : int) : int =
  let (n : int) = int_gen () in
  if n < x then
    let (_ : int) = below_zero_gen n in
    0
  else Err

let[@assert] below_zero_gen ?r:(x = ((true : [%v: int]) [@over])) =
  (v == 0 : [%v: int])
