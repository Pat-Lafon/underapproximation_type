let abs (x : int) =
  let (b : bool) = x == 0 in
  if b then 0
  else
    let (y : int) = x + 1 in
    let (z : int) = y - 1 in
    z
