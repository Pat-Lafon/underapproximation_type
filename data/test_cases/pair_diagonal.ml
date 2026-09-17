let diagonal (u : unit) : int * int =
  let (x : int) = int_gen () in
  (x, x)

let[@assert] diagonal ?l:(u = ((true : [%v: unit]) [@over])) =
  (true : [%v: int * int]) [@under]
