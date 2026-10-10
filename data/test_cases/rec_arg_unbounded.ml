let rec unbounded_gen (x : int) : int =
  let (n : int) = int_gen () in
  let (_ : int) = unbounded_gen n in
  0

let[@assert] unbounded_gen ?r:(x = ((true : [%v: int]) [@over])) =
  (v == 0 : [%v: int])
