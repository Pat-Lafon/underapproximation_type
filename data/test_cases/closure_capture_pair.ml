let f (g : unit -> int) : int = g ()

let[@assert] f
    ?r:(_ = fun ?r:(_ = ((true : [%v: unit]) [@over])) -> (true : [%v: int])) =
  (true : [%v: int])

let diagonal_via_closure (u : unit) : int * int =
  let (x : int) = int_gen () in
  let g : unit -> int = fun (_ : unit) -> x in
  let (y : int) = f g in
  (x, y)

let[@assert] diagonal_via_closure ?l:(u = ((true : [%v: unit]) [@over])) =
  (true : [%v: int * int]) [@under]
