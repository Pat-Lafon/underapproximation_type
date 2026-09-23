let tree_root_or_zero (t : int tree) : int =
  match t with Leaf -> 0 | Node (x, _, _) -> x

(* This could add multiple [_] to the typing context which would be a bug if so *)
let wildcard_match_gen (t : int tree) : int =
  let (x : int) = int_gen () in
  match t with
  | Leaf -> if x > 0 then x else Err
  | Node (_, _, _) -> if x > 0 then x else Err

let[@assert] wildcard_match_gen ?l:(t = ((true : [%v: int tree]) [@over])) =
  (0 < v : [%v: int]) [@under]
