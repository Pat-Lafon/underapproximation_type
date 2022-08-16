(* let concat =
  let s1 = (v : int list) true in
  let s2 = (v : int list) true in
  (v : int list) (fun (u : 'fa) ->
      iff (mem v u) (mem s1 u || mem s2 u)
      && implies (hd v u) (hd s1 u || hd s2 u))
 *)

let concat =
  let l1 = (v : int list) true in
  let l2 = (v : int list) true in
  (l3 : int list) (fun (u : 'fa) ->
    (implies (hd l1 u) (mem l3 u)))