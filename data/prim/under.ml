let[@notation] eq =
  let a = [%poly: int] in
  let b = [%poly: int] in
  (v : bool) (iff v (a == b))

let[@notation] neq =
  let a = [%poly: int] in
  let b = [%poly: int] in
  (v : bool) (iff v (a != b))

let[@notation] lt =
  let a = [%poly: int] in
  let b = [%poly: int] in
  (v : bool) (iff v (a < b))

let[@notation] gt =
  let a = [%poly: int] in
  let b = [%poly: int] in
  (v : bool) (iff v (a > b))

let[@notation] le =
  let a = [%poly: int] in
  let b = [%poly: int] in
  (v : bool) (iff v (a <= b))

let[@notation] ge =
  let a = [%poly: int] in
  let b = [%poly: int] in
  (v : bool) (iff v (a => b))

let[@notation] plus =
  let a = [%poly: int] in
  let b = [%poly: int] in
  (v : int) (v == a + b)

let[@notation] minus =
  let a = [%poly: int] in
  let b = [%poly: int] in
  (v : int) (v == a - b)

let[@notation] nil = (v : int list) (fun (u : [%forall: int]) -> not (mem v u))

let[@notation] cons =
  let h = [%poly: int] in
  let t =
    (v : int list) (fun (u : [%forall: int]) ->
        iff (hd v u) (u == h) && implies (mem v u) (u == h))
  in
  (v : int list) (fun (u : [%forall: int]) ->
      implies (mem v u) (u == h) && iff (hd v u) (u == h))

let[@notation] ileaf =
  (v : int_tree) (fun (u : [%forall: int]) -> not (mem v u))

let[@notation] _ret_two_value =
  let x = (v : int) (v > 0) in
  (v : int) (v == 1 || v == x)
