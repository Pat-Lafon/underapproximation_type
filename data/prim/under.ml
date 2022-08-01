let inteq =
  let a = (v : int) false in
  let b = (v : int) false in
  (v : bool) (iff v (a == b))

let intlt =
  let a = (v : int) false in
  let b = (v : int) false in
  (v : bool) (iff v (a < b))

let intgt =
  let a = (v : int) false in
  let b = (v : int) false in
  (v : bool) (iff v (a > b))

let intle =
  let a = (v : int) false in
  let b = (v : int) false in
  (v : bool) (iff v (a <= b))

let intge =
  let a = (v : int) false in
  let b = (v : int) false in
  (v : bool) (iff v (a => b))

let intadd =
  let a = (v : int) false in
  let b = (v : int) false in
  (v : int) (v == a + b)

let intsub =
  let a = (v : int) false in
  let b = (v : int) false in
  (v : int) (v == a - b)

let intlistnil = (v : int list) (fun (u : 'fa) -> not (mem v u))
let rev_intlistnil = (v : int list) (fun (u : 'fa) -> not (mem v u))

let intlistcons =
  let h = (v : int) false in
  let t = (v : int list) (fun (u : 'fa) -> implies (mem v u) (u == h)) in
  (v : int list)
    ((fun (u : 'ex) -> mem v u) && fun (u : 'fa) -> implies (mem v u) (u == h))

let rev_intlistcons =
  let l =
    (v : int list) (fun (u : 'ex) ->
        mem v u && fun (w : 'fa) -> implies (mem v w) (w == u))
  in
  ( (h : int) (mem l h),
    (t : int list) (fun (u : 'fa) -> implies (mem t u) (mem l u)) )

let _ret_two_value =
  let x = (v : int) (v > 0) in
  (v : int) (v == 1 || v == x)
