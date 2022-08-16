let eq =
  let a = (v : int) true in
  let b = (v : int) true in
  (v : bool) (iff v (a == b))

let neq =
  let a = (v : int) true in
  let b = (v : int) true in
  (v : bool) (iff v (a != b))

let lt =
  let a = (v : int) true in
  let b = (v : int) true in
  (v : bool) (iff v (a < b))

let gt =
  let a = (v : int) true in
  let b = (v : int) true in
  (v : bool) (iff v (a > b))

let le =
  let a = (v : int) true in
  let b = (v : int) true in
  (v : bool) (iff v (a <= b))

let ge =
  let a = (v : int) true in
  let b = (v : int) true in
  (v : bool) (iff v (a => b))

let plus =
  let a = (v : int) true in
  let b = (v : int) true in
  (v : int) (v == a + b)

let minus =
  let a = (v : int) true in
  let b = (v : int) true in
  (v : int) (v == a - b)

let nil = (v : int list) (fun (u : 'fa) -> (not (mem v u)) && not (hd v u))

let cons =
  let h = (v : int) true in
  let t = (v : int list) true in
  (v : int list) (fun (u : 'fa) ->
      iff (mem v u) (mem t u || u == h)
      && iff (hd v u) (u == h)
      && implies (hd v u) (mem v u))

(* let is_empty =
  let l1 = (v : int list) true in
  (v : bool) (fun (u : 'fa) ->
    implies (mem l1 u) (v) &&
    implies (not v) (not (mem l1 u))) *)

(* let push =
  let x = (v : int) true in
  let l1 = (v : int list) true in
  (v: int list) (fun (u: 'fa) ->
    implies (hd v u) (x == u) &&
    implies (mem l1 u) (mem v u)
  ) *)

(* let top =
  let l1 = (v: int list) true in
  (v : int) (fun (u:'fa) ->
    iff (v == u) (hd l1 u)
  ) *)

(* let tail =
  let l1 = (v: int list) true in
  (v : int list) (fun (u : 'fa) ->
    implies (mem l1 u) ((mem v u) || (hd l1 u)) &&
    implies (mem v u) (mem l1 u)
  ) *)

let is_empty =
  let l9 = (v:int list) true in
  (v : bool) (fun (u: 'fa) ->
    true && (not (mem l9 u)))

let push =
  let x0 = (v:int) true in
  let l0 = (v:int list) true in
  (l1:int list) (fun (u_0:'fa) ->
    fun (u_1:'fa) ->
      (iff (hd l1 u_0) (x0 == u_0)) &&
      (iff (mem l1 u_0) ((ord l1 x0 u_0) || (hd l1 u_0))) &&
      (iff (ord l1 u_0 u_1) ((hd l1 u_0) || (mem l0 u_1)))
    )

let top =
  let l3 = (v:int list) true in
  (x1 : int) (fun (u_0:'fa) ->
    (iff (x1 == u_0) (hd l3 u_0)))

let tail =
  let l4 = (v:int list) true in
  (l5: int list) (fun (u_0: 'fa) -> fun (u_1: 'fa) ->
    (implies (hd l5 u_0) ((mem l5 u_0) && (implies (ord l5 u_1 u_0) ((ord l5 u_0 u_1) && (implies (hd l4 u_0) (hd l4 u_1)))))) &&
    (implies ((not (mem l4 u_1)) && ((mem l5 u_0) && (not (hd l4 u_0)))) (hd l5 u_0)) &&
    (implies (mem l5 u_0) ((ord l4 u_1 u_0) || ((mem l4 u_0) && (hd l5 u_0 || (ord l5 u_0 u_1 || ((not (ord l5 u_0 u_1)) && (not (hd l4 u_1)))))))) &&
    (implies ((ord l4 u_1 u_0) || ((hd l5 u_0) || (ord l5 u_0 u_1 || ((u_0 == u_1) && ((not (hd l4 u_0)) && (mem l4 u_0)))))) (mem l5 u_0)) &&
    ((implies (ord l5 u_0 u_1) ((ord l4 u_0 u_1) && (mem l5 u_0))) && (implies ((ord l4 u_0 u_1) && (implies (hd l4) ( (not (ord l4 u_1 u_0)) && (mem l5 u_0)))) (ord l5 u_0 u_1)))
  )