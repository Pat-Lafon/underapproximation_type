let[@library] ( == ) =
  let a = (true : [%v: int]) [@over] in
  let b = (true : [%v: int]) [@over] in
  (iff v (a == b) : [%v: bool]) [@under]

let[@library] ( != ) =
  let a = (true : [%v: int]) [@over] in
  let b = (true : [%v: int]) [@over] in
  (iff v (a != b) : [%v: bool]) [@under]

let[@library] ( < ) =
  let a = (true : [%v: int]) [@over] in
  let b = (true : [%v: int]) [@over] in
  (iff v (a < b) : [%v: bool]) [@under]

let[@library] ( > ) =
  let a = (true : [%v: int]) [@over] in
  let b = (true : [%v: int]) [@over] in
  (iff v (a > b) : [%v: bool]) [@under]

let[@library] ( <= ) =
  let a = (true : [%v: int]) [@over] in
  let b = (true : [%v: int]) [@over] in
  (iff v (a <= b) : [%v: bool]) [@under]

let[@library] ( >= ) =
  let a = (true : [%v: int]) [@over] in
  let b = (true : [%v: int]) [@over] in
  (iff v (a >= b) : [%v: bool]) [@under]

let[@library] ( + ) =
  let a = (true : [%v: int]) [@over] in
  let b = (true : [%v: int]) [@over] in
  (v == a + b : [%v: int]) [@under]

let[@library] ( - ) =
  let a = (true : [%v: int]) [@over] in
  let b = (true : [%v: int]) [@over] in
  (v == a - b : [%v: int]) [@under]

let[@library] TT = (true : [%v: unit]) [@under]
let[@library] True = (v : [%v: bool]) [@under]
let[@library] False = (not v : [%v: bool]) [@under]
let[@library] true = (v : [%v: bool]) [@under]
let[@library] false = (not v : [%v: bool]) [@under]
let[@library] Nil = (emp v : [%v: int list]) [@under]

let[@library] Cons =
  let x = (true : [%v: int]) [@over] in
  let xs = (true : [%v: int list]) [@over] in
  (hd v x && tl v xs : [%v: int list]) [@under]

let[@library] list_mem =
  let xs = (true : [%v: int list]) [@over] in
  let x = (true : [%v: int]) [@over] in
  (v == list_mem xs x : [%v: bool]) [@under]

(* the built-in random generators *)

let[@library] int_range =
  let a = (true : [%v: int]) [@over] in
  let b = (1 + a < v : [%v: int]) [@over] in
  (a < v && v < b : [%v: int]) [@under]

let[@library] bool_gen =
  let _ = (true : [%v: unit]) [@over] in
  (true : [%v: bool]) [@under]

let[@library] int_gen =
  let _ = (true : [%v: unit]) [@over] in
  (true : [%v: int]) [@under]

let[@library] nat_gen =
  let _ = (true : [%v: unit]) [@over] in
  (v >= 0 : [%v: int]) [@under]

let[@library] int_range_inc =
  let a = (true : [%v: int]) [@over] in
  let b = (a <= v : [%v: int]) [@over] in
  (a <= v && v <= b : [%v: int]) [@under]

let[@library] int_range_inex =
  let a = (true : [%v: int]) [@over] in
  let b = (a <= v : [%v: int]) [@over] in
  (a <= v && v < b : [%v: int]) [@under]

(* This is int_range_inex except the first argument is zero
     * Additionally I've strengthened the precondition on b so that the resulting
   coverage must not be empty *)
let[@library] int_range_inex_zero =
   let b = (v > 0 : [%v: int]) [@over] in
   (0 <= v && v < b : [%v: int]) [@under]

(* This is subtraction except I've built in that the result must not be
   negative and the minus 1 is built in *)
let[@library] difference_inex =
  let a = (true : [%v: int]) [@over] in
  let b = (v < a : [%v: int]) [@over] in
  (v == (a - b) - 1 && v >= 0 : [%v: int]) [@under]

let[@library] increment =
  let n = (true : [%v: int]) [@over] in
  (v == n + 1 : [%v: int]) [@under]

let[@library] decrement =
  let n = (true : [%v: int]) [@over] in
  (v == n - 1 : [%v: int]) [@under]

let[@library] double =
  let n = (true : [%v: int]) [@over] in
  (v == n * 2 : [%v: int]) [@under]

let[@library] lt_eq_one =
  let s = (true : [%v: int]) [@over] in
  (iff v (s <= 1) && iff (not v) (s > 1) : [%v: bool]) [@under]

(* uniquel  *)

let[@library] gt_eq_int_gen =
  let x = (true : [%v: int]) [@over] in
  (v >= x : [%v: int]) [@under]

let[@library] sized_list_gen =
  let s = (true : [%v: int]) [@over] in
  (len v s : [%v: int list]) [@under]

let[@library] sizecheck =
  let x = (true : [%v: int]) [@over] in
  (iff v (x == 0) && iff (not v) (x > 0) : [%v: bool]) [@under]

let[@library] subs =
  let s = (true : [%v: int]) [@over] in
  (v == s - 1 : [%v: int]) [@under]

let[@library] incr =
  let s = (true : [%v: int]) [@over] in
  (v == s + 1 : [%v: int]) [@under]

let[@library] head =
  let s = (true : [%v: int list]) [@over] in
  (hd s v: [%v: int]) [@under]

let[@library] dummy = (true : [%v: unit]) [@under]

let[@library] hidden_list_gen =
  let _ = (true : [%v: unit]) [@over] in
  (true : [%v: int list]) [@under]
