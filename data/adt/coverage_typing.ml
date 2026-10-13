let[@library] ( <= ) =
  let a = (true : [%v: int]) [@over] in
  let b = (true : [%v: int]) [@over] in
  (iff v (a <= b) : [%v: bool]) [@under]

let[@library] ( - ) =
  let a = (true : [%v: int]) [@over] in
  let b = (true : [%v: int]) [@over] in
  (v == a - b : [%v: int]) [@under]

let[@library] true = (v : [%v: bool]) [@under]
let[@library] false = (not v : [%v: bool]) [@under]

let[@library] bool_gen =
  let _ = (true : [%v: unit]) [@over] in
  (true : [%v: bool]) [@under]

let[@library] int_gen =
  let _ = (true : [%v: unit]) [@over] in
  (true : [%v: int]) [@under]

let[@library] Nil = (is_nil v : [%v: ilist]) [@under]

let[@library] Cons =
  let x = (true : [%v: int]) [@over] in
  let xs = (true : [%v: ilist]) [@over] in
  (is_cons v && head v == x && tail v == xs : [%v: ilist]) [@under]
