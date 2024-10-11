let[@assert] rty1 =
  let s = (0 <= v : [%v: int]) [@over] in
  let x = (true : [%v: int]) [@over] in
  (len v s && sorted v && fun (u : int) -> (hd v u) #==> (x <= u)
    : [%v: int list])
    [@under]

let[@assert] rty2 =
  let s = (0 <= v : [%v: int]) [@over] in
  let x = (true : [%v: int]) [@over] in
  (not (emp v) && len v s && sorted v && fun (u : int) -> (hd v u) #==> (x <= u)
    : [%v: int list])
    [@under]