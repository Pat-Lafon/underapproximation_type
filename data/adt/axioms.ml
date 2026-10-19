let[@axiom] len_geq_0 (l : ilist) (n : int) = (len l n)#==>(n >= 0)

let[@axiom] len_functional (l : ilist) (r1 : int) (r2 : int) =
  (len l r1 && len l r2)#==>(r1 == r2)

let[@axiom] len_total (l : ilist) = fun ((res [@exists]) : int) -> len l res

let[@axiom] len_0 (l : ilist) (res : int) =
  (is_nil l && 0 == res)#==>(len l res)

let[@axiom] len_0_fwd (l : ilist) (res : int) =
  (len l res && is_nil l)#==>(0 == res)

let[@axiom] len_1 (l : ilist) (xs : ilist) (res_0 : int) (res : int) =
  ((is_cons l && tail l == xs) && len xs res_0 && 1 + res_0 == res)#==>(len l
                                                                          res)

let[@axiom] len_1_fwd (l : ilist) (res : int) (xs : ilist) =
  (len l res && is_cons l && tail l == xs)
  #==> (fun ((res_0 [@exists]) : int) -> len xs res_0 && 1 + res_0 == res)
