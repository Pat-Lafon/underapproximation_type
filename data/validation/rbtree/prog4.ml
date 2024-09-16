let rec rbtree_gen (inv : int) (color : bool) (h : int) : int rbtree =
  if sizecheck h then
    if color then Rbtleaf
    else if bool_gen () then Rbtleaf
    else Rbtnode (true, Rbtleaf, int_gen (), Rbtleaf)
  else
    let (hh : int) = subs h in
    let (rt : int) = int_gen () in
    if color then
      Err
    else
      let (c : bool) = bool_gen () in
      if c then
        let (lt3 : int rbtree) = rbtree_gen (subs inv) true h in
        let (rt3 : int rbtree) = rbtree_gen (subs inv) true h in
        Rbtnode (true, lt3, rt, rt3)
      else
        let (lt4 : int rbtree) = rbtree_gen (subs (subs inv)) false hh in
        let (rt4 : int rbtree) = rbtree_gen (subs (subs inv)) false hh in
        Rbtnode (false, lt4, rt, rt4)

let[@assert] rbtree_gen =
  let inv = (v >= 0 : [%v: int]) [@over] in
  let color = (true : [%v: bool]) [@over] in
  let[@assert] h =
    (v >= 0 && if color then v + v == inv else v + v + 1 == inv
      : [%v: int])
      [@over]
  in
  (num_black v h && no_red_red v
   &&
   if color then not (rb_root_color v true)
   else (h == 0) #==> (not (rb_root_color v false))
    : [%v: int rbtree])
    [@under]
