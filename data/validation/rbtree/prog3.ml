let rec rbtree_gen (inv : int) (color : bool) (h : int) : int rbtree =
  if sizecheck h then
    if color then Rbtleaf else if bool_gen () then Rbtleaf else Err
  else if color then
    let (lt2 : int rbtree) = rbtree_gen (subs inv) false (subs h) in
    let (rt2 : int rbtree) = rbtree_gen (subs inv) false (subs h) in
    Rbtnode (false, lt2, int_gen (), rt2)
  else
    let (c : bool) = bool_gen () in
    if c then
      let (lt3 : int rbtree) = rbtree_gen (subs inv) true h in
      let (rt3 : int rbtree) = rbtree_gen (subs inv) true h in
      Rbtnode (true, lt3, int_gen (), rt3)
    else
      let (lt4 : int rbtree) = rbtree_gen (subs (subs inv)) false (subs h) in
      let (rt4 : int rbtree) = rbtree_gen (subs (subs inv)) false (subs h) in
      Rbtnode (false, lt4, int_gen (), rt4)

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
