let rec goal (inv : int) (c : bool) (height : int) =
  (if lt_eq_one height
   then
     Rbtnode
       (true, (goal (increment inv) c (increment inv)), (increment height),
         (goal (increment height) c (increment height)))
   else
     Rbtnode
       (true, (goal (increment height) c height), (int_gen ()),
         (goal (int_gen ()) c (increment inv))) : int rbtree)
