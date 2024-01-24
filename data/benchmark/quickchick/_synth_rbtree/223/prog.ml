let rec goal (inv : int) (c : bool) (height : int) =
  (if lt_eq_one height
   then
     Rbtnode
       (true, (goal (increment (int_gen ())) false inv), (increment inv),
         (goal (increment height) c (increment height)))
   else
     Rbtnode
       (true, (goal inv true inv), (increment inv),
         (goal (int_gen ()) c (increment inv))) : int rbtree)