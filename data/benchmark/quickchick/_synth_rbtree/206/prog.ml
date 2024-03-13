let rec goal (inv : int) (c : bool) (height : int) =
  (if lt_eq_one inv
   then
     Rbtnode
       (true, (goal (int_gen ()) false (increment height)), (increment inv),
         (goal (int_gen ()) false inv))
   else goal (increment (int_gen ())) true (increment inv) : int rbtree)