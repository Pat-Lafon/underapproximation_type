let rec goal (inv : int) (c : bool) (height : int) =
  (if c
   then
     Rbtnode
       (true, (goal (int_gen ()) true inv), (increment height),
         (goal (increment inv) false (increment height)))
   else
     if c
     then
       Rbtnode
         (true, (goal (int_gen ()) c (increment (int_gen ()))), (int_gen ()),
           (goal r false inv))
     else
       if c
       then
         Rbtnode
           (true, (goal (increment inv) false (increment inv)), inv,
             (goal (increment inv) false (increment inv)))
       else
         if c
         then
           Rbtnode
             (true, (goal (increment inv) false (increment inv)),
               (increment inv), (goal r c inv))
         else
           if lt_eq_one height
           then goal (increment inv) true (increment inv)
           else
             Rbtnode
               (true, (goal (increment inv) true (increment inv)),
                 (increment height), (goal (increment inv) false height)) : 
  int rbtree)
