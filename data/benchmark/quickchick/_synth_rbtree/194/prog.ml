let rec goal (inv : int) (c : bool) (height : int) =
  (if c
   then
     Rbtnode
       (true, (goal (int_gen ()) true inv), (int_gen ()),
         (goal (int_gen ()) false (int_gen ())))
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
           (true, (goal (increment inv) true (int_gen ())),
             (increment height), (goal (increment inv) c inv))
       else
         if c
         then
           Rbtnode
             (true, (goal r true inv), (increment (int_gen ())),
               (goal (increment inv) true (increment r)))
         else
           if c
           then
             Rbtnode
               (true, (goal height true (increment (int_gen ()))),
                 (increment height), (goal r c (increment height)))
           else
             Rbtnode
               (true, (goal height true (increment inv)), (increment height),
                 (goal (increment inv) false (increment r))) : int rbtree)
