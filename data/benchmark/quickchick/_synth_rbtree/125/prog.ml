let rec goal (inv : int) (c : bool) (height : int) =
  (if c
   then
     Rbtnode
       (true, (goal inv c inv), (increment inv),
         (goal inv true (increment r)))
   else
     if c
     then
       Rbtnode
         (true, (goal (increment height) true (increment (int_gen ()))),
           (int_gen ()), (goal (increment height) c height))
     else
       if c
       then
         Rbtnode
           (true, (goal (increment height) true (increment inv)),
             (increment inv), (goal (increment height) c (int_gen ())))
       else
         if c
         then
           Rbtnode
             (true, (goal r true inv), (increment inv),
               (goal (int_gen ()) false inv))
         else
           if lt_eq_one inv
           then
             Rbtnode
               (true, (goal inv false inv), (increment (int_gen ())),
                 (goal (increment height) true (increment inv)))
           else
             Rbtnode
               (true, (goal (increment inv) c inv), (increment height),
                 (goal inv false (increment (int_gen ())))) : int rbtree)
