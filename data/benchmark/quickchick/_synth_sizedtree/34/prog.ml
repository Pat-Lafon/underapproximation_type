let rec goal (s0 : int) =
  (if sizecheck s0
   then Leaf
   else
     if bool_gen ()
     then Node ((subs s0), (goal s01), (goal s01))
     else Node ((subs s0), (goal s01), (goal s01)) : int tree)
