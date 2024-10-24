let rec goal (size : int) (x0 : int) =
  (if sizecheck x0
   then (subs x0) :: (goal (subs size) x0)
   else goal (subs size) (gt_eq_int_gen x0) : int list)
