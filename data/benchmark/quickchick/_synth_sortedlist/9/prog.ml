let rec goal (size : int) (x0 : int) =
  (if sizecheck size then [] else x0 :: (goal (subs size) x0) : int list)
