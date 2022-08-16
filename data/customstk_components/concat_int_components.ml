let rec concat (l1 : int list) (l2: int list) : int list =
  if is_empty l1 then l2
  else push (top l1) (concat (tail l1) l2)