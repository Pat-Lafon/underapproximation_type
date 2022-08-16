let rec concat (l1 : Stack.t) (l2: Stack.t) : Stack.t =
  if Stack.is_empty l1 then l2
  else Stack.push (Stack.top l1) (concat (Stack.tail l1) l2)