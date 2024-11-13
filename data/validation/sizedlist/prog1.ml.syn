let rec sized_list_gen = fun s ->
  let (xccc7) = sizecheck s in
  match xccc7 with
  | True -> Nil
  | False ->
      let (xccc8) = bool_gen () in
      (match xccc8 with
       | True -> []
       | False ->
           let (xccc9) = subs s in
           let (xccc10) = sized_list_gen xccc9 in
           let (xccc11) = int_gen () in xccc11 :: xccc10)