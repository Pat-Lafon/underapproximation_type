let rec sized_list_gen (s : int) : int list =
  Err

let[@assert] sized_list_gen =
  let s = (0 <= v : [%v: int]) [@over] in
  (emp v : [%v: int list]) [@under]
