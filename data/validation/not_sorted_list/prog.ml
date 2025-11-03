let rec not_sorted_list_gen (s : int) (idx : int) : int list =
  if s == idx then
    let (l : int list) = sized_list_gen (s - 1) in
    let (y : int) = head l in
    let (x : int) = gt_eq_int_gen y in
    x :: l
  else int_gen () :: not_sorted_list_gen (s - 1) idx

let[@assert] not_sorted_list_gen =
  let s = ((2 <= v : [%v: int]) [@over]) in
  let idx = ((2 <= v && v <= s : [%v: int]) [@over]) in
  ((len v s && not (sorted v)
    && (fun ((u1 [@exists]) : int) ((u2 [@exists]) : int) -> index idx v u1 && index (idx-1) v u2 && u1 > u2)
    : [%v: int list])
    [@under])
