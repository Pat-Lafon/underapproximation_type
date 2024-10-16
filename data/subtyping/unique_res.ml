let[@assert] rty1 =
  let s = (0 <= v : [%v: int]) [@over] in
  (fun (l [@exists] : int list), (fun (x [@exists] : bool), ((fun (x_6 [@exists] : bool), ((x_6 <=> s == 0) && (¬x_6 <=> s > 0) && ¬x_6 && (∃s_17, (s_17 >= 0 && s_17 < s && s_17 == (s - 1) && (len l s_17 && uniq l && ¬list_mem l x))))) && (∃l, (∃x, ((∃x_6, ((x_6 <=> s == 0) && (¬x_6 <=> s > 0) && ¬x_6 && (∃s_17, (s_17 >= 0 && s_17 < s && s_17 == (s - 1) && (len l s_17 && uniq l && ¬list_mem l x))))) && (∃_x9, (hd _x9 x && tl _x9 l && v == _x9)))))))
    : [%v: int list])
    [@under]

let[@assert] rty2 =
  let s = (0 <= v : [%v: int]) [@over] in
  ((not (emp v)) && len v s && uniq v : [%v: int list]) [@under]
