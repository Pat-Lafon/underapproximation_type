let[@assert] rty1 =
  let s = (0 <= v : [%v: int]) [@over] in
  (* todo: somehow move x into the final query??*)
  let x = (true : [%v: int]) [@over] in
  (fun ((l [@exists]) : int list) ((s1 [@exists]) : int) ->
     s > 0 && s1 >= 0 && s1 < s
     && s1 == s - 1
     && len l s1 && uniq l
     && (not (list_mem l x))
     && hd v x && tl v l
    : [%v: int list])
    [@under]

let[@assert] rty2 =
  let s = (0 <= v : [%v: int]) [@over] in
  let x = (true : [%v: int]) [@over] in
  (fun ((s1 [@exists]) : int) ((l [@exists]) : int list) ->
     s > 0 && s1 >= 0 && s1 < s
     && s1 == s - 1
     && len l s1 && uniq l
     && (not (list_mem l x))
     && (not (emp v))
     && len v s && uniq v
    : [%v: int list])
    [@under]
