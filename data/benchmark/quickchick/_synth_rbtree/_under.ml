external method_predicates : t = "numblack" "hdcolor" "noredred"
let[@library] r = 
   (true : [%v: int]) [@under]


let[@assert] goal =
  let inv = (v >= 0 : [%v: int]) [@over] in
  let c = (true : [%v: bool]) [@over] in
  let[@assert] height =
    (v >= 0 && implies c (v + v == inv) && implies (not c) (v + v + 1 == inv)
      : [%v: int])
      [@over]
  in
  (* the height is the number of black nodes *)
  (numblack v height && noredred v
   && fun (u : int) ->
   (* parent is red; the hdcolor cannot be red *)
   (c && not (hdcolor v true))
   || (* parent is black; the hdcolor can be any color *)
   ((not c) && implies (height == 0) (hdcolor v true))
    : [%v: int rbtree])
    [@under]
