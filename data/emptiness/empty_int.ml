let[@assert] rty =
  let s = ((0 <= v : [%v: int]) [@over]) in
  ((v == s && v < 0 : [%v: int]) [@under])
