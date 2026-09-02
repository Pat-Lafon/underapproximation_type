let[@assert] rty =
  let s = ((0 <= v : [%v: int]) [@over]) in
  ((v == s + 1 : [%v: int]) [@under])
