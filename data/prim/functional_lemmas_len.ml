let il_mem (l : [%forall: int list]) (u : [%forall: int]) (w : [%forall: int]) =
  implies (u == w) (implies (mem l u) (mem l w))

let il_hd (l : [%forall: int list]) (u : [%forall: int]) (w : [%forall: int]) =
  implies (u == w) (implies (hd l u) (hd l w))

let il_len (l : [%forall: int list]) (u : [%forall: int]) (w : [%forall: int]) =
  implies (u == w) (implies (len l u) (len l w))

let it_mem (l : [%forall: int tree]) (u : [%forall: int]) (w : [%forall: int]) =
  implies (u == w) (implies (mem l u) (mem l w))

let it_hd (l : [%forall: int tree]) (u : [%forall: int]) (w : [%forall: int]) =
  implies (u == w) (implies (hd l u) (hd l w))

let it_len (l : [%forall: int tree]) (u : [%forall: int]) (w : [%forall: int]) =
  implies (u == w) (implies (len l u) (len l w))
