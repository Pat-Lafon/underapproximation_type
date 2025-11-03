val ( == ) : 'a -> 'a -> bool
val ( != ) : 'a -> 'a -> bool
val ( < ) : int -> int -> bool
val ( <= ) : int -> int -> bool
val ( > ) : int -> int -> bool
val ( >= ) : int -> int -> bool
val ( + ) : int -> int -> int
val ( - ) : int -> int -> int
val ( * ) : int -> int -> int
val not : bool -> bool
val ite : bool -> 'a -> 'a -> 'a
(* dt *)

(* others *)
val int_range : int -> int -> int
val bool_gen : unit -> bool
val int_gen : unit -> int
val nat_gen : unit -> int
val int_range_inc : int -> int -> int
val int_range_inex : int -> int -> int
val int_range_inex_zero : int -> int
val difference_inex : int -> int -> int
val increment : int -> int
val decrement : int -> int
val double : int -> int
val lt_eq_one : int -> bool
val gt_eq_int_gen : int -> int
val sizecheck : int -> bool
val subs : int -> int
val incr : int -> int
val dummy : unit
val head : int list -> int
val sized_list_gen : int -> int list


(* method predicates *)
(* for lists *)
val len : 'a list -> int -> bool
val emp : 'a list -> bool
val hd : 'a list -> 'a -> bool
val tl : 'a list -> 'a list -> bool
val list_mem : int list -> int -> bool
val sorted : 'a list -> bool
val uniq : 'a list -> bool
val all_evens : 'a list -> bool
val index : int -> int list -> int -> bool