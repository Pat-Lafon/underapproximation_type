val get_num_arr : stlc_ty -> int
val gen_type : unit -> stlc_ty
val vars_with_type : stlc_tyctx -> stlc_ty -> stlc_term
val gen_term_no_app : stlc_tyctx -> stlc_ty -> stlc_term


val is_const : stlc_term -> bool
val is_var : stlc_term -> bool
val is_abs : stlc_term -> bool
val is_app : stlc_term -> bool
val typing : stlc_tyctx -> stlc_term -> stlc_ty -> bool
val num_app : stlc_term -> int -> bool


val num_arr : stlc_ty -> int -> bool
val stlc_ty_nat : stlc_ty -> bool
val stlc_ty_arr1 : stlc_ty -> stlc_ty -> bool
val stlc_ty_arr2 : stlc_ty -> stlc_ty -> bool
val stlc_const : stlc_term -> int -> bool
val stlc_id : stlc_term -> int -> bool
val stlc_app1 : stlc_term -> stlc_term -> bool
val stlc_app2 : stlc_term -> stlc_term -> bool
val stlc_abs_ty : stlc_term -> stlc_ty -> bool
val stlc_abs_body : stlc_term -> stlc_term -> bool
val stlc_tyctx_emp : stlc_tyctx -> bool
val stlc_tyctx_hd : stlc_tyctx -> stlc_ty -> bool
val stlc_tyctx_tl : stlc_tyctx -> stlc_tyctx -> bool


val sizecheck : int -> bool
val bool_gen : unit -> bool
val int_range_inex : int -> int -> int
val ( - ) : int -> int -> int
val ( + ) : int -> int -> int
val ( >= ) : int -> int -> bool
val ( == ) : 'a -> 'a -> bool
val ( < ) : int -> int -> bool
val ( > ) : int -> int -> bool
val ( <= ) : int -> int -> bool


(* method predicates *)
(* for lists *)
val len : 'a list -> int -> bool
val emp : 'a list -> bool
val hd : 'a list -> 'a -> bool
val tl : 'a list -> 'a list -> bool
val list_mem : 'a list -> 'a -> bool
val sorted : 'a list -> bool
val uniq : 'a list -> bool


(* for tree *)
val depth : 'a tree -> int -> bool
val leaf : 'a tree -> bool
val root : 'a tree -> 'a -> bool
val lch : 'a tree -> 'a tree -> bool
val rch : 'a tree -> 'a tree -> bool
val tree_mem : 'a tree -> 'a -> bool
val bst : 'a tree -> bool
val heap : 'a tree -> bool
val complete : 'a tree -> bool


(* for rbtree *)
val num_black : 'a rbtree -> int -> bool
val rb_leaf : 'a rbtree -> bool
val rb_root : 'a rbtree -> 'a -> bool
val rb_root_color : 'a rbtree -> bool -> bool
val rb_lch : 'a rbtree -> 'a rbtree -> bool
val rb_rch : 'a rbtree -> 'a rbtree -> bool
val no_red_red : 'a rbtree -> bool

(* for stream *)
val forc : 'a stream lazyty -> 'a stream
val _forc : int -> int
val stream_len : 'a stream -> int -> bool
val stream_emp : 'a stream -> bool
val stream_hd : 'a stream -> 'a -> bool
val stream_tl : 'a stream -> 'a stream -> bool

(* for bankersq *)
val bankersq_len : 'a bankersq -> int -> bool
val bankersq1 : 'a bankersq -> int -> bool
val bankersq2 : 'a bankersq -> 'a stream -> bool
val bankersq3 : 'a bankersq -> int -> bool
val bankersq4 : 'a bankersq -> 'a stream -> bool

(* for batchedq *)
val batchedq_len : 'a batchedq -> int -> bool
val batchedq1 : 'a batchedq -> 'a list -> bool
val batchedq2 : 'a batchedq -> 'a list -> bool

(* for leftisthp *)
val leftisthp_depth : 'a leftisthp -> int -> bool
val leftisthp_leaf : 'a leftisthp -> bool
val leftisthp_root : 'a leftisthp -> 'a -> bool
val leftisthp_rank : 'a leftisthp -> int -> bool
val leftisthp_lch : 'a leftisthp -> 'a leftisthp -> bool
val leftisthp_rch : 'a leftisthp -> 'a leftisthp -> bool