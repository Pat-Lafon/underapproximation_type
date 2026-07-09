(** Predefined data type declarations. Loaded together with normal_typing.ml,
    which holds the matching val signatures. *)

(** Premitive type *)

type 'a option = None | Some of 'a

type 'a tezosTree =
  | TezosLeaf of 'a
  | TezosNode1 of 'a * 'a tezosTree
  | TezosNode2 of 'a * 'a tezosTree * 'a tezosTree

(* NOTE: pair are builtin *)
(* val fst : 'a * 'b -> 'a *)
(* val snd : 'a * 'b -> 'b *)

(** lists *)

type 'a list = Nil | Cons of 'a * 'a list

(** trees *)

type 'a tree = Leaf | Node of 'a * 'a tree * 'a tree

(** Stream *)

type 'a lazyty = Lazyty of 'a
type 'a stream = Streamnil | Streamlazycons of 'a * 'a stream lazyty

(** leftisthp *)

type 'a leftisthp =
  | Lhpleaf
  | Lhpnode of int * 'a * 'a leftisthp * 'a leftisthp

(** rbtree *)

type 'a rbtree = Rbtleaf | Rbtnode of bool * 'a rbtree * 'a * 'a rbtree

(** stlc *)

type stlc_ty = Stlc_ty_nat | Stlc_ty_arr of stlc_ty * stlc_ty

type stlc_term =
  | Stlc_const of int
  | Stlc_id of int
  | Stlc_app of stlc_term * stlc_term
  | Stlc_abs of stlc_ty * stlc_term

type stlc_measure = Measure of int * int

(** Xen API *)

(** enum type encoded as int; *)

(* type file_kind = *)
(*   | S_BLK = 0 *)
(*   | S_CHR = 1 *)
(*   | S_DIR = 2 *)
(*   | S_FIFO = 3 *)
(*   | S_LNK = 4 *)
(*   | S_REG = 5 *)
(*   | S_SOCK = 6 *)

type fd = {
  size : int;
  delay_read : Delay.t option;
  delay_write : Delay.t option;
  kind : int;
}

(** [select_fd_spec] defines a behaviour for a select input: a file descriptor
    kind and how long before any event happens on it *)

type select_fd_spec = { kind : int; wait : float }

(** Vellvm *)

(* LLVM types *)
type typ =
  | TYPE_I of int
  | TYPE_Void
  | TYPE_Vector of int * typ
  | TYPE_Array of int * typ
  | TYPE_Others

(* LLVM dynamic values *)
type dvalue =
  | DVALUE_I of int * int
  | DVALUE_None
  | DVALUE_Vector of typ * dvalue list
  | DVALUE_Array of typ * dvalue list
  | DVALUE_Others

(** Herdtools7 *)

type literal =
  | L_Int of int
  | L_Bool of bool
  | L_Real of float
  | L_BitVector of char list
  | L_String of string

type expr =
  | E_Literal of literal
  | E_Var of string
  | E_Binop of string * expr * expr
  | E_Unop of string * expr
  | E_Slice of expr * slice list
  | E_Cond of expr * expr * expr
  | E_Tuple of expr list
  | E_Others

type slice =
  | Slice_Single of expr
      (** [Slice_Single i] is the slice of length [1] at position [i]. *)
  | Slice_Range of expr * expr
      (** [Slice_Range (j, i)] denotes the slice from [i] to [j - 1]. *)
  | Slice_Length of expr * expr
      (** [Slice_Length (i, n)] denotes the slice starting at [i] of length [n].
      *)
  | Slice_Star of expr * expr
      (** [Slice_Start (factor, length)] denotes the slice starting at
          [factor * length] of length [n]. *)

(** Zipperposition *)

type pt_term =
  | PT_Var of string
  | PT_Ite of pt_term * pt_term * pt_term
  | PT_App of pt_term * pt_term list
