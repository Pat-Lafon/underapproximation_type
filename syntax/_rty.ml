open Sexplib.Std
open Mtyped
open Cty

type ou = Over | Under [@@deriving sexp]

type 't rty =
  | RtyBase of { ou : ou; cty : 't cty }
  | RtyBaseArr of { argcty : 't cty; arg : (string[@bound]); retty : 't rty }
  | RtyArrArr of { argrty : 't rty; retty : 't rty }
  | RtyTuple of 't rty list
  | RtyPolyType of { pt : string; rty : 't rty }
  | RtyPolyPred of { pred : ('t, string) typed; rty : 't rty }
[@@deriving sexp]
