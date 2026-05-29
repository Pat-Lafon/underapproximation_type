open Sexplib.Std
open Mtyped
open Raw_term
open Term
open Rty
open Prop
open Constructor_declaration

module Nt = Normalty.Ntyped

type type_decl =
  | Decl_constructors of constructor_declaration list
  | Decl_record of (Nt.t, string) typed list
[@@deriving sexp]

type 't item =
  | MTyDecl of {
      type_name : string;
      type_params : string list;
      type_decl : type_decl;
    }
  | MValDecl of ('t, string) typed
  | MMethodPred of ('t, string) typed
  | MAxiom of { name : string; prop : 't prop }
  | MFuncImpRaw of {
      name : ('t, string) typed;
      if_rec : bool;
      body : ('t, 't raw_term) typed;
    }
  | MFuncImp of {
      name : ('t, string) typed;
      if_rec : bool;
      body : ('t, 't term) typed;
    }
  | MRty of { is_assumption : bool; name : string; rty : 't rty }
[@@deriving sexp]
