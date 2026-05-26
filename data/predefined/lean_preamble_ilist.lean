import ProofAutomation

-- Preamble for failed subtyping queries (ilist only)

inductive ilist where
  | Nil
  | Cons (head : Int) (tail : ilist)
  deriving DecidableEq

@[simp, grind =] def is_nil : ilist → Bool
  | .Nil => true
  | .Cons _ _ => false

@[simp, grind =] def is_cons : ilist → Bool
  | .Nil => false
  | .Cons _ _ => true

@[simp, grind =] def head : ilist → Option Int
  | .Nil => none
  | .Cons h _ => some h

@[simp, grind =] def tail : ilist → Option ilist
  | .Nil => none
  | .Cons _ t => some t

def len_impl : ilist → Int
  | .Nil => 0
  | .Cons _ xs => 1 + len_impl xs

def len (l : ilist) (n : Int) : Prop :=
  len_impl l = n

def is_even_impl (x : Int) : Bool := x % 2 == 0

def is_even (x : Int) (res : Bool) : Prop :=
  is_even_impl x = res

def mem_impl : ilist → Int → Bool
  | .Nil, _ => false
  | .Cons h t, x => h == x || mem_impl t x

def mem (l : ilist) (x : Int) (res : Bool) : Prop :=
  mem_impl l x = res

def uniq_impl : ilist → Bool
  | .Nil => true
  | .Cons h t => !mem_impl t h && uniq_impl t

def uniq (l : ilist) (res : Bool) : Prop :=
  uniq_impl l = res

def sorted_impl : ilist → Bool
  | .Nil => true
  | .Cons _ .Nil => true
  | .Cons x (.Cons y ys) => decide (x ≤ y) && sorted_impl (.Cons y ys)

def sorted (l : ilist) (res : Bool) : Prop :=
  sorted_impl l = res

def all_evens_impl : ilist → Bool
  | .Nil => true
  | .Cons h t => is_even_impl h && all_evens_impl t

def all_evens (l : ilist) (res : Bool) : Prop :=
  all_evens_impl l = res

def all_equal_impl : ilist → Int → Bool
  | .Nil, _ => true
  | .Cons h t, x => h == x && all_equal_impl t x

def all_equal (l : ilist) (x : Int) (res : Bool) : Prop :=
  all_equal_impl l x = res

-- Axiom namespace: definitions available to grind/simp for proving axioms.
-- lean_dump.ml emits 'end Axioms' + 'open Axioms' after the axioms, before
-- the subtyping query. The namespace gives every Cobb axiom a real
-- `Axioms.ax_<n>` prefix that `Helpers.isAxiomName` can filter on.
namespace Axioms
  attribute [local simp] is_nil is_cons head tail
    len_impl len
    is_even_impl is_even
    mem_impl mem
    uniq_impl uniq
    sorted_impl sorted
    all_evens_impl all_evens
    all_equal_impl all_equal
  attribute [local grind cases] ilist Bool
  attribute [local grind =] is_nil is_cons head tail
    len_impl len
    is_even_impl is_even
    mem_impl mem
    uniq_impl uniq
    sorted_impl sorted
    all_evens_impl all_evens
    all_equal_impl all_equal
