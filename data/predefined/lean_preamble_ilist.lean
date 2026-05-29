import ProofAutomation

-- Preamble for failed subtyping queries (ilist only)

inductive ilist where
  | Nil
  | Cons (head : Int) (tail : ilist)
  deriving DecidableEq, Repr, Plausible.Arbitrary

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

  -- Bridge lemmas: assert the wrapper holds at the impl value. Patterns are
  -- keyed on the impl so they fire after `[local grind =]` unfolds the
  -- wrapper out of the E-graph. Wrapper-keyed `grind_pattern`s on dumped
  -- `ax_<n>` theorems (emitted by lean_dump.ml) can then match with the
  -- output variable bound to `<fn>_impl args`.
  theorem len_intro (l : ilist) : len l (len_impl l) := rfl
  grind_pattern len_intro => len_impl l

  theorem is_even_intro (x : Int) : is_even x (is_even_impl x) := rfl
  grind_pattern is_even_intro => is_even_impl x

  theorem mem_intro (l : ilist) (x : Int) : mem l x (mem_impl l x) := rfl
  grind_pattern mem_intro => mem_impl l x

  theorem uniq_intro (l : ilist) : uniq l (uniq_impl l) := rfl
  grind_pattern uniq_intro => uniq_impl l

  theorem sorted_intro (l : ilist) : sorted l (sorted_impl l) := rfl
  grind_pattern sorted_intro => sorted_impl l

  theorem all_evens_intro (l : ilist) : all_evens l (all_evens_impl l) := rfl
  grind_pattern all_evens_intro => all_evens_impl l

  theorem all_equal_intro (l : ilist) (x : Int) :
      all_equal l x (all_equal_impl l x) := rfl
  grind_pattern all_equal_intro => all_equal_impl l x
