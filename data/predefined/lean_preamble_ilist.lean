import ProofAutomation
import PPTheorems

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

def len : ilist → Int → Prop
  | .Nil, n => n = 0
  | .Cons _ xs, n => len xs (n - 1)

def sorted : ilist → Prop
  | .Nil => True
  | .Cons _ .Nil => True
  | .Cons x (.Cons y ys) => x ≤ y ∧ sorted (.Cons y ys)

def mem : ilist → Int → Prop
  | .Nil, _ => False
  | .Cons h t, x => h = x ∨ mem t x

def uniq : ilist → Prop
  | .Nil => True
  | .Cons h t => ¬mem t h ∧ uniq t

-- Axiom section: definitions available to grind/simp for proving axioms.
-- lean_dump.ml emits 'end Axioms' after the axioms, before the subtyping query.
section Axioms
  attribute [local simp] is_nil is_cons head tail len sorted mem uniq
  attribute [local grind cases] ilist Bool
  attribute [local grind =] is_nil is_cons head tail len sorted mem uniq
