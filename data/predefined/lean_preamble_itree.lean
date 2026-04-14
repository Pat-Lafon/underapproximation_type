import ProofAutomation
import PPTheorems

-- Preamble for failed subtyping queries (itree only)

inductive itree where
  | Leaf
  | Node (value : Int) (left : itree) (right : itree)
  deriving DecidableEq

@[simp, grind =] def is_leaf : itree → Bool
  | .Leaf => true
  | .Node _ _ _ => false

@[simp, grind =] def is_node : itree → Bool
  | .Leaf => false
  | .Node _ _ _ => true

@[simp, grind =] def value : itree → Option Int
  | .Leaf => none
  | .Node v _ _ => some v

@[simp, grind =] def left : itree → Option itree
  | .Leaf => none
  | .Node _ l _ => some l

@[simp, grind =] def right : itree → Option itree
  | .Leaf => none
  | .Node _ _ r => some r

def depth : itree → Int → Prop
  | .Leaf, n => n = 0
  | .Node _ l r, n => ∃ dl dr : Int, depth l dl ∧ depth r dr ∧ n = 1 + max dl dr

def complete : itree → Prop
  | .Leaf => True
  | .Node _ l r => complete l ∧ complete r ∧ ∃ h : Int, depth l h ∧ depth r h

def height : itree → Int → Prop := depth

def leaf : itree → Int → Prop
  | .Leaf, _ => False
  | .Node v .Leaf .Leaf, x => v = x
  | .Node _ l r, x => leaf l x ∨ leaf r x

def lower_bound : itree → Int → Prop
  | .Leaf, _ => True
  | .Node y l r, x => x ≤ y ∧ lower_bound l x ∧ lower_bound r x

def upper_bound : itree → Int → Prop
  | .Leaf, _ => True
  | .Node y l r, x => y ≤ x ∧ upper_bound l x ∧ upper_bound r x

def bst : itree → Prop
  | .Leaf => True
  | .Node x l r => bst l ∧ bst r ∧ upper_bound l x ∧ lower_bound r x

-- Axiom section: definitions available to grind/simp for proving axioms.
-- lean_dump.ml emits 'end Axioms' after the axioms, before the subtyping query.
section Axioms
  attribute [local simp] is_leaf is_node value left right
    depth complete height leaf lower_bound upper_bound bst
  attribute [local grind cases] itree Bool
  attribute [local grind =] is_leaf is_node value left right
    depth complete height leaf lower_bound upper_bound bst
