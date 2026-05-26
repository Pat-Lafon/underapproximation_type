import ProofAutomation

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

def depth_impl : itree → Int
  | .Leaf => 0
  | .Node _ l r =>
      if depth_impl l > depth_impl r then 1 + depth_impl l
      else                                1 + depth_impl r

def depth (t : itree) (res : Int) : Prop :=
  depth_impl t = res

def complete_impl : itree → Bool
  | .Leaf => true
  | .Node _ l r =>
      complete_impl l && complete_impl r && (depth_impl l == depth_impl r)

def complete (t : itree) (res : Bool) : Prop :=
  complete_impl t = res

def lower_bound_impl : itree → Int → Bool
  | .Leaf, _ => true
  | .Node y l r, x => decide (x ≤ y) && lower_bound_impl l x && lower_bound_impl r x

def lower_bound (t : itree) (x : Int) (res : Bool) : Prop :=
  lower_bound_impl t x = res

def upper_bound_impl : itree → Int → Bool
  | .Leaf, _ => true
  | .Node y l r, x => decide (y ≤ x) && upper_bound_impl l x && upper_bound_impl r x

def upper_bound (t : itree) (x : Int) (res : Bool) : Prop :=
  upper_bound_impl t x = res

def bst_impl : itree → Bool
  | .Leaf => true
  | .Node x l r => bst_impl l && bst_impl r && upper_bound_impl l x && lower_bound_impl r x

def bst (t : itree) (res : Bool) : Prop :=
  bst_impl t = res

-- Axiom namespace: definitions available to grind/simp for proving axioms.
-- lean_dump.ml emits 'end Axioms' + 'open Axioms' after the axioms, before
-- the subtyping query. The namespace gives every Cobb axiom a real
-- `Axioms.ax_<n>` prefix that `Helpers.isAxiomName` can filter on.
namespace Axioms
  attribute [local simp] is_leaf is_node value left right
    depth_impl depth complete_impl complete
    lower_bound_impl lower_bound
    upper_bound_impl upper_bound
    bst_impl bst
  attribute [local grind cases] itree Bool
  attribute [local grind =] is_leaf is_node value left right
    depth_impl depth complete_impl complete
    lower_bound_impl lower_bound
    upper_bound_impl upper_bound
    bst_impl bst
