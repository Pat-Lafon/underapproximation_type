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

def height_impl : itree → Int := depth_impl

def height (t : itree) (res : Int) : Prop :=
  height_impl t = res

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
    depth_impl depth complete_impl complete height_impl height
    leaf lower_bound upper_bound bst
  attribute [local grind cases] itree Bool
  attribute [local grind =] is_leaf is_node value left right
    depth_impl depth complete_impl complete height_impl height
    leaf lower_bound upper_bound bst
