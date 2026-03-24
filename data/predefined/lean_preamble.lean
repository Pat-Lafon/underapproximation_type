import ProofAutomation

-- Preamble for failed subtyping queries
-- This file is prepended to each dumped Lean file.
-- Edit this to add or modify type/predicate declarations.

-- Type declarations
inductive ilist where
  | Nil
  | Cons (head : Int) (tail : ilist)
  deriving DecidableEq

inductive itree where
  | Leaf
  | Node (value : Int) (left : itree) (right : itree)
  deriving DecidableEq

inductive rbtree where
  | Rbtleaf
  | Rbtnode (color : Bool) (left : rbtree) (value : Int) (right : rbtree)
  deriving DecidableEq

-- inductive StlcTy where
--   | Stlc_ty_nat
--   | Stlc_ty_arr (t1 : StlcTy) (t2 : StlcTy)

-- inductive StlcTerm where
--   | Stlc_const (n : Int)
--   | Stlc_id (n : Int)
--   | Stlc_app (t1 : StlcTerm) (t2 : StlcTerm)
--   | Stlc_abs (ty : StlcTy) (body : StlcTerm)

-- inductive StlcTyctx where
--   | Stlc_tyctx_nil
--   | Stlc_tyctx_cons (ty : StlcTy) (rest : StlcTyctx)

-- ilist recognizers/accessors

@[simp]
def is_nil : ilist → Bool
  | .Nil => true
  | .Cons _ _ => false

@[simp]
def is_cons : ilist → Bool
  | .Nil => false
  | .Cons _ _ => true

@[simp]
def head : ilist → Option Int
  | .Nil => none
  | .Cons h _ => some h

@[simp]
def tail : ilist → Option ilist
  | .Nil => none
  | .Cons _ t => some t

-- itree recognizers/accessors

@[simp]
def is_leaf : itree → Bool
  | .Leaf => true
  | .Node _ _ _ => false

@[simp]
def is_node : itree → Bool
  | .Leaf => false
  | .Node _ _ _ => true

@[simp]
def value : itree → Option Int
  | .Leaf => none
  | .Node v _ _ => some v

@[simp]
def left : itree → Option itree
  | .Leaf => none
  | .Node _ l _ => some l

@[simp]
def right : itree → Option itree
  | .Leaf => none
  | .Node _ _ r => some r

-- rbtree recognizers/accessors

@[simp]
def is_rbtleaf : rbtree → Bool
  | .Rbtleaf => true
  | .Rbtnode _ _ _ _ => false

@[simp]
def is_rbtnode : rbtree → Bool
  | .Rbtleaf => false
  | .Rbtnode _ _ _ _ => true

@[simp]
def color : rbtree → Option Bool
  | .Rbtleaf => none
  | .Rbtnode c _ _ _ => some c

@[simp]
def value_rb : rbtree → Option Int
  | .Rbtleaf => none
  | .Rbtnode _ _ v _ => some v

@[simp]
def left_rb : rbtree → Option rbtree
  | .Rbtleaf => none
  | .Rbtnode _ l _ _ => some l

@[simp]
def right_rb : rbtree → Option rbtree
  | .Rbtleaf => none
  | .Rbtnode _ _ _ r => some r

-- Method predicate definitions (list)

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

-- Method predicate definitions (itree)

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

-- Method predicate definitions (rbtree)
-- Convention: color = false means black, color = true means red

def numblack : rbtree → Int → Prop
  | .Rbtleaf, n => n = 0
  | .Rbtnode c l _ r, n =>
    if ¬c then numblack l (n - 1) ∧ numblack r (n - 1)
    else numblack l n ∧ numblack r n

def noredred : rbtree → Prop
  | .Rbtleaf => True
  | .Rbtnode c l _ r =>
    if c then noredred l ∧ noredred r
    else
      match l, r with
      | .Rbtnode c' _ _ _, .Rbtnode c'' _ _ _ =>
          c' ∧ c'' ∧ noredred l ∧ noredred r
      | .Rbtnode c' _ _ _, .Rbtleaf => c' ∧ noredred l
      | .Rbtleaf, .Rbtnode c'' _ _ _ => c'' ∧ noredred r
      | .Rbtleaf, .Rbtleaf => True

def hdcolor : rbtree → Bool → Prop
  | .Rbtleaf, _ => False
  | .Rbtnode c _ _ _, c' => c = c'

def rbtree_invariant : rbtree → Int → Prop
  | t, h => noredred t ∧ numblack t h ∧ hdcolor t false
