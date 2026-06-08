import ProofAutomation

-- Preamble for failed subtyping queries (rbtree only)
-- This file is prepended to each dumped Lean file.
-- The `namespace Axioms` at the end is closed by lean_dump.ml after the
-- axioms; lean_dump.ml then emits `open Axioms` so bare `ax_<n>`
-- references work in the subtyping query body.

inductive irbtree where
  | Rbtleaf
  | Rbtnode (color : Bool) (left : irbtree) (value : Int) (right : irbtree)
  deriving DecidableEq, Repr, Plausible.Arbitrary

@[simp, grind =] def is_rbtleaf : irbtree → Bool
  | .Rbtleaf => true
  | .Rbtnode _ _ _ _ => false

@[simp, grind =] def is_rbtnode : irbtree → Bool
  | .Rbtleaf => false
  | .Rbtnode _ _ _ _ => true

@[simp, grind =] def color : irbtree → Option Bool
  | .Rbtleaf => none
  | .Rbtnode c _ _ _ => some c

@[simp, grind =] def value : irbtree → Option Int
  | .Rbtleaf => none
  | .Rbtnode _ _ v _ => some v

@[simp, grind =] def left : irbtree → Option irbtree
  | .Rbtleaf => none
  | .Rbtnode _ l _ _ => some l

@[simp, grind =] def right : irbtree → Option irbtree
  | .Rbtleaf => none
  | .Rbtnode _ _ _ r => some r

def num_black_impl : irbtree → Int → Bool
  | .Rbtleaf, h => h == 0
  | .Rbtnode c l _ r, h =>
    if ¬c then num_black_impl l (h - 1) && num_black_impl r (h - 1)
    else num_black_impl l h && num_black_impl r h

def num_black (t : irbtree) (h : Int) (res : Bool) : Prop :=
  num_black_impl t h = res

-- Bridge lemma: every num_black-witnessed height is non-negative. Closes the
-- `(num_black t 0 true) ∧ color t = false → False`-shape axioms (e.g. ax_30)
-- by making the height-non-neg fact reachable from `num_black_impl t h` via
-- E-matching, without prove_axiom having to unfold the recursive impl.
@[grind →]
theorem num_black_nonneg (t : irbtree) (h : Int) :
    num_black t h true → h ≥ 0 := by
  induction t generalizing h with
  | Rbtleaf => simp [num_black, num_black_impl]; omega
  | Rbtnode c l _ r ihl _ =>
    simp only [num_black, num_black_impl]
    cases c <;> simp <;> intro hyp _
    · have := ihl (h - 1) hyp; omega
    · exact ihl h hyp

grind_pattern num_black_nonneg => num_black_impl t h

def no_red_red_impl : irbtree → Bool
  | .Rbtleaf => true
  | .Rbtnode c l _ r =>
    if ¬c then no_red_red_impl l && no_red_red_impl r
    else
      match l, r with
      | .Rbtnode c' _ _ _, .Rbtnode c'' _ _ _ =>
          !c' && !c'' && no_red_red_impl l && no_red_red_impl r
      | .Rbtnode c' _ _ _, .Rbtleaf => !c' && no_red_red_impl l
      | .Rbtleaf, .Rbtnode c'' _ _ _ => !c'' && no_red_red_impl r
      | .Rbtleaf, .Rbtleaf => true

def no_red_red (t : irbtree) (res : Bool) : Prop :=
  no_red_red_impl t = res

-- Axiom namespace: definitions are available to grind/simp for proving axioms.
-- lean_dump.ml emits 'end Axioms' + 'open Axioms' after the axioms, before
-- the subtyping query. The namespace gives every Cobb axiom a real
-- `Axioms.ax_<n>` prefix that `Helpers.isAxiomName` can filter on.
namespace Axioms
  attribute [local simp] is_rbtleaf is_rbtnode color value left right
    num_black_impl num_black no_red_red_impl no_red_red
  attribute [local grind cases] irbtree Bool
  attribute [local grind =] is_rbtleaf is_rbtnode color value left right
    num_black_impl num_black no_red_red_impl no_red_red
