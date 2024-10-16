Require Import Setoid.
Require Import Lia.

From Coq Require Export Logic.Classical_Pred_Type.

From MyProject Require Import Tactics.

Inductive Tree : Type :=
| Leaf
| Node (l : Tree) (v : nat) (r : Tree).

Inductive depth : Tree -> nat -> Prop :=
| depth_leaf : depth Leaf 0
| depth_node : forall v l r n,
  depth l n -> depth r n ->
  depth (Node l v r) (n + 1).

Inductive complete : Tree -> Prop :=
| CompleteLeaf :
complete Leaf
| CompleteNode : forall n x l r,
complete l -> complete r -> depth l n -> depth r n ->
complete (Node l x r).

Inductive leaf : Tree -> Prop :=
| leaf_i : leaf Leaf.

Inductive lch : Tree -> Tree -> Prop :=
| lch_i: forall v l r, lch (Node l v r) l.

Inductive rch  : Tree -> Tree  -> Prop :=
| rch_i: forall v l r, rch (Node l v r) r.

Hint Constructors leaf: core.
(* Hint Constructors root: core. *)
Hint Constructors lch: core.
Hint Constructors rch: core.
Hint Constructors depth: core.
Hint Constructors complete: core.
Hint Unfold not: core.

Lemma tree_complete_leaf : forall l, (leaf l -> complete l). Proof.
    intros. my_inversion H. auto.
 Qed. Hint Resolve tree_complete_leaf: core.

Lemma tree_depth_leaf : forall l, (leaf l -> depth l 0). Proof.
    intros. my_inversion H. auto.
 Qed. Hint Resolve tree_depth_leaf: core.

Lemma tree_complete_node : forall l, (forall l1, (forall l2, (forall n, ((complete l1 /\ (complete l2 /\ (depth l1 n /\ (depth l2 n /\ (lch l l1 /\ rch l l2))))) -> complete l)))). Proof.
intros. simp. destruct l.
    - constructor.
    - my_inversion H3; clear H3. my_inversion H4; clear H4. econstructor; eauto.
 Qed. Hint Resolve tree_complete_node: core.

Lemma tree_depth_node : forall l, (forall l1, (forall l2, (forall n, ((depth l1 n /\ (depth l2 n /\ (lch l l1 /\ rch l l2))) -> depth l (n + 1))))). Proof.
    intros. simp. destruct l.
    - my_inversion H1.
    - my_inversion H1; clear H1. my_inversion H2; clear H2. constructor; auto.
 Qed. Hint Resolve tree_depth_node: core.

Lemma tree_complete_lch_complete : forall l, (forall l1, ((lch l l1 /\ complete l) -> complete l1)). Proof.
    intros. simp. my_inversion H0. my_inversion H. my_inversion H.
 Qed. Hint Resolve tree_complete_lch_complete: core.

Lemma tree_complete_rch_complete : forall l, (forall l1, ((rch l l1 /\ complete l) -> complete l1)). Proof.
    intros. simp. my_inversion H0. my_inversion H. my_inversion H.
 Qed. Hint Resolve tree_complete_rch_complete: core.

Lemma tree_complete_lch_depth_minus_1 : forall l, (forall l1, (forall n, ((lch l l1 /\ (complete l /\ depth l n)) -> depth l1 (n - 1)))). Proof.
    intros. simp. my_inversion H1; clear H1. my_inversion H. my_inversion H; clear H. assert (n0 + 1 - 1 = n0). lia. rewrite H. auto.
 Qed. Hint Resolve tree_complete_lch_depth_minus_1: core.

Lemma tree_complete_rch_depth_minus_1 : forall l, (forall l1, (forall n, ((rch l l1 /\ (complete l /\ depth l n)) -> depth l1 (n - 1)))). Proof.
    intros. simp. my_inversion H1; clear H1. my_inversion H. my_inversion H; clear H. assert (n0 + 1 - 1 = n0). lia. rewrite H. auto.
 Qed. Hint Resolve tree_complete_rch_depth_minus_1: core.