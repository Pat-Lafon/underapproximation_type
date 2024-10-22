Require Import Setoid.
Require Import Lia.

From Coq Require Export Logic.Classical_Pred_Type.

From MyProject Require Import Tactics.

Inductive Tree : Type :=
| Leaf
| Node (l : Tree) (v : nat) (r : Tree).

Inductive depth : Tree -> nat -> Prop :=
| depth_leaf : depth Leaf 0
| depth_node : forall v l r n n1 n2,
  depth l n1 -> depth r n2 ->
  n = (max n1 n2) ->
  depth (Node l v r) (S n).

Inductive complete : Tree -> Prop :=
| CompleteLeaf :
complete Leaf
| CompleteNode : forall n x l r,
complete l -> complete r -> depth l n -> depth r n -> depth (Node l x r) (S n) ->
complete (Node l x r).

Inductive leaf : Tree -> Prop :=
| leaf_i : leaf Leaf.

Inductive root : Tree -> nat -> Prop :=
| root_i : forall l v r, root (Node l v r) v.

Inductive lch : Tree -> Tree -> Prop :=
| lch_i: forall v l r, lch (Node l v r) l.

Inductive rch  : Tree -> Tree  -> Prop :=
| rch_i: forall v l r, rch (Node l v r) r.

Inductive tree_mem : Tree -> nat -> Prop :=
| BstNode_root : forall l v r, tree_mem (Node l v r) v
| BstNode_child : forall l v c r, (tree_mem l c \/ tree_mem r c) -> tree_mem (Node l v r) c.

Inductive bst : Tree -> Prop :=
| BstLeaf : bst Leaf
| BstNode : forall x l r, (forall lo, tree_mem l lo -> lo < x) -> (forall hi, tree_mem r hi -> x < hi) -> bst l -> bst r -> bst (Node l x r).

Hint Constructors leaf: core.
Hint Constructors root: core.
Hint Constructors lch: core.
Hint Constructors rch: core.
Hint Constructors depth: core.
Hint Constructors complete: core.
Hint Constructors tree_mem: core.
Hint Constructors bst: core.
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
    - my_inversion H3; clear H3. my_inversion H4; clear H4. econstructor; eauto. econstructor; eauto. lia.
 Qed. Hint Resolve tree_complete_node: core.

Lemma tree_depth_node : forall l, (forall l1, (forall l2, (forall n, ((depth l1 n /\ (depth l2 n /\ (lch l l1 /\ rch l l2))) -> depth l (n + 1))))). Proof.
    intros. simp. destruct l.
    - my_inversion H1.
    - my_inversion H1; clear H1. my_inversion H2; clear H2. assert (n + 1 = S n). lia. rewrite H1. econstructor; eauto. lia.
 Qed. Hint Resolve tree_depth_node: core.

Lemma tree_complete_lch_complete : forall l, (forall l1, ((lch l l1 /\ complete l) -> complete l1)). Proof.
    intros. simp. my_inversion H0. my_inversion H. my_inversion H.
 Qed. Hint Resolve tree_complete_lch_complete: core.

Lemma tree_complete_rch_complete : forall l, (forall l1, ((rch l l1 /\ complete l) -> complete l1)). Proof.
    intros. simp. my_inversion H0. my_inversion H. my_inversion H.
 Qed. Hint Resolve tree_complete_rch_complete: core.

Lemma max_helper : forall n1 n2, 0 = Nat.max n1 n2 -> (n1 = 0 /\ n2 = 0). Proof.
    intros. destruct n1; destruct n2; auto. my_inversion H.
Qed.

Lemma max_helper2 : forall n n1 n2, n = Nat.max n1 n2 -> (n1 = n \/ n2 = n). Proof.
    intros. destruct n1; destruct n2; auto. my_inversion H. simp.
    apply PeanoNat.Nat.max_case. left; auto. right; auto.
Qed.

Lemma max_helper3 : forall n1 n2, (n1 = Nat.max n1 n2 \/ n2 = Nat.max n1 n2). Proof.
    intros.
    apply PeanoNat.Nat.max_case. left; auto. right; auto.
Qed.

Lemma depth_helper : forall t n1 n2, depth t n1 -> depth t n2 -> n1 = n2.
Proof.
    induction t; simpl; intros.
    + inversion H. inversion H0. reflexivity.
    + inversion H; subst. inversion H0; subst.
      specialize IHt2 with n3 n4.
      specialize IHt1 with n0 n1.
      apply IHt1 in H4.
      - subst. apply IHt2 in H6.
      * subst. reflexivity.
      * assumption.
      - assumption.
Qed.

Lemma tree_complete_lch_depth_minus_1 : forall l, (forall l1, (forall n, ((lch l l1 /\ (complete l /\ depth l n)) -> depth l1 (n - 1)))). Proof.
    intros. simp. destruct l.
    - my_inversion H.
    - my_inversion H0. my_inversion H; clear H. my_inversion H1. apply PeanoNat.Nat.max_case.
        + assert (S n2 - 1 = n2); try lia. rewrite H; auto.
        + assert (S n3 - 1 = n3); try lia. rewrite H. assert (n3 = n0).
            * eapply depth_helper; eauto.
            * subst; auto.
Qed. Hint Resolve tree_complete_lch_depth_minus_1: core.

Lemma tree_complete_rch_depth_minus_1 : forall l, (forall l1, (forall n, ((rch l l1 /\ (complete l /\ depth l n)) -> depth l1 (n - 1)))).
Proof.
    intros. simp. destruct l.
    - my_inversion H.
    - my_inversion H0. my_inversion H; clear H. my_inversion H1. apply PeanoNat.Nat.max_case.
        + assert (S n2 - 1 = n2); try lia. rewrite H. assert (n2 = n0).
            * eapply depth_helper; eauto.
            * subst; auto.
        + assert (S n3 - 1 = n3); try lia. rewrite H; auto.
Qed. Hint Resolve tree_complete_rch_depth_minus_1: core.

 Lemma tree_leaf_bst : forall l, (leaf l -> bst l). Proof.
    intros. my_inversion H. constructor.
  Qed. Hint Resolve tree_leaf_bst: core.

Lemma tree_bst_lch_bst : forall l, (forall l1, ((lch l l1 /\ bst l) -> bst l1)). Proof.
    intros. simp. my_inversion H0.
    - my_inversion H.
    - my_inversion H.
 Qed. Hint Resolve tree_bst_lch_bst: core.

Lemma tree_bst_rch_bst : forall l, (forall l1, ((rch l l1 /\ bst l) -> bst l1)). Proof.
    intros. simp. my_inversion H0.
    - my_inversion H.
    - my_inversion H.
 Qed. Hint Resolve tree_bst_rch_bst: core.

Lemma tree_bst_lch_mem_lt_root : forall l, (forall l1, (forall x, (forall y, ((bst l /\ (lch l l1 /\ (root l x /\ tree_mem l1 y))) -> y < x)))). Proof.
    intros. simp.
    - my_inversion H.
        + my_inversion H1.
        + my_inversion H1; clear H1. my_inversion H0; clear H0. apply H3. auto.
 Qed. Hint Resolve tree_bst_lch_mem_lt_root: core.

Lemma tree_bst_rch_mem_gt_root : forall l, (forall l1, (forall x, (forall y, ((bst l /\ (rch l l1 /\ (root l x /\ tree_mem l1 y))) -> x < y)))). Proof.
        intros. simp.
    - my_inversion H.
        + my_inversion H1.
        + my_inversion H1; clear H1. my_inversion H0; clear H0. apply H4. auto.
 Qed. Hint Resolve tree_bst_rch_mem_gt_root: core.

 Lemma tree_root_mem : forall l, (forall x, (root l x -> tree_mem l x)). Proof.
    intros. my_inversion H. auto.
  Qed. Hint Resolve tree_root_mem: core.

Lemma tree_mem_lch_mem : forall l, (forall l1, (forall x, ((lch l l1 /\ tree_mem l1 x) -> tree_mem l x))). Proof.
    intros. simp. my_inversion H; clear H. auto.
Qed. Hint Resolve tree_mem_lch_mem: core.

Lemma tree_mem_rch_mem : forall l, (forall l1, (forall x, ((rch l l1 /\ tree_mem l1 x) -> tree_mem l x))). Proof.
    intros. simp. my_inversion H. auto.
 Qed. Hint Resolve tree_mem_rch_mem: core.

Lemma tree_leaf_no_root : forall l, (forall x, (leaf l -> ~root l x)). Proof.
    intros. my_inversion H. unfold not. intro. my_inversion H0.
 Qed. Hint Resolve tree_leaf_no_root: core.

Lemma tree_leaf_no_ch : forall l, (forall l1, (leaf l -> ~(lch l l1 \/ rch l l1))). Proof.
    intros. unfold not; intro. my_inversion H. my_inversion H0; my_inversion H1.
 Qed. Hint Resolve tree_leaf_no_ch: core.

Lemma tree_no_leaf_exists_ch : forall l, (exists l1, (exists l2, (~leaf l -> (lch l l1 /\ rch l l2)))). Proof.
    intros. destruct l; repeat econstructor.
    - destruct H; constructor. Unshelve. constructor. constructor.
    - destruct H; constructor.
 Qed. Hint Resolve tree_no_leaf_exists_ch: core.

Lemma tree_no_leaf_exists_root : forall l, (exists x, (~leaf l -> root l x)). Proof.
    intros. destruct l; repeat econstructor. intro. destruct H. constructor. Unshelve. constructor.
 Qed. Hint Resolve tree_no_leaf_exists_root: core.

Lemma tree_root_no_leaf : forall l, (forall x, (root l x -> ~leaf l)). Proof.
    - intros. my_inversion H. unfold not. intros. my_inversion H0.
 Qed. Hint Resolve tree_root_no_leaf: core.

Lemma tree_ch_no_leaf : forall l, (forall l1, ((lch l l1 \/ rch l l1) -> ~leaf l)). Proof.
    intros. my_inversion H; clear H; unfold not; intro; my_inversion H0; my_inversion H.
Qed. Hint Resolve tree_ch_no_leaf: core.

Lemma tree_depth_geq_0 : forall l, (forall n, (depth l n -> n >= 0)). Proof.
    intros. lia.
 Qed. Hint Resolve tree_depth_geq_0: core.

Lemma tree_leaf_depth_0 : forall l, (forall n, ((leaf l /\ depth l n) -> n = 0)). Proof.
    intros. simp. my_inversion H. my_inversion H0.
 Qed. Hint Resolve tree_leaf_depth_0: core.

Lemma tree_positive_depth_is_not_leaf : forall l, (forall n, ((depth l n /\ n > 0) -> ~leaf l)). Proof.
    intros. simp. unfold not. intro. my_inversion H1. my_inversion H. my_inversion H0.
 Qed. Hint Resolve tree_positive_depth_is_not_leaf: core.

Lemma tree_depth_exists : forall l, exists n, depth l n.
Proof.
    intro. induction l.
    - exists 0. constructor.
    - my_inversion IHl1. my_inversion IHl2. exists (S (max x x0)). econstructor; eauto.
Qed.

Lemma tree_ch_depth_ex : forall l, (forall l1, (forall n, (exists n1, (((lch l l1 \/ rch l l1) /\ depth l n) -> depth l1 n1)))). Proof.
    intros. assert (exists n', depth l1 n'). apply tree_depth_exists. destruct H. exists x. intro. auto.
Qed. Hint Resolve tree_ch_depth_ex: core.


Lemma tree_ch_depth_minus_1 : forall l, (forall l1, (forall n, (forall n1, (((lch l l1 \/ rch l l1) /\ (depth l n /\ depth l1 n1)) -> n1 <= (n - 1))))).
Proof.
    intros. simp. my_inversion H0.
    - destruct H; my_inversion H.
    - destruct H; my_inversion H; clear H. assert (n1 = n2). eapply depth_helper; eauto. lia. assert (n1 = n3). eapply depth_helper; eauto. lia.
Qed.
Hint Resolve tree_ch_depth_minus_1: core.

Lemma tree_depth_0_is_leaf : forall l, (forall n, ((depth l n /\ n = 0) -> leaf l)). Proof.
    intros. simp. my_inversion H. constructor.
Qed. Hint Resolve tree_depth_0_is_leaf: core.
