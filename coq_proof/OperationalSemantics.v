From stdpp Require Import mapset.
From Coq Require Import Logic.ClassicalFacts.
From Coq Require Import Classical.
From CT Require Import CoreLang.
From CT Require Import CoreLangProp.

Import Atom.
Import CoreLang.
Import Tactics.
Import NamelessTactics.

Inductive eval_op: biop -> constant -> constant -> constant -> Prop :=
| eval_op_plus: forall (a b: nat), eval_op op_plus a b (a + b)
| eval_op_eq: forall (a b: nat), eval_op op_eq a b (Nat.eqb a b)
| eval_op_lt: forall (a b: nat), eval_op op_lt a b (Nat.ltb a b)
| eval_op_rannat: forall (a b c: nat), eval_op op_rannat a b c.

Global Hint Constructors eval_op: core.

Reserved Notation "t1 '↪' t2" (at level 60).

(** the small step operational semantics *)
Inductive step : tm -> tm -> Prop :=
| ST_LetOp: forall op (c1 c2 c3: constant) e,
    body e ->
    eval_op op c1 c2 c3 -> (tletbiop op c1 c2 e) ↪ (e ^t^ c3)
| ST_Lete1: forall e1 e1' e,
    body e ->
    e1 ↪ e1' ->
    (tlete e1 e) ↪ (tlete e1' e)
| ST_Lete2: forall (v1: value) e,
    lc v1 -> body e ->
    (tlete (tvalue v1) e) ↪ (e ^t^ v1)
| ST_LetAppLam: forall T (v_x: value) e1 e,
    body e1 -> body e -> lc v_x ->
    (tletapp (vlam T e1) v_x e) ↪ tlete (e1 ^t^ v_x) e
| ST_LetAppFix: forall T_f (v_x: value) Tx (e1: tm) e,
    body (vlam T_f e1) -> lc v_x -> body e ->
    tletapp (vfix T_f (vlam Tx e1)) v_x e ↪
            tletapp ((vlam T_f e1) ^v^ v_x) (vfix T_f (vlam Tx e1)) e
| ST_Matchb_true: forall e1 e2,
    lc e1 -> lc e2 ->
    (tmatchb true e1 e2) ↪ e1
| ST_Matchb_false: forall e1 e2,
    lc e1 -> lc e2 ->
    (tmatchb false e1 e2) ↪ e2
where "t1 '↪' t2" := (step t1 t2).

Definition relation (X : Type) := X -> X -> Prop.

Lemma step_regular: forall e1 e2, e1 ↪ e2 -> lc e1 /\ lc e2.
Proof.
  intros.
  induction H; split; auto.
  - destruct H. econstructor; auto. apply H.
  - apply open_lc_tm; auto.
  - destruct_hyp_conj. rewrite lete_lc_body; split; auto.
  - destruct_hyp_conj. rewrite lete_lc_body; split; auto.
  - try destruct_hyp_conj. rewrite lete_lc_body; split; auto.
  - apply open_lc_tm; auto.
  - rewrite letapp_lc_body; split; auto. rewrite lc_abs_iff_body; auto.
  - rewrite lete_lc_body; split; auto. apply open_lc_tm; auto.
  - rewrite letapp_lc_body; split; auto. rewrite lc_fix_iff_body; auto.
    rewrite body_vlam_eq; eauto.
  - rewrite letapp_lc_body; split; auto.
    + eapply open_lc_value; eauto.
    + split; auto. rewrite body_vlam_eq in H. rewrite lc_fix_iff_body; eauto.
Qed.

Lemma step_regular1: forall e1 e2, e1 ↪ e2 -> lc e1.
Proof.
  intros. apply step_regular in H. destruct H; auto.
Qed.

Lemma step_regular2: forall e1 e2, e1 ↪ e2 -> lc e2.
Proof.
  intros. apply step_regular in H. destruct H; auto.
Qed.

Global Hint Resolve step_regular1: core.
Global Hint Resolve step_regular2: core.

Inductive multistep : relation tm :=
| multistep_refl : forall (x : tm),
    lc x ->
    multistep x x
| multistep_step : forall (x y z : tm),
    step x y ->
    multistep y z ->
    multistep x z.

Global Hint Constructors multistep : core.

Theorem multistep_R : forall (x y : tm),
    step x y -> multistep x y.
Proof.
  intros x y H.
  apply multistep_step with y. apply H. apply multistep_refl; eauto.
Qed.

Theorem multistep_trans :
  forall (x y z : tm),
      multistep x y  ->
      multistep y z ->
      multistep x z.
Proof.
  intros x y z G H.
  induction G.
    - (* multistep_refl *) assumption.
    - (* multistep_step *)
      apply multistep_step with y. assumption.
      apply IHG. assumption.
Qed.

Definition normal_form (t : tm) : Prop :=
  ~ exists t', t ↪ t'.

Definition deterministic {tm : Type} (R : relation tm) :=
  forall x y1 y2 : tm, R x y1 -> R x y2 -> y1 = y2.

Notation "t1 '↪*' t2" := (multistep t1 t2) (at level 40).

Lemma multi_step_regular: forall e1 e2, e1 ↪* e2 -> lc e1 /\ lc e2.
Proof.
  intros.
  induction H; auto. destruct IHmultistep. split; auto. eapply step_regular1; eauto.
Qed.

Lemma multi_step_regular1: forall e1 e2, e1 ↪* e2 -> lc e1.
Proof.
  intros. apply multi_step_regular in H. destruct H; auto.
Qed.

Lemma multi_step_regular2: forall e1 e2, e1 ↪* e2 -> lc e2.
Proof.
  intros. apply multi_step_regular in H. destruct H; auto.
Qed.

Ltac step_regular_simp :=
  repeat match goal with
    | [H: _ ↪ _ |- lc _] => apply step_regular in H; destruct H; auto
    | [H: _ ↪ _ |- body _] => apply step_regular in H; destruct H; auto
    end.

Lemma tlete_terr_exfalso: forall e (v: value), ~ tlete terr e ↪* v.
Proof.
  intros. intro H.
  inversion H; subst. inversion H0; subst. inversion H6.
Qed.

Lemma tlete_value_exists: forall e (v_x v: value), tlete v_x e ↪* v <-> lc v_x /\ body e /\ e ^t^ v_x ↪* v.
Proof.
  split; intros.
  - inversion H; subst. inversion H0; subst; auto. inversion H6.
  - econstructor; repeat destruct_hyp_conj; auto. instantiate (1:= e ^t^ v_x). constructor; auto.
    auto.
Qed.

Lemma open_eq_terr: forall e u, e ^t^ u = terr -> e = terr.
Proof.
  induction e; simpl; intros; auto; inversion H.
Qed.
