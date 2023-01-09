From stdpp Require Import mapset.
From CT Require Import CoreLangProp.
From CT Require Import ListCtx.
From CT Require Import BasicTypingProp.
From CT Require Import OperationalSemanticsProp.

Import Atom.
Import CoreLang.
Import Tactics.
Import NamelessTactics.
Import ListCtx.
Import BasicTyping.
Import BasicTypingProp.
Import OperationalSemantics.
Import OperationalSemanticsProp.

Definition mk_app e1 e2 :=
  tlete e1 (tlete e2 (tletapp (vbvar 1) (vbvar 0) (vbvar 0))).

Definition mk_app_v1 v1 e2 :=
  tlete e2 (tletapp v1 (vbvar 0) (vbvar 0)).

Definition mk_nat_gen := tletbiop op_rannat 0 0 (vbvar 0).

Notation " nat-gen " := (mk_nat_gen) (at level 10, right associativity).

Definition mk_bool_gen :=
  tletbiop op_rannat 0 0 (tletbiop op_eq (vbvar 0) 0 (vbvar 0)).

Notation " bool-gen " := (mk_bool_gen) (at level 10, right associativity).

Definition mk_non_deter_choice e1 e2 :=
  tlete (bool-gen) (tmatchb (vbvar 0) e1 e2).

Notation " e1 '⊕' e2 " := (mk_non_deter_choice e1 e2) (at level 90, right associativity).

Definition mk_term_meet_nat e1 e2 :=
  tlete e1 (tlete e2 (tletbiop op_eq (vbvar 0) (vbvar 1)
                        (tmatchb (vbvar 0) (vbvar 1) terr)
    )).

Notation " e1 '⊗nat' e2 " := (mk_term_meet_nat e1 e2) (at level 90, right associativity).

Definition mk_term_meet_bool e1 e2 :=
  tlete e1 (tlete e2 (tmatchb (vbvar 0) (tmatchb (vbvar 1) true terr) (tmatchb (vbvar 1) terr false))).

Notation " e1 '⊗bool' e2 " := (mk_term_meet_bool e1 e2) (at level 90, right associativity).

Definition mk_term_meet (T: base_ty) e1 e2 :=
  match T with
  | TBool => e1 ⊗bool e2
  | TNat => e1 ⊗nat e2
  end.

Notation " e1 '⊗{' T '}' e2 " := (mk_term_meet T e1 e2) (at level 90, right associativity).

(* lc property *)

Lemma body_vbvar_zero: body (vbvar 0).
Proof.
  econstructor. instantiate (1:= ∅). simpl; auto.
Qed.

Ltac lc_solver1 :=
  match goal with
  | [|- lc (tvalue (vconst _))] => constructor
  | [|- body (tvalue (vbvar 0))] => apply body_vbvar_zero; auto
  | [H: lc (tlete ?u _) |- lc ?u] => invclear H; auto
  end || lc_solver.

Ltac step_solver1 :=
  repeat match goal with
    | [|- lc _ ] => step_length_regular_simp1; lc_solver1
    | [|- body _ ] => step_length_regular_simp1; lc_solver1
    | [|- eval_op _ _ _ _ ] => constructor; simpl; lc_solver1
    | [|- _ ↪ _] => constructor; simpl; lc_solver1
    | [|- ?a_ ↪* ?a] => constructor; lc_solver1
    | [|- _ ^t^ _ ↪* _] => simpl; repeat rewrite open_rec_lc_tm; auto
    | [|- tmatchb (vconst _) ?e _ ↪* ?e ] => apply multistep_R; constructor; auto
    | [|- tmatchb (vconst _) _ ?e ↪* ?e ] => apply multistep_R; constructor; auto
    end; auto.

Lemma mk_term_meet_nat_lc: forall e1 e2, lc e1 -> lc e2 -> lc (e1 ⊗nat e2).
Proof.
  intros. unfold mk_term_meet_nat.
  lc_solver1.
Qed.

Lemma mk_term_meet_bool_lc: forall e1 e2, lc e1 -> lc e2 -> lc (e1 ⊗bool e2).
Proof.
  intros. unfold mk_term_meet_bool.
  lc_solver1.
Qed.

Lemma mk_term_meet_lc: forall T e1 e2, lc e1 -> lc e2 -> lc (e1 ⊗{T} e2).
Proof.
  intros. destruct T.
  apply  mk_term_meet_nat_lc; auto.
  apply  mk_term_meet_bool_lc; auto.
Qed.

Lemma mk_app_lc: forall e1 e2, lc e1 -> lc e2 -> lc (mk_app e1 e2).
Proof.
  intros.
  auto_exists_L; intros; simpl; rewrite open_rec_lc_tm; auto.
  repeat (auto_exists_L; intros; simpl).
Qed.

Lemma mk_app_body: forall e2, lc e2 -> body (tlete e2 (tletapp (vbvar 1) (vbvar 0) (vbvar 0))).
Proof.
  intros. unfold body.
  auto_exists_L; intros; simpl. rewrite open_rec_lc_tm; auto.
  repeat (auto_exists_L; intros; simpl).
Qed.

Lemma mk_bool_gen_body: body (tletbiop op_eq (vbvar 0) 0 (vbvar 0)).
Proof.
  exists ∅. intros. econstructor; eauto.
  rewrite decide_True; auto.
  instantiate (1:= ∅).
  intros. rewrite decide_False; eauto. simpl. eauto.
Qed.

Lemma mk_bool_gen_lc: lc (bool-gen).
Proof.
  unfold mk_bool_gen. repeat lc_solver.
  apply mk_bool_gen_body; auto.
Qed.

Lemma mk_non_deter_choice_body: forall e1 e2, lc e1 -> lc e2 -> body (tmatchb (vbvar 0) e1 e2).
Proof.
  intros.
  lc_solver.
Qed.

Lemma mk_non_deter_choice_lc: forall e1 e2, lc e1 -> lc e2 -> lc (e1 ⊕ e2).
Proof.
  intros. unfold mk_non_deter_choice.
  lc_solver. apply mk_bool_gen_lc.
Qed.

(* step property *)

Lemma mk_app_step: forall e1 e1' e2,
    lc e2 ->
    e1 ↪ e1' -> mk_app e1 e2 ↪ mk_app e1' e2.
Proof.
  unfold mk_app; intros.
  econstructor; auto. apply mk_app_body; auto.
Qed.

Lemma mk_app_multistep: forall e1 e1' e2,
    lc e2 ->
    e1 ↪* e1' -> mk_app e1 e2 ↪* mk_app e1' e2.
Proof.
  intros. generalize dependent e2.
  induction H0; intros.
  - constructor; auto. apply mk_app_lc; auto.
  - eapply multistep_trans; eauto. apply multistep_R. eapply mk_app_step; eauto.
Qed.

Lemma mk_bool_gen_reduce_to_all_bool: forall (b:bool), (bool-gen) ↪* b.
Proof.
  intros. unfold mk_bool_gen.
  destruct b.
  - econstructor. instantiate (1:= (tletbiop op_eq (vbvar 0) 0 (vbvar 0)) ^t^ 0).
    repeat constructor. apply mk_bool_gen_body; auto.
    simpl; econstructor. instantiate (1:= (vbvar 0) ^t^ true).
    step_solver1. step_solver1.
  - econstructor. instantiate (1:= (tletbiop op_eq (vbvar 0) 0 (vbvar 0)) ^t^ 1).
    step_solver1. apply mk_bool_gen_body; auto.
    simpl; econstructor. instantiate (1:= (vbvar 0) ^t^ false).
    step_solver1. step_solver1.
Qed.

Lemma mk_nat_gen_reduce_to_all_nat: forall (n:nat), (nat-gen) ↪* n.
Proof.
  intros. econstructor. instantiate (1:= (vbvar 0) ^t^ n). repeat constructor. lc_solver1.
  simpl. apply multistep_refl. lc_solver1.
Qed.

Global Hint Resolve mk_bool_gen_reduce_to_all_bool: core.
Global Hint Resolve mk_nat_gen_reduce_to_all_nat: core.

Lemma mk_non_deter_choice_reduce_to_two_branchs: forall e1 e2, lc e1 -> lc e2 -> (e1 ⊕ e2) ↪* e1 /\ (e1 ⊕ e2) ↪* e2.
Proof.
  intros. split; unfold mk_non_deter_choice.
  - apply multistep_trans with (tlete true (tmatchb (vbvar 0) e1 e2)).
    + apply multistep_lete. lc_solver1. apply mk_bool_gen_reduce_to_all_bool.
    + econstructor. instantiate (1:= (tmatchb (vbvar 0) e1 e2) ^t^ true).
      step_solver1. step_solver1.
  - apply multistep_trans with (tlete false (tmatchb (vbvar 0) e1 e2)).
    + apply multistep_lete. lc_solver1. apply mk_bool_gen_reduce_to_all_bool.
    + econstructor. instantiate (1:= (tmatchb (vbvar 0) e1 e2) ^t^ false).
      step_solver1. step_solver1.
Qed.

(* Lemma mk_app_step2: forall (v1: value) e2 e2', *)
(*     lc v1 -> *)
(*     e2 ↪ e2' -> mk_app v1 e2 ↪ mk_app v1 e2'. *)
(* Proof. *)
(*   unfold mk_app; intros. *)
(*   econstructor; auto. apply mk_app_body; auto. *)
(* Qed. *)

(* Lemma mk_app_multistep2: forall e1 e1' e2, *)
(*     lc e2 -> *)
(*     e1 ↪* e1' -> mk_app e1 e2 ↪* mk_app e1' e2. *)
(* Proof. *)
(*   intros. generalize dependent e2. *)
(*   induction H0; intros. *)
(*   - constructor; auto. apply mk_app_lc; auto. *)
(*   - eapply multistep_trans; eauto. apply multistep_R. eapply mk_app_step1; eauto. *)
(* Qed. *)

Lemma matchb_spec: forall (cond: bool) (e1 e2: tm) (v:value),
    (tmatchb cond e1 e2) ↪* v -> (cond = true /\ e1 ↪* v) \/ (cond = false /\ e2 ↪* v).
Proof.
  intros. destruct cond.
  - left; split; auto. invclear H. invclear H0. auto.
  - right; split; auto. invclear H. invclear H0. auto.
Qed.

Lemma meet_nat_condition_spec: forall (x1 x2: nat) (v:value),
    x1 = x2 /\ v = x1 <-> tletbiop op_eq x1 x2 (tmatchb (vbvar 0) x1 terr) ↪* v.
Proof.
  split; intros; mydestr; subst.
  - econstructor. instantiate (1:= (tmatchb (vbvar 0) x2 terr) ^t^ true).
    { step_solver1. exists ∅; simpl; intros. step_solver1. erewrite <- PeanoNat.Nat.eqb_refl. econstructor. }
    simpl. apply multistep_R. econstructor; step_solver1.
  - destruct (Nat.eq_dec x1 x2); subst.
    + split; auto. invclear H. invclear H0. simpl in H1. invclear H7. rewrite PeanoNat.Nat.eqb_refl in H1.
      apply matchb_spec in H1. destruct H1; mydestr; auto.
      invclear H0; auto. invclear H1. invclear H0. invclear H1.
    + apply Nat.eqb_neq in n. invclear H. invclear H0. invclear H1. invclear H7. rewrite n in H.
      invclear H. invclear H0. invclear H.
Qed.

Lemma mk_term_meet_nat_step: forall e1 e2,
    [] ⊢t e1 ⋮t TNat -> [] ⊢t e2 ⋮t TNat ->
    (forall (v: value), e1 ↪* v /\ e2 ↪* v <-> (e1 ⊗nat e2) ↪* v).
Proof.
  split; intros; mydestr. repeat split; step_solver1.
  - assert ([] ⊢t v ⋮v TNat). eapply multi_preservation_value in H; eauto.
    apply empty_basic_typing_nat_value_exists in H3.
    apply multistep_trans with (v ⊗nat e2). { unfold mk_term_meet_nat. apply multistep_lete; auto; step_solver1. }
    apply multistep_trans with (tlete e2 (tletbiop op_eq (vbvar 0) v (tmatchb (vbvar 0) (vbvar 1) terr))).
    { unfold mk_term_meet_nat. econstructor.
      instantiate (1:= (tlete e2 (tletbiop op_eq (vbvar 0) (vbvar 1) (tmatchb (vbvar 0) (vbvar 1) terr))) ^t^ v).
      step_solver1. simpl.
      rewrite open_rec_lc_tm; step_solver1.
      rewrite open_rec_lc_value; step_solver1.
    }
    apply multistep_trans with (tlete v (tletbiop op_eq (vbvar 0) v (tmatchb (vbvar 0) (vbvar 1) terr))).
    { unfold mk_term_meet_nat. apply multistep_lete; auto; step_solver1.
      rewrite open_rec_lc_value; step_solver1.
    }
    econstructor. instantiate (1:=(tletbiop op_eq (vbvar 0) v (tmatchb (vbvar 0) (vbvar 1) terr)) ^t^ v).
    { step_solver1. rewrite open_rec_lc_value; step_solver1. }
    simpl. rewrite open_rec_lc_value; step_solver1.
    destruct H3; subst. rewrite <- meet_nat_condition_spec. split; auto.
  - unfold mk_term_meet_nat in H1.
    repeat
    match goal with
    | [H: tlete _ _ ↪* _ |- _] => rewrite lete_step_spec in H; mydestr
    | [H: ( _ ^t^ _ ) ↪* _ |- _] => simpl in H; rewrite open_rec_lc_tm in H; step_solver1; try basic_typing_solver2
    | [H: _ ⊢t ?e ⋮t _, H': ?e ↪* _  |- _] =>
        eapply multi_preservation_value in H; eauto; apply empty_basic_typing_nat_value_exists in H; destruct H; subst
    end.
    simpl in H5. rewrite <- meet_nat_condition_spec in H5. mydestr; subst. split; auto.
Qed.
(* basic typing *)

Lemma mk_app_typable: forall e1 e2 Γ T1 T2,
    Γ ⊢t e1 ⋮t T1 ⤍ T2 -> Γ ⊢t e2 ⋮t T1 -> Γ ⊢t (mk_app e1 e2) ⋮t T2.
Proof.
  intros.
  auto_exists_L; intros; simpl; rewrite open_rec_lc_tm; try op_solver.
  econstructor; eauto; try op_solver.
  - auto_exists_L_intros.
    eapply T_LetApp with (T1 := T1) (Tx := T2).
    basic_typing_vfavr_solver. basic_typing_vfavr_solver.
    auto_exists_L_intros.
    basic_typing_vfavr_solver.
Qed.

Lemma mk_bool_gen_typable: forall Γ, ok Γ -> Γ ⊢t (bool-gen) ⋮t TBool.
Proof.
  intros. unfold mk_bool_gen.
  auto_exists_L; simpl; intros.
  econstructor; eauto; simpl. { basic_typing_vfavr_solver. } auto_exists_L_intros.
  basic_typing_vfavr_solver.
Qed.

Lemma mk_nat_gen_typable: forall Γ, ok Γ -> Γ ⊢t (nat-gen) ⋮t TNat.
Proof.
  intros. unfold mk_nat_gen.
  auto_exists_L; simpl; intros.
  econstructor; eauto; simpl. { basic_typing_vfavr_solver. }
Qed.

Global Hint Resolve mk_bool_gen_typable: core.
Global Hint Resolve mk_nat_gen_typable: core.

Lemma mk_non_deter_choice_typable: forall e1 e2 Γ T,
    Γ ⊢t e1 ⋮t T -> Γ ⊢t e2 ⋮t T -> Γ ⊢t (e1 ⊕ e2) ⋮t T.
Proof.
  intros. unfold mk_non_deter_choice.
  econstructor; eauto; simpl. apply mk_bool_gen_typable; basic_typing_solver2. auto_exists_L_intros.
  repeat rewrite open_rec_lc_tm by op_solver.
  econstructor; eauto; simpl. basic_typing_vfavr_solver.
  apply basic_typing_weaken_tm_pre; eauto; basic_typing_solver2.
  apply basic_typing_weaken_tm_pre; eauto; basic_typing_solver2.
Qed.
