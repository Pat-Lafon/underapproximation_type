From stdpp Require Import mapset.
From CT Require Import CoreLangProp.
From CT Require Import ListCtx.
From CT Require Import BasicTypingProp.
From CT Require Import OperationalSemantics.
From CT Require Import ErrOperationalSemanticsProp.

Import Atom.
Import CoreLang.
Import Tactics.
Import NamelessTactics.
Import ListCtx.
Import BasicTyping.
Import BasicTypingProp.
Import OperationalSemantics.
Import ErrOperationalSemantics.

Definition mk_app e1 e2 :=
  tlete e1 (tlete e2 (tletapp (vbvar 1) (vbvar 0) (vbvar 0))).

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

Lemma mk_app_step: forall e1 e1' e2,
    lc e2 ->
    e1 ↪ e1' -> mk_app e1 e2 ↪ mk_app e1' e2.
Proof.
  unfold mk_app; intros.
  econstructor; auto. apply mk_app_body; auto.
Qed.

(* The logical relation only works for the halting terms *)

Definition halt (e: tm) := exists (v: value), e ↪* v.

Lemma op_trans_halt: forall (e e': tm), e ↪ e' -> halt e' -> halt e.
Proof.
  intros. destruct H0. exists x. eapply multistep_step; eauto.
Qed.

Fixpoint basicR (T: ty) (e: tm) : Prop :=
  [] ⊢t e ⋮t T /\ halt e /\
    match T with
    | TBase _ => True
    | T1 ⤍ T2 => forall e1, basicR T1 e1 -> basicR T2 (mk_app e e1)
    end.

Lemma basicR_typable_empty: forall T e, basicR T e -> [] ⊢t e ⋮t T.
Proof.
  intros.
  induction T; destruct H; auto.
Qed.

Lemma basicR_halt: forall T e, basicR T e -> halt e.
Proof.
  intros.
  induction T; simpl in H; repeat destruct_hyp_conj; auto.
Qed.

Ltac op_solver1 :=
  op_simpl;
  auto;
  repeat match goal with
    | [H: halt ?e', H': ?e ↪ ?e' |- halt ?e ] => eapply op_trans_halt; eauto
    | [H: _ ⊢t ?e ⋮t _ |- lc ?e ] => apply basic_typing_regular_tm in H; destruct H; auto
    | [H: basicR _ ?e |- lc ?e ] => apply basicR_typable_empty in H; auto
    | [H: basicR _ ?e |- halt ?e ] => apply basicR_halt in H; auto
    | [H: basicR _ ?e |- [] ⊢t ?e ⋮t _ ] => apply basicR_typable_empty in H; eauto
    | [H: _ ↪ ?e |- lc ?e] => apply multi_step_regular2 in H; auto
    | [H: ?Γ ⊢t ?e ⋮t ?T |- (?Γ ++ _) ⊢t ?e ⋮t _] => apply basic_typing_weaken_tm_pre; eauto
    | [H: ?Γ ⊢t _ ⋮t _ |- ok _ ] => apply basic_typing_regular_tm in H; destruct H
    end; listctx_set_solver.

Lemma mk_app_typable: forall e1 e2 Γ T1 T2,
    Γ ⊢t e1 ⋮t T1 ⤍ T2 -> Γ ⊢t e2 ⋮t T1 -> Γ ⊢t (mk_app e1 e2) ⋮t T2.
Proof.
  intros.
  auto_exists_L; intros; simpl; rewrite open_rec_lc_tm; try op_solver1.
  econstructor; eauto; try op_solver1.
  - auto_exists_L_intros.
    eapply T_LetApp with (T1 := T1) (Tx := T2).
    basic_typing_vfavr_solver. basic_typing_vfavr_solver.
    auto_exists_L_intros.
    basic_typing_vfavr_solver.
Qed.

(* Lemma step_preserves_basicR : ∀ T e e', (e ↪ e') → basicR T e → basicR T e'. *)
(* Proof. *)
(*   induction T; simpl; intros; repeat destruct_hyp_conj; repeat split; auto; *)
(*   try (eapply preservation; eauto). *)
(*   op_solver1. *)
(*   intros. apply IHT2 with (e := (mk_app e e1)); auto. *)
(*   apply mk_app_step; op_solver1. *)
(* Qed. *)

(* Lemma multistep_preserves_basicR : ∀ T e e', (e ↪* e') → basicR T e → basicR T e'. *)
(* Proof. *)
(*   intros. induction H; auto. apply IHmultistep. eapply step_preserves_basicR; eauto. *)
(* Qed. *)

Lemma step_preserves_basicR' : ∀ T e e', [] ⊢t e ⋮t T -> (e ↪ e') → basicR T e' → basicR T e.
Proof.
  induction T; simpl; intros; repeat destruct_hyp_conj; repeat split; auto; try op_solver1.
  intros. apply IHT2 with (e' := (mk_app e' e1)); auto.
  - unfold mk_app. eapply mk_app_typable; eauto. apply basicR_typable_empty; auto.
  - econstructor; auto. apply basicR_typable_empty in H4. basic_typing_solver2.
Qed.

Lemma multistep_preserves_basicR' : ∀ T e e', (e ↪* e') → [] ⊢t e ⋮t T -> basicR T e' → basicR T e.
Proof.
  intros T e e' H.
  induction H; intros; auto.
  eapply step_preserves_basicR'; eauto. apply IHmultistep; auto. eapply preservation; eauto.
Qed.

(* Instantiations *)

Definition env := listctx value.
Fixpoint tm_msubst (ss:env) (t:tm) : tm :=
  match ss with
  | nil => t
  | ((x,s)::ss') => tm_msubst ss' ({x := s}t t)
  end.

Fixpoint value_msubst (ss:env) (t:value) : value :=
  match ss with
  | nil => t
  | ((x,s)::ss') => value_msubst ss' ({x := s}v t)
  end.

Inductive instantiation : (listctx ty) -> env -> Prop :=
| instantiation_nil: instantiation [] []
| instantiation_cons: forall x T (v: value) c e,
    basicR T v ->
    x ∉ ctxdom c ->
    instantiation c e ->
    instantiation ((x, T) :: c) ((x, v) :: e).

Lemma instantiation_regular_ok: forall Γt Γv, instantiation Γt Γv -> ctxdom Γt = ctxdom Γv /\ ok Γt /\ ok Γv.
Proof.
  intros. induction H; repeat destruct_hyp_conj; repeat split; intros; auto;
    try  listctx_set_solver;
  try (simpl; rewrite H2; auto; try listctx_set_solver).
  - rewrite ok_pre_destruct; split; auto. rewrite <- H2; auto.
Qed.

Lemma instantiation_regular_lc: forall Γt Γv, instantiation Γt Γv -> (forall x v, ctxfind Γv x = Some v -> lc v).
Proof.
  intros. assert (ok Γv). apply instantiation_regular_ok in H. repeat destruct_hyp_conj; auto.
  induction H; simpl; auto.
  - simpl in H0. listctx_set_solver.
  - simpl in H0. repeat var_dec_solver. apply basicR_typable_empty in H. op_simpl. listctx_set_solver.
Qed.

Lemma instantiation_regular_closed: forall Γt Γv, instantiation Γt Γv -> (forall x v, ctxfind Γv x = Some v -> closed_value v).
Proof.
  unfold closed_value.
  intros. assert (ok Γv). apply instantiation_regular_ok in H. repeat destruct_hyp_conj; auto.
  induction H; simpl; auto.
  - simpl in H0. listctx_set_solver.
  - simpl in H0. repeat var_dec_solver. apply basicR_typable_empty in H. op_simpl.
    apply basic_typing_contains_fv_value in H6. simpl in H6. my_set_solver.
    apply IHinstantiation; auto.
    listctx_set_solver.
Qed.

Lemma instantiation_regular: forall Γt Γv, instantiation Γt Γv ->
                                      (forall x v, ctxfind Γv x = Some v -> lc v) /\
                                        (forall x v, ctxfind Γv x = Some v -> closed_value v) /\
                                        ctxdom Γt = ctxdom Γv /\ ok Γt /\ ok Γv.
Proof.
  intros. split.
  eapply instantiation_regular_lc; eauto.
  split.
  eapply instantiation_regular_closed; eauto.
  apply instantiation_regular_ok; auto.
Qed.

Lemma tm_msubst_closed: ∀ e, closed_tm e -> (forall ss, tm_msubst ss e = e).
Proof.
  unfold closed_tm.
  intros.
  induction ss; simpl; auto.
  destruct a. rewrite subst_fresh_tm; auto. fast_set_solver!!.
Qed.

Lemma value_msubst_closed: ∀ e, closed_value e -> (forall ss, value_msubst ss e = e).
Proof.
  unfold closed_value.
  intros.
  induction ss; simpl; auto.
  destruct a. rewrite subst_fresh_value; auto. fast_set_solver!!.
Qed.

Lemma instantiation_R : ∀ c e,
    instantiation c e →
    ∀ x t T,
      ctxfind c x = Some T →
      ctxfind e x = Some t → basicR T t.
Proof.
  intros c e V. induction V; simpl ; intros.
  - inversion H.
  - repeat var_dec_solver.
    eapply IHV; eauto.
Qed.

Ltac basic_typing_solver2 :=
  (repeat match goal with
     | [H: [] ⊢t ?e ⋮t _ |- _ ⊢t ?e ⋮t _ ] => eapply basic_typing_weaken_tm_pre in H; eauto; listctx_set_solver
     | [H: [] ⊢t ?e ⋮v _ |- _ ⊢t ?e ⋮v _ ] => eapply basic_typing_weaken_value_pre in H; eauto; listctx_set_solver
     | [H: _ ⊢t (tvalue _) ⋮t _ |- _ ] => inversion H; subst; clear H
     | [|- _ ⊢t (vconst _) ⋮v _ ] => constructor; listctx_set_solver
     | [|- _ ⊢t (vfvar _) ⋮v _ ] => constructor; listctx_set_solver
     | [|- _ ⊢t terr ⋮t _ ] => constructor; listctx_set_solver
     | [H: halt ?e', H': ?e ↪ ?e' |- halt ?e ] => eapply op_trans_halt; eauto
     | [H: basicR _ ?e |- halt ?e ] => apply basicR_halt in H; auto
     | [H: basicR _ (tvalue ?v) |- closed_value ?v] => apply basicR_typable_empty in H
     | [H: basicR _ ?e |- closed_tm ?e] => apply basicR_typable_empty in H
     | [H: _ ⊢t ?v ⋮v _ |- closed_value ?v] =>
         apply basic_typing_contains_fv_value in H; simpl in H; fast_set_solver
     | [H: _ ⊢t (tvalue ?v) ⋮t _ |- closed_value ?v] =>
         apply basic_typing_contains_fv_tm in H; simpl in H; fast_set_solver
     | [H: _ ⊢t ?v ⋮t _ |- closed_tm ?v] =>
         apply basic_typing_contains_fv_tm in H; simpl in H; fast_set_solver
     | [H: basicR ?T (tvalue ?v) |- (_ ⊢t ?v ⋮v ?T)] => apply basicR_typable_empty in H
     | [H: basicR ?T ?e |- (_ ⊢t ?e ⋮t ?T)] => apply basicR_typable_empty in H
     end) || basic_typing_solver1.

Lemma instantiation_R_exists : ∀ c e,
    instantiation c e →
    ∀ x T,
      ctxfind c x = Some T →
      (exists t, ctxfind e x = Some t /\ basicR T t /\ closed_value t).
Proof.
  intros c e V. induction V; simpl ; intros.
  - inversion H.
  - repeat var_dec_solver. exists v. split; auto. split; auto. basic_typing_solver2.
Qed.

Lemma msubst_var: ∀ ss (x: atom) (v: value), closed_value v -> ctxfind ss x = Some v -> value_msubst ss x = v.
Proof.
  induction ss; simpl; intros.
  - inversion H0.
  - destruct a. repeat var_dec_solver. rewrite value_msubst_closed; auto.
Qed.

Lemma msubst_var_none: ∀ ss (x: atom), ctxfind ss x = None -> value_msubst ss x = x.
Proof.
  induction ss; simpl; intros; auto.
  - destruct a. repeat var_dec_solver.
Qed.

Lemma msubst_vlam: ∀ ss Tx e, value_msubst ss (vlam Tx e) = vlam Tx (tm_msubst ss e).
Proof.
  induction ss; simpl; intros; auto; auto_destruct_pair.
  eapply IHss.
Qed.

Lemma msubst_open_tm: ∀ Γv e k (x: atom),
  ok Γv ->
  (forall x v, ctxfind Γv x = Some v -> closed_value v /\ lc v) ->
  x ∉ ctxdom Γv ->
  {k ~t> x} (tm_msubst Γv e) = tm_msubst Γv ({k ~t> x} e).
Proof.
  induction Γv; simpl; intros; auto.
  - auto_destruct_pair.
    assert (closed_value v /\ lc v). eapply (H0 a v); eauto. repeat var_dec_solver.
    rewrite subst_open_var_tm.
    rewrite IHΓv; auto. listctx_set_solver.
    intros. specialize (H0 x0 v0). repeat var_dec_solver. apply ctxfind_some_implies_in_dom in H3. rewrite ok_pre_destruct in H. destruct H. fast_set_solver. fast_set_solver. fast_set_solver. destruct H2; auto.
Qed.

Lemma msubst_open_value: ∀ Γv e k (x: atom),
  ok Γv ->
  (forall x v, ctxfind Γv x = Some v -> closed_value v /\ lc v) ->
  x ∉ ctxdom Γv ->
  {k ~v> x} (value_msubst Γv e) = value_msubst Γv ({k ~v> x} e).
Proof.
  induction Γv; simpl; intros; auto.
  - auto_destruct_pair.
    assert (closed_value v /\ lc v). eapply (H0 a v); eauto. repeat var_dec_solver.
    rewrite subst_open_var_value.
    rewrite IHΓv; auto. listctx_set_solver.
    intros. specialize (H0 x0 v0). repeat var_dec_solver. apply ctxfind_some_implies_in_dom in H3. rewrite ok_pre_destruct in H. destruct H. fast_set_solver. fast_set_solver. fast_set_solver. destruct H2; auto.
Qed.

Ltac instantiation_regular_solver :=
  match goal with
  | [H: instantiation ?a ?b |- _ ∉ _ ] =>
      apply instantiation_regular_ok in H; repeat destruct_hyp_conj; auto; listctx_set_solver
  | [H: instantiation ?a ?b |- ok _ ] =>
      apply instantiation_regular_ok in H; repeat destruct_hyp_conj; auto; listctx_set_solver
  | [H: instantiation ?a ?b |- forall x v, ctxfind ?b x = Some v -> _ ] =>
      apply instantiation_regular in H; repeat destruct_hyp_conj; eauto; listctx_set_solver
  end.

Lemma msubst_vfix: ∀ ss Tx (e: value), value_msubst ss (vfix Tx e) = vfix Tx (value_msubst ss e).
Proof.
  induction ss; simpl; intros; auto; auto_destruct_pair.
  eapply IHss.
Qed.

Lemma msubst_value: ∀ ss (v: value), tm_msubst ss v = tvalue (value_msubst ss v).
Proof.
  induction ss; simpl; intros; auto; auto_destruct_pair.
  eapply IHss.
Qed.

Lemma msubst_tlete: ∀ ss e1 e2, tm_msubst ss (tlete e1 e2) = tlete (tm_msubst ss e1) (tm_msubst ss e2).
Proof.
  induction ss; simpl; intros; auto; auto_destruct_pair.
  eapply IHss.
Qed.

Lemma msubst_tletbiop: ∀ ss op v1 v2 e,
    tm_msubst ss (tletbiop op v1 v2 e) = tletbiop op (value_msubst ss v1) (value_msubst ss v2) (tm_msubst ss e).
Proof.
  induction ss; simpl; intros; auto; auto_destruct_pair.
  eapply IHss.
Qed.

Lemma msubst_tletapp: ∀ ss v1 v2 e,
    tm_msubst ss (tletapp v1 v2 e) = tletapp (value_msubst ss v1) (value_msubst ss v2) (tm_msubst ss e).
Proof.
  induction ss; simpl; intros; auto; auto_destruct_pair.
  eapply IHss.
Qed.

Lemma msubst_tmatchb: ∀ ss v e1 e2,
    tm_msubst ss (tmatchb v e1 e2) = tmatchb (value_msubst ss v) (tm_msubst ss e1) (tm_msubst ss e2).
Proof.
  induction ss; simpl; intros; auto; auto_destruct_pair.
  eapply IHss.
Qed.

Lemma closed_has_type_under_empty_value: forall Γ (v: value) T, Γ ⊢t v ⋮v T -> closed_value v -> [] ⊢t v ⋮v T.
Proof.
  apply (rev_ind (fun Γ => forall (v: value) T, Γ ⊢t v ⋮v T -> closed_value v -> [] ⊢t v ⋮v T)); intros; auto.
  auto_destruct_pair.
  destruct (tricky_closed_value_exists t) as (vv & Hvv).
  apply (basic_typing_subst_value_pre _ a vv) in H0. rewrite subst_fresh_value in H0. auto. my_set_solver.
  apply Hvv. op_simpl.
Qed.

Lemma closed_has_type_under_empty_tm: forall Γ (v: tm) T, Γ ⊢t v ⋮t T -> closed_tm v -> [] ⊢t v ⋮t T.
Proof.
  apply (rev_ind (fun Γ => forall (v: tm) T, Γ ⊢t v ⋮t T -> closed_tm v -> [] ⊢t v ⋮t T)); intros; auto.
  auto_destruct_pair.
  destruct (tricky_closed_value_exists t) as (vv & Hvv).
  apply (basic_typing_subst_tm_pre _ a vv) in H0. rewrite subst_fresh_tm in H0. auto. my_set_solver.
  apply Hvv. op_simpl.
Qed.

Lemma closed_has_type_under_any_ctx_value: forall Γ (v: value) T, Γ ⊢t v ⋮v T -> closed_value v -> (forall Γ', ok Γ' -> Γ' ⊢t v ⋮v T).
Proof.
  intros. apply closed_has_type_under_empty_value in H; auto. basic_typing_solver2.
Qed.

Lemma closed_has_type_under_any_ctx_tm: forall Γ (v: tm) T, Γ ⊢t v ⋮t T -> closed_tm v -> (forall Γ', ok Γ' -> Γ' ⊢t v ⋮t T).
Proof.
  intros. apply closed_has_type_under_empty_tm in H; auto. basic_typing_solver2.
Qed.

Ltac msubst_preserves_typing_tac :=
  match goal with
  | [a: atom |- _ ] => repeat specialize_with a
  end;
  repeat match goal with
    | [|- _ ⊢t ((tm_msubst _ _) ^t^ _) ⋮t _ ] =>
        rewrite msubst_open_tm; try instantiation_regular_solver; try fast_set_solver
    | [|- _ ⊢t ((value_msubst _ _) ^v^ _) ⋮v _ ] =>
        rewrite msubst_open_value; try instantiation_regular_solver; try fast_set_solver
    | [H: context [_ ⊢t (tm_msubst _ _) ⋮t ?T] |- _ ⊢t _ ⋮t ?T] =>
        eapply H; eauto; try (rewrite app_assoc; auto)
    end.

Ltac msubst_preserves_typing_tac2 :=
  (repeat match goal with
     | [|- closed_value _] => unfold closed_value; intros; listctx_set_solver
     | [ |- _ ⊢t mk_app _ _ ⋮t ?T ] => eapply mk_app_typable; eauto
     | [ |- _ ⊢t (value_msubst _ _) ⋮v ?T ] => rewrite value_msubst_closed
     | [ |- _ ⊢t (tvalue (value_msubst _ _)) ⋮t ?T ] => rewrite value_msubst_closed
     end; basic_typing_solver2).

Lemma msubst_preserves_typing_tm_aux: ∀ Γ e T,
    Γ ⊢t e ⋮t T -> (forall Γt Γt' Γv, Γ = Γt ++ Γt' -> instantiation Γt Γv -> Γt' ⊢t (tm_msubst Γv e) ⋮t T).
Proof.
  apply (tm_has_type_mutual_rec
           (fun Γ v T P => forall Γt Γt' Γv, Γ = Γt ++ Γt' -> instantiation Γt Γv -> Γt' ⊢t (value_msubst Γv v) ⋮v T)
           (fun Γ e T P => forall Γt Γt' Γv, Γ = Γt ++ Γt' -> instantiation Γt Γv -> Γt' ⊢t (tm_msubst Γv e) ⋮t T)
        ); simpl; intros; subst; listctx_set_simpl; repeat destruct_hyp_conj.
  - msubst_preserves_typing_tac2.
  - assert (forall x v, ctxfind Γv x = Some v -> closed_value v). eapply instantiation_regular_closed; eauto.
    rewrite ctxfind_app in e; auto. destruct e.
    + eapply instantiation_R_exists in H0; eauto. destruct H0 as (v & Hv1 & Hv2 & Hv3).
      erewrite msubst_var; eauto. basic_typing_solver2.
    + rewrite msubst_var_none; basic_typing_solver2.
      apply instantiation_regular_ok in H0. repeat destruct_hyp_conj. rewrite <- H0.
      apply ctxfind_app_exclude in o. my_set_solver.
  - rewrite msubst_vlam. auto_exists_L; simpl; intros.
    msubst_preserves_typing_tac.
  - rewrite msubst_vfix. rewrite msubst_vlam. auto_exists_L; simpl; intros. repeat specialize_with f.
    msubst_preserves_typing_tac.
    specialize (H Γt (Γt' ++ [(f, Tx ⤍ T)]) Γv).
    rewrite msubst_vlam in H.
    rewrite msubst_open_tm; try instantiation_regular_solver. apply H; auto.
    rewrite app_assoc; auto.
  - rewrite tm_msubst_closed. basic_typing_solver2. unfold closed_tm; listctx_set_solver.
  - rewrite msubst_value. eauto.
  - rewrite msubst_tlete. auto_exists_L; simpl; intros.
    msubst_preserves_typing_tac.
  - rewrite msubst_tletbiop. auto_exists_L; simpl; intros.
    msubst_preserves_typing_tac.
  - rewrite msubst_tletapp. auto_exists_L; simpl; intros.
    msubst_preserves_typing_tac.
  - rewrite msubst_tmatchb. auto_exists_L; simpl; intros.
Qed.

Lemma msubst_preserves_typing_tm: ∀ Γt Γv, instantiation Γt Γv → (forall e T , Γt ⊢t e ⋮t T -> [] ⊢t (tm_msubst Γv e) ⋮t T).
Proof.
  intros. eapply msubst_preserves_typing_tm_aux; eauto. op_simpl.
Qed.

Lemma msubst_preserves_typing_value_aux: ∀ Γ e T,
    Γ ⊢t e ⋮v T -> (forall Γt Γt' Γv, Γ = Γt ++ Γt' -> instantiation Γt Γv -> Γt' ⊢t (value_msubst Γv e) ⋮v T).
Proof.
  apply (value_has_type_mutual_rec
           (fun Γ v T P => forall Γt Γt' Γv, Γ = Γt ++ Γt' -> instantiation Γt Γv -> Γt' ⊢t (value_msubst Γv v) ⋮v T)
           (fun Γ e T P => forall Γt Γt' Γv, Γ = Γt ++ Γt' -> instantiation Γt Γv -> Γt' ⊢t (tm_msubst Γv e) ⋮t T)
        ); simpl; intros; subst; listctx_set_simpl; repeat destruct_hyp_conj.
  - msubst_preserves_typing_tac2.
  - assert (forall x v, ctxfind Γv x = Some v -> closed_value v). eapply instantiation_regular_closed; eauto.
    rewrite ctxfind_app in e; auto. destruct e.
    + eapply instantiation_R_exists in H0; eauto. destruct H0 as (v & Hv1 & Hv2 & Hv3).
      erewrite msubst_var; eauto. basic_typing_solver2.
    + rewrite msubst_var_none; basic_typing_solver2.
      apply instantiation_regular_ok in H0. repeat destruct_hyp_conj. rewrite <- H0.
      apply ctxfind_app_exclude in o. my_set_solver.
  - rewrite msubst_vlam. auto_exists_L; simpl; intros.
    msubst_preserves_typing_tac.
  - rewrite msubst_vfix. rewrite msubst_vlam. auto_exists_L; simpl; intros. repeat specialize_with f.
    msubst_preserves_typing_tac.
    specialize (H Γt (Γt' ++ [(f, Tx ⤍ T)]) Γv).
    rewrite msubst_vlam in H.
    rewrite msubst_open_tm; try instantiation_regular_solver. apply H; auto.
    rewrite app_assoc; auto.
  - rewrite tm_msubst_closed. basic_typing_solver2. unfold closed_tm; listctx_set_solver.
  - rewrite msubst_value. eauto.
  - rewrite msubst_tlete. auto_exists_L; simpl; intros.
    msubst_preserves_typing_tac.
  - rewrite msubst_tletbiop. auto_exists_L; simpl; intros.
    msubst_preserves_typing_tac.
  - rewrite msubst_tletapp. auto_exists_L; simpl; intros.
    msubst_preserves_typing_tac.
  - rewrite msubst_tmatchb. auto_exists_L; simpl; intros.
Qed.

Lemma msubst_preserves_typing_value: ∀ Γt Γv, instantiation Γt Γv → (forall e T , Γt ⊢t e ⋮v T -> [] ⊢t (value_msubst Γv e) ⋮v T).
Proof.
  intros. eapply msubst_preserves_typing_value_aux; eauto. op_simpl.
Qed.

Lemma msubst_terr: ∀ ss, tm_msubst ss terr = terr.
Proof.
  induction ss; simpl; intros; auto.
  - destruct a. auto.
Qed.

Inductive ty_arrow_argR: ty -> ty -> ty -> Prop :=
| ty_arrow_argR_base: forall Tx (B: base_ty), ty_arrow_argR (Tx ⤍ B) Tx B
| ty_arrow_argR_arrow: forall Tx T1 T2,
    (forall T', ty_arrow_argR (Tx ⤍ T') Tx T') ->
    ty_arrow_argR (Tx ⤍ T1 ⤍ T2) Tx (T1 ⤍ T2).

(* Lemma ty_arrow_argR_eq: forall T' (Tx: base_ty), ty_arrow_argR (Tx ⤍ T') Tx T'. *)
(* Proof. *)
(*   induction T'; intros. constructor. *)
(*   constructor. intros. *)
(*   induction T2; intros; auto. *)
(*   - generalize dependent b. induction T'. intros. constructor. *)
(*     intros. constructor. intros. *)

(*   constructor. *)
(*   constructor. *)

(* Lemma ty_arrow_argR_simp1: forall Tx, (forall (T': base_ty), ty_arrow_argR (Tx ⤍ T') Tx T'). *)
(* Proof. *)
(*   induction Tx; intros; auto. constructor. constructor. intros. *)
(*   specialize (IHTx1 T'). inversion IHTx1; subst. constructor. *)


(* Lemma ty_arrow_argR_simp: forall T3 T1 T2, ty_arrow_argR T1 T2 T3 <-> (T1 = (T2 ⤍ T3)). *)
(* Proof. *)
(*   induction T1; split; intros. *)
(*   - induction H; auto. *)
(*   - inversion H. *)
(*   - induction H; auto. *)
(*   - inversion H; subst; clear H. rewrite IHT1_2. *)
(*     generalize dependent T2. *)

(* Lemma ty_arrow_argR_simp: forall T3 T1 T2, ty_arrow_argR T1 T2 T3 <-> (T1 = (T2 ⤍ T3)). *)
(* Proof. *)
(*   induction T1; split; intros. *)
(*   - induction H; auto. *)
(*   - subst. constructor. *)
(*   - induction H; auto. *)
(*   - subst. constructor. intros. *)
(*     destruct T'. constructor. constructor. *)
(*   split. *)
(*   - intros. induction H; auto. *)
(*   - intros. subst. *)
(*     generalize dependent T2. *)
(*     induction T3; intros. *)
(*     + constructor. *)
(*     + constructor. intros.  *)
(*   Admitted. *)

Lemma basicR_app_aux: forall Tf Tx T,
    ty_arrow_argR Tf Tx T -> forall e_x e_f, basicR Tx e_x -> basicR Tf e_f -> basicR T (mk_app e_f e_x).
Proof.
  intros Tx Tf T H.
Admitted.

Lemma basicR_app: forall Tx e_x T e_f, basicR (Tx ⤍ T) e_f -> basicR Tx e_x -> basicR T (mk_app e_f e_x).
Proof.
  induction Tx; intros.
  - destruct T. admit. split. admit. intros.
Admitted.


(* Lemma basicR_terr_aux: forall e1 T1 T2, basicR T1 e1 -> basicR T2 (mk_app terr e1). *)
(* Proof. *)
(*   intros. destruct T2. split; auto. admit. *)
(*   split. admit. intros. *)
(*   induction e1 *)
(*   intros. *)
(*   constructor. auto. intros. *)
(*   induction T1; simpl; split; intros; repeat destruct_hyp_conj; auto. *)
(*   - admit. *)

(* Lemma basicR_terr: forall T, basicR T terr. *)
(* Proof. *)
(*   induction T; simpl; split; intros; auto. *)

(* Lemma basic_R_perservation: forall (e e': tm) T, basicR e T -> *)

Lemma msubst_R_tm: ∀ Γt Γv, instantiation Γt Γv → (forall e T, Γt ⊢t e ⋮t T -> halt e -> basicR T (tm_msubst Γv e)).
Proof.
  intros. generalize dependent Γv. generalize dependent H1.
  apply (tm_has_type_mutual_rec
           (fun Γt v T P => halt e -> ∀ Γv : env, instantiation Γt Γv → basicR T (value_msubst Γv v))
           (fun Γt e T P => halt e -> ∀ Γv : env, instantiation Γt Γv → basicR T (tm_msubst Γv e))
        ); simpl; intros; subst; listctx_set_simpl;
    repeat split; intros; repeat destruct_hyp_conj; auto;
    repeat match goal with
      | [|- [] ⊢t mk_app _ _ ⋮t ?T ] => eapply mk_app_typable; eauto
      | [|- _ ⊢t _ ⋮t _] => (eapply msubst_preserves_typing_tm; eauto) || (constructor; auto; eapply msubst_preserves_typing_value; eauto)
      | [|- _ ⊢t _ ⋮v _] => try (eapply msubst_preserves_typing_value; eauto)
      end.
  - rewrite value_msubst_closed. admit. basic_typing_solver2.
  - eapply instantiation_R_exists in e0; eauto. repeat destruct_hyp_conj. erewrite msubst_var; eauto.
  - rewrite msubst_vlam. admit.
  - rewrite msubst_vlam.
    assert (halt e1). basic_typing_solver2. destruct H4 as (v1 & Hv1).
    auto_pose_fv x. repeat specialize_with x.
    specialize (H (Γv ++ [(x, v1)])).
    apply multistep_preserves_basicR' with ((tm_msubst Γv e0) ^t^ v1). admit.
    admit.
    admit.
  - rewrite msubst_vfix. admit.
  - rewrite msubst_vfix. destruct H4 as (v1 & Hv1).
    auto_pose_fv x. repeat specialize_with x.
    specialize (H (Γv ++ [(x, (vfix (Tx ⤍ T0) (value_msubst Γv (vlam Tx e0))))])). admit.
  - admit

  - rewrite msubst_terr. 
    apply basicR_typable_empty in Hv2. 
    
  - unfold mk_app.
  (repeat match goal with
      | [ |- [] ⊢t mk_app _ _ ⋮t ?T ] => eapply mk_app_typable; eauto
      | [ |- [] ⊢t (tvalue (value_msubst _ _)) ⋮t ?T ] =>
          rewrite value_msubst_closed; repeat constructor; auto; unfold closed_value; intros; listctx_set_solver
      end).
  eapply mk_app_typable; eauto. constructor; auto.
  eapply msubst_preserves_typing_value.
  admit.
  admit.
  admit.
    (repeat match goal with
      | [ |- [] ⊢t mk_app _ _ ⋮t ?T ] => eapply mk_app_typable; eauto
      | [ |- [] ⊢t (tvalue (value_msubst _ _)) ⋮t ?T ] =>
          rewrite value_msubst_closed; repeat constructor; auto; unfold closed_value; intros; listctx_set_solver
      end).

  admit.

  Lemma msubst_preserves_typing : ∀ Γt Γv ,
      instantiation Γt Γv →
      (forall e, Γt ⊢t e ⋮t T -> basic T (tm_msubst Γv e)).
    ∀ Gamma t S, (mupdate Γt c) ⊢ t \in S →

                                       Γ ⊢ t value_msubst Γv v ⋮t T

    Proof.

  assert ([] ⊢t vlam Tx (tm_msubst Γv e0) ⋮t Tx ⤍ T0).
  auto_pose_fv x; assert (x ∉ L) as Htmp by fast_set_solver; specialize (H x Htmp); try clear Htmp.
  specialize (H Γv). constructor. econstructor. simpl.
  admit. admit.
  admit.
  admit.
  admit.
  rewrite tm_msubst_closed; simpl; auto. admit. unfold closed_tm; intros; listctx_set_solver.
  admit.
  admit.
  admit.
  admit.
  admit.

  econstructor. econstructor. auto_exists_L_intros.
  eapply mk_app_typable; eauto.
  rewrite value_msubst_closed. repeat econstructor; auto. listctx_set_solver.
  repeat match goal with
         | [ |- [] ⊢t mk_app _ _ ⋮t ?T ] => eapply mk_app_typable; eauto
         | [ |- [] ⊢t (tvalue (value_msubst _ _)) ⋮t ?T ] =>
             rewrite value_msubst_closed; repeat constructor; auto; unfold closed_value; intros; listctx_set_solver
         end.
  try (rewrite value_msubst_closed; repeat constructor; auto; unfold closed_value; intros; listctx_set_solver).
  try (rewrite value_msubst_closed; repeat constructor; auto; unfold closed_value; intros; listctx_set_solver).
  eapply mk_app_typable; eauto.
  try (rewrite value_msubst_closed; repeat constructor; auto; unfold closed_value; intros; listctx_set_solver).
  eapply mk_app_typable; eauto.
  eapply mk_app_typable; eauto.
  try (rewrite value_msubst_closed; repeat constructor; auto; unfold closed_value; intros; listctx_set_solver).
  rewrite tm_msubst_closed. repeat constructor; auto.
  induction H0; simpl; intros.
  - 

Lemma msubst_preserves_typing : ∀ Γt Γv ,
     instantiation Γt Γv →
     (forall e, Γt ⊢t e ⋮t T -> basic T (tm_msubst Γv e)).
     ∀ Gamma t S, (mupdate Γt c) ⊢ t \in S →
     Gamma ⊢ { (msubst Γv t) } \in S.
Proof.
    intros c e H. induction H; intros.
    simpl in H. simpl. auto.
    simpl in H2. simpl.
    apply IHinstantiation.
    eapply substitution_preserves_typing; eauto.
    apply (R_typable_empty H0).
Qed.
