Set Warnings "-notation-overridden,-parsing".

From PLF Require Import Maps.
From PLF Require Import CoreLangSimp.
From PLF Require Import NormalTypeSystemSimp.
From PLF Require Import LinearContext.
From PLF Require Import RfTypeDef.
From PLF Require Import TypeClosedSimp.
From PLF Require Import TermOrdering.
From PLF Require Import DenotationSimp.
From PLF Require Import CtxErase.
From PLF Require Import DenotationAux.
From PLF Require Import TermMeet.
From PLF Require Import WellFormedSimp.
From Coq Require Import Logic.FunctionalExtensionality.
From Coq Require Import Logic.ClassicalFacts.
From Coq Require Import Lists.List.
From Coq Require Import FunInd.
From Coq Require Import Recdef.

Import CoreLangSimp.
Import NormalTypeSystemSimp.
Import LinearContext.
Import Nstate.
Import NoDup.
Import RfTypeDef.
Import TypeClosedSimp.
Import DenotationSimp.
Import CtxErase.
Import DenotationAux.
Import TermMeet.
Import WellFormedSimp.
Import ListNotations.

(* aux denotation of over *)

Global Hint Constructors well_formed_type: core.

Lemma tmR_in_ctx_preserve_arrarr: forall Gamma st x (t1 t2: underty) e (tau: underty),
    tmR_in_ctx_aux st (Gamma <l> x :l: Uty (t1 u--> t2)) tau e ->
    tmR_in_ctx_aux st Gamma ((t1 u--> t2) u--> tau) (vlam x (u\_ (t1 u--> t2) _/) e).
Proof with eauto.
  intro Gamma.
  induction Gamma; simpl; intros st x t1 t2 e tau HD.
  - setoid_rewrite app_nil_l in HD. constructor. constructor... inversion HD; subst...
    constructor... split...
    + apply tmR_in_ctx_aux_implies_has_type in HD... simpl in HD. simpl. apply T_Value. apply T_Lam...
      (* eapply weakening... unfold includedin. intros. inversion H. *)
    + intros e_x He_xD e3 Happ. inversion Happ; subst. simpl.
      assert (tmR_in_ctx_aux st [] tau (tlete x e_x e)) as HH...
      eapply step_preserve_under_denotation... apply eta11... inversion HH; subst. inversion H1...
  - destruct a as (a & tau_a).
    assert (type_ctx_no_dup (st\_ st _/) ((a, tau_a) :: Gamma <l> x :l: (t1 u--> t2))) as Hnodup...
    inversion HD; subst.
    + constructor...
      intros c_x Hc_xD.
      eapply step_preserve_ctx_denotation. apply eta_lete_const_to_subst.
      simpl... destruct (eqb_spec a x)...
      { exfalso. eapply type_ctx_no_dup_fst_last_diff_name... }
      eapply step_preserve_ctx_denotation... apply eta_lete_const_to_subst_in_lam...
    + constructor...
      destruct H9 as (e_x_hat & He_x_hatD & HH).
      exists e_x_hat. split...
      intros e_x He_xD.
      eapply step_preserve_ctx_denotation... eapply eta_closed_term_can_captured_by_lam...
    + constructor...
      intros e_x He_xD.
      eapply step_preserve_ctx_denotation... eapply eta_closed_term_can_captured_by_lam...
    + constructor...
      intros e_x He_xD.
      eapply step_preserve_ctx_denotation... eapply eta_closed_term_can_captured_by_lam...
Qed.

(* Assume there is no dup in the context to simplify the proof. *)
Lemma tmR_in_ctx_preserve_oarr: forall Gamma st x (tau_x: overbasety) e (tau: underty),
    tmR_in_ctx_aux st (Gamma <l> x :l: Oty tau_x) tau e ->
    tmR_in_ctx_aux st Gamma (x o: tau_x o--> tau) (vlam x (o\_ tau_x _/) e).
Proof with eauto.
  intro Gamma.
  induction Gamma; simpl; intros st x tau_x e tau HD.
  - setoid_rewrite app_nil_l in HD. inversion HD; subst. constructor... constructor... constructor...
    split.
    + simpl. constructor... constructor... apply tmR_in_ctx_aux_implies_has_type in HD...
    + intros c_x Hc_xD e3 Happ. inversion Happ; subst. simpl.
      (* assert (empty \N- c_x \Tin T) as Hc_xT... eapply over_tmR_aux_has_type in Hc_xD... *)
      eapply step_preserve_under_denotation... apply eta1...
      assert (tmR_in_ctx_aux (x |-> (tvalue c_x, T); st) [] tau (tlete x c_x e)) as HH...
      inversion HH; subst. inversion H1...
  - destruct a as (a & tau_a).
    assert (type_ctx_no_dup (st\_ st _/) ((a, tau_a) :: Gamma <l> x :l: tau_x)) as Hnodup...
    inversion HD; subst.
    + constructor...
      intros c_x Hc_xD.
      eapply step_preserve_ctx_denotation. apply eta_lete_const_to_subst.
      simpl... destruct (eqb_spec a x)... { exfalso. eapply type_ctx_no_dup_fst_last_diff_name... }
      eapply step_preserve_ctx_denotation... apply eta_lete_const_to_subst_in_lam...
    (* eapply IHGamma... *)
    (* apply type_ctx_no_dup_ctx_sub with (Gamma1 := (a, Oty ({{v:T | phi}}))::nil)... *)
    + constructor...
      destruct H9 as (e_x_hat & He_x_hatD & HH).
      exists e_x_hat. split...
      intros e_x He_xD.
      (* intros c_x Hc_xE Hc_xT e_x He_xD. *)
      eapply step_preserve_ctx_denotation... eapply eta_closed_term_can_captured_by_lam...
    (* apply IHGamma... *)
    (* apply type_ctx_no_dup_ctx_sub with (Gamma1 := (a, Uty ([[v:T | phi]]))::nil)... *)
    + constructor...
      intros e_x He_xD.
      eapply step_preserve_ctx_denotation... eapply eta_closed_term_can_captured_by_lam...
    (* apply IHGamma... *)
    (* eapply type_ctx_no_dup_ctx_sub with (Gamma1 := (a, Uty (a0 o: {{v:T | phi}} o--> tau_b))::nil)... *)
    + constructor...
      intros e_x He_xD.
      eapply step_preserve_ctx_denotation... eapply eta_closed_term_can_captured_by_lam...
      (* apply IHGamma... *)
      (* eapply type_ctx_no_dup_ctx_sub with (Gamma1 := (a, Uty (t1 u--> t2))::nil)... *)
Qed.

(* Definition st_less_than_constant (x: string) (st1: nstate) (c2: constant) := *)
(*   match st1 x with *)
(*   | None => True *)
(*   | Some (tvalue (vconst c1), _) => const_order c1 c2 *)
(*   | Some (_, _) => False *)
(*   end. *)

(* Definition st_wf_order (x: string) (st1 st2 : nstate) := *)
(*   match st2 x with *)
(*   | None => False *)
(*   | Some (tvalue (vconst c2), _) => st_less_than_constant x st1 c2 *)
(*   | Some (_, _) => False *)
(*   end. *)

(* Global Hint Constructors Acc: core. *)

(* Lemma st_wf_order_wf' : forall x, forall c_x, forall st1, *)
(*     (st_less_than_constant x st1 c_x) -> Acc (st_wf_order x) st1. *)
(* Proof with eauto. *)
(*   intros x. *)
(*   apply (well_founded_induction_type *)
(*            const_order_is_well_founded *)
(*            (fun c_x => forall st1, *)
(*                 (st_less_than_constant x st1 c_x) -> Acc (st_wf_order x) st1)). *)
(*   intros c_x Hind st1 Hst1. *)
(*   unfold st_less_than_constant in Hst1. *)
(*   constructor... intros st' Hst'. *)
(*   unfold st_wf_order in Hst'. *)
(*   destruct (st1 x) eqn:HH; subst... *)
(*   - destruct p; subst... *)
(*     destruct t; subst; try inversion Hst'. *)
(*     destruct v; subst; try inversion Hst'. *)
(*     destruct c; subst; try inversion Hst'. *)
(*     eapply Hind... *)
(*   - inversion Hst'. *)
(* Defined. *)

(* Theorem st_wf_order_is_well_founded : forall x, well_founded (st_wf_order x). *)
(*   red; intros. constructor... *)
(*   intros st2 Hst2. unfold st_wf_order in Hst2. *)
(*   destruct (a x); subst; try inversion Hst2. *)
(*   destruct p; subst. *)
(*   destruct t; subst; try inversion Hst2. *)
(*   destruct v; subst; try inversion Hst2. *)
(*   destruct c; subst; try inversion Hst2. *)
(*   eapply st_wf_order_wf'; eauto. *)
(* Defined. *)

Lemma tmR_in_ctx_preserve_fix_aux_c: forall x (c_x: constant) st (T:base_ty) phi f e tau,
    (overbase_tmR_aux st ({{v:T | phi}}) c_x) ->
    (forall (c_x : constant),
        overbase_tmR_aux st ({{v:T | phi}}) c_x ->
        under_tmR_aux (x |-> (tvalue c_x, T); st) ((x o: {{v:T | well_founded_constraint x phi}} o--> tau) u--> tau)
                      (vlam f (T t--> (u\_ tau _/)) (tlete x c_x e))) ->
    under_tmR_aux (x |-> (tvalue c_x, T); st) tau
                  (tletapp x (vfix f (T t--> (u\_ tau _/)) x T e) c_x x).
Proof with eauto.
  intros x.
  apply (well_founded_induction_type
           const_order_is_well_founded
           (fun c_x => forall st (T:base_ty) phi f e tau,
                (overbase_tmR_aux st ({{v:T | phi}}) c_x) ->
                (forall (c_x : constant),
                    overbase_tmR_aux st ({{v:T | phi}}) c_x ->
                    under_tmR_aux (x |-> (tvalue c_x, T); st) ((x o: {{v:T | well_founded_constraint x phi}} o--> tau) u--> tau)
                                  (vlam f (T t--> (u\_ tau _/)) (tlete x c_x e))) ->
                under_tmR_aux (x |-> (tvalue c_x, T); st) tau
                              (tletapp x (vfix f (T t--> (u\_ tau _/)) x T e) c_x x))).
  intros c_x Hind st T phi f e tau Hc_xD HeDraw.
  assert (empty \N- c_x \Tin T). eapply over_tmR_aux_has_type in Hc_xD...
  assert (under_tmR_aux (x |-> (tvalue c_x, T); st) ((x o: {{v:T | well_founded_constraint x phi}} o--> tau) u--> tau)
                        (vlam f (T t--> (u\_ tau _/)) (tlete x c_x e))) as HeD...
  inversion HeD; subst. destruct H1.
  destruct (exists_fresh_var_of_value (vfix f (T t--> (u\_ tau _/)) x T e)) as (x1 & x2 & Hx1x2 & Hfree).
  assert (under_tmR_aux (x |-> (tvalue c_x, T); st) tau
                        (tlete x1 (vlam f (T t--> (u\_ tau _/)) (tlete x c_x e))
                               (tlete x2 (vfix f (T t--> (u\_ tau _/)) x T e) (tletapp x x1 x2 x)))).
  eapply H2...
  constructor... { inversion H0; subst... } split.
  - simpl. simpl in H1. inversion H1;subst... inversion H5;subst... inversion H6;subst...
    assert (T1 = T). eapply constant_base_ty_unique... subst...
  - intros c_x' Hc_x'D e3 Happ. inversion Happ; subst... simpl. clear Happ.
    rewrite update_shadow.
    assert (const_order c_x' c_x) as Horder. eapply constraint_phi_implies_order...
    assert (under_tmR_aux (x |-> (tvalue c_x', T); st) tau
                          (tletapp x (vfix f (T t--> (u\_ tau _/)) x T e) c_x' x)).
    eapply Hind with (phi:=phi)...
    + eapply constraint_phi_implies_subtyping...
    + eapply step_preserve_under_denotation... eapply eta_fix1...
  - eapply step_preserve_under_denotation... apply eta_fix2...
Qed.

Lemma tmR_aux_preserve_fix: forall x st (T:base_ty) phi f e tau,
    f <> x ->
    st_type_closed_in_ctx (st\_ st _/) nil (x o: {{v:T | phi}} o--> tau) ->
    tmR_aux st (x o: {{v:T | phi}}
                       o--> ((x o: {{v:T | well_founded_constraint x phi}} o--> tau) u--> tau))
            (vlam x T (vlam f (T t--> (u\_ tau _/)) e)) ->
    tmR_aux st (x o: {{v:T | phi}} o--> tau) (vfix f (T t--> (u\_ tau _/)) x T e).
Proof with eauto.
  intros x st T phi f e tau Hneqfx Hclosed H.
  inversion H; subst... inversion H2; subst... clear H H2. destruct H1.
  constructor... constructor...
  split. { inversion H; subst... inversion H4; subst... inversion H5; subst... inversion H6; subst...
           constructor... constructor... rewrite update_permute... }
  intros c_x Hc_x e3 Happ. inversion Happ; subst... simpl. clear Happ.
  assert (under_tmR_aux (x |-> (tvalue c_x, T); st) tau
                  (tletapp x (vfix f (T t--> (u\_ tau _/)) x T e) c_x x)).
  eapply tmR_in_ctx_preserve_fix_aux_c...
  - intros c_x' Hc_x'D.
    assert (empty \N- c_x' \Tin T). eapply over_tmR_aux_has_type in Hc_x'D...
    assert (ty_of_const c_x' = T) as HTT... { assert (empty \N- c_x' \Tin ty_of_const c_x')...
                                              eapply constant_base_ty_unique in H4...
                                              destruct c_x'; simpl; simpl in H4; subst... destruct T... inversion H4. destruct T... inversion H4... }
    assert (under_tmR_aux (x |-> (tvalue c_x', T); st)
                          ((x o: {{v:T | well_founded_constraint x phi}} o--> tau) u--> tau)
                          (tlete x1 (vlam x T (vlam f (T t--> (u\_ tau _/)) e))
                                 (tlete x2 c_x' (tletapp x x1 x2 x)))).
    apply H1... eapply step_preserve_under_denotation... eapply eta_fix3...
  - eapply step_preserve_under_denotation... eapply eta_fix1...
Qed.

Lemma tmR_in_ctx_preserve_fix: forall Gamma st x (T:base_ty) phi f e tau,
    (* ctx_inv st Gamma -> *)
    f <> x ->
    st_type_closed_in_ctx (st\_ st _/) Gamma (x o: {{v:T | phi}} o--> tau) ->
    tmR_in_ctx_aux st Gamma
                   (x o: {{v:T | phi}}
                           o--> ((x o: {{v:T | well_founded_constraint x phi}} o--> tau) u--> tau))
                   (vlam x T (vlam f (T t--> (u\_ tau _/)) e)) ->
    tmR_in_ctx_aux st Gamma (x o: {{v:T | phi}} o--> tau) (vfix f (T t--> (u\_ tau _/)) x T e).
Proof with eauto.
  intro Gamma.
  induction Gamma; simpl; intros st x Tx phix f e tau Hneqfx Hclosed HeD.
  - constructor... apply tmR_aux_preserve_fix... inversion HeD...
  - destruct a as (a & tau_a).
    assert (type_ctx_no_dup (st\_ st _/) ((a, tau_a) :: Gamma)) as Hnodup...
    inversion HeD; subst. clear HeD.
    + constructor...
      intros c_x Hc_xD.
      assert (tmR_in_ctx_aux (a |-> (tvalue c_x, T); st) Gamma
                             (x o: {{v:Tx | phix}}
                                     o--> ((x o: {{v:Tx | well_founded_constraint x phix}} o--> tau) u--> tau))
                             (tlete a c_x (vlam x Tx (vlam f (Tx t--> (u\_ tau _/)) e)))) as HF.
      apply H9...
      assert (tmR_in_ctx_aux (a |-> (tvalue c_x, T); st) Gamma
                             (x o: {{v:Tx | phix}}
                                     o--> ((x o: {{v:Tx | well_founded_constraint x phix}} o--> tau) u--> tau))
                             (vlam x Tx (vlam f (Tx t--> (u\_ tau _/)) (tlete a c_x e)))) as HF'.
      eapply step_preserve_ctx_denotation... eapply eta_fix4...
      assert (tmR_in_ctx_aux (a |-> (tvalue c_x, T); st) Gamma (x o: {{v:Tx | phix}} o--> tau)
                             (vfix f (Tx t--> (u\_ tau _/)) x Tx (tlete a c_x e))).
      eapply IHGamma... { eapply st_type_closed_in_ctx_destruct_overbase_front in Hclosed... rewrite nstate_to_tystate_hd... }
      eapply step_preserve_ctx_denotation... eapply eta_fix5...
    + constructor...
      destruct H9 as (e_x_hat & He_x_hatD & HH).
      exists e_x_hat. split...
      intros e_x He_xD.
      assert (tmR_in_ctx_aux (a |-> (e_x_hat, T); st) Gamma
                             (x o: {{v:Tx | phix}} o--> ((x o: {{v:Tx | well_founded_constraint x phix}} o--> tau) u--> tau))
                             (tlete a e_x (vlam x Tx (vlam f (Tx t--> (u\_ tau _/)) e))))...
      assert (tmR_in_ctx_aux (a |-> (e_x_hat, T); st) Gamma
                             (x o: {{v:Tx | phix}} o--> ((x o: {{v:Tx | well_founded_constraint x phix}} o--> tau) u--> tau))
                             (vlam x Tx (vlam f (Tx t--> (u\_ tau _/)) (tlete a e_x e))))...
      eapply step_preserve_ctx_denotation... eapply eta_fix6...
      assert (tmR_in_ctx_aux (a |-> (e_x_hat, T); st) Gamma (x o: {{v:Tx | phix}} o--> tau)
                             (vfix f (Tx t--> (u\_ tau _/)) x Tx (tlete a e_x e))).
      eapply IHGamma... { eapply st_type_closed_in_ctx_destruct_underbase_front in Hclosed... rewrite nstate_to_tystate_hd... }
      eapply step_preserve_ctx_denotation... eapply eta_fix7...
    + constructor...
      intros e_x He_xD.
      assert (tmR_in_ctx_aux st Gamma
                             (x o: {{v:Tx | phix}} o--> ((x o: {{v:Tx | well_founded_constraint x phix}} o--> tau) u--> tau))
                             (tlete a e_x (vlam x Tx (vlam f (Tx t--> (u\_ tau _/)) e))))...
      assert (tmR_in_ctx_aux st Gamma
                             (x o: {{v:Tx | phix}} o--> ((x o: {{v:Tx | well_founded_constraint x phix}} o--> tau) u--> tau))
                             (vlam x Tx (vlam f (Tx t--> (u\_ tau _/)) (tlete a e_x e))))...
      eapply step_preserve_ctx_denotation... eapply eta_fix6...
      assert (tmR_in_ctx_aux st Gamma (x o: {{v:Tx | phix}} o--> tau)
                             (vfix f (Tx t--> (u\_ tau _/)) x Tx (tlete a e_x e))).
      eapply IHGamma... { eapply st_type_closed_in_ctx_destruct_oarr_front in Hclosed... }
      eapply step_preserve_ctx_denotation... eapply eta_fix7...
    + constructor...
      intros e_x He_xD.
      assert (tmR_in_ctx_aux st Gamma
                             (x o: {{v:Tx | phix}} o--> ((x o: {{v:Tx | well_founded_constraint x phix}} o--> tau) u--> tau))
                             (tlete a e_x (vlam x Tx (vlam f (Tx t--> (u\_ tau _/)) e))))...
      assert (tmR_in_ctx_aux st Gamma
                             (x o: {{v:Tx | phix}} o--> ((x o: {{v:Tx | well_founded_constraint x phix}} o--> tau) u--> tau))
                             (vlam x Tx (vlam f (Tx t--> (u\_ tau _/)) (tlete a e_x e))))...
      eapply step_preserve_ctx_denotation... eapply eta_fix6...
      assert (tmR_in_ctx_aux st Gamma (x o: {{v:Tx | phix}} o--> tau)
                             (vfix f (Tx t--> (u\_ tau _/)) x Tx (tlete a e_x e))).
      eapply IHGamma... { eapply st_type_closed_in_ctx_destruct_arrar_front in Hclosed... }
      eapply step_preserve_ctx_denotation... eapply eta_fix7...
Qed.

Global Hint Resolve tmR_has_type: core.

Lemma tmR_in_ctx_preserve_application: forall Gamma st x1 x2 x (e1 e2: tm) tau a T phi,
    x1 <> x2 -> ~ x1 \FVtm e2 ->
    tmR_in_ctx_aux st Gamma (a o: {{v: T | phi}} o--> tau) e1 ->
    tmR_in_ctx_aux st Gamma ([[v: T | phi]]) e2 ->
    (forall (c2: constant), tmR_in_ctx_aux st Gamma ({{v: T | phi}}) c2 ->
                       tmR_in_ctx_aux st Gamma (under_subst_c a c2 tau)
                                      (tlete x1 e1 (tlete x2 e2 (tletapp x x1 x2 x)))
    ).
Proof with eauto.
  intro Gamma.
  induction Gamma; simpl; intros st x1 x2 x e1 e2 tau a0 T phi Hx1x2 Hx1free Hv1D Hv2D c2 Hc2D.
  - inversion Hv1D; subst. inversion Hv2D; subst. clear Hv1D Hv2D. inversion Hc2D; subst. clear Hc2D.
    assert (e2 -->* c2) as Hc2E...
    assert (empty \N- c2 \Tin T) as Hc2T; try tmR_implies_has_type...
    inversion H; subst. inversion H0; subst. clear H H0.
    constructor... constructor...
    inversion H4; subst. destruct H0 as (Hv1T & HH).
    assert (under_tmR_aux (a0 |-> (tvalue c2, T); st) tau (tlete x1 e1 (tlete x2 c2 (tletapp x x1 x2 x))))... apply HH... inversion H1...
    rewrite <- under_tmR_aux_st_update...
    eapply step_preserve_under_denotation... apply eta_snd_let_reduce...
  - destruct a as (a & tau_a).
    assert (empty \N- c2 \Tin T) as Hc2T...
    { eapply tmR_in_ctx_aux_implies_has_type in Hc2D... rewrite const_ctx_independent in Hc2D... }
    assert (type_ctx_no_dup (st\_ st _/) ((a, tau_a) :: Gamma)) as Hnodup...
    inversion Hv1D; subst.
    + constructor... inversion H3... inversion H5...
      intros c_x He_xD. inversion Hv2D; subst.
      assert (empty \N- c_x \Tin T0) as Hc_xT; try tmR_implies_has_type...
      assert (tmR_in_ctx_aux (a |-> (tvalue c_x, T0); st) Gamma (a0 o: {{v:T | phi}} o--> tau) (tlete a c_x e1)) as HHv1...
      assert (tmR_in_ctx_aux (a |-> (tvalue c_x, T0); st) Gamma ([[v:T | phi]]) (tlete a c_x e2)) as HHv2...
      assert (tmR_in_ctx_aux (a |-> (tvalue c_x, T0); st) Gamma (<u[ a0 |c-> c2 ]> tau) (tlete x1 (tlete a c_x e1) (tlete x2 (tlete a c_x e2) (tletapp x x1 x2 x)))). eapply IHGamma...
      { inversion Hc2D; subst...
        eapply step_preserve_ctx_denotation... eapply eta_subst_in_const...
      }
      eapply step_preserve_ctx_denotation... eapply eta3...
    + constructor... inversion H3... inversion H5...
      destruct H9 as (e_x_hat1 & He_x_hat1D & HH1).
      inversion Hv2D; subst.
      { destruct H14 as (e_x_hat2 & He_x_hat2D & HH2).
        inversion Hc2D; subst.
        destruct H18 as (e_x_hat3 & He_x_hat3D & HH3)...
        destruct (meet_of_three_terms_exists e_x_hat1 e_x_hat2 e_x_hat3 T0) as (e_x_hat & HT & HE); try tmR_implies_has_type...
        exists e_x_hat... split. eapply meet_of_three_terms_implies_denotation in HE...
        assert (empty \N- e_x_hat1 \Tin T0) as He_x_hat1T... eapply tmR_has_type in He_x_hat1D...
        assert (empty \N- e_x_hat2 \Tin T0) as He_x_hat2T... eapply tmR_has_type in He_x_hat2D...
        intros e_x He_xD.
        assert (tmR_in_ctx_aux (a |-> (e_x_hat1, T0); st) Gamma (a0 o: {{v:T | phi}} o--> tau) (tlete a e_x e1)) as Hv1...
        assert (tmR_in_ctx_aux (a |-> (e_x_hat2, T0); st) Gamma ([[v:T | phi]]) (tlete a e_x e2)) as Hv2...
        apply meet_of_three_terms_term_order in HE... destruct HE as (HEE1 & HEE2 & HEE3).
        assert (tmR_in_ctx_aux (a |-> (e_x_hat, T0); st) Gamma (<u[ a0 |c-> c2 ]> tau)
                               (tlete x1 (tlete a e_x e1) (tlete x2 (tlete a e_x e2) (tletapp x x1 x2 x))))...
        eapply IHGamma...
        - eapply step_preserve_ctx_denotation... eapply eta_subst_in_const...
        - eapply step_preserve_ctx_denotation... eapply eta3...
      }
    + constructor... inversion H3... inversion H5...
      inversion Hv1D; subst. inversion Hv2D; subst.
      intros e_x He_xD.
      assert (tmR_in_ctx_aux st Gamma (a0 o: {{v:T | phi}} o--> tau) (tlete a e_x e1)) as Hv1...
      assert (tmR_in_ctx_aux st Gamma ([[v:T | phi]]) (tlete a e_x e2)) as Hv2...
      assert (tmR_in_ctx_aux st Gamma (<u[ a0 |c-> c2 ]> tau) (tlete x1 (tlete a e_x e1) (tlete x2 (tlete a e_x e2) (tletapp x x1 x2 x))))... eapply IHGamma...
      { inversion Hc2D; subst... eapply step_preserve_ctx_denotation... eapply eta_subst_in_const... }
      eapply step_preserve_ctx_denotation... eapply eta3...
    + constructor... inversion H3... inversion H5...
      inversion Hv1D; subst. inversion Hv2D; subst.
      intros e_x He_xD.
      assert (tmR_in_ctx_aux st Gamma (a0 o: {{v:T | phi}} o--> tau) (tlete a e_x e1))...
      assert (tmR_in_ctx_aux st Gamma ([[v:T | phi]]) (tlete a e_x e2))...
      assert (tmR_in_ctx_aux st Gamma (<u[ a0 |c-> c2 ]> tau) (tlete x1 (tlete a e_x e1) (tlete x2 (tlete a e_x e2) (tletapp x x1 x2 x))))... eapply IHGamma...
      { inversion Hc2D; subst... eapply step_preserve_ctx_denotation... eapply eta_subst_in_const... }
      eapply step_preserve_ctx_denotation... eapply eta3...
Qed.

Lemma tmR_in_ctx_preserve_oarr_c_application: forall Gamma st x (v1: value) (c2: constant) tau a T phi,
    tmR_in_ctx_aux st Gamma (a o: {{v: T | phi}} o--> tau) v1 ->
    tmR_in_ctx_aux st Gamma ([[v: T | phi]]) c2 ->
    tmR_in_ctx_aux st Gamma (under_subst_c a c2 tau) (tletapp x v1 c2 x).
Proof with eauto.
  intro Gamma; simpl; intros st x v1 c2 tau a0 T phi Hv1D Hv2D.
  destruct (exists_fresh_var_of_value c2) as (x1 & x2 & Hx1x2 & Hfree).
  eapply tmR_in_ctx_preserve_application with (x1:=x1) (x2:=x2) (x:=x) (e2:=c2) (c2:=c2) in Hv1D...
  eapply step_preserve_ctx_denotation... eapply eta4...
Qed.

Lemma tmR_in_ctx_preserve_oarr_var_application: forall Gamma st x (v1: value) (name2: string) tau a T phi,
    tmR_in_ctx_aux st Gamma (a o: {{v: T | phi}} o--> tau) v1 ->
    tmR_in_ctx_aux st Gamma ([[v: T | phi]]) name2 ->
    tmR_in_ctx_aux st Gamma (under_subst_id a name2 tau) (tletapp x v1 name2 x).
Proof with eauto.
  intro Gamma; simpl; intros st x v1 id2 tau a0 T phi Hv1D Hv2D.
  destruct (exists_fresh_var_of_value id2) as (x1 & x2 & Hx1x2 & Hfree).
  assert ((forall (c2: constant), tmR_in_ctx_aux st Gamma ({{v: T | phi}}) c2 ->
                             tmR_in_ctx_aux st Gamma (under_subst_c a0 c2 tau)
                                            (tlete x1 v1 (tlete x2 id2 (tletapp x x1 x2 x)))
         )). eapply tmR_in_ctx_preserve_application...
  assert (tmR_in_ctx_aux st Gamma (<u[ a0 |id-> id2 ]> tau) (tlete x1 v1 (tlete x2 id2 (tletapp x x1 x2 x)))). eapply denotation_last_var_to_const...
  eapply step_preserve_ctx_denotation... eapply eta5...
Qed.

Lemma tmR_in_ctx_preserve_oarr_application: forall Gamma st x (v1: value) (c2: cid) tau a T phi,
    tmR_in_ctx_aux st Gamma (a o: {{v: T | phi}} o--> tau) v1 ->
    tmR_in_ctx_aux st Gamma ([[v: T | phi]]) c2 ->
    tmR_in_ctx_aux st Gamma (under_subst_cid a c2 tau) (tletapp x v1 c2 x).
Proof with eauto.
  intros. destruct c2.
  - eapply tmR_in_ctx_preserve_oarr_c_application...
  - eapply tmR_in_ctx_preserve_oarr_var_application...
Qed.

Lemma tmR_in_ctx_preserve_arrarr_application_aux: forall Gamma st x (e1 e2: tm) tau tau1 x1 x2,
    x1 <> x2 -> ~ x1 \FVtm e2 ->
    tmR_in_ctx_aux st Gamma (tau1 u--> tau) e1 ->
    tmR_in_ctx_aux st Gamma tau1 e2 ->
    tmR_in_ctx_aux st Gamma tau (tlete x1 e1 (tlete x2 e2 (tletapp x x1 x2 x))).
Proof with eauto.
  intro Gamma.
  induction Gamma; simpl; intros st x v1 v2 tau tau_x x1 x2 Hx1x2 Hfree Hv1D Hv2D.
  - inversion Hv1D; subst. inversion Hv2D; subst. clear Hv1D Hv2D.
    inversion H; subst. inversion H3; subst. clear H H3. inversion H0; subst. clear H0.
    destruct H2 as (Hv1T & HH).
    constructor...
  - destruct a as (a & tau_a).
    inversion Hv1D; subst.
    + constructor... { inversion H5; subst... } inversion Hv2D; subst.
      intros c_x He_xD.
      assert (empty \N- c_x \Tin T) as Hc_xT; try tmR_implies_has_type.
      assert (tmR_in_ctx_aux (a |-> (tvalue c_x, T); st) Gamma (tau_x u--> tau) (tlete a c_x v1)) as HHv1...
      assert (tmR_in_ctx_aux (a |-> (tvalue c_x, T); st) Gamma tau_x (tlete a c_x v2)) as HHv2...
      assert (tmR_in_ctx_aux (a |-> (tvalue c_x, T); st) Gamma tau
                             (tlete x1 (tlete a c_x v1) (tlete x2 (tlete a c_x v2) (tletapp x x1 x2 x)))). eapply IHGamma...
      eapply step_preserve_ctx_denotation... eapply eta3...
    + constructor... { inversion H5; subst... }
      {
        destruct H9 as (e_x_hat1 & He_x_hat1D & HH1).
        inversion Hv2D; subst.
        destruct H14 as (e_x_hat2 & He_x_hat2D & HH2).
        destruct (meet_of_two_terms_exists e_x_hat1 e_x_hat2 T) as (e_x_hat & HT & HE); try tmR_implies_has_type...
        exists e_x_hat... split. eapply meet_of_two_terms_implies_denotation in HE...
        intros e_x He_xD.
        assert (empty \N- e_x_hat1 \Tin T) as He_x_hat1T; try tmR_implies_has_type.
        assert (empty \N- e_x_hat2 \Tin T) as He_x_hat2T; try tmR_implies_has_type.
        assert (tmR_in_ctx_aux (a |-> (e_x_hat1, T); st) Gamma (tau_x u--> tau) (tlete a e_x v1)) as Hv1...
        assert (tmR_in_ctx_aux (a |-> (e_x_hat2, T); st) Gamma tau_x (tlete a e_x v2)) as Hv2...
        apply meet_of_two_terms_term_order in HE... destruct HE as (HEE1 & HEE2).
        assert (tmR_in_ctx_aux (a |-> (e_x_hat, T); st) Gamma tau (tlete x1 (tlete a e_x v1) (tlete x2 (tlete a e_x v2) (tletapp x x1 x2 x)))). eapply IHGamma...
        - eapply step_preserve_ctx_denotation... eapply eta3...
      }
    + constructor... inversion H3... inversion H5...
      inversion Hv2D; subst.
      intros e_x He_xD.
      assert (tmR_in_ctx_aux st Gamma (tau_x u--> tau) (tlete a e_x v1)) as Hv1...
      assert (tmR_in_ctx_aux st Gamma tau_x (tlete a e_x v2)) as Hv2...
      assert (tmR_in_ctx_aux st Gamma tau (tlete x1 (tlete a e_x v1) (tlete x2 (tlete a e_x v2) (tletapp x x1 x2 x))))...
      eapply step_preserve_ctx_denotation... eapply eta3...
    + constructor... inversion H3... inversion H5...
      inversion Hv2D; subst.
      intros e_x He_xD.
      assert (tmR_in_ctx_aux st Gamma (tau_x u--> tau) (tlete a e_x v1)) as Hv1...
      assert (tmR_in_ctx_aux st Gamma tau_x (tlete a e_x v2)) as Hv2...
      assert (tmR_in_ctx_aux st Gamma tau (tlete x1 (tlete a e_x v1) (tlete x2 (tlete a e_x v2) (tletapp x x1 x2 x))))...
      eapply step_preserve_ctx_denotation... eapply eta3...
Qed.

Lemma tmR_in_ctx_preserve_arrarr_application: forall Gamma st x (v1 v2: value) tau tau1,
    tmR_in_ctx_aux st Gamma (tau1 u--> tau) v1 ->
    tmR_in_ctx_aux st Gamma tau1 v2 ->
    tmR_in_ctx_aux st Gamma tau (tletapp x v1 v2 x).
Proof with eauto.
  intro Gamma; simpl; intros st x v1 v2 tau tau1 Hv1D Hv2D.
  destruct (exists_fresh_var_of_value v2) as (x1 & x2 & Hx1x2 & Hfree).
  assert (tmR_in_ctx_aux st Gamma tau (tlete x1 v1 (tlete x2 v2 (tletapp x x1 x2 x)))).
  eapply tmR_in_ctx_preserve_arrarr_application_aux...
  eapply step_preserve_ctx_denotation... eapply eta6...
Qed.

Lemma tmR_in_ctx_preserve_biop_application_aux: forall Gamma st op x1 x2 x (e1 e2: tm) phi1 phi2,
    x1 <> x2 -> ~ x1 \FVtm e2 ->
    tmR_in_ctx_aux st Gamma ([[v: fst_ty_of_op op | phi1]]) e1 ->
    tmR_in_ctx_aux st Gamma ([[v: snd_ty_of_op op | phi2]]) e2 ->
    (forall (c1 c2: constant),
        tmR_in_ctx_aux st Gamma ({{v: fst_ty_of_op op | phi1}}) c1 ->
        tmR_in_ctx_aux st Gamma ({{v: snd_ty_of_op op | phi2}}) c2 ->
        tmR_in_ctx_aux st Gamma (mk_op_retty_from_cids op c1 c2)
                       (tlete x1 e1 (tlete x2 e2 (tletbiop x op x1 x2 x)))).
Proof with eauto.
  intro Gamma.
  induction Gamma; simpl; intros st op x1 x2 x e1 e2 phi1 phi2 Hx1x2 Hx1free Hv1D Hv2D c1 c2 Hc1D Hc2D.
  - inversion Hv1D; subst. inversion Hv2D; subst. clear Hv1D Hv2D.
    inversion Hc1D; subst. inversion Hc2D; subst. clear Hc1D Hc2D.
    assert (e1 -->* c1) as Hc1E... assert (e2 -->* c2) as Hc2E...
    eapply step_preserve_ctx_denotation... eapply eta_op... apply op_c_denoation_safe...
  - destruct a as (a & tau_a).
    inversion Hv1D; subst.
    + constructor... inversion Hv2D; subst.
      intros c_x He_xD.
      assert (empty \N- c_x \Tin T) as Hc_xT; try tmR_implies_has_type.
      assert (tmR_in_ctx_aux (a |-> (tvalue c_x, T); st) Gamma ([[v:fst_ty_of_op op | phi1]]) (tlete a c_x e1)) as HHv1...
      assert (tmR_in_ctx_aux (a |-> (tvalue c_x, T); st) Gamma ([[v:snd_ty_of_op op | phi2]]) (tlete a c_x e2)) as HHv2...
      assert (tmR_in_ctx_aux (a |-> (tvalue c_x, T); st) Gamma (mk_op_retty_from_cids op c1 c2)
                             (tlete x1 (tlete a c_x e1) (tlete x2 (tlete a c_x e2) (tletbiop x op x1 x2 x)))).
      eapply IHGamma...
      { eapply tmR_in_ctx_overhead_not_free... } { eapply tmR_in_ctx_overhead_not_free... }
      eapply step_preserve_ctx_denotation... eapply eta9...
    + constructor...
      destruct H9 as (e_x_hat1 & He_x_hat1D & HH1).
      inversion Hv2D; subst.
      { destruct H14 as (e_x_hat2 & He_x_hat2D & HH2).
        inversion Hc1D; subst.
        destruct H18 as (e_x_hat3 & He_x_hat3D & HH3)...
        inversion Hc2D; subst.
        destruct H22 as (e_x_hat4 & He_x_hat4D & HH4)...
        destruct (meet_of_four_terms_exists e_x_hat1 e_x_hat2 e_x_hat3 e_x_hat4 T)
          as (e_x_hat & HT & HE); try tmR_implies_has_type...
        exists e_x_hat... split. eapply meet_of_four_terms_implies_denotation in HE...
        assert (empty \N- e_x_hat1 \Tin T) as He_x_hat1T... eapply tmR_has_type in He_x_hat1D...
        assert (empty \N- e_x_hat2 \Tin T) as He_x_hat2T... eapply tmR_has_type in He_x_hat2D...
        intros e_x He_xD.
        assert (tmR_in_ctx_aux (a |-> (e_x_hat1, T); st) Gamma ([[v:fst_ty_of_op op | phi1]]) (tlete a e_x e1)) as Hv1...
        assert (tmR_in_ctx_aux (a |-> (e_x_hat2, T); st) Gamma ([[v:snd_ty_of_op op | phi2]]) (tlete a e_x e2)) as Hv2...
        apply meet_of_four_terms_term_order in HE... destruct HE as (HEE1 & HEE2 & HEE3 & HEE4).
        assert (tmR_in_ctx_aux (a |-> (e_x_hat, T); st) Gamma (mk_op_retty_from_cids op c1 c2)
                               (tlete x1 (tlete a e_x e1) (tlete x2 (tlete a e_x e2) (tletbiop x op x1 x2 x)))).
        eapply IHGamma...
        - eapply step_preserve_ctx_denotation... eapply eta_subst_in_const...
        - eapply step_preserve_ctx_denotation... eapply eta_subst_in_const...
        - eapply step_preserve_ctx_denotation... eapply eta9...
      }
    + constructor...
      inversion Hv1D; subst. inversion Hv2D; subst.
      intros e_x He_xD.
      assert (tmR_in_ctx_aux st Gamma ([[v:fst_ty_of_op op | phi1]]) (tlete a e_x e1)) as Hv1...
      assert (tmR_in_ctx_aux st Gamma ([[v:snd_ty_of_op op | phi2]]) (tlete a e_x e2)) as Hv2...
      assert (tmR_in_ctx_aux st Gamma (mk_op_retty_from_cids op c1 c2)
                             (tlete x1 (tlete a e_x e1) (tlete x2 (tlete a e_x e2) (tletbiop x op x1 x2 x)))).
      eapply IHGamma...
      { eapply tmR_in_ctx_oarrhead_not_free... } { eapply tmR_in_ctx_oarrhead_not_free... }
      eapply step_preserve_ctx_denotation... eapply eta9...
    + constructor...
      inversion Hv1D; subst. inversion Hv2D; subst.
      intros e_x He_xD.
      assert (tmR_in_ctx_aux st Gamma ([[v:fst_ty_of_op op | phi1]]) (tlete a e_x e1)) as Hv1...
      assert (tmR_in_ctx_aux st Gamma ([[v:snd_ty_of_op op | phi2]]) (tlete a e_x e2)) as Hv2...
      assert (tmR_in_ctx_aux st Gamma (mk_op_retty_from_cids op c1 c2)
                             (tlete x1 (tlete a e_x e1) (tlete x2 (tlete a e_x e2) (tletbiop x op x1 x2 x)))).
      eapply IHGamma...
      { eapply tmR_in_ctx_arrarrhead_not_free... } { eapply tmR_in_ctx_arrarrhead_not_free... }
      eapply step_preserve_ctx_denotation... eapply eta9...
Qed.

Lemma tmR_in_ctx_preserve_biop_application: forall Gamma st x op (v1 v2: cid),
    st_type_closed_in_ctx (st\_ st _/) Gamma (mk_op_retty_from_cids op v1 v2) ->
    tmR_in_ctx_aux st Gamma (mk_op_retty_from_cids op v1 v2) (tletbiop x op v1 v2 x).
Proof with eauto.
  intros Gamma st x op v1 v2 Hclosed.
  destruct (exists_fresh_var_of_value v2) as (x1 & x2 & Hx1x2 & Hfree).
  assert (exists phi1, tmR_in_ctx_aux st Gamma ([[v: fst_ty_of_op op | phi1]]) v1) as (phi1 & Hv1D). eapply closed_op_rty_implies_fst_rty_exists...
  assert (exists phi2, tmR_in_ctx_aux st Gamma ([[v: snd_ty_of_op op | phi2]]) v2) as (phi2 & Hv2D). eapply closed_op_rty_implies_snd_rty_exists...
  assert (forall (c1 c2: constant),
             tmR_in_ctx_aux st Gamma ({{v: fst_ty_of_op op | phi1}}) c1 ->
             tmR_in_ctx_aux st Gamma ({{v: snd_ty_of_op op | phi2}}) c2 ->
             tmR_in_ctx_aux st Gamma (mk_op_retty_from_cids op c1 c2)
                            (tlete x1 v1 (tlete x2 v2 (tletbiop x op x1 x2 x)))).
  eapply tmR_in_ctx_preserve_biop_application_aux...
  eapply denotation_last_var_to_const2...
  intros c1 c2 Hc1D Hc2D.
  eapply step_preserve_ctx_denotation... eapply eta10...
Qed.

Lemma tmR_in_ctx_preserve_matchb_true: forall Gamma st (v: value) e1 e2 tau,
    type_ctx_no_dup (st\_ st _/) Gamma ->
    tmR_in_ctx_aux st Gamma (mk_eq_constant true) v ->
    tmR_in_ctx_aux st Gamma tau e1 ->
    tmR_in_ctx_aux st Gamma tau (tmatchb v e1 e2).
Proof with eauto.
  intros Gamma st v e1 e2 tau Hnodup Hv He1.
  assert ((exists n : bool, v = n) \/ (exists name : string, v = name)) as HH. apply tmR_in_ctx_aux_implies_has_type in Hv... inversion Hv; subst. apply bool_value_cid_exists in H1...
  destruct HH.
  - destruct H as (b & Hb); subst. apply mk_eq_constant_is_itsefl_in_ctx in Hv. rewrite Hv.
    eapply step_preserve_ctx_denotation... apply eta_matchb_true...
  - destruct H as (id & Hid); subst. rewrite tmR_in_ctx_id_eq_c... simpl. rewrite eqb_refl.
    apply step_preserve_ctx_denotation with (e:= ([id := true] e1))... apply eta_matchb_true...
    rewrite <- tmR_in_ctx_id_eq_c...
Qed.

Lemma tmR_in_ctx_preserve_matchb_false: forall st Gamma (v: value) e1 e2 tau,
    type_ctx_no_dup (st\_ st _/) Gamma ->
    tmR_in_ctx_aux st Gamma (mk_eq_constant false) v ->
    tmR_in_ctx_aux st Gamma tau e2 ->
    tmR_in_ctx_aux st Gamma tau (tmatchb v e1 e2).
Proof with eauto.
  intros st Gamma v e1 e2 tau Hnodup Hv He1.
  assert ((exists n : bool, v = n) \/ (exists name : string, v = name)) as HH. apply tmR_in_ctx_aux_implies_has_type in Hv... inversion Hv; subst. apply bool_value_cid_exists in H1...
  destruct HH.
  - destruct H as (b & Hb); subst. apply mk_eq_constant_is_itsefl_in_ctx in Hv. rewrite Hv.
    eapply step_preserve_ctx_denotation... apply eta_matchb_false...
  - destruct H as (id & Hid); subst. rewrite tmR_in_ctx_id_eq_c... simpl. rewrite eqb_refl.
    apply step_preserve_ctx_denotation with (e:= ([id := false] e2))... apply eta_matchb_false...
    rewrite <- tmR_in_ctx_id_eq_c...
Qed.