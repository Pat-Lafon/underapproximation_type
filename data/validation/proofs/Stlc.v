Require Import Setoid.
Require Import Lia.

Require Import List.
Import ListNotations.

From Coq Require Export Logic.Classical_Pred_Type.

From MyProject Require Import Tactics.

Definition tvar := nat.
Definition var := nat.

Inductive type : Type :=
| N : type
| Arrow : type -> type -> type.

Inductive term : Type :=
| Const : nat -> term
| Id : var -> term
| App : term -> term -> term
| Abs : type -> term -> term.

(* Terms that do not have applications *)
Inductive app_free : term -> Prop :=
| ConsNoApp : forall n, app_free (Const n)
| IdNoApp : forall x, app_free (Id x)
| AbsNoApp : forall ty (t : term),
               app_free t -> app_free (Abs ty t).

Inductive num_arr : type -> nat -> Prop :=
| num_arr_const :  num_arr (N) 0
| num_arr_app : forall t1 t2 n2, num_arr t2 n2 -> num_arr (Arrow t1 t2) (n2 + 1).

Inductive num_app : term -> nat -> Prop :=
| num_app_const : forall n, num_app (Const n) 0
| num_app_id : forall v, num_app (Id v) 0
| num_app_app : forall t1 t2 n1 n2, num_app t1 n1 -> num_app t2 n2 -> num_app (App t1 t2) (1 + n1 + n2)
| num_app_abs : forall t ty n, num_app t n -> num_app (Abs ty t) (n).

Inductive is_const : term -> Prop :=
| is_const_i : forall n, is_const (Const n).

Inductive is_var : term -> Prop :=
| is_var_i : forall v, is_var (Id v).

Inductive is_app: term -> Prop :=
| is_app_i : forall t1 t2, is_app (App t1 t2).

Inductive is_abs: term -> Prop :=
| is_abs_i : forall t ty, is_abs (Abs ty t).

Inductive stlc_id: term -> var -> Prop :=
| stlc_id_i : forall v, stlc_id (Id v) v.

Inductive stlc_const: term -> nat -> Prop :=
| stlc_const_i : forall n, stlc_const (Const n) n.

Inductive stlc_app1: term -> term -> Prop :=
| stlc_app1_i : forall t1 t2, stlc_app1 (App t1 t2) t1.

Inductive stlc_app2: term -> term -> Prop :=
| stlc_app2_i : forall t1 t2, stlc_app2 (App t1 t2) t2.

Inductive stlc_abs_ty : term -> type -> Prop :=
| stlc_abs_ty_i : forall t ty, stlc_abs_ty (Abs ty t) ty.

Inductive stlc_abs_body: term -> term -> Prop :=
| stlc_abs_body_i : forall t ty, stlc_abs_body (Abs ty t) t.

Inductive stlc_ty_nat: type -> Prop :=
| stlc_ty_nat_i : stlc_ty_nat (N).

Inductive stlc_ty_arr1 : type -> type -> Prop :=
| stlc_ty_arr1_i : forall t1 t2, stlc_ty_arr1 (Arrow t1 t2) t1.

Inductive stlc_ty_arr2 : type -> type -> Prop :=
| stlc_ty_arr2_i : forall t1 t2, stlc_ty_arr2 (Arrow t1 t2) t2.

Definition env := list type.

(* Inductive bind : env -> nat -> type -> Prop :=
| BindNow   : forall tau env, bind (tau :: env) 0 tau
| BindLater : forall tau tau' x env,
    bind env x tau -> bind (tau' :: env) (S x) tau. *)

Inductive stlc_tyctx_hd : env -> type -> Prop :=
| stlc_tyctx_hd_i : forall env ty, stlc_tyctx_hd (ty :: env) ty.

Inductive stlc_tyctx_tl : env -> env -> Prop :=
| stlc_tyctx_tl_i : forall ty g, stlc_tyctx_tl (ty :: g) g.

Inductive typing (e : env) : term -> type -> Prop :=
| TId :
    forall x tau,
      nth_error e x = Some tau ->
      typing e (Id x) tau
| TConst :
    forall n,
      typing e (Const n) N
| TAbs :
    forall t tau1 tau2,
      typing (tau1 :: e) t tau2 ->
      typing e (Abs tau1 t) (Arrow tau1 tau2)
| TApp :
    forall t1 t2 tau1 tau2,
      typing e t1 (Arrow tau1 tau2) ->
      typing e t2 tau1 ->
      typing e (App t1 t2) tau2.

Hint Constructors type: core.
Hint Constructors term: core.
Hint Constructors app_free: core.
Hint Constructors num_arr: core.
Hint Constructors num_app: core.
Hint Constructors is_const: core.
Hint Constructors is_var: core.
Hint Constructors is_app: core.
Hint Constructors is_abs: core.
Hint Constructors stlc_id: core.
Hint Constructors stlc_const: core.
Hint Constructors stlc_app1: core.
Hint Constructors stlc_app2: core.
Hint Constructors stlc_ty_nat: core.
Hint Constructors stlc_ty_arr2: core.
Hint Unfold not: core.

Lemma stlc_num_arr_geq_0 : forall tau, (forall n, (num_arr tau n -> n >= 0)). Proof.
    intros. lia.
Qed. Hint Resolve stlc_num_arr_geq_0: core.

Lemma stlc_num_arr_arr : forall tau, (forall tau_body, (forall m, (stlc_ty_arr2 tau tau_body -> (num_arr tau_body m <-> num_arr tau (m + 1))))). Proof.
    intros. my_inversion H. split.
    - intro. econstructor. auto.
    - intro. my_inversion H0. assert (n2 = m). lia. subst. auto.
 Qed. Hint Resolve stlc_num_arr_arr: core.

Lemma stlc_const_num_app_0 : forall v, (forall n, ((is_const v /\ num_app v n) -> n = 0)). Proof.
    intros. simp. destruct v; my_inversion H. my_inversion H0.
Qed. Hint Resolve stlc_const_num_app_0: core.

Lemma stlc_var_num_app_0 : forall v, (forall n, ((is_var v /\ num_app v n) -> n = 0)). Proof.
    intros. simp. destruct v; my_inversion H. my_inversion H0.
Qed. Hint Resolve stlc_var_num_app_0: core.

Lemma stlc_num_app_gt_0_is_abs_or_app : forall v, (forall n, ((num_app v n /\ n > 0) -> (is_abs v \/ is_app v))). Proof.
    intros. simp. destruct v.
    - my_inversion H. my_inversion H0.
    - my_inversion H. my_inversion H0.
    - right. constructor.
    - left. constructor.
Qed. Hint Resolve stlc_num_app_gt_0_is_abs_or_app: core.

Lemma simple_num_arr : forall tau, (exists n, num_arr tau n). Proof.
    intros. induction tau.
    - exists 0. constructor.
    - destruct IHtau2. eauto.
Qed.

Lemma stlc_typing_num_arr : forall gamma, (forall v, (forall tau, (exists n, (typing gamma v tau -> num_arr tau n)))). Proof.
    intros.  assert (exists n, num_arr tau n). eapply simple_num_arr. destruct H. eexists. intro. eauto.
Qed. Hint Resolve stlc_typing_num_arr: core.

Lemma stlc_term_4_cases : forall v, (is_const v \/ (is_var v \/ (is_abs v \/ is_app v))). Proof.
    intros. destruct v.
    - left; auto.
    - right. left. auto.
    - right. right. right. auto.
    - right. right. left. auto.
Qed. Hint Resolve stlc_term_4_cases: core.

Lemma stlc_term_disjoint1 : forall v, ~(is_const v /\ is_var v). Proof.
    intros. destruct v; unfold not; intro; simp; my_inversion H; my_inversion H0.
 Qed. Hint Resolve stlc_term_disjoint1: core.

Lemma stlc_term_disjoint2 : forall v, ~(is_const v /\ is_abs v). Proof.
    intros. destruct v; unfold not; intro; simp; my_inversion H; my_inversion H0.
 Qed. Hint Resolve stlc_term_disjoint2: core.

Lemma stlc_term_disjoint3 : forall v, ~(is_const v /\ is_app v). Proof.
    intros; destruct v; unfold not; intro; simp; my_inversion H; my_inversion H0.
 Qed. Hint Resolve stlc_term_disjoint3: core.

Lemma stlc_term_disjoint4 : forall v, ~(is_var v /\ is_abs v). Proof.
    intros; destruct v; unfold not; intro; simp; my_inversion H; my_inversion H0.
Qed. Hint Resolve stlc_term_disjoint4: core.

Lemma stlc_term_disjoint5 : forall v, ~(is_var v /\ is_app v). Proof.
    intros; destruct v; unfold not; intro; simp; my_inversion H; my_inversion H0.
 Qed. Hint Resolve stlc_term_disjoint5: core.

Lemma stlc_term_disjoint6 : forall v, ~(is_abs v /\ is_app v). Proof.
    intros; destruct v; unfold not; intro; simp; my_inversion H; my_inversion H0.
 Qed. Hint Resolve stlc_term_disjoint6: core.

Lemma stlc_term_const_typing_nat : forall gamma, (forall v, (forall tau, ((is_const v /\ typing gamma v tau) -> stlc_ty_nat tau))). Proof.
    intros. simp. my_inversion H; clear H. my_inversion H0. constructor.
 Qed. Hint Resolve stlc_term_const_typing_nat: core.

Lemma stlc_id_is_var : forall v, (forall id, (stlc_id v id -> is_var v)). Proof.
    intros. my_inversion H. constructor.
 Qed. Hint Resolve stlc_id_is_var: core.

Lemma stlc_const_is_const : forall v, (forall c, (stlc_const v c -> is_const v)). Proof.
    intros. my_inversion H. auto.
 Qed. Hint Resolve stlc_const_is_const: core.

Lemma stlc_term_destruct1 : forall term, (exists c, (is_const term -> stlc_const term c)). Proof.
    intros. destruct term0.
    - exists n. intro. constructor.
    - eexists. intro. my_inversion H.
    - eexists. intro. my_inversion H.
    - eexists. intro. my_inversion H.
    Unshelve. constructor. constructor. constructor.
 Qed. Hint Resolve stlc_term_destruct1: core.

Lemma stlc_term_destruct2 : forall term, (exists c, (is_var term -> stlc_id term c)). Proof.
    intros. destruct term0.
    - eexists. intro. my_inversion H.
    - exists v. auto.
    - eexists. intro. my_inversion H.
    - eexists. intro. my_inversion H.
    Unshelve. constructor. constructor. constructor.
 Qed. Hint Resolve stlc_term_destruct2: core.

Lemma stlc_term_destruct3 : forall term, (exists t1, (exists t2, (is_app term -> (stlc_app1 term t1 /\ stlc_app2 term t2)))). Proof.
    intros. destruct term0.
    - repeat econstructor; my_inversion H.
    - repeat econstructor; my_inversion H.
    - repeat econstructor; my_inversion H.
    - repeat econstructor; my_inversion H.
    Unshelve. all: repeat constructor.
 Qed. Hint Resolve stlc_term_destruct3: core.

Lemma stlc_term_destruct4 : forall term, (exists ty, (exists body, (is_abs term -> (stlc_abs_ty term ty /\ stlc_abs_body term body)))). Proof.
    intros. destruct term0.
    - repeat econstructor; my_inversion H.
    - repeat econstructor; my_inversion H.
    - repeat econstructor; my_inversion H.
    - repeat econstructor.
    Unshelve. all: repeat constructor.
Qed. Hint Resolve stlc_term_destruct4: core.

Lemma stlc_term_abs_typing_arr : forall gamma, (forall v, (forall tau, (forall ty, (forall body, (exists body_ty, ((stlc_abs_ty v ty /\ (stlc_abs_body v body /\ typing gamma v tau)) -> (stlc_ty_arr1 tau ty /\ stlc_ty_arr2 tau body_ty))))))). Proof.
    intro. intro. generalize dependent gamma. destruct v.
    - intros. repeat econstructor; simp; my_inversion H0.
    - intros. repeat econstructor; simp; my_inversion H0.
    - intros. repeat econstructor; simp; my_inversion H0.
    - intros. destruct tau; repeat econstructor; simp; my_inversion H0; clear H0; my_inversion H; clear H; my_inversion H1. constructor.
Unshelve. all: repeat constructor.
Qed. Hint Resolve stlc_term_abs_typing_arr: core.

Lemma stlc_typing_app_tau_destruct : forall gamma, (forall v, (forall tau, (forall t1, (forall t2, ((typing gamma v tau /\ (stlc_app1 v t1 /\ stlc_app2 v t2)) -> (exists func_ty, (exists arg_ty, (stlc_ty_arr1 func_ty arg_ty /\ (stlc_ty_arr2 func_ty tau /\ (typing gamma t1 func_ty /\ typing gamma t2 arg_ty)))))))))). Proof.
    intros. simp. my_inversion H0; clear H0. my_inversion H1; clear H1. my_inversion H. repeat econstructor; eauto.
Qed. Hint Resolve stlc_typing_app_tau_destruct: core.

Lemma stlc_tyctx_cons : forall ty, (forall gamma, (exists v, (stlc_tyctx_hd v ty /\ stlc_tyctx_tl v gamma))). Proof.
    intros. destruct gamma.
    - repeat econstructor.
    - repeat econstructor.
 Qed. Hint Resolve stlc_tyctx_cons: core.

Lemma stlc_num_app_geq_0 : forall v, (forall n, (num_app v n -> 0 <= n)). Proof.
    intros. lia.
 Qed. Hint Resolve stlc_num_app_geq_0: core.

Lemma stlc_num_app_abs_body_eq : forall v, (forall body, (forall n, ((stlc_abs_body v body /\ num_app v n) -> num_app body n))). Proof.
    intros. simp. my_inversion H. my_inversion H0.
Qed. Hint Resolve stlc_num_app_abs_body_eq: core.

Lemma stlc_num_app_abs_body_eq_rev : forall v, (forall body, (forall n, ((stlc_abs_body v body /\ num_app body n) -> num_app v n))). Proof.
    intros. simp. my_inversion H. auto.
 Qed. Hint Resolve stlc_num_app_abs_body_eq_rev: core.

Lemma stlc_num_app_app_rev : forall v, (forall t1, (forall t2, (forall n, ((stlc_app1 v t1 /\ (stlc_app2 v t2 /\ num_app v n)) -> (exists m1, (exists m2, (num_app t1 m1 /\ (num_app t2 m2 /\ (m1 + m2) = (n - 1))))))))). Proof.
    intros. simp. my_inversion H1; clear H1.
    - my_inversion H0.
    - my_inversion H0.
    - my_inversion H0; clear H0. my_inversion H; clear H. exists n1. exists n2. split; auto. split; auto. lia.
    - my_inversion H0.
Qed. Hint Resolve stlc_num_app_app_rev: core.

(* TODO update STLC axioms *)
Lemma stlc_abd_typing_rev : forall gamma, (forall v, (forall tau, (forall ty, (forall body, (forall body_ty, (forall gamma1, ((typing gamma v tau /\ stlc_ty_arr1 tau ty /\ stlc_ty_arr2 tau body_ty /\ (stlc_abs_ty v ty /\ (stlc_abs_body v body /\ (stlc_tyctx_hd gamma1 ty /\ stlc_tyctx_tl gamma1 gamma)))) -> typing gamma1 body body_ty))))))). Proof.
    intros. simp. my_inversion H0; clear H0. my_inversion H1; clear H1. my_inversion H2; clear H2. my_inversion H4; clear H4. my_inversion H5; clear H5. my_inversion H3; clear H3. my_inversion H.
Qed. Hint Resolve stlc_abd_typing_rev: core.


Lemma stlc_const_typing_nat : forall gamma, (forall v, (forall tau, ((is_const v /\ typing gamma v tau) -> stlc_ty_nat tau))). Proof.
    intros. simp.
Qed. Hint Resolve stlc_const_typing_nat: core.

Lemma stlc_app_num_app_geq_0 : forall v, (forall n, ((is_app v /\ num_app v n) -> n > 0)). Proof.
    intros. simp. my_inversion H. my_inversion H0. lia.
 Qed. Hint Resolve stlc_app_num_app_geq_0: core.
