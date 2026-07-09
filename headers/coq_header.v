From Stdlib Require Import ZArith Bool Lia.
Open Scope Z_scope.
Coercion is_true : bool >-> Sortclass.
Definition some_Z (x : Z) : option Z := Some x.
Coercion some_Z : Z >-> option.
Definition some_bool (x : bool) : option bool := Some x.
Coercion some_bool : bool >-> option.
Arguments some_Z /.
Arguments some_bool /.

Ltac spec_ihs :=
  repeat match goal with
  | [ IH : forall _ : Z, _ = _ -> _ |- _ ] => specialize (IH _ eq_refl)
  | [ IH : forall _ : bool, _ = _ -> _ |- _ ] => specialize (IH _ eq_refl)
  end.

(* Turn boolean comparisons/connectives into [Prop] so [lia] and [intuition] can use them. *)
Ltac reflect_bools :=
  try unfold is_true in *;
  repeat (rewrite Z.gtb_ltb in * || rewrite Z.geb_leb in *
       || rewrite Z.eqb_eq in *  || rewrite Z.eqb_neq in *
       || rewrite Z.ltb_lt in *  || rewrite Z.ltb_ge in *
       || rewrite Z.leb_le in *  || rewrite Z.leb_gt in *
       || rewrite Bool.eqb_true_iff in * || rewrite Bool.eqb_false_iff in *
       || rewrite Bool.andb_true_iff in * || rewrite Bool.andb_false_iff in *
       || rewrite Bool.orb_true_iff in *  || rewrite Bool.orb_false_iff in *
       || rewrite Bool.negb_true_iff in * || rewrite Bool.negb_false_iff in *).

Ltac leaf := try lia; try reflexivity; try congruence.

Ltac bsplit :=
  repeat match goal with
  | [ |- context[?e] ] =>
      lazymatch type of e with
      | bool => lazymatch e with true => fail | false => fail | _ => destruct e eqn:? end
      end
  end.

(* [cbn_noarith] unfolds measures/wrappers/recognizers but leaves [+]/[-]/[*]/unary-[-]
   folded: reducing [1 + m_impl t] through [Pos.succ] yields a raw positive-bit [match]
   (no head symbol) [lia]'s [zify] can't reflect, cutting the result off from the IH atom. *)
Ltac cbn_noarith := cbn -[Z.add Z.sub Z.mul Z.opp] in *.

Ltac solver :=
  repeat first
    [ progress cbn_noarith
    | progress intros | progress subst | progress spec_ihs
    | match goal with [ H : _ /\ _ |- _ ] => destruct H end
    | match goal with [ H : Some _ = Some _ |- _ ] => injection H as H end
    | match goal with [ |- _ /\ _ ] => split end
    | match goal with [ |- exists _, _ ] => eexists end
    | reflexivity
    | match goal with [ H : context[if ?b then _ else _] |- _ ] => destruct b eqn:? end
    | match goal with [ |- context[if ?b then _ else _] ] => destruct b eqn:? end
    | lia | congruence ];
  try (bsplit; cbn in *; reflect_bools; intuition leaf).

(* Induct on the datatype binder — that's where the measure recurses, so the IH is useful. *)
Ltac intro_and_induct :=
  lazymatch goal with
  | [ |- forall _ : Z, _ ]    => intro; intro_and_induct
  | [ |- forall _ : bool, _ ] => intro; intro_and_induct
  | [ |- forall _ : ?T, _ ]   =>
      lazymatch type of T with
      | Prop => idtac
      | _ => let x := fresh in intro x; induction x
      end
  | _ => idtac
  end.

Ltac dt_destruct :=
  match goal with
  | [ H : context[match ?e with _ => _ end] |- _ ] =>
      lazymatch type of e with bool => fail | Z => fail | option _ => fail | _ => destruct e eqn:? end
  | [ |- context[match ?e with _ => _ end] ] =>
      lazymatch type of e with bool => fail | Z => fail | option _ => fail | _ => destruct e eqn:? end
  end.

(* [autounfold] surfaces the datatype scrutinee left by the measure's inner [match]
   (emitter files recognizers/accessors into [axunfold]); [dt_destruct] then splits it,
   gated so non-nested axioms skip it. *)
Create HintDb axunfold.
Ltac nested_solver :=
  intro_and_induct;
  repeat (try solver; autounfold with axunfold in *; progress (try dt_destruct));
  solver.
Ltac prove_axiom := solve [ nested_solver ].
