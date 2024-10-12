

(* TODO Haven't touched yet *)

Lemma stlc_num_arr_geq_0 : forall tau, (forall n, (num_arr tau n -> n >= 0)). Proof. Qed. Hint Resolve stlc_num_arr_geq_0: core.

Lemma stlc_num_arr_arr : forall tau, (forall tau_body, (forall m, (stlc_ty_arr2 tau tau_body -> (num_arr tau_body (m - 1) <-> num_arr tau m)))). Proof. Qed. Hint Resolve stlc_num_arr_arr: core.

Lemma stlc_const_num_app_0 : forall v, (forall n, ((is_const v /\ num_app v n) -> n = 0)). Proof. Qed. Hint Resolve stlc_const_num_app_0: core.

Lemma stlc_var_num_app_0 : forall v, (forall n, ((is_var v /\ num_app v n) -> n = 0)). Proof. Qed. Hint Resolve stlc_var_num_app_0: core.

Lemma stlc_num_app_gt_0_is_abs_or_app : forall v, (forall n, ((num_app v n /\ n > 0) -> (is_abs v \/ is_app v))). Proof. Qed. Hint Resolve stlc_num_app_gt_0_is_abs_or_app: core.

Lemma stlc_typing_num_arr : forall gamma, (forall v, (forall tau, (exists n, (typing gamma v tau -> num_arr tau n)))). Proof. Qed. Hint Resolve stlc_typing_num_arr: core.

Lemma stlc_term_4_cases : forall v, (is_const v \/ (is_var v \/ (is_abs v \/ is_app v))). Proof. Qed. Hint Resolve stlc_term_4_cases: core.

Lemma stlc_term_disjoint1 : forall v, ~(is_const v /\ is_var v). Proof. Qed. Hint Resolve stlc_term_disjoint1: core.

Lemma stlc_term_disjoint2 : forall v, ~(is_const v /\ is_abs v). Proof. Qed. Hint Resolve stlc_term_disjoint2: core.

Lemma stlc_term_disjoint3 : forall v, ~(is_const v /\ is_app v). Proof. Qed. Hint Resolve stlc_term_disjoint3: core.

Lemma stlc_term_disjoint4 : forall v, ~(is_var v /\ is_abs v). Proof. Qed. Hint Resolve stlc_term_disjoint4: core.

Lemma stlc_term_disjoint5 : forall v, ~(is_var v /\ is_app v). Proof. Qed. Hint Resolve stlc_term_disjoint5: core.

Lemma stlc_term_disjoint6 : forall v, ~(is_abs v /\ is_app v). Proof. Qed. Hint Resolve stlc_term_disjoint6: core.

Lemma stlc_term_const_typing_nat : forall gamma, (forall v, (forall tau, ((is_const v /\ typing gamma v tau) -> stlc_ty_nat tau))). Proof. Qed. Hint Resolve stlc_term_const_typing_nat: core.

Lemma stlc_id_is_var : forall v, (forall id, (stlc_id v id -> is_var v)). Proof. Qed. Hint Resolve stlc_id_is_var: core.

Lemma stlc_const_is_const : forall v, (forall c, (stlc_const v c -> is_const v)). Proof. Qed. Hint Resolve stlc_const_is_const: core.

Lemma stlc_term_destruct1 : forall term, (exists c, (is_const term -> stlc_const term c)). Proof. Qed. Hint Resolve stlc_term_destruct1: core.

Lemma stlc_term_destruct2 : forall term, (exists c, (is_var term -> stlc_id term c)). Proof. Qed. Hint Resolve stlc_term_destruct2: core.

Lemma stlc_term_destruct3 : forall term, (exists t1, (exists t2, (is_app term -> (stlc_app1 term t1 /\ stlc_app2 term t2)))). Proof. Qed. Hint Resolve stlc_term_destruct3: core.

Lemma stlc_term_destruct4 : forall term, (exists ty, (exists body, (is_abs term -> (stlc_abs_ty term ty /\ stlc_abs_body term body)))). Proof. Qed. Hint Resolve stlc_term_destruct4: core.

Lemma stlc_term_abs_typing_arr : forall gamma, (forall v, (forall tau, (forall ty, (forall body, (exists body_ty, ((stlc_abs_ty v ty /\ (stlc_abs_body v body /\ typing gamma v tau)) -> (stlc_ty_arr1 tau ty /\ stlc_ty_arr2 tau body_ty))))))). Proof. Qed. Hint Resolve stlc_term_abs_typing_arr: core.

Lemma stlc_typing_app_tau_destruct : forall gamma, (forall v, (forall tau, (forall t1, (forall t2, ((typing gamma v tau /\ (stlc_app1 v t1 /\ stlc_app2 v t2)) -> (exists func_ty, (exists arg_ty, (stlc_ty_arr1 func_ty arg_ty /\ (stlc_ty_arr2 func_ty tau /\ (typing gamma t1 func_ty /\ typing gamma t2 arg_ty)))))))))). Proof. Qed. Hint Resolve stlc_typing_app_tau_destruct: core.

Lemma stlc_tyctx_cons : forall ty, (forall gamma, (exists v, (stlc_tyctx_hd v ty /\ stlc_tyctx_tl v gamma))). Proof. Qed. Hint Resolve stlc_tyctx_cons: core.

Lemma stlc_num_app_geq_0 : forall v, (forall n, (num_app v n -> 0 <= n)). Proof. Qed. Hint Resolve stlc_num_app_geq_0: core.

Lemma stlc_num_app_abs_body_eq : forall v, (forall body, (forall n, ((stlc_abs_body v body /\ num_app v n) -> num_app body n))). Proof. Qed. Hint Resolve stlc_num_app_abs_body_eq: core.

Lemma stlc_num_app_abs_body_eq_rev : forall v, (forall body, (forall n, ((stlc_abs_body v body /\ num_app body n) -> num_app v n))). Proof. Qed. Hint Resolve stlc_num_app_abs_body_eq_rev: core.

Lemma stlc_num_app_app_rev : forall v, (forall t1, (forall t2, (forall n, ((stlc_app1 v t1 /\ (stlc_app2 v t2 /\ num_app v n)) -> (exists m1, (exists m2, (num_app t1 m1 /\ (num_app t2 m2 /\ (m1 + m2) = (n - 1))))))))). Proof. Qed. Hint Resolve stlc_num_app_app_rev: core.

Lemma stlc_abd_typing_rev : forall gamma, (forall v, (forall tau, (forall ty, (forall body, (forall body_ty, (forall gamma1, ((typing gamma v tau /\ (stlc_abs_ty v ty /\ (stlc_abs_body v body /\ (stlc_tyctx_hd gamma1 ty /\ stlc_tyctx_tl gamma1 gamma)))) -> typing gamma1 body body_ty))))))). Proof. Qed. Hint Resolve stlc_abd_typing_rev: core.

Lemma stlc_const_typing_nat : forall gamma, (forall v, (forall tau, ((is_const v /\ typing gamma v tau) -> stlc_ty_nat tau))). Proof. Qed. Hint Resolve stlc_const_typing_nat: core.

Lemma stlc_const_num_app_0 : forall v, (forall n, ((is_const v /\ num_app v n) -> n = 0)). Proof. Qed. Hint Resolve stlc_const_num_app_0: core.

Lemma stlc_app_num_app_geq_0 : forall v, (forall n, ((is_app v /\ num_app v n) -> n > 0)). Proof. Qed. Hint Resolve stlc_app_num_app_geq_0: core.
