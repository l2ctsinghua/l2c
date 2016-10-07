(* *********************************************************************)
(*                                                                     *)
(*              The L2C verified compiler                              *)
(*                                                                     *)
(*            L2C Group, Tsinghua University                           *)
(*                                                                     *)
(*  Copyright Tsinghua University.  All rights reserved.  This file is *)
(*  distributed under the terms of the GNU General Public License as   *)
(*  published by the Free Software Foundation, either version 2 of the *)
(*  License, or (at your option) any later version.  This file is also *)
(*  distributed under the terms of the INRIA Non-Commercial License    *)
(*  Agreement.                                                         *)
(*                                                                     *)
(* *********************************************************************)

Require Import Coqlib.
Require Import AST.
Require Import Integers.
Require Import Cltypes.
Require Import List.
Require Import Permutation.
Require Import Lvalues.
Require Import Lident.
Require Import Lustre.
Require Import LustreS.
Require Import Lenv.
Require Import Lsem.
Require Import Lenvmatch.
Require Import LsemT.

Section CORRECTNESS.

Variable semkind: bool.
Variable p: program.
Variable gc: locenv.

Lemma eval_expr_determ:
  forall te a ty v1,
  eval_expr gc (type_block p) te a ty v1 ->
  forall v2, eval_expr gc (type_block p) te a ty v2 ->
  v1 = v2.
Proof.
  induction 1; intros.
  +inv H1. eapply eval_sexp_determ; eauto.
  +inv H4; eapply eval_sexps_determ in H0; eauto; inv H0.
   eapply eval_sexp_determ in H; eauto. inv H.
   rewrite H14 in H2. inv H2. eapply load_mvl_determ; eauto.
   congruence.
  +inv H4; eapply eval_sexps_determ in H; eauto; inv H.
   congruence.
   eapply eval_sexp_determ; eauto.
  +inv H3. eapply eval_sexp_determ in H; eauto. inv H.
   rewrite H7 in H0. inv H0. eapply eval_sexp_determ; eauto.
  +inv H5. eapply eval_sexp_determ in H; eauto. subst.
   rewrite H11 in H1. inv H1. eapply eval_sexp_determ; eauto.
  +inv H3. eapply eval_sexps_determ in H; eauto. inv H.
   congruence.
  +inv H0. eapply eval_typecmp_determ in H; eauto. subst. auto.
Qed.

Lemma store_loop_determ:
  forall t ta id v ta1,
  store_loop t ta id v ta1 ->
  forall ta2, store_loop t ta id v ta2 ->
  ta1 = ta2.
Proof.
  intros. inv H. inv H0.
  eapply eval_cast_determ in H1; eauto. subst.
  eapply store_mvl_determ in H2; eauto.
  subst; auto.
Qed.

Lemma eval_node_determ:
  forall e e1' fd vargs vrets1,
  eval_node semkind p gc e e1' fd vargs vrets1->
  forall e2' vrets2,
  eval_node semkind p gc e e2' fd vargs vrets2 ->
  e1' = e2' /\ vrets1 = vrets2.
Proof.
  intros until vrets1.
  induction 1 using eval_node_ind2 with
  (P0:= fun nk te e te1' e1' ss =>
     forall te2' e2',
     eval_stmts semkind p gc nk te e te2' e2' ss ->
     te1' = te2' /\ e1' = e2')
  (P1:= fun nk te e te1' e1' s ta1 ta2=>
     forall te2' e2' ta3,
     eval_stmt semkind p gc nk te e te2' e2' s ta1 ta3 ->
     te1' = te2' /\ e1' = e2' /\ ta2 = ta3)
  (P2:= fun nk te e te1' e1' f ta1 ta2 =>
     forall te2' e2' ta3,
     eval_hstmt semkind p gc nk te e te2' e2' f ta1 ta3 ->
     te1' = te2' /\ e1' = e2' /\ ta2 = ta3)
  ( P3 := fun nk te se se1 args atys vargs i cdef lhs rtys1 vrets1 =>
     forall se2 rtys2 vrets2,
     eval_apply semkind p gc nk te se se2 args atys vargs i cdef lhs rtys2 vrets2 ->
     se1 = se2 /\ rtys1 = rtys2 /\ vrets1 = vrets2); intros.
  +inversion_clear H7.
   eapply alloc_variables_determ in H; eauto. subst.
   eapply locenv_setvars_determ in H1; eauto. subst.
   destruct semkind.
   -destruct H2 as [? [? ?]]. destruct H11 as [? [? ?]].
    apply eval_index_stmts_correct with (eql2:=ss) in H12; eauto.
    *apply IHeval_node in H12; auto. destruct H12. inv H17.
     apply eval_poststmt_permut with (l2:=ss0) in H4; eauto.
     eapply eval_poststmt_determ in H13; eauto. subst eh3.
     eapply locenv_getvars_determ in H14; eauto.
     apply Permutation_trans with (nd_stmt f); auto. apply Permutation_sym; auto.
     eapply ids_norepet_fbyids_norepet_permut; eauto.
    *eapply topo_sorted_eqs_simpl; eauto.
    *apply Permutation_trans with (nd_stmt f); auto. apply Permutation_sym; auto.
    *eapply topo_sorted_eqs_simpl; eauto.
    *eapply ids_norepet_instid_permut; eauto.
    *constructor.
     eapply ids_norepet_fbyids_flagid_notin; eauto.
     eapply ids_norepet_fbyids_norepet_permut; eauto.
   -subst. eapply IHeval_node in H12; eauto.
    destruct H12. inv H1.
    eapply eval_poststmt_determ in H13; eauto. subst.
    eapply locenv_getvars_determ in H14; eauto.
  +inv H; auto.
  +inversion_clear H1. destruct IHeval_node with te3 e3 ta0 as [? [? ?]]; auto. subst; auto.
  +inversion_clear H3. repeat (split; auto).
   eapply eval_expr_determ in H; eauto. subst.
   eapply eval_cast_determ in H1; eauto. subst.
   eapply locenv_setlvar_determ; eauto.
  +inversion_clear H2. eapply eval_sexps_determ in H; eauto. subst.
   eapply IHeval_node in H4; eauto. destruct H4 as [? [? ?]]; subst.
   eapply locenv_setvars_determ in H1; eauto.
  +inversion_clear H2. eapply IHeval_node in H3;eauto. destruct H3. subst.
   eapply store_loop_determ in H0; eauto. subst. auto.
  +inversion_clear H0; auto. eapply eval_sexp_determ in H; eauto. inv H.
  +inv H3. eapply eval_sexp_determ in H13; eauto. inv H13.
   eapply IHeval_node in H7; eauto. destruct H7 as [? [? ?]]; subst.
   eapply eval_eqf_determ in H13; eauto. subst. auto.
  +inv H. auto.
  +inv H5. eapply eval_sexp_determ in H; eauto. subst.
   eapply eval_cast_determ in H2; eauto. subst.
   eapply locenv_setlvar_determ in H3; eauto. subst. auto.
  +inv H5. eapply eval_lindexs_determ in H; eauto. subst.
   eapply eval_sexp_determ in H0; eauto. subst.
   eapply IHeval_node in H20; eauto. destruct H20 as [? [? ?]].
   subst. eapply eval_cast_determ in H2; eauto. subst.
   eapply store_env_determ in H22; eauto.
  +inv H. auto.
  +inv H5. eapply eval_sexp_determ in H; eauto. subst.
   eapply eval_cast_determ in H0; eauto. subst.
   eapply locenv_setlvar_determ in H1; eauto. subst. auto.
  +inv H; auto.
  +inv H5. eapply eval_sexp_determ in H0; eauto. subst.
   eapply eval_cast_determ in H3; eauto. subst.
   eapply locenv_setlvar_determ in H4; eauto.
   eapply eval_sexp_determ in H; eauto. inv H.
  +inv H5. eapply eval_sexp_determ in H; eauto. inv H.
   eapply eval_sexp_determ in H0; eauto. subst.
   eapply eval_cast_determ in H2; eauto. subst.
   eapply locenv_setlvar_determ in H3; eauto.
  +inv H11. eapply eval_sexp_determ in H2; eauto. subst.
   eapply eval_fbyn_init_determ in H3; eauto. subst.
   eapply eval_eqf_determ in H4; eauto. subst.
   eapply eval_sexp_determ in H5; eauto. subst.
   eapply eval_cast_determ in H8; eauto. subst.
   eapply locenv_setlvar_determ in H9; eauto.
   eapply eval_sexp_determ in H1; eauto. inv H1.
  +inv H8. eapply eval_sexp_determ in H1; eauto. inv H1.
   eapply eval_sexp_determ in H26; eauto. subst.
   eapply eval_cast_determ in H29; eauto. subst.
   eapply locenv_setlvar_determ in H30; eauto.
  +inv H2. eapply eval_sexp_determ in H; eauto. subst.
   rewrite H14 in H0. inv H0. auto.
  +inv H3. eapply eval_sexp_determ in H17; eauto. inv H17.
   rewrite H18 in H0. inv H0.
   eapply eval_typecmp_determ in H1; eauto. subst.
   eapply locenv_setlvar_determ in H2; eauto.
  +inv H3. eapply eval_sexp_determ in H18; eauto. inv H18.
   eapply eval_sexp_determ in H19; eauto. subst.
   eapply eval_cast_determ in H20; eauto. subst.
   eapply locenv_setlvar_determ in H21; eauto.
  +inv H6. eapply eval_sexp_determ in H13; eauto. inv H13.
   rewrite H19 in H0. inv H0.
   eapply eval_sexp_determ in H3; eauto. subst.
   eapply eval_cast_determ in H4; eauto. subst.
   eapply locenv_setlvar_determ in H5; eauto.
  +inv H1. eapply eval_sexp_determ in H14; eauto. inv H14.
   eapply eval_eqf_determ in H0; eauto.
  +inv H0. eapply eval_eqf_determ in H; eauto.
  +inv H0. eapply eval_eqf_determ in H; eauto.
  +inv H5. eapply eval_sexp_determ in H11; eauto. inv H11.
   eapply eval_sexp_determ in H0; eauto. subst.
   eapply eval_cast_determ in H3; eauto. subst.
   eapply locenv_setlvar_determ in H4; eauto.
  +inv H4. eapply eval_sexp_determ in H18; eauto. inv H18.
   eapply eval_sexp_determ in H20; eauto. subst.
   eapply eval_cast_determ in H21; eauto. subst.
   eapply locenv_setlvar_determ in H22; eauto.
  +inv H2. eapply eval_eqf_determ in H14; eauto.
   eapply eval_sexp_determ in H10; eauto. inv H10.
   eapply eval_sexp_determ in H13; eauto. inv H13.
  +inv H1; auto. eapply eval_sexp_determ in H4; eauto. inv H4.
   eapply eval_sexp_determ in H10; eauto. inv H10.
  +inv H4. eapply eval_sexps_determ in H0; eauto. subst.
   eapply eval_sexp_determ in H12; eauto. inv H12.
   eapply locenv_getarys_determ in H18; eauto. destruct H18; subst.
   eapply IHeval_node in H19; eauto. destruct H19 as [? [? ?]].
   subst. eapply locenv_setarys_determ in H20; eauto.
  +inv H7. eapply eval_sexp_determ in H24; eauto. inv H24.
   eapply IHeval_node in H25; eauto. destruct H25. subst.
   eapply eval_sexp_determ in H26; eauto. subst.
   eapply eval_sexps_determ in H27; eauto. subst.
   eapply locenv_getarys_determ in H28; eauto. destruct H28; subst.
   eapply IHeval_node0 in H29; eauto. destruct H29 as [? [? ?]]. inv H9. inv H10.
   eapply locenv_setlvar_determ in H30; eauto. subst.
   eapply locenv_setarys_determ in H31; eauto.
  +inv H9. destruct H0, H11. rewrite H2 in H0. inv H0.
   assert(A: ef = ef0).
     eapply call_env_determ1; eauto.
   subst.
   eapply eval_casts_determ in H3; eauto. subst.
   eapply IHeval_node in H16; eauto. destruct H16; subst.
  eapply call_env_determ2 in H15; eauto.
Qed.

End CORRECTNESS.