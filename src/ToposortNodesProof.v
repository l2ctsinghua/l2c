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
Require Import Errors.
Require Import Maps.
Require Import Integers.
Require Import List.
Require Import Permutation.
Require Import Lident.
Require Import Lustre.
Require Import LustreS.
Require Import Toposort.
Require Import ExtraList.
Require Import Ltypes.
Require Import Lvalues.
Require Import Lenv.
Require Import Lsem.
Require Import LsemT.
Require Import Toposort.

Section CORRECTNESS.

Variable prog1 prog2: program.
Variable gc: locenv.

Hypothesis TRANS:
  toposort_nodes_program prog1 = OK prog2.

Hypothesis GIDS_NOREPET:
  list_norepet (globidsof prog1).

Lemma toposort_nodes_program_globids_norepet:
  list_norepet (globidsof prog2).
Proof.
  apply list_norepet_permut with (globidsof prog1); auto.
  unfold globidsof. monadInv TRANS. simpl in *.
  apply Permutation_app. apply Permutation_refl.
  apply Permutation_map. apply toposort_nodes_permutation; auto.
Qed.

Lemma toposort_nodes_program_topo_sorted:
  topo_sorted (deps_of_nodes (node_block prog2)).
Proof.
  monadInv TRANS. simpl.
  apply nodes_toposorted in EQ.
  destruct EQ. auto.
Qed.

Lemma find_funct_match:
  forall id, find_funct (node_block prog1) id = find_funct (node_block prog2) id.
Proof.
  intros.
  eapply find_funct_permut; eauto.
  +monadInv TRANS. simpl.
   eapply toposort_nodes_permutation; eauto.
  +apply list_norepet_app in GIDS_NOREPET.
   destruct GIDS_NOREPET as [? [A ?]]. auto.
Qed.

Lemma trans_node_call_func:
  forall c fd, call_func (node_block prog1) c fd ->
  call_func (node_block prog2) c fd.
Proof.
  unfold call_func. intuition.
  rewrite <-find_funct_match; auto.
Qed.

Lemma eval_node_correct:
  forall e e' fd vargs vrets,
  eval_node true prog1 gc e e' fd vargs vrets ->
  eval_node true prog2 gc e e' fd vargs vrets.
Proof.
  intros until vrets.
  induction 1 using eval_node_ind2 with
  (P0:= fun nk te e te' e' ss =>
     eval_stmts true prog2 gc nk te e te' e' ss)
  (P1:= fun nk te e te' e' s ta1 ta2 =>
     eval_stmt true prog2 gc nk te e te' e' s ta1 ta2)
  (P2:= fun nk te e te' e' f ta1 ta2 =>
     eval_hstmt true prog2 gc nk te e te' e' f ta1 ta2)
  ( P3 := fun nk se se1 args atys vargs i cdef l rtys vrets =>
     eval_apply true prog2 gc nk se se1 args atys vargs i cdef l rtys vrets); simpl; intros;
  try (econstructor; eauto; fail).
  +apply eval_Sassign with v v'; auto.
   monadInv TRANS. simpl. auto.
  +eapply eval_Sfby_cycle_n; eauto.
  +eapply eval_Sfbyn_cycle_n; eauto.
  +eapply eval_Hmaptyeq; eauto. monadInv TRANS. simpl. auto.
  +eapply eval_Hboolred_false; eauto.
  +econstructor 1; eauto.
   eapply trans_node_call_func; eauto.
Qed.

Theorem exec_prog_correct_general:
  forall e main vass vrss n maxn,
  exec_prog prog1 gc (eval_node true) main e n maxn vass vrss ->
  exec_prog prog2 gc (eval_node true) main e n maxn vass vrss.
Proof.
  induction 1; intros.
  +constructor 1 with mrss; trivial.
  +apply eval_node_correct in H0; auto.
   constructor 2 with e'; auto.
Qed.

Lemma init_node_correct:
  forall e fd,
  init_node prog1 e fd ->
  init_node prog2 e fd.
Proof.
  intros until fd.
  induction 1 using init_node_ind2 with
  ( P0 := fun e1 e2 l =>
      init_stmt prog2 e1 e2 l
   ); intros.
 +(*init_node*)
  constructor 1; auto.
 +(*nil*)
  constructor.
 +(*cons*)
  constructor 2 with se1 fd ef; auto.
  eapply trans_node_call_func; eauto.
Qed.

Lemma initial_states_match:
  forall main e,
  initial_state prog1 gc init_node main e ->
  initial_state prog2 gc init_node main e.
Proof.
  intros. inv H.
  +constructor 1; simpl; auto.
   -monadInv TRANS. auto.
   -rewrite <-find_funct_match; auto.
    monadInv TRANS; auto.
   -apply init_node_correct; auto.
Qed.

Theorem trans_program_correct:
  forall e main vass vrss maxn,
  initial_state prog1 gc init_node main e->
  exec_prog prog1 gc (eval_node true) main e 1 maxn vass vrss ->
  initial_state prog2 gc init_node main e
    /\ exec_prog prog2 gc (eval_node true) main e 1 maxn vass vrss.
Proof.
  intros. split.
  apply initial_states_match; auto.
  apply exec_prog_correct_general; auto.
Qed.

End CORRECTNESS.
