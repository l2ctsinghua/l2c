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
  toposort_stmts_program prog1 = OK prog2.

Lemma toposort_stmts_program_globids:
  globidsof prog2 = globidsof prog1.
Proof.
  intros.
  unfold globidsof. monadInv TRANS. simpl in *.
  f_equal. symmetry.
  apply trans_nodes_fids_eq with trans_node_block; eauto.
  intros. monadInv H. auto.
Qed.

Lemma trans_nodes_blocks_depends_match:
  forall l1 l2,
  mmap trans_node_block l1 = OK l2 ->
  depends_match (deps_of_nodes_simpl l1) (deps_of_nodes_simpl l2).
Proof.
  induction l1; simpl; intros.
  +inv H. simpl. constructor.
  +monadInv H. simpl. constructor; auto.
   -monadInv EQ. monadInv EQ0. split; simpl; auto.
    apply flat_map_permutation.
    apply toposort_stmts_permutation; auto.
   -apply IHl1; auto.
Qed.

Lemma toposort_stmts_nodes_topo_sorted:
  topo_sorted (deps_of_nodes (node_block prog1)) ->
  topo_sorted (deps_of_nodes (node_block prog2)).
Proof.
  intros. apply topo_sorted_nodes_simpl in H.
  apply topo_sorted_nodes_simpl.
  eapply depends_match_toposorted; eauto.
  monadInv TRANS. simpl.
  apply trans_nodes_blocks_depends_match; auto.
Qed.

Lemma find_funct_match:
  forall id main1,
  find_funct (node_block prog1) id = Some main1 ->
  exists main2, find_funct (node_block prog2) id = Some main2
    /\ trans_node_block main1 = OK main2.
Proof.
  intros. monadInv TRANS. simpl.
  eapply find_funcs_monad_exits in H; eauto.
  destruct H as [fd2 [? ?]].
  exists fd2. split; auto.
  intros. monadInv H0; auto.
Qed.

Lemma trans_node_call_func:
  forall c fd1,
  call_func (node_block prog1) c fd1 ->
  exists fd2, call_func (node_block prog2) c fd2
    /\ trans_node_block fd1 = OK fd2.
Proof.
  unfold call_func. intuition.
  destruct find_funct_match with (callid c) fd1 as [fd2 [? ?]]; auto.
  exists fd2. intuition.
  monadInv H6. monadInv EQ. auto.
  monadInv H6. monadInv EQ. auto.
  monadInv H6. monadInv EQ. auto.
Qed.

Lemma toposort_node_ids_norepet:
  forall f f',
  ids_norepet f ->
  toposort_node f = OK f' ->
  ids_norepet f'.
Proof.
  unfold ids_norepet, allidsof, allvarsof, predidof.
  intros. monadInv H0. simpl in *.
  apply toposort_stmts_permutation in EQ. intuition.
  +eapply list_norepet_permut; eauto.
   apply Permutation_app; apply Permutation_map; apply flat_map_permutation; auto.
  +red; intros. apply H1; auto.
   apply in_app_or in H4. apply Permutation_sym in EQ; auto.
   destruct H4; apply in_or_app; [left | right].
   -apply Permutation_in with (map fst (fbyvarsof x)); auto.
    apply Permutation_map. apply flat_map_permutation; auto.
   -apply Permutation_in with (map instid (instidof x)); auto.
    apply Permutation_map. apply flat_map_permutation; auto.
  +apply H3; auto. eapply Permutation_in in H2; eauto.
   apply Permutation_map. apply flat_map_permutation; auto.
   apply Permutation_sym; auto.
Qed.

Lemma toposort_stmts_program_topo_sorted:
  forall fd,
  In fd (node_block prog2) ->
  topo_sorted (deps_of_stmts (nd_stmt (snd fd))).
Proof.
  intros. monadInv TRANS. simpl in *.
  eapply in_mmap_iff in EQ; eauto.
  destruct EQ as [fd' [? ?]].
  monadInv H0. monadInv EQ. simpl in *.
  apply eqs_toposorted in EQ0.
  destruct EQ0; auto.
Qed.

Lemma eval_toposorted_stmts_correct:
  forall nid nk te1 te2 e1 e2 ss f,
  ids_norepet f ->
  stmts_topo_match (nd_stmt f) ss ->
  In (nid, f) (node_block prog2) ->
  topo_sorted (deps_of_stmts_simpl (nd_stmt f)) ->
  eval_stmts true prog2 gc nk te1 e1 te2 e2 ss ->
  eval_stmts true prog2 gc nk te1 e1 te2 e2 (nd_stmt f).
Proof.
  intros. destruct H0 as [A [A1 A2]].
  apply eval_index_stmts_correct with ss; eauto.
  +eapply topo_sorted_eqs_simpl; eauto.
  +apply Permutation_sym; auto.
  +eapply ids_norepet_instid_permut; eauto.
  +constructor.
   -eapply ids_norepet_fbyids_flagid_notin; eauto.
   -eapply ids_norepet_fbyids_norepet_permut; eauto.
Qed.

Lemma toposort_node_stmts_topo_match1:
  forall f f' ss,
  stmts_topo_match (nd_stmt f) ss ->
  toposort_node f = OK f' ->
  stmts_topo_match (nd_stmt f') ss.
Proof.
  unfold stmts_topo_match. intuition.
  apply Permutation_trans with (nd_stmt f); auto.
  apply Permutation_sym.
  monadInv H0. simpl.
  apply toposort_stmts_permutation; auto.
Qed.

Lemma toposort_node_stmts_topo_match2:
  forall f f' ss,
  stmts_topo_match (nd_stmt f) ss ->
  toposort_node f = OK f' ->
  stmts_topo_match (nd_stmt f') (nd_stmt f').
Proof.
  intros. repeat (split; auto).
  +monadInv H0. simpl.
   apply eqs_toposorted in EQ.
   destruct EQ; auto.
  +destruct H as [? [? ?]].
   apply nodup_lids_perm with (deps_of_stmts_simpl ss); auto.
   apply Permutation_map.
   apply Permutation_trans with (nd_stmt f).
   apply Permutation_sym; auto.
   monadInv H0. apply toposort_stmts_permutation; auto.
Qed.

Lemma eval_node_correct:
  forall e e' fd1 vargs vrets,
  eval_node true prog1 gc e e' fd1 vargs vrets ->
  forall fd2, trans_node_block fd1 = OK fd2 ->
  find_funct (node_block prog1) (fst fd1) = Some fd1 ->
  eval_node true prog2 gc e e' fd2 vargs vrets.
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
  +monadInv H7. simpl in *.
   apply exec_node with te te1 te2 eh1 (nd_stmt x); auto.
   -monadInv EQ. auto.
   -apply toposort_node_ids_norepet with f; auto.
   -monadInv EQ. auto.
   -eapply toposort_node_stmts_topo_match2; eauto.
   -apply eval_toposorted_stmts_correct with nid ss; auto.
    *eapply toposort_node_ids_norepet; eauto.
    *eapply toposort_node_stmts_topo_match1; eauto.
    *destruct find_funct_match with nid (nid,f) as [f' [? ?]]; auto.
     unfold trans_node_block in *. simpl in *. rewrite EQ in *.
     simpl in *. inv H9. apply find_funct_in2 with nid; auto.
    *apply topo_sorted_eqs_simpl.
     monadInv EQ. simpl.
     apply eqs_toposorted in EQ0.
     destruct EQ0; auto.
    *monadInv EQ; auto.
   -destruct H2 as [A [A1 A2]].
    apply eval_poststmt_permut with ss; auto.
    *apply Permutation_trans with (nd_stmt f).
     apply Permutation_sym; auto.
     monadInv EQ. apply toposort_stmts_permutation; auto.
    *apply list_norepet_permut with (map fst (fbyvarsof (nd_stmt f))); auto.
     apply ids_norepet_fbyids_norepet; auto.
     apply Permutation_map.
     apply flat_map_permutation; auto.
   -monadInv EQ. auto.
   -monadInv EQ. auto.
  +apply eval_Sassign with v v'; auto.
   monadInv TRANS. simpl. auto.
  +eapply eval_Sfby_cycle_n; eauto.
  +eapply eval_Sfbyn_cycle_n; eauto.
  +eapply eval_Hmaptyeq; eauto. monadInv TRANS. simpl. auto.
  +eapply eval_Hboolred_false; eauto.
  +destruct trans_node_call_func with cdef fd as [fd' [? ?]]; auto.
   constructor 1 with fd' ef ef' vargs'; auto.
   -monadInv H10. monadInv EQ. auto.
   -monadInv H10. monadInv EQ. auto.
   -monadInv H10. monadInv EQ. auto.
   -apply IHeval_node; auto.
    destruct H0.
    apply find_funct_eq with (callid cdef); auto.
Qed.

Theorem exec_prog_correct_general:
  forall e main1 vass vrss n maxn,
  exec_prog prog1 gc (eval_node true) main1 e n maxn vass vrss ->
  forall main2, trans_node_block main1 = OK main2 ->
  find_funct (node_block prog1) (fst main1) = Some main1 ->
  exec_prog prog2 gc (eval_node true) main2 e n maxn vass vrss.
Proof.
  induction 1; intros.
  +constructor 1 with mrss; trivial.
   monadInv H1. monadInv EQ; auto.
  +constructor 2 with e'; auto.
   -apply eval_node_correct with main1; auto.
Qed.

Lemma init_node_correct:
  forall e fd1,
  init_node prog1 e fd1 ->
  forall fd2,
  trans_node_block fd1 = OK fd2 ->
  init_node prog2 e fd2.
Proof.
  intros until fd1.
  induction 1 using init_node_ind2 with
  ( P0 := fun nk e1 e2 l1 =>
      init_stmt prog2 nk e1 e2 l1
   ); intros.
 +(*init_node*)
  monadInv H3. simpl in *. constructor 1; auto.
  -apply toposort_node_ids_norepet with f; auto.
  -apply eval_init_permut with (nd_stmt f); auto.
   monadInv EQ. simpl.
   eapply toposort_stmts_permutation; eauto.
   eapply ids_norepet_fbyids_norepet; eauto.
  -intros. apply H1. monadInv EQ; simpl in *.
   apply Permutation_in with (map snd (nd_rets f ++ fbyvarsof x0)); auto.
   apply Permutation_map. apply Permutation_app.
   apply Permutation_refl.
   apply flat_map_permutation. apply Permutation_sym.
   eapply toposort_stmts_permutation; eauto.
  -apply alloc_index_stmt_correct with (instidof (nd_stmt f)); auto.
   *apply flat_map_permutation.
    monadInv EQ. simpl.
    eapply toposort_stmts_permutation; eauto.
   *monadInv EQ; auto.
   *eapply ids_norepet_instid; eauto.
 +(*nil*)
  constructor.
 +(*cons*)
  destruct trans_node_call_func with c fd as [fd' [? ?]]; auto.
  constructor 2 with se1 fd' ef; auto.
  monadInv H5. monadInv EQ; simpl; auto.
Qed.

Lemma initial_states_match:
  forall main1 e,
  initial_state prog1 gc init_node main1 e ->
  exists main2, initial_state prog2 gc init_node main2 e
    /\ trans_node_block main1 = OK main2.
Proof.
  intros. inv H.
  +destruct find_funct_match with (node_main prog1) main1 as [main2 [? ?]]; auto.
   exists main2. split; auto.
   constructor 1; simpl; auto.
   -monadInv TRANS. auto.
   -monadInv TRANS; auto.
   -apply init_node_correct with main1; auto.
Qed.

Theorem trans_program_correct:
  forall e main1 vass vrss maxn,
  initial_state prog1 gc init_node main1 e->
  exec_prog prog1 gc (eval_node true) main1 e 1 maxn vass vrss ->
  exists main2, initial_state prog2 gc init_node main2 e
    /\ exec_prog prog2 gc (eval_node true) main2 e 1 maxn vass vrss
    /\ nd_rets (snd main1) = nd_rets (snd main2)
    /\ nd_args (snd main1) = nd_args (snd main2).
Proof.
  intros.
  destruct initial_states_match with main1 e as [main2 [? ?]]; auto.
  exists main2; intuition.
  apply exec_prog_correct_general with main1; auto.
  inv H; eapply find_funct_eq; eauto.
  monadInv H2. monadInv EQ; auto.
  monadInv H2. monadInv EQ; auto.
Qed.

End CORRECTNESS.
