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

(** Correctness proof for translation of reset functions. *)

Require Import Coqlib.
Require Import AST.
Require Import Errors.
Require Import Maps.
Require Import Integers.
Require Import Inclusion.
Require Import List.
Require Import Cltypes.
Require Import ExtraList.
Require Import Lident.
Require Import Lustre.
Require Import LustreF.
Require Import Lint.
Require Import Lvalues.
Require Import Ltypes.
Require Import Lenv.
Require Import Lenvmatch.
Require Import Lsem.
Require Import LsemF.
Require Import LsemD.
Require Import LsemE.
Require Import ResetfuncGen.

Section CORRECTNESS.

Variable prog1: program.
Variable prog2: program.

Hypothesis TRANS:
  trans_program prog1 = OK prog2.

Hypothesis GID_NOREPET:
  list_norepet (globidsof prog1).

Section NODE_CORRECT.

Hypothesis GID_RANGE:
  ids_plt ACG_EQU (map fst (const_block prog1)).

Lemma prog2_nodeids_norepet:
  list_norepet (map fst (node_block prog2)).
Proof.
  apply trans_program_gids_norepet with (p':=prog2) in GID_NOREPET; auto.
  apply list_norepet_app in GID_NOREPET.
  destruct GID_NOREPET as [? [? ?]]. auto.
Qed.

Lemma find_node:
  forall fid fd,
  list_norepet (map fst (node_block prog2)) ->
  find_funct (node_block prog1) fid = Some fd ->
  find_funct (node_block prog2) fid = Some fd.
Proof.
  unfold trans_program in *.
  destruct (list_in_list _ _); inv TRANS. simpl.
  destruct prog1; simpl; intros.
  rewrite map_app in H. apply list_norepet_app in H.
  destruct H as [? [? ?]].
  rewrite find_funct_app_notin_right; auto.
  red. intros. red in H2. red in H2.
  generalize H0; intros.
  apply find_funct_fid in H4. subst.
  apply find_funct_in2 in H0.
  apply in_map with (B:=ident) (f:=(fst (B:=func))) in H0.
  eapply H2; eauto.
Qed.

Lemma call_node_correct:
  forall nid cdef nd fd,
  list_norepet (map fst (node_block prog2)) ->
  call_node (node_block prog1) nid cdef nd fd ->
  call_node (node_block prog2) nid cdef nd fd.
Proof.
  unfold call_node,call_func.
  intuition; apply find_node; auto.
Qed.

Lemma call_func_correct:
  forall cdef fd,
  list_norepet (map fst (node_block prog2)) ->
  Lustre.call_func (node_block prog1) cdef fd ->
  Lustre.call_func (node_block prog2) cdef fd.
Proof.
  unfold Lustre.call_func.
  intuition; apply find_node; auto.
Qed.

Lemma trans_node_all_correct:
  forall gc e e' node vargs vrets,
  eval_node prog1 gc e e' node vargs vrets ->
  eval_node prog2 gc e e' node vargs vrets.
Proof.
  intros gc.
  induction 1 using eval_node_ind2 with
  ( P0 := fun nid te e te' e' s =>
      eval_stmt prog2 gc nid te e te' e' s);
   simpl; intros; try (econstructor; eauto; fail).
  +(*eval_Scall_node*)
   apply eval_Scall with ef ef' fd nd vargs vargs' vrets i; auto.
   apply call_node_correct; auto.
   apply prog2_nodeids_norepet.
  +(*eval_Scall_func*)
   apply eval_Fcall with ef ef' vl fd vargs vargs' vrets; auto.
   apply call_func_correct; auto.
   apply prog2_nodeids_norepet.
Qed.

Lemma trans_init_body_svars_fld_match:
  forall f fld,
  svars_fld_match (svarsof f) fld ->
  svars_fld_match (svarsof (trans_init_body f)) fld.
Proof.
  unfold svarsof, trans_init_body. simpl.
  intros. auto. red. red in H. intros.
  apply H. apply in_or_app; auto.
Qed.

Lemma trans_init_nodes_find:
  forall l fid fd,
  find_funct l fid = Some fd ->
  nd_kind (snd fd) = true ->
  find_funct (flat_map trans_init_nodes l) (reset_id fid) = Some (trans_init_node fd).
Proof.
  induction l; simpl; intros.
  +congruence.
  +unfold trans_init_nodes at 1.
   destruct (identeq _ _) eqn:?.
   -inv H. unfold func in *. rewrite H0. simpl.
    unfold reset_id. rewrite identeq_shift.
    unfold func in *. rewrite Heqb; auto.
   -unfold func in *. destruct (nd_kind (snd a)); simpl; auto.
    unfold reset_id. unfold func in *.
    rewrite identeq_shift, Heqb; auto.
    apply IHl; auto.
Qed.

Lemma find_reset_node:
  forall fid fd,
  find_funct (node_block prog1) fid = Some fd ->
  nd_kind (snd fd) = true ->
  find_funct (node_block prog2) (reset_id fid) = Some (trans_init_node fd).
Proof.
  unfold trans_program in *.
  destruct (list_in_list _ _); inv TRANS.
  simpl. intros.
  apply find_funct_app.
  apply trans_init_nodes_find; auto.
Qed.

Lemma trans_call_node:
  forall nid c nd fd,
  call_node (node_block prog1) nid c nd fd ->
  nd_kind (snd fd) = true ->
  call_node (node_block prog2) (reset_id nid) (trans_calldef c) (trans_init_node nd) (trans_init_node fd).
Proof.
  unfold call_node,call_func.
  intuition; simpl; apply find_reset_node; auto.
  rewrite H0 in *. apply callorder_true; auto.
Qed.

Lemma alloc_node_correct:
  forall e main,
  alloc_node prog1 e main ->
  alloc_node prog2 e main.
Proof.
  intros until main.
  induction 1 using alloc_node_ind2 with
  ( P0 := fun nid e e' l =>
       alloc_stmt prog2 nid e e' l
   ); simpl; intros; eauto.
 +(*node*)
  constructor; simpl; auto.
 +(*nil*)
  constructor.
 +(*cons*)
  constructor 2 with se1 nd fd ef; auto.
  apply call_node_correct; auto.
  apply prog2_nodeids_norepet.
Qed.

Lemma alloc_variables_loopid_range_perm:
  forall l te, alloc_variables empty_locenv (mkloopid l) te ->
  locenv_range_perm_vars te (mkloopid l).
Proof.
  intros.
  destruct mkloopid_range with l; rewrite H0 in *.
  eapply alloc_variables_range_perm; simpl; eauto.
  constructor; auto. constructor.
  intros. destruct H1; inv H1. simpl.
  unfold Int.max_signed. simpl. omega.
  red; simpl; intros. tauto.
Qed.

Lemma eval_loop_init:
  forall gc e e1 m,
  store_env type_int32s e ACG_I Int.zero (Vint Int.zero) e1 ->
  e ! ACG_I = Some (m, type_int32s) ->
  forall eh, eval_eqf gc e eh e1 eh loop_init.
Proof.
  intros.
  constructor 1 with (Vint Int.zero) (Vint Int.zero); auto.
  constructor; simpl; auto.
  constructor 1 with Mint32; auto.
  constructor 1 with Mint32; auto.
  constructor 1 with ACG_I Int.zero; auto.
  constructor 1 with m; auto.
Qed.

Definition mkarrayenv(e1 e2: env)(i j: nat): list env :=
  list_repeat i e2 ++ list_repeat (j - i) e1.

Lemma mkarrayenv_length:
  forall ef ef' i j, (i <= j)%nat ->
  length (mkarrayenv ef ef' i j) = j.
Proof.
  unfold mkarrayenv. intros.
  rewrite app_length. repeat rewrite length_list_repeat.
  omega.
Qed.

Lemma eval_loop_cond_false:
  forall gc te eh i,
  eval_sexp gc te eh (Svar ACG_I type_int32s) (Vint i) ->
  eval_sexp gc te eh (loop_cond i) Vfalse.
Proof.
  intros. unfold loop_cond.
  apply eval_Sbinop with (Vint i) (Vint i); simpl; auto.
  constructor; simpl; auto.
  unfold Int.lt. destruct (zlt _ _); try omega. auto.
Qed.

Lemma eval_loop_cond_true:
  forall gc te eh i j,
  Lsem.eval_sexp gc te (Svar ACG_I type_int32s) (Vint i) ->
  Int.unsigned i < Int.unsigned j <= Int.max_signed ->
  eval_sexp gc te eh (loop_cond j) Vtrue.
Proof.
  intros. unfold loop_cond.
  apply eval_Sbinop with (Vint i) (Vint j); simpl; auto.
  eapply eval_sexp_sexp; eauto.
  constructor; simpl; auto.
  unfold Int.lt,zlt. repeat rewrite Int.signed_eq_unsigned; try omega.
  destruct (Z_lt_dec _ _); try omega; auto.
Qed.

Lemma eval_eqf_loop_add:
  forall gc te te' eh i m,
  eval_sexp gc te eh (Svar ACG_I type_int32s) (Vint (int_of_nat i)) ->
  (i + 1 <= nat_of_Z Int.max_signed)%nat ->
  store_env type_int32s te ACG_I Int.zero (Vint (int_of_nat (i + 1))) te' ->
  te ! ACG_I = Some (m, type_int32s) ->
  eval_eqf gc te eh te' eh loop_add.
Proof.
  unfold loop_add, int_of_nat. intros.
  rewrite Nat2Z.inj_add in H1. simpl in H1.
  constructor 1 with (Vint (Int.repr (Z.of_nat i + 1))) (Vint (Int.repr (Z.of_nat i + 1))).
  +eapply eval_Sbinop; simpl; eauto.
   constructor; simpl; auto.
   simpl. unfold Int.add. rewrite Int.unsigned_one.
   rewrite Int.unsigned_repr; try omega; auto.
   generalize Int.max_signed_unsigned; intros.
   split; try omega. apply Zle_trans with Int.max_signed; try omega.
   apply Z2Nat.inj_le; try omega.
   unfold Int.max_signed. simpl. omega.
   rewrite Nat2Z.id; try omega.
   unfold nat_of_Z in *. omega.
  +simpl. auto.
  +constructor 1 with Mint32; auto.
  +constructor 1 with Mint32; auto.
  +constructor 1 with ACG_I Int.zero; auto.
   constructor 1 with m; auto.
Qed.

Lemma mkarrayenv_replace_nth1:
  forall i k ef ef',
  mkarrayenv ef ef' (S i) (S i + 1 + k) = replace_nth (mkarrayenv ef ef' i (S i + 1 + k)) i ef'.
Proof.
  unfold mkarrayenv, replace_nth. intros.
  rewrite firstn_length_app2; rewrite length_list_repeat; try omega.
  rewrite minus_diag. simpl firstn. rewrite <-app_nil_end.
  rewrite skipn_length_app; rewrite length_list_repeat; try omega.
  replace (S i - i)%nat with 1%nat by omega.
  rewrite skipn_list_repeat; try omega.
  replace (S i)%nat with (i+1)%nat by omega.
  rewrite list_repeat_add_one, app_ass.
  replace (i + 1 + 1 + k - (i + 1))%nat with (i + 1 + 1 + k - i - 1)%nat; try omega.
  auto.
Qed.

Lemma mkarrayenv_replace_nth2:
  forall i ef ef',
  mkarrayenv ef ef' (i + 1) (i + 1) = replace_nth (mkarrayenv ef ef' i (i + 1)) i ef'.
Proof.
  unfold mkarrayenv, replace_nth. intros.
  rewrite firstn_length_app2; rewrite length_list_repeat; try omega.
  repeat rewrite minus_diag. simpl firstn. repeat rewrite <-app_nil_end.
  rewrite skipn_length_app; rewrite length_list_repeat; try omega.
  replace (S i - i)%nat with 1%nat by omega.
  rewrite skipn_list_repeat; try omega.
  rewrite list_repeat_add_one.
  replace (i + 1 - i - 1)%nat with 0%nat; try omega.
  auto.
Qed.

Lemma nth_makarrayenv:
  forall i j ef ef',
  (i + 1 <= j <= nat_of_Z Int.max_signed)%nat ->
  nth_error (mkarrayenv ef ef' i j) (nat_of_int (int_of_nat i)) = value ef.
Proof.
  intros. rewrite <-nat_of_int_of_nat; try omega.
  unfold mkarrayenv. rewrite nth_error_app2.
  rewrite length_list_repeat.
  replace (i-i)%nat with 0%nat; try omega.
  remember (j-i)%nat. destruct n; simpl; auto. omega.
  rewrite length_list_repeat. omega.
Qed.

Lemma unsigned_int_of_nat_le_max:
  forall i,
  (i <= nat_of_Z Int.max_signed)%nat ->
  Int.unsigned (int_of_nat i) <= Int.max_signed.
Proof.
  unfold int_of_nat. intros.
  apply Nat2Z.inj_le in H. rewrite nat_of_Z_eq in H.
  generalize Int.max_signed_unsigned; intros.
  rewrite Int.unsigned_repr; try omega.
  unfold Int.max_signed. simpl. omega.
Qed.

Lemma eval_for_loop_call_rec:
  forall gc nid c nd fd ef ef' eh k i te te' se se' m,
  call_node (node_block prog2) nid c nd fd ->
  eval_node prog2 gc ef ef' fd nil nil ->
  Lsem.eval_sexp gc te (Svar ACG_I type_int32s) (Vint (int_of_nat i)) ->
  store_env type_int32s te ACG_I Int.zero (Vint (int_of_nat ((i+1)+k))) te' ->
  se ! (instid c) = Some (mkarrayenv ef ef' i ((i+1)+k)) ->
  se' = PTree.set (instid c) (mkarrayenv ef ef' ((i+1)+k) ((i+1)+k)) se ->
  ((i+1)+k <= nat_of_Z Int.max_signed)%nat ->
  callnum c = Some (int_of_nat ((i+1)+k)) ->
  cakind c = true ->
  te ! ACG_I = Some (m, type_int32s) ->
  te ! (callid c) = None ->
  eval_stmt prog2 gc nid te (mkenv eh se) te' (mkenv eh se')
    (Sfor None (loop_cond (int_of_nat ((i+1)+k))) loop_add
      (Scall (Some (Svar ACG_I type_int32s)) nil c nil)).
Proof.
  induction k; intros.
  +replace (i + 1 + 0)%nat with (i+1)%nat in *; try omega.
   apply eval_Sfor_loop with te te' eh eh se'; auto.
   -eapply eval_loop_cond_true; eauto. split.
    apply unsigned_int_of_nat_le; try omega.
    apply unsigned_int_of_nat_le_max; try omega.
   -eapply eval_Scall; eauto; try constructor.
    rewrite H6. econstructor 1; eauto.
    constructor 1 with (mkarrayenv ef ef' i (i + 1)); auto.
    *apply nth_makarrayenv; try omega.
    *rewrite <-nat_of_int_of_nat; try omega.
     subst. f_equal. apply mkarrayenv_replace_nth2; auto.
    *rewrite H6. rewrite mkarrayenv_length; try omega.
     simpl intof_opti. unfold int_of_nat.
     generalize Int.max_signed_unsigned; intros.
     rewrite Int.unsigned_repr; try omega.
     apply Nat2Z.inj_le in H5. rewrite nat_of_Z_eq in H5; try omega.
     unfold Int.max_signed. simpl. omega.
    *inv H0. simpl. inv H14. auto.
    *inv H0. simpl. inv H11. auto.
    *tauto.
    *tauto.
   -eapply eval_eqf_loop_add; eauto.
    eapply eval_sexp_sexp; eauto.
   -apply eval_Sfor_false; auto.
    apply eval_loop_cond_false; auto.
    apply eval_Rlvalue with ACG_I Int.zero Lid; simpl; auto.
    inv H2. constructor 1 with m'; auto. rewrite PTree.gss; auto. congruence.
    eapply store_env_load_int_eq; eauto.
  +replace (i + 1 + S k)%nat with ((S i)+1 + k)%nat in *; try omega.
   assert(A:exists te1, store_env type_int32s te ACG_I Int.zero (Vint (int_of_nat (i+1))) te1).
     apply load_env_int_store_exists with (Vint (int_of_nat i)); auto.
     inv H1. inv H10. inv H11. auto. congruence.
   destruct A as [te1 A].
   remember (PTree.set (instid c) (mkarrayenv ef ef' (S i) (S i + 1 + k)) se) as se1.
   apply eval_Sfor_loop with te te1 eh eh se1; auto.
   -eapply eval_loop_cond_true; eauto. split.
    apply unsigned_int_of_nat_le; try omega.
    apply unsigned_int_of_nat_le_max; auto.
   -eapply eval_Scall; eauto; try constructor.
    rewrite H6. econstructor 1; eauto.
    constructor 1 with (mkarrayenv ef ef' i (S i + 1 + k)); auto.
    *apply nth_makarrayenv; try omega.
    *rewrite <-nat_of_int_of_nat; try omega.
     subst. f_equal. apply mkarrayenv_replace_nth1; auto.
    *rewrite H6. rewrite mkarrayenv_length; try omega.
     simpl intof_opti. unfold int_of_nat.
     replace (S (i + 1 + k)) with (S i + 1 + k)%nat; try omega.
     rewrite Int.unsigned_repr; try omega.
     generalize Int.max_signed_unsigned; intros.
     split; try omega. apply Nat2Z.inj_le in H5; try omega.
     rewrite nat_of_Z_eq in H5; try omega.
     unfold Int.max_signed. simpl; omega.
    *inv H0. simpl. inv H14. auto.
    *inv H0. simpl. inv H11. auto.
    *tauto.
    *tauto.
  -eapply eval_eqf_loop_add; eauto.
    replace (i+1)%nat with (S i); try omega.
    eapply eval_sexp_sexp; eauto. omega.
  -generalize A. intros A1. inv A1.
   apply IHk with m'; auto.
   *replace (S i) with (i+1)%nat; try omega.
    apply Lsem.eval_Rlvalue with ACG_I Int.zero Lid; auto.
    constructor 1 with m'; auto. rewrite PTree.gss; auto. congruence.
    constructor. eapply store_env_load_int_eq; eauto.
    constructor.
   *eapply store_env_trans; eauto.
   *subst. rewrite PTree.gss; auto.
   *subst. rewrite ptree_set_repeat;auto.
   *rewrite PTree.gss; auto. congruence.
   *rewrite PTree.gso; auto. red; intros; subst. congruence.
Qed.

Lemma eval_for_loop_call:
  forall gc nid c nd fd ef ef' j eh te te' se se' m,
  call_node (node_block prog2) (reset_id nid) (trans_calldef c) (trans_init_node nd) (trans_init_node fd) ->
  eval_node prog2 gc ef ef' (trans_init_node fd) nil nil ->
  load_env type_int32s te ACG_I Int.zero (Vint Int.zero)->
  store_env type_int32s te ACG_I Int.zero (Vint j) te' ->
  se ! (instid c) = Some (list_repeat (nat_of_int j) ef) ->
  se' = PTree.set (instid c) (list_repeat (nat_of_int j) ef') se ->
  0 < Int.unsigned j <= Int.max_signed ->
  callnum c = Some j ->
  cakind c = true ->
  te ! ACG_I = Some (m, type_int32s) ->
  te ! (reset_id (callid c)) = None ->
  eval_stmt prog2 gc (reset_id nid) te (mkenv eh se) te' (mkenv eh se')
    (Sfor None (loop_cond j) loop_add
      (Scall (Some (Svar ACG_I type_int32s)) nil (trans_calldef c) nil)).
Proof.
  intros. rewrite (int_of_nat_of_int j); try omega.
  assert(A: (0 < nat_of_int j)%nat).
    unfold nat_of_int. apply Nat2Z.inj_lt; try omega.
    rewrite nat_of_Z_eq; simpl; try omega.
  assert(A1: ((0+1)+((nat_of_int j)-1) = (nat_of_int j))%nat). omega.
  rewrite <-A1.
  apply eval_for_loop_call_rec with (trans_init_node nd) (trans_init_node fd) ef ef' m; auto.
  +apply Lsem.eval_Rlvalue with ACG_I Int.zero Lid; auto.
   constructor 1 with m; auto. constructor; auto. constructor.
  +rewrite A1. rewrite <-int_of_nat_of_int; auto.
  +rewrite A1. unfold mkarrayenv. simpl. rewrite H3.
   repeat f_equal. omega.
  +rewrite A1. unfold mkarrayenv. subst. rewrite minus_diag.
   simpl. rewrite <-app_nil_end. auto.
  +rewrite A1. destruct H5. unfold nat_of_int.
   apply Z2Nat.inj_le in H10; try omega.
   unfold nat_of_Z, Z.to_nat in *; auto.
  +rewrite A1. simpl. rewrite H6.
   rewrite <-int_of_nat_of_int; auto.
Qed.

Lemma callnum_some_mkloopid:
  forall c i l, In c l ->
  callnum c = Some i ->
  mkloopid l = (ACG_I, type_int32s) :: nil.
Proof.
  induction l; simpl; intros.
  inv H.
  destruct H; subst.
  rewrite H0. auto.
  destruct (callnum a); auto.
Qed.

Lemma eval_flag_init:
  forall gc eh eh1 te,
  store_env type_bool eh ACG_INIT Int.zero (Vint Int.one) eh1 ->
  locenv_range_perm_var eh ACG_INIT type_bool ->
  eval_eqf gc te eh te eh1 (Ssvar ACG_INIT type_bool, Sconst (Cbool true) type_bool).
Proof.
  intros. constructor 1 with Vtrue Vtrue; simpl;auto.
  constructor; simpl; auto.
  constructor 1 with Mint8unsigned; auto.
  constructor 1 with Mint8unsigned; auto.
  constructor 2 with ACG_INIT Int.zero; auto.
  destruct H0 as [m [? [? ?]]].
  constructor 3 with m; auto.
Qed.

Lemma reset_ids_loopid_notin:
  ~ In ACG_I (map fst (flat_map trans_init_nodes (node_block prog1))).
Proof.
  unfold trans_program in *.
  destruct (list_in_list _ _) eqn:?; try congruence.
  apply list_in_list_disjoint in Heqb; auto.
  red; intros. eapply Heqb; simpl; eauto.
Qed.

Lemma trans_init_node_correct:
  forall gc e e' main,
  init_env prog1 e e' main ->
  gc ! ACG_I = None ->
  eval_node prog2 gc e e' (trans_init_node main) nil nil
    /\ node_match prog2 (trans_init_node main) main.
Proof.
  intros until main.
  induction 1 using init_env_ind2 with
  ( P0 := fun nid se se' l =>
       forall l1 te eh, locenv_range_perm_vars te (mkloopid l1) ->
       list_norepet (map instid l) ->
       gc ! ACG_I = None ->
       incl l l1 ->
       (forall c, In c l1 -> cakind c = true) ->
       ptree_ids_none (map fst (flat_map trans_init_nodes (node_block prog1))) te ->
       exists te',eval_stmt prog2 gc (reset_id nid) te (mkenv eh se) te' (mkenv eh se') (trans_init_stmt l)
         /\ calldefs_match prog2 (map trans_calldef l) l
   ); intros; eauto.
 +(*node*)
   destruct alloc_variables_exists with (mkloopid (instidof (nd_stmt f))) empty_locenv
      as [te A]; auto.
   destruct IHinit_env with (instidof (nd_stmt f)) te eh1 as [te' [? ?]]; auto.
     apply alloc_variables_loopid_range_perm; auto.
     apply ids_norepet_instid; auto.
     red; auto.
     eapply instidof_cakind_true; eauto.
     red; intros. erewrite alloc_variables_notin_eq; eauto. apply PTree.gempty.
      destruct mkloopid_range with (instidof (nd_stmt f)) as [A1 | A1]; rewrite A1; auto.
      red; simpl; intros. destruct H5; subst; try tauto.
      apply reset_ids_loopid_notin; auto.
   split.
   -apply exec_node with te te te';simpl; try (constructor; fail); auto.
    *unfold trans_init_body, lvarsof. simpl.
     rewrite <-app_nil_end; auto.
    *apply trans_init_body_ids_norepet; auto.
    *inv H0; auto.
     apply eval_Sseq with te (mkenv eh1 se); auto.
     constructor.
     eapply eval_flag_init; eauto.
    *apply trans_init_body_svars_fld_match; auto.
   -constructor 1; auto; unfold trans_init_node.
    remember (trans_init_body _). simpl. subst.
    rewrite trans_init_body_instidof. auto.
 +(*nil*)
  exists te. split; auto; constructor.
 +(*call_cons*)
   simpl. inversion_clear H5.
   generalize H. intros A. apply trans_call_node in A.
   unfold trans_init_calldef.
   destruct IHinit_env as [B B1]; auto.
     destruct H as [? [? [? [? [? [? [? ?]]]]]]].
   remember (callnum c). destruct o.
   -assert(A1: mkloopid l1 = (ACG_I, type_int32s) :: nil).
      apply callnum_some_mkloopid with (c:=c) (i:=i); auto.
      apply H7; simpl; auto.
    rewrite A1 in *.
    destruct has_type_store_env_exists with te (Vint i) type_int32s ACG_I
      as [te1 A2]; simpl; auto.

    destruct IHinit_env0 with l te1 eh as [te' [A3 A4]]; auto.
      eapply store_env_range_perm_vars; eauto.
      destruct mkloopid_range with l as [C | C]; rewrite C; auto.
        red; simpl; intros; tauto.
      red; auto.
      intros. apply H8. apply H7; simpl; auto.
      eapply store_env_ptree_ids_none; eauto.
    exists te'. split.
    apply eval_Sseq with te1 (mkenv eh se1); auto.
    destruct has_type_store_env_exists with te (Vint Int.zero) type_int32s ACG_I
      as [te0 A6]; simpl; auto.
    destruct H4 with ACG_I type_int32s as [m [A7 A8]]; simpl; auto.
    apply eval_Sfor_start with te0 eh; auto.
    apply eval_loop_init with m; auto.
    assert(A9: exists m', te0 ! ACG_I = Some (m', type_int32s)).
      inv A6. exists m'. rewrite PTree.gss; auto. congruence.
    destruct A9 as [m' A9].
    apply eval_for_loop_call with nd fd ef ef' m'; auto.
    *eapply store_env_load_int_eq; eauto.
    *eapply store_env_trans; eauto.
    *destruct A as [? [? [? [? [? [? [? [? [? ?]]]]]]]]].
     simpl in *. rewrite <-Heqo in *. omega.
    *apply H8. apply H7; simpl; auto.
    *eapply store_env_ptree_ids_none; eauto.
     erewrite <-find_funct_fid with (fid:=callid c) (fd:=fd); eauto.
     apply reset_ids_map_in. eapply find_funct_in2; eauto.
       rewrite <-H16. apply H8. apply H7; simpl; auto.
    *constructor 2 with (trans_init_node fd) fd; auto.
     destruct A as [? [? [? [? [? [? ?]]]]]]; auto.
     apply find_node; auto.
     apply prog2_nodeids_norepet; auto.
   -destruct IHinit_env0 with l1 te eh  as [te' [A5 A6]]; auto.
     red; intros. apply H7. simpl; auto.
    exists te'. split.
    apply eval_Sseq with te (mkenv eh se1); auto.
    apply eval_Scall with ef ef' (trans_init_node fd) (trans_init_node nd) nil nil nil Int.zero; simpl; auto.
    *apply H8. apply H7; simpl; auto.
    *rewrite <-Heqo. econstructor 2; eauto.
    *constructor 1 with (ef::nil); simpl; try rewrite <-Heqo; simpl; auto.
    *constructor.
    *constructor.
    *constructor.
    *constructor.
    *red; intros; tauto.
    *apply H9; simpl; auto.
     erewrite <-find_funct_fid with (fid:=callid c) (fd:=fd); eauto.
     apply reset_ids_map_in. eapply find_funct_in2; eauto.
       rewrite <-H16. apply H8. apply H7; simpl; auto.
    *constructor 2 with (trans_init_node fd) fd; auto.
     destruct A as [? [? [? [? [? [? ?]]]]]]; auto.
     apply find_node; auto.
     apply prog2_nodeids_norepet; auto.
   -destruct H as [? [? [? [? [? [? [? ?]]]]]]]; auto.
    unfold func in *. rewrite <-H16. apply H8. apply H7; simpl; auto.
Qed.

Lemma node_main_eq:
  node_main prog2 = node_main prog1.
Proof.
  unfold trans_program in *.
  destruct (list_in_list _ _); inv TRANS.
  subst. destruct prog1; auto.
Qed.

Lemma init_genvc_none:
  forall gc,
  init_genvc (const_block prog1) = Some gc ->
  gc ! ACG_I = None.
Proof.
  intros. eapply init_genvc_notin_none; eauto.
  apply ids_plt_le_notin with ACG_EQU; auto.
  unfold Ple, ACG_I, ACG_EQU. omega.
Qed.

Lemma initial_states_match:
  forall gc main e,
  Lenv.initial_state1 prog1 gc (fun p e fd => LsemE.init_node p e fd) main e ->
  nd_kind (snd main) = true ->
  initial_node_state prog2 gc main e.
Proof.
  induction 1; intros.
  destruct alloc_init_node_exists with prog1 e main as [e0 [A A1]]; auto.
  apply trans_init_node_correct with (gc:=gc) in A1; eauto.
  destruct A1 as [A1 A2].
  constructor 1 with e0 (trans_init_node main); auto.
  +unfold trans_program in *. destruct (list_in_list _ _); inv TRANS.
   destruct prog1; auto.
  +rewrite node_main_eq.
   apply find_reset_node; auto.
  +rewrite node_main_eq.
   apply find_node; auto. apply prog2_nodeids_norepet.
  +apply alloc_node_correct; auto.
  +apply init_genvc_none; auto.
Qed.

Theorem exec_prog_correct_node:
  forall gc e main mass vrss n maxn,
  Lenv.exec_prog1 prog1 gc eval_node main e n maxn mass vrss ->
  Lenv.exec_prog1 prog2 gc eval_node main e n maxn mass vrss.
Proof.
  induction 1; intros.
  +constructor 1 with mrss; trivial.
  +constructor 2 with e'; auto.
   apply trans_node_all_correct; auto.
Qed.

Theorem trans_program_node_correct:
  forall gc e main vass vrss maxn,
  Lenv.initial_state1 prog1 gc (fun p e fd => LsemE.init_node p e fd) main e ->
  Lenv.exec_prog1 prog1 gc eval_node main e 1 maxn vass vrss ->
  nd_kind (snd main) = true ->
  initial_node_state prog2 gc main e
    /\ Lenv.exec_prog1 prog2 gc eval_node main e 1 maxn vass vrss.
Proof.
  intros. apply initial_states_match in H; auto.
  repeat (split; auto).
  apply exec_prog_correct_node; auto.
Qed.

End NODE_CORRECT.

End CORRECTNESS.
