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

(** Correctness proof for input parameters and global consts classification. *)

Require Import AST.
Require Import Coqlib.
Require Import Errors.
Require Import Maps.
Require Import Integers.
Require Import List.
Require Import ExtraList.
Require Import Lident.
Require Import Cltypes.
Require Import Ltypes.
Require Import Lustre.
Require Import LustreF.
Require Import Lvalues.
Require Import Lenv.
Require Import Lenvmatch.
Require Import Lsem.
Require Import LsemF.
Require Import LsemD.
Require Import LsemC.
Require Import Permutation.
Require Import ClassifyRetsVar.
Require Import ClassifyArgsVar.

Section CORRECTNESS.

Variable prog1 prog2: program.

Hypothesis TRANSL:
  trans_program prog1 = OK prog2.

Hypothesis GID_NOREPET:
  list_norepet (globidsof prog1).

Hypothesis GID_RANGE:
  ids_plt ACG_EQU (map fst (const_block prog1)).

Hypothesis ID_RANGE:
  ids_range ACG_MEMCPY (node_block prog1).

Section NODE_CORRECT.

Variable gc1: locenv.

Hypothesis GENV_NONE:
  gc1 ! ACG_I = None.

Definition ptree_ids_in(l: list ident)(e: locenv): Prop :=
  (forall id, ~ In id l -> e ! id = None)
  /\ (forall id, In id l -> exists mt, e ! id = Some mt).

Lemma eval_sexp_match:
forall te1 e,
(
  forall a v,
  LsemF.eval_sexp gc1 te1 e a v ->
  forall gc2 ta te2 ids lids,
  locenv_match gc1 gc2 ->
  ptree_noids_match ids te1 te2 ->
  ptree_ids_match ids te1 ta ->
  ptree_ids_none ids te2 ->
  ptree_ids_in (lids++ids) te1 ->
  eval_sexp gc2 ta te2 e (trans_sexp (trans_v ids lids) a) v
)
/\
(
  forall a id o k,
  LsemF.eval_lvalue gc1 te1 e a id o k ->
  forall gc2 ta te2 ids lids,
  locenv_match gc1 gc2 ->
  ptree_noids_match ids te1 te2 ->
  ptree_ids_match ids te1 ta ->
  ptree_ids_none ids te2 ->
  ptree_ids_in (lids++ids) te1 ->
  match k with
  | Gid | Sid =>
    eval_lvalue gc2 ta te2 e (trans_sexp (trans_v ids lids) a) id o k
  | Lid =>
    eval_lvalue gc2 ta te2 e (trans_sexp (trans_v ids lids) a) id o (if in_list id ids then Aid else k)
  | Aid => False
  end
).
Proof.
 intros until e.
 apply LsemF.eval_sexp_lvalue_ind; intros; simpl.
 +constructor; simpl; auto.
 +constructor 2 with v1; auto.
  rewrite trans_sexp_typeof; auto.
 +constructor 3 with v1 v2; auto;
  repeat rewrite trans_sexp_typeof; auto.
 +constructor 4 with v1; auto.
  rewrite trans_sexp_typeof; auto.
 +generalize H3; intros A. eapply H0 in H3; eauto.
  destruct k; try tauto; simpl in *.
  -apply eval_Rlvalue with id ofs Gid; simpl; auto;
   rewrite trans_sexp_typeof; auto.
   eapply load_env_match; eauto.
  -apply eval_Rlvalue with id ofs (if in_list id ids then Aid else Lid); auto;
   rewrite trans_sexp_typeof; auto.
   destruct (in_list id ids) eqn:?; simpl in *; auto.
   eapply ptree_ids_match_load_env; eauto.
   eapply ptree_noids_match_load_env; eauto.
  -apply eval_Rlvalue with id ofs Sid; simpl; auto;
   rewrite trans_sexp_typeof; auto.
 +unfold trans_v. intros.
  destruct (in_list id ids) eqn:?.
  -constructor 4 with m; auto.
   rewrite <-H2; auto. apply in_list_true_in;auto.
  -destruct (in_list id lids) eqn:?.
   *constructor 1 with m; auto.
    rewrite <-H1; auto. apply in_list_false_notin; auto.
   *destruct H4. rewrite H4 in H. congruence. apply in_list_false_notin.
    rewrite in_list_app, Heqb, Heqb0; auto.
 +unfold trans_v. destruct (in_list _ ids) eqn:?.
  -apply in_list_true_in in Heqb. destruct H5.
   destruct H6 with id as [? ?]; auto.
   apply in_or_app; auto. congruence.
  -destruct (in_list id lids) eqn:?.
   *apply in_list_true_in in Heqb0. destruct H5.
    destruct H6 with id as [? ?]; auto.
    apply in_or_app; auto. congruence.
   *constructor 2 with m; auto. rewrite H2 in H; auto.
    apply in_list_false_notin;auto.
 +constructor 3 with m; auto.
 +destruct k; eauto;
  apply eval_Saryacc with aid z; auto;
  rewrite trans_sexp_typeof; auto.
 +destruct k; eauto;
  apply eval_Sfield with sid fld; auto;
  rewrite trans_sexp_typeof; auto.
Qed.

Lemma eval_sexps_match:
  forall te1 e al vl,
  LsemF.eval_sexps gc1 te1 e al vl ->
  forall gc2 ta te2 ids lids, locenv_match gc1 gc2 ->
  ptree_noids_match ids te1 te2 ->
  ptree_ids_match ids te1 ta ->
  ptree_ids_none ids te2 ->
  ptree_ids_in (lids++ids) te1 ->
  eval_sexps gc2 ta te2 e (trans_sexps (trans_v ids lids) al) vl.
Proof.
  induction 1; simpl; intros.
  +constructor.
  +constructor 2; auto.
   eapply eval_sexp_match; eauto.
   eapply IHForall2; eauto.
Qed.

Lemma eval_lsexp_match:
forall te1 e,
(
  forall a v,
  LsemF.eval_sexp gc1 te1 e a v ->
  forall gc2 ta te2 ids lids a', locenv_match gc1 gc2 ->
  ptree_noids_match ids te1 te2 ->
  ptree_ids_match ids te1 ta ->
  ptree_ids_none ids te2 ->
  ptree_ids_in (lids++ids) te1 ->
  list_disjoint ids lids ->
  trans_lsexp ids lids a = OK a' ->
  eval_sexp gc2 ta te2 e a' v
)
/\
(
  forall a id o k,
  LsemF.eval_lvalue gc1 te1 e a id o k ->
  forall gc2 ta te2 ids lids a', locenv_match gc1 gc2 ->
  ptree_noids_match ids te1 te2 ->
  ptree_ids_match ids te1 ta ->
  ptree_ids_none ids te2 ->
  ptree_ids_in (lids++ids) te1 ->
  list_disjoint ids lids ->
  trans_lsexp ids lids a = OK a' ->
  match k with
  | Sid =>
    eval_lvalue gc2 ta te2 e a' id o k
  | Lid =>
    eval_lvalue gc2 ta te2 e a' id o k
    /\ in_list id ids = false
  | _ => False
  end
).
 intros until e.
 apply LsemF.eval_sexp_lvalue_ind; intros; simpl in *; try congruence.
 +eapply H0 in H3; eauto. destruct k; try tauto.
  -destruct H3. apply eval_Rlvalue with id ofs Lid; simpl; auto.
   rewrite trans_lsexp_typeof with ids lids a _; auto.
   eapply ptree_noids_match_load_env; eauto.
   erewrite trans_lsexp_typeof; eauto.
  -apply eval_Rlvalue with id ofs Sid; simpl; auto.
   rewrite trans_lsexp_typeof with ids lids a _; auto.
   erewrite trans_lsexp_typeof; eauto.
 +destruct (in_list id lids) eqn:?; inv H6.
  cut (in_list id ids = false). intros.
  split; auto. constructor 1 with m; auto.
  rewrite <-H1; auto. apply in_list_false_notin; auto.
  apply in_list_true_in in Heqb; auto. apply in_list_false_notin.
  red; intros. eapply H5; eauto.
 +destruct (in_list id lids) eqn:?; inv H7.
  destruct H5. destruct H7 with id.
  apply in_or_app. left. apply in_list_true_in; auto.
  congruence.
 +inv H6. constructor 3 with m; auto.
 +monadInv H12.
  eapply eval_sexp_match in H1; eauto.
  eapply H0 in H6; eauto.
  destruct k; eauto; intuition;
  apply eval_Saryacc with aid z; auto;
  rewrite trans_lsexp_typeof with ids lids a _; auto.
 +monadInv H11. eapply H0 in H5; eauto.
  destruct k; eauto; intuition;
  apply eval_Sfield with sid fld; auto;
  rewrite trans_lsexp_typeof with ids lids a _; auto.
Qed.

Lemma store_env_ptree_ids_in:
  forall ty e id o v e1 l,
  store_env ty e id o v e1 ->
  ptree_ids_in l e ->
  ptree_ids_in l e1.
Proof.
  intros. inv H.
  destruct H0; split; intros; compare id id0; intros; subst.
  rewrite H in H1; auto. congruence.
  rewrite PTree.gso; auto.
  rewrite PTree.gss; eauto.
  rewrite PTree.gso; auto.
Qed.

Lemma store_env_ptree_match_exists_ta:
  forall ty te1 b ofs v te1',
  store_env ty te1 b ofs v te1' ->
  forall te2 ta ids, ptree_noids_match ids te1 te2 ->
  ptree_ids_match ids te1 ta ->
  in_list b ids = true ->
  exists ta', store_env ty ta b ofs v ta'
    /\ ptree_noids_match ids te1' te2
    /\ ptree_ids_match ids te1' ta'.
Proof.
  intros. apply in_list_true_in in H2.
  generalize H H2; intros A A1.
  apply H1 in H2.
  eapply store_env_match_exists in H;eauto.
  destruct H as [ta' [? ?]].
  exists ta'. split ;auto. inv A. inv H. split.
  +red; intros. rewrite PTree.gso; auto.
   red; intros; subst; auto.
  +repeat rewrite PTree.gss in H3. inv H3.
   apply ptree_ids_match_setsame; auto.
Qed.

Lemma store_env_ptree_match_exists_te:
  forall ty te1 b ofs v te1',
  store_env ty te1 b ofs v te1' ->
  forall te2 ta ids, ptree_noids_match ids te1 te2 ->
  ptree_ids_match ids te1 ta ->
  in_list b ids = false ->
  exists te2', store_env ty te2 b ofs v te2'
    /\ ptree_noids_match ids te1' te2'
    /\ ptree_ids_match ids te1' ta.
Proof.
  intros. apply in_list_false_notin in H2.
  generalize H H2; intros A A1.
  apply H0 in H2.
  eapply store_env_match_exists in H;eauto.
  destruct H as [te2' [? ?]].
  exists te2'. split ;auto. inv A. inv H. split.
  +repeat rewrite PTree.gss in H3. inv H3.
   apply ptree_noids_match_setsame; auto.
  +red; intros. rewrite PTree.gso; auto.
   red; intros; subst; auto.
Qed.

Lemma locenv_setvaddr_exists:
  forall te1 te1' e e' a v,
  locenv_setvarf gc1 te1 e a v te1' e' ->
  forall gc2 ta te2 ids lids a', locenv_match gc1 gc2 ->
  ptree_noids_match ids te1 te2 ->
  ptree_ids_match ids te1 ta ->
  ptree_ids_none (ACG_MEMCPY::ids) te2 ->
  ptree_ids_in (lids++ids) te1 ->
  list_disjoint ids lids ->
  trans_lsexp ids lids a = OK a' ->
  exists d te2', eval_vaddr gc2 ta te2 e a' d
    /\ locenv_setvaddr te2 e d v te2' e'
    /\ ptree_noids_match ids te1' te2'
    /\ ptree_ids_match ids te1' ta
    /\ ptree_ids_none (ACG_MEMCPY::ids) te2'
    /\ ptree_ids_in (lids++ids) te1'.
Proof.
  intros. inv H.
  +eapply eval_lsexp_match in H7; eauto. destruct H7.
   generalize H8; intros A.
   eapply store_env_ptree_match_exists_te in H8; eauto.
   destruct H8 as [te2' [? [? ?]]].
   eapply store_env_ptree_ids_in in A; eauto.
   exists (mkvaddr id ofs (typeof a') Lid), te2'.
   destruct H4. repeat (split; auto).
   -constructor 1. erewrite trans_lsexp_typeof; eauto.
   -inv H8. eapply ptree_ids_none_set_other; eauto.
   -red; intros. apply H3. simpl; auto.
  +exists (mkvaddr id ofs (typeof a') Sid), te2.
   repeat (split; auto).
   eapply eval_lsexp_match in H7; eauto.
   red; intros. apply H3. simpl; auto.
   constructor; auto.
   erewrite trans_lsexp_typeof; eauto.
Qed.

Lemma assign_disjoint_match:
  forall te1 e a1 a2,
  assign_disjoint (LsemF.eval_lvalue gc1 te1 e) a1 a2 ->
  forall gc2 ta te2 ids lids lh, locenv_match gc1 gc2 ->
  ptree_noids_match ids te1 te2 ->
  ptree_ids_match ids te1 ta ->
  ptree_ids_none ids te2 ->
  ptree_ids_in (lids++ids) te1 ->
  list_disjoint ids lids ->
  trans_lsexp ids lids a1 = OK lh ->
  assign_disjoint (eval_lvalue gc2 ta te2 e) lh (trans_sexp (trans_v ids lids) a2).
Proof.
  induction 1; intros.
  +constructor 1 with chunk; auto.
   erewrite trans_sexp_typeof; eauto.
  +constructor. erewrite trans_sexp_typeof; eauto.
   inv H0. eapply eval_sexp_match in H9; eauto.
   eapply eval_lsexp_match in H8; eauto.
   apply trans_lsexp_typeof in H7; auto.
   destruct H10; subst.
   -destruct H8. destruct k2; try tauto; econstructor 1; eauto;
    erewrite trans_sexp_typeof; eauto; congruence.
   -destruct k2; try tauto; econstructor 1; eauto;
    erewrite trans_sexp_typeof; eauto; congruence.
Qed.

Lemma assign_list_disjoint_match:
  forall te1 e al args,
  assign_list_disjoint (LsemF.eval_lvalue gc1 te1 e) al args ->
  forall gc2 ta te2 ids lids lhs, locenv_match gc1 gc2 ->
  ptree_noids_match ids te1 te2 ->
  ptree_ids_match ids te1 ta ->
  ptree_ids_none ids te2 ->
  ptree_ids_in (lids++ids) te1 ->
  list_disjoint ids lids ->
  trans_lsexps ids lids al = OK lhs ->
  assign_list_disjoint (eval_lvalue gc2 ta te2 e) lhs (trans_sexps (trans_v ids lids) args).
Proof.
  intros. red; intros.
  apply mmap_inversion in H6.
  apply in_split in H7. destruct H7 as [lh1 [lh2 ?]]. subst.
  apply list_forall2_infer in H6. apply Forall2_app_inv_r in H6.
  destruct H6 as [al1 [al2 [? [? ?]]]]. subst.
  unfold trans_sexps in H8. apply in_map_iff in H8.
  destruct H8 as [? [? ?]]. subst. inv H7.
  eapply assign_disjoint_match; eauto.
  apply H; auto. apply in_or_app; simpl; auto.
Qed.

Lemma lvalue_disjoints_match:
  forall te1 e a1 a2,
  lvalue_disjoint (LsemF.eval_lvalue gc1 te1 e) a1 a2 ->
  forall gc2 ta te2 ids lids x1 x2, locenv_match gc1 gc2 ->
  ptree_noids_match ids te1 te2 ->
  ptree_ids_match ids te1 ta ->
  ptree_ids_none ids te2 ->
  ptree_ids_in (lids++ids) te1 ->
  list_disjoint ids lids ->
  trans_lsexp ids lids a1 = OK x1 ->
  trans_lsexp ids lids a2 = OK x2 ->
  lvalue_disjoint (eval_lvalue gc2 ta te2 e) x1 x2.
Proof.
  induction 1; intros.
  eapply eval_lsexp_match in H; eauto.
  eapply eval_lsexp_match in H0; eauto.
  apply trans_lsexp_typeof in H10.
  destruct H1; subst.
  +destruct H.
   destruct k2; try tauto; [destruct H0 | ];
   econstructor 1; eauto; erewrite trans_lsexp_typeof; eauto.
   congruence. congruence.
  +destruct k2; try tauto; [destruct H0 | ];
   econstructor 1; eauto; erewrite trans_lsexp_typeof; eauto.
   congruence. congruence.
Qed.

Lemma lvalue_list_norepet_match:
  forall te1 e al,
  lvalue_list_norepet (LsemF.eval_lvalue gc1 te1 e) al ->
  forall gc2 ta te2 ids lids lhs, locenv_match gc1 gc2 ->
  ptree_noids_match ids te1 te2 ->
  ptree_ids_match ids te1 ta ->
  ptree_ids_none ids te2 ->
  ptree_ids_in (lids++ids) te1 ->
  list_disjoint ids lids ->
  trans_lsexps ids lids al = OK lhs ->
  lvalue_list_norepet (eval_lvalue gc2 ta te2 e) lhs.
Proof.
  induction 1; simpl; intros.
  +inv H5. constructor.
  +monadInv H7. simpl in H7. monadInv H7. inv H8.
   constructor 2; eauto.
   red; intros.
   apply in_split in H7. destruct H7 as [? [? ?]]. subst.
   apply list_forall2_infer in H13.
   apply Forall2_app_inv_r in H13. destruct H13 as [? [? [? [? ?]]]].
   subst. inv H8.
   eapply lvalue_disjoints_match; eauto.
   apply H. apply in_or_app; simpl; auto.
Qed.

Lemma eval_eqf_exists:
  forall te1 te1' e e' a,
  LsemF.eval_eqf gc1 te1 e te1' e' a ->
  forall gc2 ta te2 ids lids a', locenv_match gc1 gc2 ->
  ptree_noids_match ids te1 te2 ->
  ptree_ids_match ids te1 ta ->
  ptree_ids_none (ACG_MEMCPY::ids) te2 ->
  ptree_ids_in (lids++ids) te1 ->
  list_disjoint ids lids ->
  trans_eqf ids lids a = OK a' ->
  exists te2', eval_eqf gc2 ta te2 e te2' e' a'
    /\ ptree_noids_match ids te1' te2'
    /\ ptree_ids_match ids te1' ta
    /\ ptree_ids_none (ACG_MEMCPY::ids) te2'
    /\ ptree_ids_in (lids++ids) te1'.
Proof.
  intros. inv H. monadInv H6.
  eapply locenv_setvaddr_exists in H11; eauto.
  destruct H11 as [d [te2' [? [? [? [? [? ?]]]]]]].
  exists te2'. repeat (split; auto).
  constructor 1 with v v' d; auto.
  eapply eval_sexp_match; eauto.
  red; intros. apply H3; simpl; auto.
  rewrite trans_sexp_typeof; auto.
  erewrite trans_lsexp_typeof; eauto.
  eapply assign_disjoint_match; eauto.
  red; intros. apply H3; simpl; auto.
  erewrite trans_lsexp_typeof; eauto.
  apply H3; simpl; auto.
Qed.

Lemma locenv_match_setvars_exists:
  forall te1 al vas te1',
  locenv_setvars te1 al vas te1' ->
  forall ids lids ta te2, ptree_ids_match ids te1 ta ->
  ptree_noids_match ids te1 te2 ->
  ptree_ids_in (lids++ids) te1 ->
  incl (map fst al) ids ->
  exists ta', locenv_setvars ta al vas ta'
     /\ ptree_ids_match ids te1' ta'
     /\ ptree_noids_match ids te1' te2
     /\ ptree_ids_in (lids++ids) te1'.
Proof.
  induction 1; simpl; intros.
  +exists ta. repeat (split; auto).
   constructor.
  +generalize H0; intros A.
   eapply store_env_ptree_match_exists_ta in H0; eauto.
   destruct H0 as [ta1 [? [? ?]]].
   eapply store_env_ptree_ids_in in A; eauto.
   destruct IHlocenv_setvars with ids lids ta1 te2 as [ta' [? [? [? ?]]]]; auto.
     red; intros. apply H5; simpl; auto.
   exists ta'. repeat (split; auto).
   constructor 2 with ta1 m; eauto.
   rewrite <-H2; auto. apply H5; simpl; auto.
   apply in_list_true_in. apply H5; simpl; auto.
Qed.

Lemma trans_call_func:
  forall cdef fd,
  call_func (node_block prog1) cdef fd ->
  exists fd', trans_node fd = OK fd'
    /\ call_func (node_block prog2) cdef fd'.
Proof.
  unfold call_func. intros.
  destruct H as [? [? ?]]. subst.
  monadInv TRANSL.
  simpl in *.
  eapply find_funcs_monad_exits in H; eauto.
  destruct H as [fd' [? ?]].
  exists fd'. split; auto. monadInv H.
  monadInv EQ0. simpl in *.
  intuition.
  intros. monadInv H2. monadInv EQ0. auto.
Qed.

Lemma alloc_variables_ptree_ids_match:
  forall l1 l2 te1 te2 ta ta1,
  alloc_variables empty_locenv (l1++l2) te1 ->
  alloc_variables empty_locenv l1 te2 ->
  alloc_variables ta l2 ta1 ->
  list_disjoint (map fst l1) (map fst l2) ->
  list_norepet (map fst l2) ->
  ptree_noids_match (map fst l2) te1 te2
    /\ ptree_ids_match (map fst l2) te1 ta1
    /\ ptree_ids_in (map fst l1++map fst l2) te1.
Proof.
  intros. generalize H; intros A.
  apply alloc_variables_app in H.
  destruct H as [te0 [? ?]].
  eapply alloc_variables_determ in H; eauto.
  subst. split; [| split; [| split]]; try red; intros.
  +eapply alloc_variables_notin_eq; eauto.
  +generalize H; intros.
   apply in_map_iff in H. destruct H as [? [? ?]].
   subst. destruct x. simpl in *.
   eapply alloc_variables_norepeat_in_eq in H4; eauto.
   eapply alloc_variables_norepeat_in_eq in H1; eauto.
   rewrite H4, H1. auto.
  +erewrite alloc_variables_notin_eq; eauto.
   apply PTree.gempty. rewrite map_app; auto.
  +rewrite <-map_app in H. eapply alloc_variables_exists_in; eauto.
Qed.

Lemma locenv_getmvl_match:
  forall te1 e a v,
  LsemD.locenv_getmvl gc1 te1 e a v ->
  forall gc2 ids lids ta te2 a', locenv_match gc1 gc2 ->
  ptree_noids_match ids te1 te2 ->
  ptree_ids_match ids te1 ta ->
  ptree_ids_none ids te2 ->
  ptree_ids_in (lids++ids) te1 ->
  list_disjoint ids lids ->
  trans_lsexp ids lids a = OK a' ->
  locenv_getmvl gc2 ta te2 e a' v.
Proof.
  intros. inv H.
  eapply eval_lsexp_match in H7; eauto.
  constructor 1 with id ofs k m t; auto.
  +destruct k; tauto.
  +destruct H8; subst; simpl in *; auto.
   rewrite <-H1; auto.
   apply in_list_false_notin; intuition.
  +erewrite trans_lsexp_typeof; eauto.
Qed.

Lemma locenv_getmvls_match:
  forall te1 e l vl,
  LsemD.locenv_getmvls gc1 te1 e l vl ->
  forall ids lids gc2 ta te2 l', locenv_match gc1 gc2 ->
  ptree_noids_match ids te1 te2 ->
  ptree_ids_match ids te1 ta ->
  ptree_ids_none ids te2 ->
  ptree_ids_in (lids++ids) te1 ->
  list_disjoint ids lids ->
  mmap (trans_lsexp ids lids) l = OK l' ->
  locenv_getmvls gc2 ta te2 e l' vl.
Proof.
  induction 1; intros.
  +inv H5. constructor.
  +simpl in H7. monadInv H7.
   constructor 2; auto.
   eapply locenv_getmvl_match; eauto.
   eapply IHForall2; eauto.
Qed.

Lemma eval_lvalue_lid_disjoint:
  forall ids lids te1 e a a' id ofs k,
  LsemF.eval_lvalue gc1 te1 e a id ofs k ->
  ptree_ids_in (lids++ids) te1 ->
  trans_lsexp ids lids a = OK a' ->
  ~ In ACG_I ids ->
  lid_disjoint a ->
  lid_disjoint a'.
Proof.
  induction a; intros; inv H1; simpl; try tauto.
  +destruct (in_list _ _); inv H5; auto.
  +monadInv H5. destruct a2; simpl; auto.
   destruct H3. subst.
   generalize H2. intros. unfold trans_v.
   apply in_list_false_notin in H2; auto.
   rewrite H2. inv H. inv H8.
   destruct (in_list ACG_I lids) eqn:?; auto.
   -split; auto. eapply IHa1; eauto.
   -destruct H0. inv H.
    *rewrite H0 in H16; auto. congruence.
     apply in_list_false_notin.
     rewrite in_list_app, Heqb,H2; auto.
    *congruence.
   +monadInv H5. inv H. simpl.
    eapply IHa; eauto.
Qed.

Lemma load_env_setnew_inv:
  forall t eh i o v b m,
  load_env t (PTree.set b m eh) i o v ->
  b <> i ->
  load_env t eh i o v.
Proof.
  intros. destruct H as [m1 [t1 [? [? ?]]]].
  exists m1, t1; split; auto.
  rewrite PTree.gso in *; auto.
Qed.

Lemma eval_lvalue_setsame_left:
  forall gc2 ta te' e a b o k,
  eval_lvalue gc2 ta te' e a b o k ->
  forall te m m' t,
  te ! b = Some (m, t) ->
  te' = (PTree.set b (m',t) te) ->
  lid_disjoint a ->
  eval_lvalue gc2 ta te e a b o k.
Proof.
  induction 1; intros; subst; try (econstructor; eauto; fail).
  +constructor 1 with m0; auto.
   rewrite PTree.gss in H; auto. congruence.
  +rewrite PTree.gss in H; auto. congruence.
  +simpl in H4. destruct a1; try tauto. destruct H4; subst.
   apply eval_lvalue_lid_disjoint_not_loopid in H; auto.
   apply eval_Saryacc with aid z; auto.
   eapply IHeval_lvalue; eauto.
   inv H0. inv H4. rewrite PTree.gso in *; auto.
   apply eval_Rlvalue with ACG_I Int.zero Lid; auto.
   constructor 1 with m0; auto.
   eapply load_env_setnew_inv; eauto.
Qed.

Lemma eval_lvalue_setnew_left:
  forall gc2 ta te' e a b o k,
  eval_lvalue gc2 ta te' e a b o k ->
  forall te id m, id <> b ->
  lid_disjoint a ->
  id <> ACG_I ->
  te' = (PTree.set id m te) ->
  eval_lvalue gc2 ta te e a b o k.
Proof.
  induction 1; simpl; intros; subst; try (econstructor; eauto; fail).
  +constructor 1 with m; auto. rewrite PTree.gso in *; auto.
  +constructor 2 with m; auto. rewrite PTree.gso in *; auto.
  +destruct a1; try tauto. destruct H3; subst.
   apply eval_Saryacc with aid z; auto.
   eapply IHeval_lvalue; eauto.
   inv H0. apply eval_Rlvalue with id0 ofs0 k0; auto.
   inv H5. constructor 1 with m0; auto.
   rewrite PTree.gso in *; auto. inv H5.
   eapply load_env_setnew_inv; eauto.
Qed.

Lemma eval_lvalue_setnew_right:
  forall gc2 ta te e' a b o k,
  eval_lvalue gc2 ta te e' a b o k ->
  forall e id m, id <> b ->
  lid_disjoint a ->
  id <> ACG_I ->
  e' = (PTree.set id m e) ->
  eval_lvalue gc2 ta te e a b o k.
Proof.
  induction 1; simpl; intros; subst; try (econstructor; eauto; fail).
  +constructor 3 with m; auto. rewrite PTree.gso in *; auto.
  +destruct a1; try tauto. destruct H3; subst.
   apply eval_Saryacc with aid z; auto.
   eapply IHeval_lvalue; eauto.
   inv H0. inv H5. apply eval_Rlvalue with ACG_I Int.zero Lid; auto.
   constructor 1 with m0; auto.
Qed.

Lemma eval_lvalue_setsame_right:
  forall gc2 ta te e' a b o k,
  eval_lvalue gc2 ta te e' a b o k ->
  forall e m m' t,
  e ! b = Some (m, t) ->
  lid_disjoint a ->
  e' = (PTree.set b (m',t) e) ->
  eval_lvalue gc2 ta te e a b o k.
Proof.
  induction 1; intros; subst; try (econstructor; eauto; fail).
  +constructor 3 with m0; auto. rewrite PTree.gss in *; auto. congruence.
  +simpl in H3. destruct a1; try tauto. destruct H3; subst.
   apply eval_lvalue_lid_disjoint_not_loopid in H; auto.
   apply eval_Saryacc with aid z; auto.
   eapply IHeval_lvalue; eauto.
   inv H0. inv H4.
   apply eval_Rlvalue with ACG_I Int.zero Lid; auto.
   constructor 1 with m0; auto.
Qed.

Lemma locenv_setvaddr_eval_vaddrs:
  forall gc2 ta te1 e1 l dl,
  eval_vaddrs gc2 ta te1 e1 l dl ->
  forall a d v te e, lid_disjoint a ->
  eval_vaddr gc2 ta te e a d ->
  locenv_setvaddr te e d v te1 e1 ->
  Forall (lid_disjoint) l ->
  eval_vaddrs gc2 ta te e l dl.
Proof.
  induction 1; simpl; intros.
  +constructor.
  +inv H4. constructor 2; auto.
   -inv H. constructor; auto. inv H2.
    generalize H; intros A.
    eapply eval_lvalue_lid_disjoint_not_loopid in A; eauto.
    inv H3; inv H13; compare id id0; intros; subst.
    *eapply eval_lvalue_setsame_left; eauto.
    *eapply eval_lvalue_setnew_left; eauto.
    *eapply eval_lvalue_setsame_right; eauto.
    *eapply eval_lvalue_setnew_right; eauto.
   -apply IHForall2 with a d v; auto.
Qed.

Lemma locenv_setvaddrs_exists:
  forall te1 te1' e e' al vl,
  locenv_setvarfs gc1 te1 e al vl te1' e' ->
  forall gc2 ta te2 ids lids al', locenv_match gc1 gc2 ->
  ptree_noids_match ids te1 te2 ->
  ptree_ids_match ids te1 ta ->
  ptree_ids_none (ACG_MEMCPY::ids) te2 ->
  ptree_ids_in (lids++ids) te1 ->
  list_disjoint ids lids ->
  mmap (trans_lsexp ids lids) al = OK al' ->
  Forall lid_disjoint al ->
  ~ In ACG_I ids ->
  exists dl te2', eval_vaddrs gc2 ta te2 e al' dl
    /\ locenv_setvaddrs te2 e dl vl te2' e'
    /\ ptree_noids_match ids te1' te2'
    /\ ptree_ids_match ids te1' ta
    /\ ptree_ids_none (ACG_MEMCPY::ids) te2'
    /\ ptree_ids_in (lids++ids) te1'
    /\ Forall lid_disjoint al'.
Proof.
  induction 1; intros.
  +exists nil, te2. inv H5. repeat (split; auto).
   constructor. constructor.
  +simpl in H7. monadInv H7. inv H8. generalize H; intros A.
   eapply locenv_setvaddr_exists in H;eauto.
   destruct H as [d [te21 [? [? [? [? [? ?]]]]]]].
   destruct IHlocenv_setvarfs with gc2 ta te21 ids lids x0 as [ds [te2' [? [? [? [? [? [? ?]]]]]]]]; auto.
   cut (lid_disjoint x). intros A1.
   exists (d::ds), te2'. repeat (split; auto).
   -constructor 2; auto.
    eapply locenv_setvaddr_eval_vaddrs with (a:=x); eauto.
   -constructor 2 with te21 e1; auto.
   -inv A; eapply eval_lvalue_lid_disjoint; eauto.
Qed.

Lemma trans_node_all_correct:
  forall e e' fd vargs vrets,
  LsemD.eval_node prog1 gc1 e e' fd vargs vrets ->
  forall gc2 fd', locenv_match gc1 gc2 ->
  trans_node fd = OK fd' ->
  In fd (node_block prog1) ->
  eval_node prog2 gc2 e e' fd' vargs vrets.
Proof.
  induction 1 using LsemD.eval_node_ind2 with
  ( P0 := fun nid teL e teL' e' s =>
      forall gc2 ta teR ids lids s', locenv_match gc1 gc2 ->
      ptree_noids_match ids teL teR ->
      ptree_ids_match ids teL ta ->
      ptree_ids_none (ACG_MEMCPY::ids) teR ->
      ptree_ids_in (lids++ids) teL ->
      list_disjoint ids lids ->
      trans_stmt ids lids s = OK s' ->
      ~ In ACG_I ids ->
      exists teR', LsemC.eval_stmt prog2 gc2 ta teR e teR' e' s'
       /\ ptree_noids_match ids teL' teR'
       /\ ptree_ids_match ids teL' ta
       /\ ptree_ids_none (ACG_MEMCPY::ids) teR'
       /\ ptree_ids_in (lids++ids) teL'
  ); intros.
 +(*eval_node*)
  destruct alloc_variables_exists with (nd_vars f) empty_locenv as [teR A].
  destruct alloc_variables_exists with (nd_args f) empty_locenv as [ta A1].
  destruct H1 as [B [B1 [B2 B4]]].
  unfold allidsof, allvarsof in *. repeat rewrite map_app in B.
  rewrite app_ass in B. apply list_norepet_app in B.
  destruct B as [B [B5 B6]].
  eapply list_disjoint_app_right in B6; eauto.
  destruct B6 as [B6 B7].
  assert (A3: ptree_noids_match (map fst (nd_args f)) te teR
          /\ ptree_ids_match (map fst (nd_args f)) te ta
          /\ ptree_ids_in (map fst (nd_vars f) ++ map fst (nd_args f)) te).
    eapply alloc_variables_ptree_ids_match; eauto.
    apply list_norepet_app in B5; intuition.
  destruct A3 as [A3 [A4 A5]].
  destruct locenv_match_setvars_exists with te (nd_args f) vas te1 (map fst (nd_args f)) (map fst (nd_vars f)) ta teR
    as [ta1 [A6 [? [? ?]]]]; auto.
    red; intros; auto.
  monadInv H5. simpl in *. monadInv EQ.
  apply list_disjoint_sym in B6; auto.
  apply ID_RANGE in H6.
  apply ids_plt_le_notin with (id:=ACG_MEMCPY) in H6; try (unfold Ple; omega).
  destruct IHeval_node with gc2 ta1 teR (map fst (nd_args f)) (map fst (nd_vars f)) x0  as [teR' [? [? [? ?]]]]; auto.
    eapply alloc_variables_ptree_ids_none; eauto.
    red; simpl; intros. destruct H5; subst.
    red; intros. subst. apply H6. apply in_or_app. left.
     unfold allidsof, allvarsof. repeat rewrite map_app.
     apply in_or_app. left. apply in_or_app; auto.
    apply B6; auto.
    red; intros. apply B4. rewrite map_app, app_ass.
    apply in_or_app; auto.
  apply exec_node with ta ta1 teR teR';simpl; auto.
  rewrite map_app; auto.
 +(*eval_Sassign*)
  monadInv H6.
  eapply eval_eqf_exists with (a':=(x,trans_sexp (trans_v ids lids) a)) in H; eauto.
  destruct H as [teR' [? [? [? [? ?]]]]].
  exists teR'. repeat (split; auto).
  apply eval_Sassign; auto.
  unfold trans_eqf. simpl. rewrite EQ; auto.
 +(*eval_Scall*)
  monadInv H18.
  cut (ptree_ids_none ids teR). intros.
  eapply locenv_setvaddrs_exists in H5; eauto.
  destruct H5 as [dl [teR' [? [? [? [? [? [? ?]]]]]]]].
  assert(A: exists fd', trans_node fd = OK fd'
             /\ call_func (node_block prog2) cdef fd').
    eapply trans_call_func; eauto.
  destruct A as [fd' [A A1]].
  exists teR'. repeat (split; auto).
  subst. apply eval_Scall with ef ef' vl dl fd' vargs vargs' vrets; auto.
  -eapply eval_sexps_match; eauto.
  -rewrite trans_sexps_typeof; auto.
  -eapply locenv_getmvls_match; eauto.
  -monadInv A. monadInv EQ0; auto.
  -apply IHeval_node; auto.
   eapply call_func_in; eauto.
  -monadInv A. monadInv EQ0. simpl. unfold func in *. rewrite <- H7.
   eapply trans_lsexps_typeof; eauto.
  -rewrite trans_sexps_typeof; auto.
   monadInv A. monadInv EQ0. simpl. unfold func in *. congruence.
  -eapply lvalue_list_norepet_match; eauto.
  -eapply assign_list_disjoint_match; eauto.
  -assert(A2: In (callid cdef) ids \/ ~ In (callid cdef) ids) by tauto.
   destruct A2. apply H15; simpl; auto. rewrite <-H13; auto.
  -red; intros. apply H15; simpl; auto.
 +(*eval_Sfor_start*)
  monadInv H7. monadInv EQ. generalize EQ2; intros.
  eapply eval_eqf_exists in EQ2; eauto.
  destruct EQ2 as [teR1 [A [A1 [A2 [A3 ?]]]]].
  simpl in *.
  destruct IHeval_node with gc2 ta teR1 ids lids (Sfor None (trans_sexp (trans_v ids lids) a2) x0 x1) as [teR' [? [? [? [? ?]]]]]; auto.
    rewrite EQ1. simpl. rewrite EQ0. simpl; auto.
  exists teR'. repeat (split; auto).
  apply eval_Sfor_start with teR1 e1; auto.
 +(*eval_Sfor_false*)
  monadInv H6.
  exists teR. repeat (split; auto).
  apply eval_Sfor_false; auto.
  eapply eval_sexp_match; eauto.
  red; intros. apply H3; simpl; auto.
 +(*eval_Sfor_loop*)
  monadInv H9.
  destruct IHeval_node with gc2 ta teR ids lids x0 as [teR1 [? [? [? [? ?]]]]]; auto.
  eapply eval_eqf_exists in H1; eauto.
  destruct H1 as [teR2 [? [? [? [? ?]]]]].
  simpl in *.
  destruct IHeval_node0 with gc2 ta teR2 ids lids (Sfor None (trans_sexp (trans_v ids lids) a2) x x0) as [teR' [? [? [? ?]]]]; auto.
    rewrite EQ1. simpl. rewrite EQ. simpl; auto.
  exists teR'. repeat (split; auto).
  eapply eval_Sfor_loop; eauto.
  eapply eval_sexp_match; eauto.
  red; intros. apply H6; simpl; auto.
 +(*eval_Sskip*)
  inv H5. exists teR. repeat (split; auto). constructor.
 +(*eval_Sseq *)
  monadInv H7.
  destruct IHeval_node with gc2 ta teR ids lids x as [teR1 [? [? [? [? ?]]]]]; auto.
  destruct IHeval_node0 with gc2 ta teR1 ids lids x0 as [teR' [? [? [? [? ?]]]]]; auto.
  exists teR'. repeat (split; auto).
  eapply eval_Sseq; eauto.
 +(*eval_Sif*)
  monadInv H8.
  destruct IHeval_node with gc2 ta teR ids lids (if b then x else x0) as [teR1 [? [? [? [? ?]]]]]; auto.
    destruct b; auto.
  exists teR1. repeat (split; auto).
  apply eval_Sif with v b; auto.
  -eapply eval_sexp_match; eauto.
   red; intros. apply H5; simpl; auto.
  -rewrite trans_sexp_typeof; auto.
 +(*eval_Scase*)
  monadInv H8. inv H1.
  eapply eval_eqf_exists with (a':=(x,trans_sexp (trans_v ids lids) a)) in H15; eauto.
  destruct H15 as [teR' [? [? [? [? ?]]]]].
  exists teR'. repeat (split; auto).
  apply eval_Scase with i (trans_sexp (trans_v ids lids) a); eauto.
  -eapply eval_sexp_match; eauto.
   red; intros. apply H5; simpl; auto.
  -eapply trans_select_case; eauto.
  -apply eval_Sassign; auto.
  -unfold trans_eqf. simpl. rewrite EQ; auto.
Qed.

Lemma exec_prog_correct:
  forall fd e n maxn vass vrss,
  exec_prog prog1 gc1 LsemD.eval_node fd e n maxn vass vrss ->
  forall gc2 fd', locenv_match gc1 gc2 ->
  trans_node fd = OK fd' ->
  In fd (node_block prog1) ->
  exec_prog prog2 gc2 eval_node fd' e n maxn vass vrss.
Proof.
  induction 1; intros.
  +constructor 1; auto.
  +constructor 2 with e'; auto.
   -monadInv H4. monadInv EQ. auto.
   -eapply trans_node_all_correct; eauto.
Qed.

End NODE_CORRECT.

Lemma trans_typedef_alloc_globals_exists:
  forall l gc, exists gc', alloc_globals gc (map trans_typedef l) = Some gc'.
Proof.
  induction l; simpl; intros.
  exists gc. auto.
  unfold alloc. simpl. rewrite store_zeros_zero; auto.
Qed.

Lemma init_genvc_norepet_match:
  forall l2 l1 gc1,
  init_genvc l2 = Some gc1 ->
  exists gc2, init_genvc ((map trans_typedef l1)++l2) = Some gc2
    /\ locenv_match gc1 gc2.
Proof.
  unfold init_genvc. intros.
  destruct trans_typedef_alloc_globals_exists with l1 empty_locenv as [gc2 ?]; auto.
  destruct alloc_globals_match with l2 empty_locenv gc1 gc2 as [gc2' [? ?]]; auto.
  red. intros. rewrite PTree.gempty in *. congruence.
  exists gc2'. split; auto.
  eapply alloc_globals_app; eauto.
Qed.

Lemma init_genvc_match:
  forall gc1, init_genvc (const_block prog1) = Some gc1 ->
  exists gc2, init_genvc (const_block prog2) = Some gc2
    /\ locenv_match gc1 gc2.
Proof.
  intros. monadInv TRANSL.
  simpl in *.
  eapply init_genvc_norepet_match; eauto.
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

Lemma initial_state_match:
  forall gc1 e main1,
  initial_state prog1 gc1 LsemD.eval_node main1 e ->
  exists main2 gc2, initial_state prog2 gc2 LsemC.eval_node main2 e
    /\ trans_node main1 = OK main2
    /\ locenv_match gc1 gc2
    /\ gc1 ! ACG_I = None
    /\ In main1 (node_block prog1).
Proof.
  induction 1; simpl; intros.
  destruct init_genvc_match with gc1 as [gc2 [? ?]]; auto.
  generalize H0 H1; intros A1 A2.
  apply find_funcs_monad_exits with (f:= trans_node) (l2:= node_block prog2) in H0; auto.
  apply find_funcs_monad_exits with (f:= trans_node) (l2:= node_block prog2) in H1; auto.
  destruct H0 as [fi2 [? ?]]. destruct H1 as [main2 [? ?]].
  apply init_genvc_none in H.
  exists main2, gc2. repeat (split; auto).
  -constructor 1 with e fi2 vr; auto.
    *monadInv TRANSL. auto.
    *monadInv TRANSL. auto.
    *monadInv H0. monadInv EQ. monadInv H1. monadInv EQ. auto.
    *monadInv H1. monadInv EQ; auto.
    *monadInv H1. monadInv EQ; auto.
    *monadInv H1. monadInv EQ; auto.
    *eapply trans_node_all_correct; eauto.
     eapply find_funct_in2; eauto.
  -eapply find_funct_in2; eauto.
  -monadInv TRANSL. simpl. auto.
  -intros ? ? A. monadInv A. auto.
  -monadInv TRANSL. auto.
  -intros ? ? A. monadInv A. auto.
Qed.

Theorem trans_program_correct:
  forall gc1 e main1 vass vrss maxn,
  initial_state prog1 gc1 LsemD.eval_node main1 e ->
  exec_prog prog1 gc1 LsemD.eval_node main1 e 1 maxn vass vrss ->
  exists main2 gc2, initial_state prog2 gc2 LsemC.eval_node main2 e
    /\ exec_prog prog2 gc2 LsemC.eval_node main2 e 1 maxn vass vrss.
Proof.
  intros.
  destruct initial_state_match with gc1 e main1 as [main2 [gc2 [? [? [? [? ?]]]]]]; auto.
  exists main2, gc2. split; auto.
  eapply exec_prog_correct; eauto.
Qed.

Theorem trans_gids_norepet:
  list_norepet (map fst (const_block prog2) ++ map fst (node_block prog2)).
Proof.
  monadInv TRANSL.
  simpl in *. repeat rewrite map_app.
  rewrite map_map. simpl.
  eapply trans_nodes_fids_eq in EQ; eauto.
  rewrite <-EQ. unfold globidsof in *.
  rewrite map_map. simpl.
  rewrite <-map_app. auto.
  intros. monadInv H; auto.
Qed.

End CORRECTNESS.
