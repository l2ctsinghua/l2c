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
Require Import Maps.
Require Import Memdata.
Require Import Integers.
Require Import List.
Require Import ExtraList.
Require Import Lident.
Require Import Ctypes.
Require Import Cltypes.
Require Import Ltypes.
Require Import Lustre.
Require Import LustreS.
Require Import Lint.
Require Import Lvalues.
Require Import Lenv.
Require Import Lenvmatch.
Require Import Lsem.
Require Import LsemT.
Require Import LsemS.
Require Import Toposort.
Require Import Permutation.

Section CORRECTNESS.

Variable progT: LustreS.program.

Hypothesis ID_RANGE:
  ids_range ACG_B (node_block progT).

Hypothesis GID_RANGE:
  ids_plt ACG_EQU (globidspltof progT).

Definition env_none(e: locenv): Prop :=
  e ! ACG_I = None /\ e ! ACG_B = None.

Definition ptree_noids_none(l: list ident)(te: locenv): Prop :=
  forall id, ~ In id l -> te ! id = None.

Definition locenv_matcht(l: list (ident*type))(te eh1 eh2: locenv): Prop :=
  ptree_noids_match (map fst l) eh1 eh2
  /\ locenv_match te eh2
  /\ ptree_ids_none (map fst l) eh1
  /\ locenv_range_perm_vars eh2 l
  /\ ptree_noids_none (map fst l) te.

Lemma locenv_matcht_empty_locenv:
  forall l te eh1 eh2,
  locenv_matcht l te eh1 eh2 ->
  locenv_matcht l empty_locenv eh1 eh2.
Proof.
  unfold locenv_matcht, locenv_match.
  intuition. rewrite PTree.gempty in *. congruence.
  red. intros. apply PTree.gempty.
Qed.

Lemma alloc_variables_match:
  forall eh1 l l1 eh1',
  alloc_variables eh1 l eh1' ->
  list_disjoint (ACG_I :: nil) (map fst l) ->
  forall eh2, ptree_noids_match (map fst l1) eh1 eh2 ->
  ptree_ids_none (map fst l1) eh1 ->
  list_norepet (map fst l) ->
  list_norepet (map fst l1) ->
  (forall a, In a l1 -> a = (ACG_I, type_int32s)) ->
  exists eh2', alloc_variables eh2 (l1++l) eh2'
    /\ locenv_matcht l1 empty_locenv eh1' eh2'.
Proof.
  induction 1; intros.
  +rewrite <-app_nil_end.
   destruct alloc_variables_exists with l1 eh2 as [eh2' ?].
   exists eh2'. split; auto.
   repeat (split; eauto).
   -red; intros. symmetry.
    rewrite alloc_variables_notin_eq with (e:=eh2) (al:=l1); auto.
    rewrite H0; auto.
   -red. intros. rewrite PTree.gempty in *. congruence.
   -apply alloc_variables_range_perm with eh2; auto.
    intros. apply H4 in H6.
    unfold Int.max_signed.
    inv H6; simpl; omega.
   -red. intros. apply PTree.gempty.
  +destruct IHalloc_variables with (PTree.set id (alloc (sizeof ty),ty) eh2) as [eh2' [? ?]]; auto.
   -red. intros. eapply H0; eauto. simpl; auto.
   -apply ptree_noids_match_setsame; auto.
   -red. intros. rewrite PTree.gso; auto.
    eapply H0; simpl; eauto. apply in_map_iff in H6.
    destruct H6 as [? [? ?]]. subst. apply H5 in H7.
    subst; auto.
   -inv H3; auto.
   -exists eh2'. split; auto.
    apply alloc_variables_permut with ((id, ty) :: l1 ++ vars); auto.
    apply Permutation_cons_app; auto.
    constructor; auto.
    apply list_norepet_permut with (map fst (l1 ++ (id, ty) :: vars)).
    rewrite map_app. apply list_norepet_app; intuition.
    red; intros. apply H0; auto.
    apply in_map_iff in H8.
    destruct H8 as [? [? A2]]. subst.
    apply H5 in A2. subst. simpl; auto.
    apply Permutation_map. apply Permutation_sym.
    apply Permutation_cons_app; auto.
Qed.

Lemma locenv_matcht_store_env_exists:
  forall l ty e1 id o v e1' e2 te,
  store_env ty e1 id o v e1' ->
  locenv_matcht l te e1 e2 ->
  exists e2', store_env ty e2 id o v e2'
    /\ locenv_matcht l te e1' e2'.
Proof.
  unfold locenv_matcht.
  induction 1. intros. intuition.
  exists (PTree.set id (m',t) e2). repeat split; auto.
  +constructor 1 with m; auto.
   rewrite <-H3; auto. red; intros.
   rewrite H4 in H; auto. congruence.
  +eapply ptree_noids_match_setsame; eauto.
  +eapply locenv_match_addnewid; eauto.
   rewrite H7; auto. red; intros.
   rewrite H4 in H; auto. congruence.
  +red; intros. rewrite PTree.gso; auto.
   red; intros. subst. rewrite H4 in H; auto. congruence.
  +apply locenv_range_perm_vars_setid with (m:=m); auto.
   rewrite <-H3; auto. red; intros.
   rewrite H4 in H; auto. congruence.
   eapply store_mvl_length; eauto.
Qed.

Lemma locenv_matcht_store_env_te_exists:
  forall l t te id v te' e1 e2,
  store_env t te id Int.zero v te' ->
  locenv_matcht l te e1 e2 ->
  In (id, t) l ->
  exists e2', store_env t e2 id Int.zero v e2'
    /\ locenv_matcht l te' e1 e2'.
Proof.
  unfold locenv_matcht.
  intros. inv H. intuition.
  destruct H6 with id t as [m0 [A [A1 A2]]]; auto.
  exists (PTree.set id (m', t0) e2). repeat split; auto.
  +constructor 1 with m; auto.
  +red; intros. rewrite PTree.gso; auto.
   red; intros. subst. rewrite H8 in H2; auto.
   congruence.
  +apply locenv_match_addsameid; auto.
  +eapply locenv_range_perm_vars_setid; eauto.
   eapply store_mvl_length; eauto.
  +red; intros. rewrite PTree.gso; auto.
   red; intros. subst. rewrite H8 in H2; auto.
   congruence.
Qed.

Lemma locenv_setvars_exists:
  forall l1 eh1 l vl eh1',
  locenv_setvars eh1 l vl eh1' ->
  forall te eh2, locenv_matcht (mkloopmapw l1) te eh1 eh2 ->
  exists eh2', locenv_setvars eh2 l vl eh2'
    /\ locenv_matcht (mkloopmapw l1) te eh1' eh2'.
Proof.
  induction 1; simpl; intros.
  econstructor. split; eauto. econstructor.
  eapply locenv_matcht_store_env_exists in H0; eauto.
  destruct H0 as [eh1' [? ?]].
  destruct IHlocenv_setvars with te eh1' as [eh2' [? ?]]; auto.
  exists eh2'. split; auto. constructor 2 with eh1' m; auto.
  destruct H2 as [? [? [? ?]]]. erewrite <-H2; eauto.
  red; intros. rewrite H7 in H; auto. congruence.
Qed.

Lemma alloc_store_same:
  forall chunk v m m',
  store chunk (alloc (size_chunk chunk)) 0 v = Some m' ->
  range_perm m 0 (size_chunk chunk) ->
  size_chunk chunk = Z_of_nat (length m) ->
  store chunk m 0 v = Some m'.
Proof.
  unfold store. intros.
  destruct (valid_access_dec (alloc (size_chunk chunk)) chunk 0); inv H.
  rewrite pred_dec_true; auto. f_equal. simpl.
  apply replace_map_all_eq; auto.
  unfold alloc. rewrite H1, length_list_repeat, nat_of_Z_of_nat; auto.
  rewrite encode_val_length. unfold size_chunk_nat.
  rewrite H1, nat_of_Z_of_nat. omega.
  eapply length_valid_access; eauto.
  unfold alloc. rewrite H1, length_list_repeat, nat_of_Z_of_nat; auto.
Qed.

Lemma locenv_matcht_setloop_match:
  forall (gc: locenv) l eh te eh1 c t id m' v,
  locenv_matcht l te eh eh1 ->
  store c (alloc (sizeof t)) 0 v = Some m' ->
  In (id, t) l ->
  access_mode t = By_value c ->
  locenv_matcht l (PTree.set id (m',t) te) eh (PTree.set id (m',t) eh1).
Proof.
  unfold locenv_matcht, env_none.
  intros. destruct H as [? [? [? [? ?]]]].
  repeat split; auto.
  +red; intros. rewrite PTree.gso; auto.
   red; intros. subst.
   apply in_map with (f:=fst) in H1. auto.
  +eapply locenv_match_addsameid; eauto.
  +red; intros. destruct H5 with id0 ty as [m1 [A [A1 A2]]]; auto.
   destruct H5 with id t as [m2 [B [B1 B2]]]; auto.
   red; intros.
   compare id id0; intros; subst.
   -rewrite A in B. inv B.
    exists m'. rewrite PTree.gss; auto. split; [| split]; auto.
    apply store_length in H0. rewrite <-H0.
    unfold alloc. rewrite length_list_repeat. auto.
    generalize (sizeof_pos t); intros.
    rewrite nat_of_Z_eq; omega.
    eapply store_valid_access in H0; eauto.
    destruct H0.
    erewrite <-sizeof_chunk_eq; eauto.
   -exists m1. rewrite PTree.gso; auto.
  +red; intros. rewrite PTree.gso; auto.
   red. intros. subst.
   apply in_map with (f:=fst) in H1. auto.
Qed.

Lemma env_none_ptree_ids_none:
  forall gc l, env_none gc ->
  ptree_ids_none (map fst (mkloopmapw l)) gc.
Proof.
  intros. red; intros. destruct H.
  apply mkloopmapw_idrange in H0. subst; auto.
Qed.

Lemma ptree_noids_match_locenv_match:
  forall gc l e1 e2 ,
  ptree_noids_match (map fst (mkloopmapw l)) e1 e2 ->
  ptree_ids_none (map fst (mkloopmapw l)) e1 ->
  env_none gc ->
  locenv_match e1 e2 /\ locenv_disjoint gc e1 e2.
Proof.
  intros. split; intros; red; intros.
  +rewrite <-H; auto. red; intros.
   rewrite H0 in H2; auto. congruence.
  +assert(In id (map fst (mkloopmapw l)) \/ ~ In id (map fst (mkloopmapw l))). tauto.
   eapply env_none_ptree_ids_none with (l:=l) in H1; eauto.
   destruct H4. rewrite H1 in H3; auto. congruence.
   rewrite H in H2; auto.
Qed.

Lemma locenv_matcht_simpl:
  forall gc l te e1 e2 ,
  locenv_matcht (mkloopmapw l) te e1 e2 ->
  env_none gc ->
  locenv_match e1 e2 /\ locenv_disjoint gc e1 e2.
Proof.
  intros. destruct H as [? [? [? ?]]].
  eapply ptree_noids_match_locenv_match; eauto.
Qed.

Lemma comp_funcs_id_ptree_none:
  forall aid ty l (e1 e2: locenv),
  find_funct (type_block progT) aid = Some (aid, ty) ->
  ptree_noids_match l e1 e2 ->
  incl l (ACG_I :: nil) ->
  is_arystr ty = true ->
  e1 ! (comp_funcs_id aid) = None ->
  e2 ! (comp_funcs_id aid) = None.
Proof.
  intros.
  rewrite <-H0; auto. red; intros.
  apply H1 in H4. simpl in *.
  apply find_funct_in2 in H.
  eapply flat_map_filter_type_in in H; eauto.
  cut (Plt ACG_EQU (comp_funcs_id aid)). intros.
  destruct H4 as [ | ]; try tauto.
  rewrite <-H4 in *. unfold Plt, ACG_EQU, ACG_I in *. omega.
  apply GID_RANGE. apply in_or_app. right. apply in_or_app; auto.
Qed.

Lemma mkloopmapw_incl:
  forall l, incl (map fst (mkloopmapw l)) (ACG_I :: nil).
Proof.
  intros. red; simpl; intros.
  apply in_map_iff in H. destruct H as [? [? ?]].
  subst. apply mkloopmapw_range in H0.
  subst; auto.
Qed.

Lemma eval_typecmp_match:
  forall gc e1 a1 a2 b,
  eval_typecmp gc (type_block progT) e1 a1 a2 b ->
  forall l e2 ,ptree_noids_match (map fst (mkloopmapw l)) e1 e2 ->
  ptree_ids_none (map fst (mkloopmapw l)) e1 ->
  env_none gc ->
  eval_typecmp gc (type_block progT) e2 a1 a2 b.
Proof.
  intros until e1.
  induction 1 using eval_typecmp_ind2 with
  ( P0 := fun a1 a2 num aty i b =>
      forall l e2 ,ptree_noids_match (map fst (mkloopmapw l)) e1 e2 ->
      ptree_ids_none (map fst (mkloopmapw l)) e1 ->
      env_none gc ->
      eval_arycmp gc (type_block progT) e2 a1 a2 num aty i b)
  ( P1 := fun a1 a2 fld ftl b =>
      forall l e2 ,ptree_noids_match (map fst (mkloopmapw l)) e1 e2 ->
      ptree_ids_none (map fst (mkloopmapw l)) e1 ->
      env_none gc ->
      eval_strcmp gc (type_block progT) e2 a1 a2 fld ftl b);
  intros; try (econstructor; eauto; fail).
 +apply eval_typecmp_chunk with chunk v; auto.
  eapply eval_sexp_match; eauto;
  eapply ptree_noids_match_locenv_match; eauto.
 +destruct ptree_noids_match_locenv_match with gc l e1 e2; auto.
  eapply eval_typecmp_array; eauto;
  try eapply eval_sexp_match; eauto.
  eapply comp_funcs_id_ptree_none; eauto.
  eapply mkloopmapw_incl; eauto.
 +destruct ptree_noids_match_locenv_match with gc l e1 e2; auto.
  eapply eval_typecmp_struct; eauto;
  try eapply eval_sexp_match; eauto.
  eapply comp_funcs_id_ptree_none; eauto.
  eapply mkloopmapw_incl; eauto.
Qed.

Lemma eval_expr_match:
  forall gc e1 s t v,
  eval_expr gc (type_block progT) e1 s t v ->
  forall l e2 ,ptree_noids_match (map fst (mkloopmapw l)) e1 e2 ->
  ptree_ids_none (map fst (mkloopmapw l)) e1 ->
  env_none gc ->
  eval_expr gc (type_block progT) e2 s t v.
Proof.
  induction s; intros; inv H.
  +econstructor; eauto.
   eapply eval_sexp_match; eauto;
   eapply ptree_noids_match_locenv_match; eauto.
  +eapply eval_Earyprj_in; eauto.
   eapply eval_sexp_match; eauto;
   eapply ptree_noids_match_locenv_match; eauto.
   eapply eval_sexps_match; eauto;
   eapply ptree_noids_match_locenv_match; eauto.
  +eapply eval_Earyprj_out; eauto.
   eapply eval_sexps_match; eauto;
   eapply ptree_noids_match_locenv_match; eauto.
   eapply eval_sexp_match; eauto;
   eapply ptree_noids_match_locenv_match; eauto.
  +econstructor; eauto;
   eapply eval_sexp_match; eauto;
   eapply ptree_noids_match_locenv_match; eauto.
  +econstructor; eauto;
   eapply eval_sexp_match; eauto;
   eapply ptree_noids_match_locenv_match; eauto.
  +eapply eval_Eprefix; eauto.
   eapply eval_sexps_match; eauto;
   eapply ptree_noids_match_locenv_match; eauto.
  +eapply eval_Etypecmp; eauto.
   eapply eval_typecmp_match; eauto.
Qed.

Lemma eval_for_init_correct:
  forall gc l ta ta1 te1 te2,
  locenv_matcht (mkloopmapw l) ta te1 te2 ->
  store_loop type_int32s ta ACG_I (Vint Int.zero) ta1 ->
  In (ACG_I, type_int32s) (mkloopmapw l) ->
  exists te2', eval_eqf gc te2 te2' loop_init
     /\ locenv_matcht (mkloopmapw l) ta1 te1 te2'.
Proof.
  intros.
  assert(A: locenv_range_perm_vars te2 (mkloopmapw l)).
    inv H; intuition.
  destruct A with ACG_I type_int32s as [m [A1 [A2 A3]]]; auto.
  inv H0. inv H3. inv H0.
  econstructor. rewrite Int.unsigned_zero in *.
  split. econstructor; eauto.
  constructor; simpl; auto.
  repeat econstructor; eauto.
  eapply alloc_store_same; eauto.
  constructor 1 with Mint32; eauto.
  eapply locenv_matcht_setloop_match; eauto.
  destruct H0; inv H0.
Qed.

Lemma eval_self_add:
  forall gc te eh2 v,
  eval_sexp gc te (self_add ACG_I) v ->
  locenv_match te eh2 ->
  env_none gc ->
  eval_sexp gc eh2 (self_add ACG_I) v.
Proof.
  intros. inv H.
  +apply eval_Sbinop with v1 v2; auto.
   eapply eval_sexp_svar_match; eauto.
   destruct H1; auto.
   eapply eval_sexp_const; eauto.
  +inv H2.
Qed.

Lemma eval_loop_cond:
  forall gc te eh2 v j,
  eval_sexp gc te (loop_cond j) v ->
  locenv_match te eh2 ->
  env_none gc ->
  eval_sexp gc eh2 (loop_cond j) v.
Proof.
  intros. inv H.
  +apply eval_Sbinop with v1 v2; auto.
   eapply eval_sexp_svar_match; eauto.
   destruct H1; auto.
   eapply eval_sexp_const; eauto.
  +inv H2.
Qed.

Lemma locenv_matcht_setlvar_exists:
  forall gc l eh1 a v eh1',
  locenv_setlvar gc eh1 a v eh1' ->
  forall te eh2, locenv_matcht (mkloopmapw l) te eh1 eh2 ->
  env_none gc ->
  exists eh2', locenv_setlvar gc eh2 a v eh2'
    /\ locenv_matcht (mkloopmapw l) te eh1' eh2'.
Proof.
  induction 1. intros.
  eapply locenv_matcht_store_env_exists in H0; eauto.
  destruct H0 as [eh2' [? ?]].
  exists eh2'. split; auto.
  constructor 1 with b ofs; eauto.
  eapply eval_lvalue_match; eauto;
  eapply locenv_matcht_simpl; eauto.
Qed.

Lemma eval_sassign_correct:
  forall gc k l e e1 te1 te1' ta ta1 ta2 te2 p s ,
  LsemT.eval_stmt false progT gc k te1 e te1' e1 (Sassign p s) ta ta1 ->
  locenv_matcht (mkloopmapw l) ta2 te1 te2 ->
  env_none gc ->
  exists te2', eval_stmt progT gc k te2 e te2' e1 (Sassign p s)
    /\ locenv_matcht (mkloopmapw l) ta2 te1' te2' .
Proof.
  intros. inv H.
  eapply locenv_matcht_setlvar_exists in H14; eauto.
  destruct H14 as [te2' [? ?]]; auto.
  exists te2'. split; auto.
  eapply eval_Sassign; eauto.
  destruct H0; intuition.
  eapply eval_expr_match; eauto.
Qed.

Lemma eval_for_start_correct:
  forall s nk l gc ta te1 te1' te2 e,
  locenv_matcht (mkloopmapw l) ta te1 te2 ->
  LsemT.eval_stmts false progT gc nk te1 e te1' e (initstmtsof1 s) ->
  env_none gc ->
  exists te2', eval_stmts progT gc nk te2 e te2' e (initstmtsof2 s)
     /\ locenv_matcht (mkloopmapw l) ta te1' te2'.
Proof.
  remember ACG_B.
  destruct s; simpl; intros;
  try (inv H0; repeat (econstructor; eauto); fail).
  +inv H0. inv H10. eapply eval_sassign_correct in H9; eauto.
   destruct H9 as [e2' [? ?]]. exists e2'; split; eauto. repeat (econstructor; eauto).
  +inv H0. inv H10. eapply eval_sassign_correct in H9; eauto.
   destruct H9 as [e2' [? ?]]. exists e2'; split; eauto. repeat (econstructor; eauto).
  +inv H0. inv H10. eapply eval_sassign_correct in H9; eauto.
   destruct H9 as [e2' [? ?]]. exists e2'; split; eauto. repeat (econstructor; eauto).
  +inv H0. inv H10. eapply eval_sassign_correct in H9; eauto.
   destruct H9 as [e2' [? ?]]. exists e2'; split; eauto. repeat (econstructor; eauto).
  +inv H0. inv H10. eapply eval_sassign_correct in H9; eauto.
   destruct H9 as [e2' [? ?]]. exists e2'; split; eauto. repeat (econstructor; eauto).
Qed.

Lemma locenv_matcht_setlvar_te_exists:
  forall gc l te id t v te',
  locenv_setlvar gc te (Svar id t) v te' ->
  forall eh1 eh2, locenv_matcht (mkloopmapw l) te eh1 eh2 ->
  In (id, t) (mkloopmapw l) ->
  exists eh2', locenv_setlvar gc eh2 (Svar id t) v eh2'
    /\ locenv_matcht (mkloopmapw l) te' eh1 eh2'.
Proof.
  intros. inv H. generalize H0; intros.
  destruct H0 as [A [A1 [A2 [A3 A4]]]].
  inv H2.
  eapply locenv_matcht_store_env_te_exists in H3; simpl; eauto.
  destruct H3 as [eh2' [? ?]].
  exists eh2'. split; auto.
  constructor 1 with b Int.zero; eauto.
  constructor 1 with m; auto.
Qed.

Lemma eval_saryacc_loopid:
  forall gc eh1 a i t v eh2,
  eval_sexp gc eh1 (Saryacc a (Sconst (Cint i) type_int32s) t) v ->
  locenv_match eh1 eh2 ->
  eval_sexp gc eh2 (Svar ACG_I type_int32s) (Vint i) ->
  locenv_disjoint gc eh1 eh2 ->
  eval_sexp gc eh2 (Saryacc a (Svar ACG_I type_int32s) t) v.
Proof.
  intros. eapply eval_aryacc_app1; eauto.
  eapply eval_sexp_match; eauto.
Qed.

Lemma locenv_setlvar_loopid:
  forall gc eh a i t v eh',
  locenv_setlvar gc eh (Saryacc a (Sconst (Cint i) type_int32s) t) v eh' ->
  eval_sexp gc eh (Svar ACG_I type_int32s) (Vint i) ->
  locenv_setlvar gc eh (Saryacc a (Svar ACG_I type_int32s) t) v eh'.
Proof.
  intros. inv H.
  constructor 1 with b ofs; auto.
  inv H1. inv H6. eapply eval_Saryacc; eauto. inv H.
Qed.

Lemma locenv_matcht_setarys_exists:
  forall gc i e1 l tys vl e1',
  locenv_setarys gc (Sconst (Cint i) type_int32s) e1 l tys vl e1' ->
  forall l1 te e2, locenv_matcht (mkloopmapw l1) te e1 e2 ->
  eval_sexp gc te (Svar ACG_I type_int32s) (Vint i) ->
  env_none gc ->
  exists e2', Lsem.locenv_setarys gc (Svar ACG_I type_int32s) e2 l tys vl e2'
    /\ locenv_matcht (mkloopmapw l1) te e1' e2'.
Proof.
  induction 1; simpl; intros.
  +exists e2; split; auto; constructor.
  +generalize H; intros A.
   eapply locenv_matcht_setlvar_exists in H; eauto.
   destruct H as [e21 [? ?]].
   destruct IHlocenv_setarys with l1 te e21 as [e2' [? ?]]; auto.
   exists e2'. split; auto.
   constructor 2 with e21; auto.
   eapply locenv_setlvar_loopid; eauto.
   destruct H1 as [? [? ?]].
   eapply eval_sexp_svar_match; eauto.
   destruct H3; auto.
Qed.

Lemma loopid_mapwid_disjoint_vars:
  forall nid f, In (nid, f) (node_block progT) ->
  list_disjoint (ACG_I::nil) (map fst (allvarsof f)).
Proof.
  intros. apply ID_RANGE in H.
  red. simpl. intros.
  destruct H0 as [ | ]; subst; auto.
  +apply ids_plt_le_notin with ACG_I _ _ in H.
   red. intros. subst. apply H. apply in_or_app; auto.
   unfold Ple, ACG_I, ACG_B. omega.
Qed.

Lemma mkloopmapw_norepet_vars:
  forall nid f, In (nid, f) (node_block progT) ->
  ids_norepet f ->
  list_norepet (map fst (mkloopmapw (nd_stmt f)) ++ map fst (allvarsof f)).
Proof.
  intros.
  apply list_norepet_app. intuition.
  +apply mkloopmapw_norepet.
  +destruct H0 as [? [? ?]]. auto.
  +apply mkloopmapw_disjoint.
   apply loopid_mapwid_disjoint_vars with nid; auto.
Qed.

Lemma locenv_matcht_eval_fbyeqs:
  forall gc te1 te2 eh1 eh2 eqs l,
  eval_fbyeqs gc te1 eh1 eh2 eqs ->
  locenv_matcht (mkloopmapw l) empty_locenv te1 te2 ->
  env_none gc ->
  eval_fbyeqs gc te2 eh1 eh2 eqs.
Proof.
  induction 1; intros; econstructor; eauto.
  inv H.
  +constructor 1 with v v'; auto.
   eapply eval_sexp_match; eauto;
   eapply locenv_matcht_simpl; eauto.
  +constructor 2; auto.
  +constructor.
Qed.

Lemma locenv_matcht_eval_poststmt:
  forall gc te1 te2 eh eh' eqs l,
  eval_poststmt gc te1 eh eqs eh' ->
  locenv_matcht (mkloopmapw l) empty_locenv te1 te2 ->
  env_none gc ->
  eval_poststmt gc te2 eh eqs eh'.
Proof.
  intros. inv H. constructor 1 with eh1; eauto.
  eapply locenv_matcht_eval_fbyeqs; eauto.
Qed.

Lemma trans_prefix_unary_expr_match_ary:
  forall gc te te2 op a1 i t1 t2 v,
  eval_sexp gc te (trans_prefix_unary_expr op (Saryacc a1 (Sconst (Cint i) type_int32s) t1) t2) v ->
  eval_sexp gc te2 (Svar ACG_I type_int32s) (Vint i) ->
  locenv_match te te2 ->
  locenv_disjoint gc te te2 ->
  eval_sexp gc te2 (trans_prefix_unary_expr op (Saryacc a1 (Svar ACG_I type_int32s) t1) t2) v.
Proof.
  intros.
  destruct op; simpl in *; try (eapply eval_saryacc_loopid; eauto);
  inv H; try (inv H3; fail);
  econstructor; eauto; eapply eval_saryacc_loopid; eauto.
Qed.

Lemma trans_prefix_unary_expr_match:
  forall gc te te2 op i t v,
  eval_sexp gc te (trans_prefix_unary_expr op (Sconst (Cint i) type_int32s) t) v ->
  eval_sexp gc te2 (Svar ACG_I type_int32s) (Vint i) ->
  locenv_match te te2 ->
  locenv_disjoint gc te te2 ->
  eval_sexp gc te2 (trans_prefix_unary_expr op (Svar ACG_I type_int32s) t) v.
Proof.
  intros.
  destruct op; simpl in *; inv H; auto; try (inv H3;fail);
  econstructor;eauto; try (inv H5; auto; inv H);
  inv H6; auto; inv H.
Qed.

Lemma eval_for_loop_add_correct:
  forall gc l ta ta1 te1 te2,
  locenv_matcht (mkloopmapw l) ta te1 te2 ->
  eval_eqf gc ta ta1 loop_add ->
  env_none gc ->
  In (ACG_I, type_int32s) (mkloopmapw l) ->
  exists te2', eval_eqf gc te2 te2' loop_add
     /\ locenv_matcht (mkloopmapw l) ta1 te1 te2'.
Proof.
  intros.
  assert(A: locenv_range_perm_vars te2 (mkloopmapw l)).
    inv H; intuition.
  destruct A with ACG_I type_int32s as [m [A1 [A2 A3]]]; auto.
  inv H0. eapply locenv_matcht_setlvar_te_exists with (eh1:=te1) (eh2:=te2) in H10; eauto.
  destruct H10 as [te2' [? ?]].
  exists te2'. split; auto.
  constructor 1 with v v'; eauto.
  eapply eval_self_add; eauto.
  destruct H; intuition.
  destruct H1; auto.
  constructor 1 with Mint32; auto.
Qed.

Lemma eval_typecmp_trans:
  forall gc l eh a1 a2 b,
  eval_typecmp gc l eh a1 a2 b ->
  forall a3 a4,
  typeof a1 = typeof a3 ->
  typeof a2 = typeof a4 ->
  (forall v, eval_sexp gc eh a1 v -> eval_sexp gc eh a3 v) ->
  (forall v, eval_sexp gc eh a2 v -> eval_sexp gc eh a4 v) ->
  (forall id o k, eval_lvalue gc eh a1 id o k -> eval_lvalue gc eh a3 id o k) ->
  (forall id o k, eval_lvalue gc eh a2 id o k -> eval_lvalue gc eh a4 id o k) ->
  eval_typecmp gc l eh a3 a4 b.
Proof.
  intros until eh.
  induction 1 using eval_typecmp_ind2 with
  ( P0 := fun a1 a2 num aty i b =>
      forall a3 a4, typeof a1 = typeof a3 ->
      typeof a2 = typeof a4 ->
      (forall v, eval_sexp gc eh a1 v -> eval_sexp gc eh a3 v) ->
      (forall v, eval_sexp gc eh a2 v -> eval_sexp gc eh a4 v) ->
      (forall id o k, eval_lvalue gc eh a1 id o k -> eval_lvalue gc eh a3 id o k) ->
      (forall id o k, eval_lvalue gc eh a2 id o k -> eval_lvalue gc eh a4 id o k) ->
      eval_arycmp gc l eh a3 a4 num aty i b)
  ( P1 := fun a1 a2 fld ftl b =>
      forall a3 a4, typeof a1 = typeof a3 ->
      typeof a2 = typeof a4 ->
      (forall v, eval_sexp gc eh a1 v -> eval_sexp gc eh a3 v) ->
      (forall v, eval_sexp gc eh a2 v -> eval_sexp gc eh a4 v) ->
      (forall id o k, eval_lvalue gc eh a1 id o k -> eval_lvalue gc eh a3 id o k) ->
      (forall id o k, eval_lvalue gc eh a2 id o k -> eval_lvalue gc eh a4 id o k) ->
      eval_strcmp gc l eh a3 a4 fld ftl b);
  intros.
 +eapply eval_typecmp_chunk with chunk v; eauto.
  congruence. congruence.
  inv H1. apply eval_Sbinop with v1 v2; auto.
  congruence. congruence. inv H9.
 +eapply eval_typecmp_array; eauto.
  congruence. congruence.
 +eapply eval_typecmp_struct; eauto.
  congruence. congruence.
 +apply eval_arycmp_loop; eauto.
  apply IHeval_typecmp; auto; intros.
  eapply eval_aryacc_app3; eauto.
  eapply eval_aryacc_app3; eauto.
  inv H8. apply eval_Saryacc with aid z; auto. congruence. congruence.
  inv H8. apply eval_Saryacc with aid z; auto. congruence. congruence.
 +apply eval_arycmp_false; auto.
 +apply eval_strcmp_cons; auto.
  eapply IHeval_typecmp; eauto; intros.
  eapply eval_field_app3; eauto.
  eapply eval_field_app3; eauto.
  inv H8. apply eval_Sfield with sid fld0; auto; try congruence.
  inv H8. apply eval_Sfield with sid fld0; auto; try congruence.
 +apply eval_strcmp_nil; auto.
Qed.

Lemma nodes_id_ptree_none:
  forall fid fd l (e1 e2: locenv),
  find_funct (node_block progT) fid = Some fd ->
  ptree_noids_match (map fst (mkloopmapw l)) e1 e2 ->
  e1 ! fid = None ->
  e2 ! fid = None.
Proof.
  intros.
  rewrite <-H0; auto. red; intros.
  apply mkloopmapw_incl in H2. simpl in *.
  generalize H; intros.
  apply find_funct_fid in H3. subst.
  apply find_funct_in2 in H.
  cut (Plt ACG_EQU (fst fd)). intros.
  destruct H2 as [ | ]; try tauto.
  rewrite <-H2 in *. unfold Plt, ACG_EQU, ACG_I in *. omega.
  apply GID_RANGE. apply in_or_app. right.
  apply in_or_app; right. apply in_map; auto.
Qed.

Lemma trans_node_all_correct:
  forall gc e e' fd vargs vrets,
  LsemT.eval_node false progT gc e e' fd vargs vrets ->
  find_funct (node_block progT) (fst fd) = Some fd ->
  env_none gc ->
  eval_node progT gc e e' fd vargs vrets.
Proof.
  intros gc.
  induction 1 using LsemT.eval_node_ind2 with
  ( P0 := fun nk te1 e te1' e' ss =>
      forall l te2,
      locenv_matcht (mkloopmapw l) empty_locenv te1 te2 ->
      env_none gc ->
      has_fors ss <= has_fors l ->
      exists te2', eval_stmts progT gc nk te2 e te2' e' ss
       /\ locenv_matcht (mkloopmapw l) empty_locenv te1' te2')
  ( P1 := fun nk te1 e te1' e' s ta ta' =>
      forall l te2,
      locenv_matcht (mkloopmapw l) ta te1 te2 ->
      env_none gc ->
      has_for s <= has_fors l ->
      exists te2', eval_stmt progT gc nk te2 e te2' e' s
        /\ locenv_matcht (mkloopmapw l) ta' te1' te2')
  ( P2 := fun nk te1 e te1' e' f ta ta' =>
      forall l te2,
      locenv_matcht (mkloopmapw l) ta te1 te2 ->
      env_none gc ->
      exists te2', eval_hstmt progT gc nk te2 e te2' e' f
        /\ locenv_matcht (mkloopmapw l) ta' te1' te2')
  ( P3 := fun nk te1 se se1 args atys vargs i cdef l rtys vrets =>
      forall l1 ta te2,
      locenv_matcht (mkloopmapw l1) ta te1 te2 ->
      env_none gc ->
      eval_apply progT gc nk te2 se se1 args atys vargs i cdef l rtys vrets); simpl; intros.
  +(*eval_node*)
   subst.
   assert (A: list_disjoint (ACG_I :: nil) (map fst (allvarsof f))).
     apply loopid_mapwid_disjoint_vars with nid; auto.
     eapply find_funct_in2; eauto.
   destruct alloc_variables_match with empty_locenv (allvarsof f) (mkloopmapw (nd_stmt f)) te empty_locenv as [te21 [? ?]]; auto.
     red; auto.
     red; intros. apply PTree.gempty.
     destruct H0; auto.
     apply mkloopmapw_norepet.
     intros. eapply mkloopmapw_range; eauto.
   destruct locenv_setvars_exists with (nd_stmt f) te (nd_args f) vas te1 empty_locenv te21 as [te22 [? ?]]; auto.
   destruct IHeval_node with (nd_stmt f) te22 as [te2' [? ?]]; auto.
     simpl. omega.
   assert (A2: list_norepet (map fst (mkloopmapw (nd_stmt f)) ++ map fst (allvarsof f))).
     apply mkloopmapw_norepet_vars with nid; auto.
     eapply find_funct_in2; eauto.
   eapply exec_node; eauto.
   eapply locenv_matcht_eval_poststmt; eauto.
   eapply locenv_match_getvars; eauto.
   eapply locenv_matcht_simpl; eauto.
  +(*eval_stmts_nil*)
   econstructor. split; eauto. econstructor.
  +(*eval_stmts_cons*)
   destruct IHeval_node with l te0 as [te21 [? ?]]; auto.
     destruct (zlt _ _).
     apply Zle_trans with (Z.max (has_for s) (has_fors ss)); auto.
     apply zmax_l_le; omega.
     generalize (has_for_range s). intros.
     apply Zle_trans with 1; try omega.
   destruct IHeval_node0 with l te21 as [te2' [? ?]]; auto.
     eapply locenv_matcht_empty_locenv; eauto.
     destruct (zlt _ _).
     apply Zle_trans with (Z.max (has_for s) (has_fors ss)); auto.
     apply zmax_r_le; omega.
     generalize (has_fors_range ss). intros. omega.
   exists te2'; split; auto. econstructor 2; eauto.
  +(*eval_Sassign*)
   apply eval_sassign_correct with (te1:=te) (ta:=ta) (ta1:=ta); auto.
   econstructor; eauto.
  +(*eval_Scall*)
   destruct locenv_setvars_exists with l te lhs vrets te' ta te2 as [te2' [? ?]]; auto.
   exists te2'. split; auto.
   eapply eval_Scall; eauto.
   -eapply eval_sexps_match; eauto;
    eapply locenv_matcht_simpl; eauto.
  +(*eval_Sfor_start*)
   eapply eval_for_start_correct in H; eauto. destruct H as [te21 [? ?]].
   eapply eval_for_init_correct in H0; eauto.
   destruct H0 as [te22 [? ?]]; auto.
   destruct IHeval_node0 with l te22 as [te2' [? ?]]; auto.
   exists te2'. split; auto.
   -eapply eval_Sfor_start; eauto.
   -apply has_fors_loop_in; auto. omega.
  +(*eval_Sfor_false*)
   exists te2; split; auto.
   eapply eval_Sfor_false; eauto.
   eapply eval_loop_cond; eauto. destruct H0 as [? [? ?]]; auto.
  +(*eval_Sfor_loop*)
   destruct IHeval_node with l te0 as [te21 [? ?]]; auto.
   eapply eval_for_loop_add_correct in H1; eauto.
   destruct H1 as [te22 [? ?]].
   destruct IHeval_node0 with l te22 as [te2' [? ?]]; auto.
   exists te2'. split; auto.
   eapply eval_Sfor_loop; eauto.
   eapply eval_loop_cond; eauto.
   inv H3; intuition. destruct H4; auto.
   apply has_fors_loop_in; auto. omega.
  +(*eval_Sarydif_nil*)
   exists te2. split; auto. constructor.
  +(*eval_Sarydif_cons*)
   eapply locenv_matcht_setlvar_exists in H3; eauto.
   destruct H3 as [te21 [? ?]].
   destruct IHeval_node with l te21 as [te2' [? ?]]; auto.
   exists te2'. split; auto.
   eapply eval_Sarydif_cons; eauto.
   eapply eval_sexp_match; eauto; eapply locenv_matcht_simpl; eauto.
  +(*eval_Smix *)
   apply eval_lindexs_match with (eh2:=te0) in H; eauto; try (eapply locenv_matcht_simpl; eauto).
   eapply eval_sassign_correct in H1; eauto.
   destruct H1 as [te21 [? ?]].
   eapply locenv_matcht_store_env_exists in H3; eauto.
   destruct H3 as [te2' [? ?]].
   exists te2'. split; auto.
   eapply eval_Smix; eauto.
   eapply eval_sexp_match; eauto; eapply locenv_matcht_simpl; eauto.
  +(*eval_Sstruct_nil*)
    exists te2. split; auto. constructor.
  +(*eval_Sstruct_cons*)
   eapply locenv_matcht_setlvar_exists in H1; eauto.
   destruct H1 as [te21 [? ?]].
   destruct IHeval_node with l te21 as [te2' [? ?]]; auto.
   exists te2'. split; auto.
   eapply eval_Sstruct_cons; eauto.
   eapply eval_sexp_match; eauto; eapply locenv_matcht_simpl; eauto.
  +(*eval_Sskip*)
   exists te2. split; auto. constructor.
  +(*eval_Sfby_1*)
   eapply locenv_matcht_setlvar_exists in H4; eauto.
   destruct H4 as [te2' [? ?]].
   exists te2'. split; auto.
   eapply eval_Sfby_cycle_1; eauto.
   eapply eval_sexp_match; eauto; eapply locenv_matcht_simpl; eauto.
  +(*eval_Sfby_n*)
   eapply locenv_matcht_setlvar_exists in H3; eauto.
   destruct H3 as [te2' [? ?]].
   exists te2'. split; auto.
   eapply eval_Sfby_cycle_n; eauto.
  +(*eval_Sfbyn_1*)
   eapply locenv_matcht_setlvar_exists in H9; eauto.
   destruct H9 as [te2' [? ?]].
   exists te2'. split; auto.
   eapply eval_Sfbyn_cycle_1; eauto.
   eapply eval_sexp_match; eauto; eapply locenv_matcht_simpl; eauto.
  +(*eval_Sfbyn_n*)
   eapply locenv_matcht_setlvar_exists in H6; eauto.
   destruct H6 as [te2' [? ?]].
   exists te2'. split; auto.
   eapply eval_Sfbyn_cycle_n; eauto.
  +(*eval_Sarrow*)
   destruct IHeval_node with l te2 as [te2' [? ?]]; auto.
   exists te2'. split; auto.
   eapply eval_Sarrow; eauto.
  +(*eval_Hmaptyeq*)
   eapply locenv_matcht_setlvar_exists in H2; eauto.
   destruct H2 as [te2' [? ?]].
   exists te2'. split; auto.
   destruct locenv_matcht_simpl with gc l ta te te2 as [A1 A2]; auto.
   destruct H3 as [A3 [A4 [A5 A6]]].
   eapply eval_sexp_svar_match in H; eauto.
   apply eval_Hmaptyeq with aid1 t b; auto.
   -eapply eval_typecmp_match in H1; eauto.
    eapply eval_typecmp_trans; eauto; intros.
    eapply eval_aryacc_app1; eauto.
    eapply eval_aryacc_app1; eauto.
     inv H3. inv H10. apply eval_Saryacc with aid0 z; auto. inv H3.
     inv H3. inv H10. apply eval_Saryacc with aid0 z; auto. inv H3.
   -eapply locenv_setlvar_loopid; eauto.
   -destruct H4; auto.
  +(*eval_Hmapary*)
   eapply locenv_matcht_setlvar_exists in H2; eauto.
   destruct H2 as [te2' [? ?]].
   destruct locenv_matcht_simpl with gc l ta te te2 as [A1 A2]; auto.
   destruct H3 as [? [? [? [? ?]]]].
   eapply eval_sexp_svar_match in H; eauto.
   exists te2'. split; auto.
   apply eval_Hmapary with v v'; auto. inv H0.
    apply eval_Sbinop with v1 v2; auto.
    eapply eval_saryacc_loopid; eauto.
    eapply eval_saryacc_loopid; eauto.
    inv H10.
    eapply locenv_setlvar_loopid; eauto.
    destruct H4; auto.
  +(*eval_Hmapunary*)
   eapply locenv_matcht_setlvar_exists in H5; eauto.
   destruct H5 as [te2' [? ?]].
   destruct locenv_matcht_simpl with gc l ta te te2 as [A1 A2]; auto.
   destruct H6 as [? [? [? [? ?]]]].
   eapply eval_sexp_svar_match in H; eauto.
   exists te2'. split; auto.
   apply eval_Hmapunary with t1 v v'; auto.
   -eapply trans_prefix_unary_expr_match_ary; eauto.
   -eapply locenv_setlvar_loopid; eauto.
   -destruct H7; auto.
  +(*eval_Hfoldary*)
   inv H0. eapply locenv_matcht_setlvar_exists in H10; eauto.
   destruct H10 as [te2' [? ?]].
   exists te2'. split; auto.
   eapply eval_Hflodary; eauto.
   destruct locenv_matcht_simpl with gc l ta te te2 as [A1 A2]; auto.
   econstructor; eauto.
   inv H5. econstructor; eauto.
   eapply eval_sexp_match; eauto.
   eapply eval_saryacc_loopid; eauto.
   destruct H1 as [? [? [? ?]]]. destruct H2.
   eapply eval_sexp_svar_match; eauto.
   inv H4.
   apply eval_sbinop_by_value in H5. destruct H5.
   econstructor; eauto.
  +(*eval_Hfoldunary*)
   inv H. eapply locenv_matcht_setlvar_exists in H9; eauto.
   destruct H9 as [te2' [? ?]].
   exists te2'. split; auto.
   eapply eval_Hflodunary; eauto.
   econstructor; eauto.
   destruct locenv_matcht_simpl with gc l ta te te2 as [A1 A2]; auto.
   eapply eval_sexp_match; eauto.
   apply eval_sunop_by_value in H4. destruct H4.
   econstructor; eauto.
  +(*eval_Hfoldcast*)
   inv H. eapply locenv_matcht_setlvar_exists in H9; eauto.
   destruct H9 as [te2' [? ?]].
   exists te2'. split; auto.
   eapply eval_Hflodcast; eauto.
   econstructor; eauto.
   destruct locenv_matcht_simpl with gc l ta te te2 as [A1 A2]; auto.
   eapply eval_sexp_match; eauto.
   apply eval_scast_by_value in H4. destruct H4.
   econstructor; eauto.
  +(*eval_Farydef*)
   eapply locenv_matcht_setlvar_exists in H4; eauto.
   destruct H4 as [te2' [? ?]].
   destruct locenv_matcht_simpl with gc l ta te te2 as [A1 A2]; auto.
   destruct H5 as [? [? [? [? ?]]]].
   eapply eval_sexp_svar_match in H; eauto.
   exists te2'. split; auto.
   apply eval_Harydef with v v'; auto.
    eapply eval_sexp_match; eauto.
    eapply locenv_setlvar_loopid; eauto.
    destruct H6; auto.
  +(*eval_Haryslc*)
   eapply locenv_matcht_setlvar_exists in H3; eauto.
   destruct H3 as [te2' [? ?]].
   destruct locenv_matcht_simpl with gc l ta te te2 as [A1 A2]; auto.
   destruct H4 as [? [? [? [? ?]]]].
   eapply eval_sexp_svar_match in H; eauto.
   exists te2'. split; auto.
   -apply eval_Haryslc with v v'; auto.
    *inv H1. apply eval_Rlvalue with id ofs k; auto.
     inv H11. econstructor; eauto. eapply eval_lvalue_match; eauto.
     inv H17. apply eval_Sbinop with v1 v2; auto.
     eapply eval_sexp_const; eauto.
     inv H20; auto. inv H1. inv H1. simpl in *.
     eapply eval_var_match; eauto.
    *eapply locenv_setlvar_loopid; eauto.
   -destruct H5; auto.
  +(*eval_Hboolred_true*)
   inv H1. eapply locenv_matcht_setlvar_exists in H11; eauto.
   destruct H11 as [te2' [? ?]].
   exists te2'. split; auto.
   destruct locenv_matcht_simpl with gc l ta te te2 as [A1 A2]; auto.
   destruct H2 as [? [? [? ?]]]. destruct H3.
   eapply eval_sexp_svar_match in H; eauto.
   eapply eval_Hboolred_true; eauto.
   eapply eval_saryacc_loopid; eauto.
   econstructor; eauto.
   eapply eval_sexp_match; eauto.
   apply eval_sbinop_by_value in H6. destruct H6.
   econstructor; eauto.
  +(*eval_Hboolred_false*)
   exists te2. split; auto.
   destruct locenv_matcht_simpl with gc l ta te te2 as [A1 A2]; auto.
   destruct H1 as [? [? [? ?]]]. destruct H2.
   eapply eval_sexp_svar_match in H; eauto.
   eapply eval_Hboolred_false; eauto.
   eapply eval_saryacc_loopid; eauto.
  +(*eval_Hmapcall*)
   generalize H3; intros A.
   eapply locenv_matcht_setarys_exists in H3; eauto.
   destruct H3 as [te2' [? ?]].
   destruct locenv_matcht_simpl with gc l ta te te2 as [A1 A2]; auto.
   exists te2'. split; auto.
   apply eval_Hmapcall with atys rtys i vl vas vrs; eauto.
   -eapply eval_sexps_match; eauto.
   -destruct H4 as [? [? [? [? ?]]]].
    eapply eval_sexp_svar_match; eauto.
    destruct H5; auto.
  +(*eval_Hmapfoldcall*)
   destruct IHeval_node with l te0 as [te21 [A A1]]; simpl; auto.
     generalize (has_fors_range l). omega.
   destruct locenv_matcht_simpl with gc l ta te1 te21 as [A2 A3]; auto.
   generalize H5 H6; intros C C1.
   eapply locenv_matcht_setlvar_exists in H5; eauto.
   destruct H5 as [te22 [? ?]].
   eapply locenv_matcht_setarys_exists in H6; eauto.
   destruct H6 as [te2' [? ?]].
   exists te2'. split; auto.
   -apply eval_Hmapfoldcall with te21 te22 i v atys vl vargs vret vrs tys; eauto.
    *eapply eval_sexp_match; eauto.
    *eapply eval_sexps_match; eauto.
    *destruct A1 as [? [? [? [? ?]]]].
     eapply eval_sexp_svar_match; eauto.
     destruct H8; auto.
  +(*eval_apply*)
   generalize H0. intros. destruct H0.
   econstructor; eauto.
   apply IHeval_node; auto.
   eapply find_funct_eq; eauto.
   destruct H9. eapply nodes_id_ptree_none; eauto.
Qed.

Theorem exec_prog_correct_general:
  forall gc e fd vass vrss n maxn,
  exec_prog progT gc (LsemT.eval_node false) fd e n maxn vass vrss ->
  find_funct (node_block progT) (fst fd) = Some fd ->
  env_none gc ->
  exec_prog progT gc eval_node fd e n maxn vass vrss.
Proof.
  induction 1; intros.
  constructor 1 with mrss; trivial.

  eapply trans_node_all_correct in H0; eauto.
  constructor 2 with e'; auto.
Qed.

Lemma init_genvc_env_none:
  forall gc,
  init_genvc (const_block progT) = Some gc ->
  env_none gc.
Proof.
  intros.
  split; eapply init_genvc_notin_none; eauto;
  apply ids_plt_le_notin with ACG_EQU; auto;
  unfold Ple, INSTRUCT,ACG_I, ACG_B, ACG_EQU; try omega;
  red; intros; apply GID_RANGE;
  apply in_or_app; auto.
Qed.

Theorem initial_state_correct:
  forall gc main e,
  initial_state progT gc init_node main e->
  find_funct (node_block progT) (fst main) = Some main
  /\ env_none gc.
Proof.
  induction 1; intros;
  apply find_funct_eq in H0; split; auto.
  +apply init_genvc_env_none; auto.
Qed.

Theorem exec_prog_correct:
  forall gc main e vass vrss n maxn,
  initial_state progT gc init_node main e->
  exec_prog progT gc (LsemT.eval_node false) main e n maxn vass vrss ->
  exec_prog progT gc eval_node main e n maxn vass vrss.
Proof.
  intros.
  apply initial_state_correct in H. destruct H as [? ?].
  apply exec_prog_correct_general; auto.
Qed.

End CORRECTNESS.
