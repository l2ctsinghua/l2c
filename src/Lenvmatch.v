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
Require Import Integers.
Require Import Inclusion.
Require Import List.
Require Import Permutation.
Require Import ExtraList.
Require Import Cltypes.
Require Import Lident.
Require Import Ltypes.
Require Import Lustre.
Require Import Lvalues.
Require Import Lenv.
Require Import Lsem.

Set Implicit Arguments.

Definition locenv_match (e1 e2: locenv) :Prop :=
  forall id r, e1!id = Some r ->  e2!id = Some r.

Definition locenv_disjoint (gc e1 e2: locenv) :Prop :=
  forall id r, e1!id = None ->  gc!id = Some r -> e2!id = None.

Lemma load_env_match:
  forall t e1 i ofs v,
  load_env t e1 i ofs v ->
  forall e2, locenv_match e1 e2 ->
  load_env t e2 i ofs v.
Proof.
  intros. destruct H as [m [t1 [? [? ?]]]].
  exists m, t1; split; auto.
Qed.

Lemma eval_var_match:
  forall gc t e1 i ofs k v,
  eval_var gc t e1 i ofs k v ->
  forall e2, locenv_match e1 e2 ->
  eval_var gc t e2 i ofs k v.
Proof.
  induction 1; intros.
  constructor 1; auto.
  constructor 2; auto.
  eapply load_env_match; eauto.
Qed.

Lemma locenv_disjoint_set_left:
  forall gc e1 e2 id1 m1,
  locenv_disjoint gc e1 e2 ->
  locenv_disjoint gc (PTree.set id1 m1 e1) e2.
Proof.
  unfold locenv_disjoint. intros.
  apply H with r; auto.
  compare id id1; intros; subst.
  +rewrite PTree.gss in H0. congruence.
  +rewrite PTree.gso in H0; auto.
Qed.

Lemma locenv_disjoint_set_right:
  forall gc e1 e2 id2 m2,
  locenv_disjoint gc e1 e2 ->
  gc ! id2 = None ->
  locenv_disjoint gc e1 (PTree.set id2 m2 e2).
Proof.
  unfold locenv_disjoint. intros.
  compare id id2; intros; subst.
  +congruence.
  +rewrite PTree.gso; auto.
   apply H with r; auto.
Qed.

Lemma locenv_disjoint_set_same:
  forall gc e1 e2 id m,
  locenv_disjoint gc e1 e2 ->
  locenv_disjoint gc (PTree.set id m e1) (PTree.set id m e2).
Proof.
  unfold locenv_disjoint. intros.
  compare id id0; intros; subst.
  +rewrite PTree.gss in H0. congruence.
  +rewrite PTree.gso in H0; auto.
   rewrite PTree.gso; auto.
   apply H with r; auto.
Qed.

Lemma alloc_variables_locenv_disjoint:
  forall gc e2 e1 al e1',
  alloc_variables e1 al e1' ->
  locenv_disjoint gc e1 e2 ->
  locenv_disjoint gc e1' e2.
Proof.
  induction 1; intros; auto.
  apply IHalloc_variables; auto.
  apply locenv_disjoint_set_left; auto.
Qed.

Lemma locenv_setvars_locenv_disjoint:
  forall gc e2 e1 al vl e1',
  locenv_setvars e1 al vl e1' ->
  locenv_disjoint gc e1 e2 ->
  locenv_disjoint gc e1' e2.
Proof.
  induction 1; intros; auto.
  apply IHlocenv_setvars; auto.
  inv H0. apply locenv_disjoint_set_left; auto.
Qed.

Lemma eval_sexp_svar_match:
  forall gc te eh2 id ty v,
  eval_sexp gc te (Svar id ty) v ->
  locenv_match te eh2 ->
  gc ! id = None ->
  eval_sexp gc eh2 (Svar id ty) v.
Proof.
  intros. inv H. inv H2.
  apply eval_Rlvalue with id0 Int.zero Lid; auto.
  constructor 1 with m; auto.
  eapply eval_var_match; eauto.
  congruence.
Qed.

Lemma eval_sexp_match:
  forall gc e1 s v,
  eval_sexp gc e1 s v ->
  forall e2, locenv_match e1 e2 ->
  locenv_disjoint gc e1 e2 ->
  eval_sexp gc e2 s v
with eval_lvalue_match:
  forall gc e1 s id ofs k,
  eval_lvalue gc e1 s id ofs k ->
  forall e2, locenv_match e1 e2 ->
  locenv_disjoint gc e1 e2 ->
  eval_lvalue gc e2 s id ofs k.
Proof.
 +induction 1; simpl; intros;
  try (econstructor; eauto; fail).
  apply eval_Rlvalue with id ofs k; auto.
   eapply eval_lvalue_match; eauto.
   eapply eval_var_match; eauto.
 +induction 1; simpl; intros; econstructor; eauto.
Qed.

Lemma eval_sexps_match:
  forall gc e1 s v,
  eval_sexps gc e1 s v ->
  forall e2, locenv_match e1 e2 ->
  locenv_disjoint gc e1 e2 ->
  eval_sexps gc e2 s v.
Proof.
  induction 1; intros; constructor.
  eapply eval_sexp_match; eauto.
  eapply IHForall2; eauto.
Qed.

Lemma eval_lindexs_match:
  forall gc eh1 t ty lis o1 o2,
  eval_lindexs gc eh1 t ty lis o1 o2 ->
  forall eh2, locenv_match eh1 eh2 ->
  locenv_disjoint gc eh1 eh2 ->
  eval_lindexs gc eh2 t ty lis o1 o2.
Proof.
  induction 1; intros; econstructor; eauto.
  eapply eval_sexp_match; eauto.
Qed.

Lemma locenv_match_addnewid:
  forall eh eh1 id v ,
  locenv_match eh eh1 ->
  eh ! id = None ->
  locenv_match eh (PTree.set id v eh1).
Proof.
  unfold locenv_match. intros.
  compare id id0; intros A; subst.
  congruence.
  rewrite PTree.gso; auto.
Qed.

Lemma locenv_match_addsameid:
  forall eR eN id m,
  locenv_match eR eN ->
  locenv_match (PTree.set id m eR) (PTree.set id m eN).
Proof.
  unfold locenv_match. intros.
  compare id id0; intros A; subst.
  rewrite PTree.gss in *; auto.
  rewrite PTree.gso in *; auto.
Qed.

Lemma locenv_match_store_env_exists:
  forall ty eh1 id ofs v eh1',
  store_env ty eh1 id ofs v eh1' ->
  forall eh2, locenv_match eh1 eh2 ->
  exists eh2', store_env ty eh2 id ofs v eh2'
    /\ locenv_match eh1' eh2'.
Proof.
  intros. inv H. apply H0 in H1.
  exists (PTree.set id (m',t) eh2). split.
  constructor 1 with m; auto.
  apply locenv_match_addsameid; auto.
Qed.

Lemma locenv_match_getvars:
  forall e1 e2 l vl,
  locenv_match e1 e2 ->
  locenv_getvars e1 l vl ->
  locenv_getvars e2 l vl.
Proof.
  induction 2; constructor; auto.
  destruct H0 as [m [? [? ?]]]. exists m; split; auto.
Qed.

Lemma alloc_global_match:
  forall a gc1 gc1' gc2,
  alloc_global gc1 a = Some gc1' ->
  locenv_match gc1 gc2 ->
  exists gc2', alloc_global gc2 a = Some gc2'
    /\ locenv_match gc1' gc2'.
Proof.
  destruct a. destruct g; simpl; intros.
  destruct (store_zeros _ _) eqn:?; try congruence.
  destruct (store_init_datas _ _ _) eqn:?; inv H.
  exists (PTree.set i (m0, gvar_info) gc2). split; auto.
  apply locenv_match_addsameid; auto.
Qed.

Lemma alloc_globals_match:
  forall l gc1 gc1' gc2,
  alloc_globals gc1 l = Some gc1' ->
  locenv_match gc1 gc2 ->
  exists gc2', alloc_globals gc2 l = Some gc2'
    /\ locenv_match gc1' gc2'.
Proof.
  induction l; simpl; intros.
  +inv H. eauto.
  +destruct (alloc_global gc1 a) eqn:?; try congruence.
   destruct alloc_global_match with a gc1 l0 gc2 as [gc21 [? ?]]; auto.
   rewrite H1. eapply IHl; eauto.
Qed.

Section PTREE_IDS.
Variable V V1: Type.

Definition ptree_ids_match(l: list ident)(e1 e2: PTree.t V): Prop :=
  forall id, In id l -> e1 ! id = e2 ! id.

Definition ptree_noids_match(l: list ident)(e1 e2: PTree.t V): Prop :=
  forall id, ~ In id l -> e1 ! id = e2 ! id.

Definition ptree_ids_none(ids: list ident)(e: PTree.t V): Prop :=
  forall id, In id ids -> e ! id = None.

Definition ptree_disjoint(e1: PTree.t V)(e2: PTree.t V1): Prop :=
  forall id m, e1 ! id = Some m -> e2 ! id = None.

Definition ptree_some_match(e1 e2: locenv) : Prop :=
  forall id m, e2 ! id = Some m -> exists m', e1 ! id = Some m'.

Lemma ptree_ids_match_swap:
  forall l e1 e2,
  ptree_ids_match l e1 e2 ->
  ptree_ids_match l e2 e1.
Proof.
  unfold ptree_ids_match. intros.
  rewrite H; auto.
Qed.

Lemma ptree_ids_match_app:
  forall l1 l2 e1 e2,
  ptree_ids_match (l1++l2) e1 e2 ->
  ptree_ids_match l1 e1 e2 /\ ptree_ids_match l2 e1 e2.
Proof.
  unfold ptree_ids_match.
  split; intros; apply H; apply in_or_app; auto.
Qed.

Lemma ptree_ids_match_trans:
  forall l e1 e2 e3,
  ptree_ids_match l e1 e2 ->
  ptree_ids_match l e2 e3 ->
  ptree_ids_match l e1 e3.
Proof.
  unfold ptree_ids_match; intros.
  rewrite H, H0; auto.
Qed.

Lemma ptree_ids_match_set:
  forall id a e l, list_disjoint (id::nil) l ->
  ptree_ids_match l e (PTree.set id a e).
Proof.
  intros. red. intros.
  rewrite PTree.gso; auto.
  eapply H in H0; eauto. simpl; auto.
Qed.

Lemma ptree_ids_none_in_list_false:
  forall ids eh1 id m,
  ptree_ids_none ids eh1 ->
  eh1 ! id = Some m ->
  in_list id ids = false.
Proof.
  intros. remember (in_list id ids).
  destruct b; auto. symmetry in Heqb.
  apply in_list_true_in in Heqb.
  apply H in Heqb. congruence.
Qed.

Lemma ptree_ids_none_set_other:
  forall ids eh1 id m m',
  ptree_ids_none ids eh1 ->
  eh1 ! id = Some m ->
  ptree_ids_none ids (PTree.set id m' eh1).
Proof.
  unfold ptree_ids_none. intros.
  rewrite PTree.gso; auto.
  red; intros; subst. rewrite H in H0; auto.
  congruence.
Qed.

Lemma ptree_disjoint_set_left:
  forall e1 e2 id v v',
  ptree_disjoint e1 e2 ->
  e1 ! id = Some v ->
  ptree_disjoint (PTree.set id v' e1) e2.
Proof.
  unfold ptree_disjoint. intros.
  compare id id0; intros; subst.
  rewrite PTree.gss in *. inv H1. apply H with v; auto.
  rewrite PTree.gso in *; eauto.
Qed.

Lemma ptree_disjoint_set_right:
  forall e1 e2 id v,
  ptree_disjoint e1 e2 ->
  e1 ! id = None ->
  ptree_disjoint e1 (PTree.set id v e2).
Proof.
  unfold ptree_disjoint. intros.
  compare id id0; intros; subst.
  rewrite PTree.gss in *. congruence.
  rewrite PTree.gso in *; eauto.
Qed.

Lemma ptree_noids_match_ids_none:
  forall ids te1 te2 id,
  ptree_noids_match ids te1 te2 ->
  ptree_ids_none ids te2 ->
  te1 ! id = None ->
  te2 ! id = None.
Proof.
  intros.
  assert(In id ids \/ ~ In id ids).
    tauto.
  destruct H2.
  apply H0; auto.
  rewrite <-H; auto.
Qed.

Inductive ptree_sets: PTree.t V  -> list ident -> list V -> PTree.t V -> Prop :=
  | ptree_sets_nil: forall e,
      ptree_sets e nil nil e
  | ptree_sets_cons: forall e e' id l v vl,
      ptree_sets (PTree.set id v e) l vl e' ->
      ptree_sets e (id::l) (v::vl) e'.

Lemma ptree_sets_trans:
  forall l1 vl1 e e1 l2 vl2 e2,
  ptree_sets e l1 vl1 e1 ->
  ptree_sets e1 l2 vl2 e2 ->
  ptree_sets e (l1 ++ l2) (vl1 ++ vl2) e2.
Proof.
  induction l1; induction vl1; simpl; intros; inversion H;
  try (subst; auto; fail);constructor 2; auto;
  apply IHl1 with e1; auto.
Qed.

Lemma ptree_ids_match_setsame:
  forall l e1 e2 id m,
  ptree_ids_match l e1 e2 ->
  ptree_ids_match l (PTree.set id m e1) (PTree.set id m e2).
Proof.
  red; intros.
  compare id id0; intros; subst.
  repeat rewrite PTree.gss; auto.
  repeat rewrite PTree.gso; auto.
Qed.

Lemma ptree_some_match_set:
  forall b m1 m2 e1 e2,
  ptree_some_match e1 e2 ->
  ptree_some_match (PTree.set b m1 e1) (PTree.set b m2 e2).
Proof.
  intros. red; intros.
  compare b id; intros.
  subst. rewrite PTree.gss. eauto.
  rewrite PTree.gso in *; auto. eapply H; eauto.
Qed.

Lemma ptree_some_match_trans:
  forall e1 e2 e3,
  ptree_some_match e1 e2 ->
  ptree_some_match e2 e3 ->
  ptree_some_match e1 e3.
Proof.
  intros. red; intros.
  apply H0 in H1. destruct H1; eauto.
Qed.

Lemma ptree_noids_match_setsame:
  forall l e1 e2 id m,
  ptree_noids_match l e1 e2 ->
  ptree_noids_match l (PTree.set id m e1) (PTree.set id m e2).
Proof.
  red; intros.
  compare id id0; intros; subst.
  repeat rewrite PTree.gss; auto.
  repeat rewrite PTree.gso; auto.
Qed.

Lemma ptree_sets_determ:
  forall e l1 vl e1,
  ptree_sets e l1 vl e1 ->
  forall e2, ptree_sets e l1 vl e2 ->
  e1 = e2.
Proof.
  induction 1; intros.
  inv H. auto.
  inv H0. auto.
Qed.

Lemma ptree_sets_shift:
  forall e l vl e',
  ptree_sets e l vl e' ->
  forall id v, ~ In id l ->
  ptree_sets (PTree.set id v e) l vl (PTree.set id v e').
Proof.
  induction 1; simpl; intros.
  constructor.
  cut (~ In id0 l); auto. intros.
  apply IHptree_sets with _ v0 in H1; eauto.
  rewrite ptree_set_swap in H1; auto.
  constructor 2; auto.
Qed.

Lemma ptree_sets_swap:
  forall e1 l1 vl1 e12,
  ptree_sets e1 l1 vl1 e12 ->
  forall l2 vl2 e2 e21,
  ptree_sets e12 l2 vl2 e2 ->
  ptree_sets e1 l2 vl2 e21 ->
  list_disjoint l1 l2 ->
  ptree_sets e21 l1 vl1 e2.
Proof.
  induction 1; intros.
  eapply ptree_sets_determ in H; eauto. subst. constructor.
  apply ptree_sets_shift with _ _ _ _ id v in H1.
  eapply IHptree_sets in H1; eauto.
  constructor 2; auto.
  red. intros. apply H2; simpl; auto.
  red. intros. red in H2. red in H2.
   eapply H2; eauto. simpl; auto.
Qed.

Lemma ptree_sets_match:
  forall e1 l ml e1',
  ptree_sets e1 l ml e1' ->
  forall e2 e2' b,
  ptree_sets e2 l ml e2' ->
  e1 ! b = e2 ! b ->
  e1' ! b = e2' ! b.
Proof.
  induction 1; intros; auto.
  inv H. auto.
  inv H0. eapply IHptree_sets; eauto.
  compare id b; intros; subst.
  repeat rewrite PTree.gss; auto.
  repeat rewrite PTree.gso; auto.
Qed.

End PTREE_IDS.

Lemma ptree_ids_match_load_env:
  forall ty te1 id ofs v,
  load_env ty te1 id ofs v ->
  forall ids ta, ptree_ids_match ids te1 ta ->
  in_list id ids = true ->
  load_env ty ta id ofs v.
Proof.
  intros. apply in_list_true_in in H1.
  apply H0 in H1. unfold load_env. rewrite <-H1; auto.
Qed.

Lemma ptree_noids_match_load_env:
  forall ty te1 id ofs v,
  load_env ty te1 id ofs v ->
  forall ids te2, ptree_noids_match ids te1 te2 ->
  in_list id ids = false ->
  load_env ty te2 id ofs v.
Proof.
  intros. apply in_list_false_notin in H1.
  apply H0 in H1. unfold load_env. rewrite <-H1; auto.
Qed.

Lemma load_env_ptree_ids_match:
  forall a e1 e2 id o v,
  load_env (typeof a) e1 id o v ->
  In id (get_expids a) ->
  ptree_ids_match (get_expids a) e1 e2 ->
  load_env (typeof a) e2 id o v.
Proof.
  unfold ptree_ids_match; intros.
  destruct H as [m [t [? [? ?]]]].
  exists m, t; split; auto.
  rewrite <-H1; auto.
Qed.

Lemma eval_var_ptree_ids_match:
  forall gc a e1 e2 id o k v,
  eval_var gc (typeof a) e1 id o k v ->
  In id (get_expids a) ->
  ptree_ids_match (get_expids a) e1 e2 ->
  eval_var gc (typeof a) e2 id o k v.
Proof.
  intros. inv H.
  constructor 1; auto.
  constructor 2; auto.
  apply load_env_ptree_ids_match with e1; auto.
Qed.

Lemma eval_sexp_ptree_ids_match:
  forall gc e1 a v,
  eval_sexp gc e1 a v ->
  forall e2, ptree_ids_match (get_expids a) e1 e2 ->
  eval_sexp gc e2 a v
with eval_lvalue_ptree_ids_match:
  forall gc e1 a id o k,
  eval_lvalue gc e1 a id o k ->
  forall e2, ptree_ids_match (get_expids a) e1 e2 ->
  eval_lvalue gc e2 a id o k.
Proof.
  +induction 1; simpl; intros; try (econstructor; eauto; fail).
   -apply ptree_ids_match_app in H4. destruct H4.
    apply eval_Sbinop with v1 v2; auto.
   -apply eval_Rlvalue with id ofs k; auto.
    apply eval_lvalue_ptree_ids_match with e1; auto.
    apply eval_var_ptree_ids_match with e1; auto.
    apply eval_lvalue_id_in_expids with gc e1 ofs k; auto.
  +induction 1; simpl; intros; try (econstructor; eauto; fail).
   apply eval_Svar with m; auto. rewrite <- H0; simpl; auto.
   apply eval_Scvar with m; auto. rewrite <- H1; simpl; auto.
   apply ptree_ids_match_app in H4. destruct H4.
   eapply eval_Saryacc; eauto.
Qed.

Lemma eval_sexp_setnew:
  forall gc e a v,
  eval_sexp gc e a v ->
  forall id m, ~ In id (get_expids a) ->
  eval_sexp gc (PTree.set id m e) a v.
Proof.
  intros. eapply eval_sexp_ptree_ids_match; eauto.
  red; intros. rewrite PTree.gso; auto. congruence.
Qed.

Lemma eval_sexps_setnew:
  forall gc e s vl,
  eval_sexps gc e s vl ->
  forall id m, ~ In id (get_expsids s) ->
  eval_sexps gc (PTree.set id m e) s vl.
Proof.
  induction 1; simpl; intros; auto.
  constructor.

  apply not_in_app in H1. destruct H1.
  subst. constructor 2.
  eapply eval_sexp_setnew; eauto.
  eapply IHForall2; eauto.
Qed.

Lemma eval_lvalue_setsame:
  forall gc te a b o k,
  eval_lvalue gc te a b o k ->
  forall m m' t,
  te ! b = Some (m, t) ->
  lid_disjoint a ->
  eval_lvalue gc (PTree.set b (m',t) te) a b o k.
Proof.
  induction 1; intros; try (econstructor; eauto; fail).
  +constructor 1 with m'; auto. rewrite PTree.gss; auto. congruence.
  +congruence.
  +simpl in H5. destruct a1; try tauto. destruct H5; subst.
   apply eval_lvalue_lid_disjoint_not_loopid in H; auto.
   apply eval_Saryacc with aid z; auto.
   apply IHeval_lvalue with m; auto.
   apply eval_sexp_setnew; auto.
   simpl. red; intros. destruct H6; subst; try tauto.
Qed.

Lemma locenv_setlvar_eval_sexp_disjoint:
  forall gc e e1 a1 a2 v1 v2,
  locenv_setlvar gc e a1 v1 e1 ->
  list_disjoint (get_lids a1) (get_expids a2) ->
  eval_sexp gc e a2 v2 ->
  eval_sexp gc e1 a2 v2.
Proof.
  intros. inv H. simpl in *.
  erewrite eval_lvalue_get_lids in H0; eauto.
  inv H3. eapply eval_sexp_setnew; eauto.
  red; intros. eapply H0; simpl; eauto.
Qed.

Lemma eval_eqf_eval_sexp_disjoint:
  forall gc e e1 eq a v,
  eval_eqf gc e e1 eq ->
  list_disjoint (get_lids (fst eq)) (get_expids a) ->
  eval_sexp gc e a v ->
  eval_sexp gc e1 a v.
Proof.
  intros. inv H.
  eapply locenv_setlvar_eval_sexp_disjoint; eauto.
Qed.

Lemma store_env_match_exists:
  forall ty te1 id ofs v te1' ta,
  store_env ty te1 id ofs v te1' ->
  te1 ! id = ta ! id ->
  exists ta', store_env ty ta id ofs v ta'
    /\ te1' ! id = ta' ! id.
Proof.
  intros. inv H.
  exists (PTree.set id (m',t) ta). split.
  constructor 1 with m; auto. rewrite <-H0; auto.
  repeat rewrite PTree.gss; auto.
Qed.

Lemma ptree_ids_match_store_exists:
  forall ty e1 id o v e1',
  store_env ty e1 id o v e1' ->
  forall e2 l, In id l ->
  ptree_ids_match l e1 e2 ->
  exists e2' m', store_env ty e2 id o v e2'
    /\ ptree_ids_match l e1' e2'
    /\ e1' ! id = e2' ! id
    /\ e1' = PTree.set id m' e1
    /\ e2' = PTree.set id m' e2.
Proof.
  induction 1. intros.
  exists (PTree.set id (m',t) e2), (m',t).
  repeat split; auto.
  +constructor 1 with m; auto. rewrite <-H3; auto.
  +eapply ptree_ids_match_setsame; eauto.
  +repeat rewrite PTree.gss; auto.
Qed.

Lemma ptree_ids_match_locenv_setlvar_exists:
  forall gc eh1 a v eh1',
  locenv_setlvar gc eh1 a v eh1' ->
  forall eh2 l, incl (get_expids a) l ->
  ptree_ids_match l eh1 eh2 ->
  exists eh2' ml, locenv_setlvar gc eh2 a v eh2'
   /\ ptree_ids_match l eh1' eh2'
   /\ ptree_sets eh1 (get_lids a) ml eh1'
   /\ ptree_sets eh2 (get_lids a) ml eh2'.
Proof.
  intros. inv H. erewrite eval_lvalue_get_lids; eauto.
  eapply ptree_ids_match_store_exists in H3; eauto.
  destruct H3 as [eh2' [m' [? [? [? [? ?]]]]]].
  exists eh2', (m'::nil). subst. repeat (split; auto).
  +constructor 1 with b ofs; auto.
   eapply eval_lvalue_ptree_ids_match; eauto.
   red; intros. apply H1; auto.
  +econstructor 2; eauto. constructor.
  +econstructor 2; eauto. constructor.
  +apply H0. eapply eval_lvalue_id_in_expids; eauto.
Qed.

Lemma store_env_ptree_some_match:
  forall t e b o v e',
  store_env t e b o v e' ->
  ptree_some_match e' e /\ ptree_some_match e e'.
Proof.
  intros. inv H.
  split; red; intros;
  compare id b; intros; subst.
  rewrite PTree.gss; eauto.
  rewrite PTree.gso; eauto.
  rewrite PTree.gss in H; eauto.
  rewrite PTree.gso in H; eauto.
Qed.

Lemma locenv_setlvar_ptree_some_match:
  forall gc e a v e',
  locenv_setlvar gc e a v e' ->
  ptree_some_match e' e /\ ptree_some_match e e'.
Proof.
  intros. inv H.
  eapply store_env_ptree_some_match; eauto.
Qed.

Lemma locenv_setvars_ptree_some_match:
  forall e l vl e',
  locenv_setvars e l vl e' ->
  ptree_some_match e' e /\ ptree_some_match e e'.
Proof.
  induction 1; intros.
  split; red; eauto.
  inv H. eapply store_env_ptree_some_match in H0; eauto.
  intuition; eapply ptree_some_match_trans; eauto.
Qed.

Lemma locenv_setarys_ptree_some_match:
  forall gc i  te l tys vrs te',
  locenv_setarys gc i te l tys vrs te' ->
  ptree_some_match te' te /\ ptree_some_match te te'.
Proof.
  induction 1; intros.
  split; red; eauto.
  eapply locenv_setlvar_ptree_some_match in H; eauto.
  intuition; eapply ptree_some_match_trans; eauto.
Qed.

Lemma locenv_setlvar_ptree_ids_match:
  forall gc e a v e' l,
  locenv_setlvar gc e a v e' ->
  list_disjoint (get_lids a) l ->
  ptree_ids_match l e e'.
Proof.
  intros. inv H.
  apply eval_lvalue_get_lids in H1.
  rewrite H1 in H0. inv H2.
  eapply ptree_ids_match_set; eauto.
Qed.

Lemma locenv_setvars_ptree_ids_match:
  forall e l vl e',
  locenv_setvars e l vl e' ->
  forall l1, list_disjoint (map fst l) l1 ->
  ptree_ids_match l1 e e'.
Proof.
  induction 1; intros; red; intros; auto.
  inv H0. rewrite <-IHlocenv_setvars with l1 _; auto.
  rewrite PTree.gso; auto. apply sym_not_eq. apply H2;simpl; auto.
  red. intros. apply H2; simpl; auto.
Qed.

Inductive locenv_stmt_sets(lids: list ident)(te1 te1' te2 te2': locenv): Prop :=
  | locenv_stmt_sets_: forall l vl,
     incl l lids  ->
     ptree_sets te1 l vl te1' ->
     ptree_sets te2 l vl te2' ->
     locenv_stmt_sets lids te1 te1' te2 te2'.

Lemma locenv_stmt_sets_refl:
  forall s te1 te2,
  locenv_stmt_sets s te1 te1 te2 te2.
Proof.
  intros.
  constructor 1 with nil nil;
  try constructor; red; intros ? A; inv A.
Qed.

Lemma locenv_stmt_sets_incl:
  forall s1 te1 te1' te2 te2' s2,
  locenv_stmt_sets s1 te1 te1' te2 te2' ->
  incl s1 s2 ->
  locenv_stmt_sets s2 te1 te1' te2 te2'.
Proof.
  intros. inv H.
  constructor 1 with l vl; auto.
  red; intros. auto.
Qed.

Lemma locenv_stmt_sets_trans:
  forall s te1 te1' te1'' te2 te2' te2'',
  locenv_stmt_sets s te1 te1' te2 te2' ->
  locenv_stmt_sets s te1' te1'' te2' te2''->
  locenv_stmt_sets s te1 te1'' te2 te2''.
Proof.
  intros. inv H; inv H0.
  constructor 1 with (l++l0) (vl++vl0);
  try (eapply ptree_sets_trans; eauto);
  apply incl_app; auto.
Qed.

Lemma ptree_sets_some_match:
  forall te1 l vl te1',
  ptree_sets te1 l vl te1' ->
  forall te2 te2', ptree_sets te2 l vl te2' ->
  ptree_some_match te1 te2 ->
  ptree_some_match te1' te2'.
Proof.
  induction 1; intros.
  inv H. auto.
  inv H0. apply IHptree_sets with (PTree.set id v te2); auto.
  apply ptree_some_match_set; auto.
Qed.

Lemma locenv_stmt_sets_ptree_some_match:
  forall l te1 te2 te1' te2',
  locenv_stmt_sets l te1 te1' te2 te2' ->
  ptree_some_match te1 te2 ->
  ptree_some_match te1' te2'.
Proof.
  induction 1. intros.
  eapply ptree_sets_some_match; eauto.
Qed.

Lemma ptree_ids_match_setvars_exists:
  forall e1 l vl e1',
  locenv_setvars e1 l vl e1' ->
  forall e2, ptree_ids_match (map fst l) e1 e2 ->
  exists e2' ml, locenv_setvars e2 l vl e2'
    /\ ptree_ids_match (map fst l) e1' e2'
    /\ ptree_sets e1 (map fst l) ml e1'
    /\ ptree_sets e2 (map fst l) ml e2'.
Proof.
  induction 1; simpl; intros.
  exists e2; exists nil; repeat split; auto; constructor.

  destruct ptree_ids_match_store_exists with ty e id Int.zero v e1 e2 (id :: map fst dl) as [e21 [m' [? [? [? [? ?]]]]]]; simpl; auto.
  destruct IHlocenv_setvars with e21 as [e2' [ml [? [? [? ?]]]]]; auto.
    red. intros. apply H4. simpl; auto.
  exists e2', (m'::ml). repeat split; auto.
  constructor 2 with e21 m; auto.
  rewrite <- H2; simpl; auto.
  red. simpl; intros. eapply ptree_sets_match; eauto.
  subst; econstructor 2; eauto.
  subst; econstructor 2; eauto.
Qed.

Lemma ptree_ids_match_eval_fbyn_init:
  forall gc id1 id2 aid t i j v2 eh1 eh1',
  eval_fbyn_init gc id1 id2 aid t i j v2 eh1 eh1' ->
  forall eh2, ptree_ids_match (ACG_INIT :: id1 :: nil) eh1 eh2 ->
  exists eh2' l ml, eval_fbyn_init gc id1 id2 aid t i j v2 eh2 eh2'
    /\ ptree_ids_match (ACG_INIT :: id1 :: nil) eh1' eh2'
    /\ incl l (id1 :: nil)
    /\ ptree_sets eh1 l ml eh1'
    /\ ptree_sets eh2 l ml eh2'.
Proof.
  induction 1; simpl; intros.
  +subst. eapply ptree_ids_match_locenv_setlvar_exists in H3; simpl; eauto.
   destruct H3 as [eh21 [m' [? [? [? ?]]]]]; simpl; auto.
   destruct IHeval_fbyn_init with eh21 as [eh2' [l [ml [? [? [? [? ?]]]]]]]; auto.
   simpl in *. exists eh2', ((id1::nil)++l), (m'++ml). repeat split; auto.
   -econstructor 1; eauto.
   -red; intros ? A. apply in_app_or in A. destruct A; auto.
   -eapply ptree_sets_trans; eauto.
   -eapply ptree_sets_trans; eauto.
   -incl_tac.
  +exists eh2,nil, nil; repeat (split; auto); try (constructor; auto; fail).
   red; simpl; auto.
Qed.

Lemma ptree_ids_match_callnd_env:
  forall cdef i se1 se1' ef ef',
  callnd_env cdef i se1 se1' ef ef' ->
  cakind cdef = true ->
  forall se2, ptree_ids_match (map instid (cons_inst cdef)) se1 se2 ->
  exists se2', callnd_env cdef i se2 se2' ef ef'
    /\ ptree_ids_match (map instid (cons_inst cdef)) se1' se2'.
Proof.
  intros. inv H. econstructor.
  unfold cons_inst in *.
  rewrite H0 in *. rewrite H1 in *; simpl; auto.
  split; auto.
  -econstructor; eauto.
  -red. simpl; intros. destruct H; auto.
   subst. repeat rewrite PTree.gss; auto.
   destruct H.
Qed.

Lemma call_env_match_ptree_sets_exist:
  forall c i se1 se1' ef ef',
  call_env c i se1 se1' ef ef' ->
  forall se2, ptree_ids_match (map instid (cons_inst c)) se1 se2 ->
  exists se2', call_env c i se2 se2' ef ef'
    /\ ptree_ids_match (map instid (cons_inst c)) se1' se2'
    /\ exists l el, incl l (map instid (cons_inst c))
        /\ ptree_sets se1 l el se1'
        /\ ptree_sets se2 l el se2'.
Proof.
  induction 1; intros.
  +generalize H0; intros.
   eapply ptree_ids_match_callnd_env in H0; eauto.
   destruct H0 as [? [? ?]].
   exists x. repeat split; auto. constructor 1; auto.
   inv H0. inv H2.
   exists (map instid (cons_inst c)). econstructor.
   unfold cons_inst in *.
   rewrite H in *. simpl in *. split; try red; auto.
   split; econstructor; eauto. econstructor.
   rewrite H1 in *; simpl; auto. rewrite H0 in *.
   inv H4. econstructor.
  +exists se2. repeat split; auto. constructor 2; auto.
   exists nil, nil. repeat split; try constructor.
   red; intros ? A; inv A.
Qed.

Inductive env_ids_match(l1 l2: list ident): env -> env -> Prop :=
  | env_ids_match_cons: forall eh1 eh2 se1 se2,
     ptree_ids_match l1 eh1 eh2 ->
     ptree_ids_match l2 se1 se2 ->
     env_ids_match l1 l2 (mkenv eh1 se1) (mkenv eh2 se2).

Lemma env_ids_match_refl:
  forall l1 l2 e,
  env_ids_match l1 l2 e e.
Proof.
  destruct e. constructor; red; auto.
Qed.

Lemma env_ids_match_swap:
  forall l1 l2 e1 e2,
  env_ids_match l1 l2 e1 e2 ->
  env_ids_match l1 l2 e2 e1.
Proof.
  induction 1.
  constructor 1. apply ptree_ids_match_swap; auto.
  apply ptree_ids_match_swap; auto.
Qed.

Lemma env_ids_match_trans:
  forall l1 l2 e1 e2 e3,
  env_ids_match l1 l2 e1 e2 ->
  env_ids_match l1 l2 e2 e3 ->
  env_ids_match l1 l2 e1 e3.
Proof.
  intros. inv H; inv H0.
  constructor 1.
  apply ptree_ids_match_trans with eh2; auto.
  apply ptree_ids_match_trans with se2; auto.
Qed.

Lemma call_env_ptree_ids_match:
  forall cdef i se se' ef ef' l,
  call_env cdef i se se' ef ef' ->
  list_disjoint (map instid (cons_inst cdef)) l ->
  ptree_ids_match l se se'.
Proof.
  unfold cons_inst.
  induction 1; rewrite H; simpl; intros.
  inv H0. destruct cdef; simpl in *.
  apply ptree_ids_match_set; auto.
  red; auto.
Qed.

Lemma locenv_range_perm_vars_setid:
  forall l eh b m m' t,
  locenv_range_perm_vars eh l ->
  eh ! b = Some (m,t) ->
  length m = length m' ->
  locenv_range_perm_vars (PTree.set b (m',t) eh) l.
Proof.
  unfold locenv_range_perm_vars. intros.
  apply H in H2. destruct H2 as [? [? [? ?]]].
  compare b id; intros; subst.
  +rewrite H2 in H0. inv H0. exists m'; split; [| split]; auto.
   -rewrite PTree.gss; auto.
   -rewrite <-H1; auto.
   -destruct H4 as [? [? ?]]. repeat split; try omega; auto.
  +exists x; split; auto. rewrite PTree.gso; auto.
Qed.

Lemma store_env_range_perm_vars:
  forall eh t b ofs v eh',
  store_env t eh b ofs v eh'->
  forall l, locenv_range_perm_vars eh l ->
  locenv_range_perm_vars eh' l.
Proof.
  intros. inv H.
  apply locenv_range_perm_vars_setid with m; auto.
  eapply store_mvl_length; eauto.
Qed.

Lemma locenv_setvars_locenv_range_perm:
  forall e l vl e' al,
  locenv_setvars e l vl e' ->
  locenv_range_perm_vars e al ->
  locenv_range_perm_vars e' al.
Proof.
  induction 1; intros; auto.
  eapply store_env_range_perm_vars in H0; eauto.
Qed.

Lemma has_type_store_env_exists:
  forall eh v t i,
  has_type v t ->
  locenv_range_perm_vars eh ((i, t) :: nil) ->
  exists eh', store_env t eh i Int.zero v eh'.
Proof.
  intros. destruct H0 with i t as [m [? [? ?]]]; simpl; auto.
  destruct has_type_access_mode with v t as [[c ?] | ?]; auto.
  +destruct valid_access_store with m c (Int.unsigned Int.zero) v as [m' ?]; eauto.
     rewrite Int.unsigned_zero. simpl.
     split. erewrite sizeof_chunk_eq; eauto.
     exists 0. auto.
   exists (PTree.set i (m',t) eh).
   exists m; auto.
   econstructor 1 with c; eauto.
  +destruct has_type_access_mode_mvl with v t as [m1 [A A2]]; auto.
   subst. generalize (sizeof_pos t); intros.
   assert (sizeof t = Z_of_nat (length m1)).
     apply mvl_type_length in A2; auto.
   destruct range_perm_store_bytes with m 0 m1 as [m' ?]; simpl; eauto.
   congruence.
   exists (PTree.set i (m',t) eh). exists m; auto.
   constructor 2; auto.
   rewrite Int.unsigned_zero. exists 0. auto.
Qed.

Lemma alloc_variables_range_perm:
  forall e al e',
  alloc_variables e al e' ->
  list_norepet (map fst al) ->
  (forall id ty, In (id,ty) al -> 0 < sizeof ty <= Int.max_signed) ->
  locenv_range_perm_vars e' al.
Proof.
  induction 1; intros.
  +red; intros. inv H1.
  +inv H0. red; simpl; intros.
   destruct H0.
   -inv H0. exists (alloc (sizeof ty0)).
    erewrite alloc_variables_notin_eq; eauto.
    rewrite PTree.gss; auto. split; auto.
    generalize (sizeof_pos ty0). intros. split.
    unfold alloc. rewrite length_list_repeat.
    rewrite nat_of_Z_eq; try omega.
    apply alloc_range_perm; auto.
    apply H1 with id0; simpl; auto.
   -eapply IHalloc_variables in H5; eauto.
    intros. apply H1 with id1; simpl; auto.
Qed.

Lemma alloc_variables_ptree_ids_none:
  forall al ef ids,
  alloc_variables empty_locenv al ef ->
  list_disjoint ids (map fst al) ->
  ptree_ids_none ids ef.
Proof.
  red; intros.
  erewrite alloc_variables_notin_eq; eauto.
  rewrite PTree.gempty; auto.
  red; intros. apply H0 with id id; auto.
Qed.

Lemma store_env_ptree_ids_none:
  forall t e id ofs v e' ids,
  store_env t e id ofs v e' ->
  ptree_ids_none ids e ->
  ptree_ids_none ids e'.
Proof.
  intros. inv H. red; intros.
  compare id id0; intros; subst.
  apply H0 in H. congruence.
  rewrite PTree.gso; auto.
Qed.

Lemma locenv_setlvar_ptree_ids_none:
  forall gc e e' a v ids,
  locenv_setlvar gc e a v e' ->
  ptree_ids_none ids e ->
  ptree_ids_none ids e'.
Proof.
  intros. inv H.
  eapply store_env_ptree_ids_none; eauto.
Qed.

Lemma eval_eqf_ptree_ids_none:
  forall gc e e' a ids,
  eval_eqf gc e e' a ->
  ptree_ids_none ids e ->
  ptree_ids_none ids e'.
Proof.
  intros. inv H.
  eapply locenv_setlvar_ptree_ids_none; eauto.
Qed.

Lemma locenv_setvars_ptree_ids_none:
  forall e al vl e' ids ,
  locenv_setvars e al vl e' ->
  ptree_ids_none ids e ->
  list_disjoint ids (map fst al) ->
  ptree_ids_none ids e'.
Proof.
  intros. red; intros.
  erewrite set_new_vars_getid_eq; eauto.
  eapply list_disjoint_notin; eauto.
Qed.

(* -------------------------- env_match --------------------------- *)

Definition subenv_match(P: env-> env -> Prop)(se1 se2: subenv): Prop :=
  (forall id, se1 ! id = None -> se2 ! id = None) /\
  (forall id l1, se1 ! id = Some l1 ->
     exists l2, se2 ! id = Some l2 /\ Forall2 P l1 l2).

Lemma subenv_match_empty:
  forall P, subenv_match P empty_subenv empty_subenv.
Proof.
  red. split; intros; auto.
  rewrite PTree.gempty in H. congruence.
Qed.

Lemma subenv_match_setsame:
  forall P se1 se2 id l1 l2,
  subenv_match P se1 se2 ->
  Forall2 P l1 l2 ->
  subenv_match P (PTree.set id l1 se1) (PTree.set id l2 se2).
Proof.
  intros. destruct H. split; intros.
  +compare id id0; intros; subst.
   -rewrite PTree.gss in H2. congruence.
   -rewrite PTree.gso in *; auto.
  +compare id id0; intros; subst.
   -rewrite PTree.gss in *. inv H2. econstructor; split; eauto.
   -rewrite PTree.gso in *; auto.
Qed.


Inductive env_match: env -> env -> Prop :=
  | env_match_: forall le1 se1 le2 se2,
      locenv_match le1 le2 ->
      subenv_match env_match se1 se2 ->
      env_match (mkenv le1 se1) (mkenv le2 se2).

Lemma env_match_empty:
  env_match empty_env empty_env.
Proof.
  constructor.
  red; auto.
  apply subenv_match_empty.
Qed.

Lemma env_match_callnd_inst_env_exists:
  forall le1 se1 le2 se2 cdef i ef1,
  env_match (mkenv le1 se1) (mkenv le2 se2) ->
  callnd_inst_env cdef i se1 ef1 ->
  exists ef2, callnd_inst_env cdef i se2 ef2.
Proof.
  intros.
  inv H; inv H0.
  destruct H6. apply H3 in H. destruct H as [? [? ?]].
  eapply Forall2_nth_error_exists in H1; eauto.
  destruct H1 as [? [? ?]].
  exists x0. econstructor; eauto.
  apply Forall2_length in H5. rewrite <-H5; auto.
Qed.

Lemma env_match_callnd_inst_env_match:
  forall le1 le2 se1 se2 c i ef1 ef2,
  env_match (mkenv le1 se1) (mkenv le2 se2) ->
  callnd_inst_env c i se1 ef1 ->
  callnd_inst_env c i se2 ef2 ->
  env_match ef1 ef2.
Proof.
  intros. inv H.
  destruct H7. inv H0; inv H1.
  destruct H2 with (instid c) efs as [l2 [? ?]]; auto.
  rewrite H0 in H1. inv H1.
  eapply Forall2_nth_error_exists in H4; eauto.
  destruct H4 as [? [? ?]]. rewrite H7 in H1.
  inv H1; auto.
Qed.

Lemma callnd_env_exists_se:
  forall cdef i se se' ef ef' le le1 se1 ef1 ef1',
  callnd_env cdef i se se' ef ef' ->
  env_match (mkenv le se) (mkenv le1 se1) ->
  callnd_inst_env cdef i se1 ef1 ->
  env_match ef' ef1' ->
  exists se1', callnd_env cdef i se1 se1' ef1 ef1'
    /\ env_match (mkenv le se') (mkenv le1 se1').
Proof.
  intros. inv H0. inv H. inv H1.
  destruct H8.
  exists (PTree.set (instid cdef)
             (replace_nth efs0 (nat_of_int i) ef1') se1); simpl.
  destruct H8 with (instid cdef) efs as [l [? ?]]; auto.
  rewrite H9 in H. inv H. split.
  +constructor 1 with efs0; auto.
  +econstructor; eauto.
   eapply subenv_match_setsame; eauto. constructor; auto.
   eapply Forall2_replace; eauto.
Qed.


Definition int_of_nat(n: nat): int :=
  Int.repr (Z_of_nat n).

Lemma int_of_nat_of_int:
  forall j, j = int_of_nat (nat_of_int j).
Proof.
  unfold nat_of_int, int_of_nat. intros.
  generalize (Int.unsigned_range j); intros.
  rewrite nat_of_Z_eq; try omega.
  rewrite Int.repr_unsigned; auto.
Qed.

Lemma nat_of_int_of_nat:
  forall n,  (n <= nat_of_Z Int.max_signed)%nat ->
  n = nat_of_int (int_of_nat n).
Proof.
  unfold nat_of_int, int_of_nat. intros.
  generalize Int.max_signed_unsigned; intros.
  rewrite Int.unsigned_repr; try omega.
  rewrite nat_of_Z_of_nat; try omega.
  split; try omega.
  apply Nat2Z.inj_le in H; try omega.
  rewrite nat_of_Z_eq in H; try omega.
  unfold Int.max_signed. simpl. omega.
Qed.

Lemma unsigned_int_of_nat_le:
  forall i j,
  (i < j <= nat_of_Z Int.max_signed)%nat ->
  Int.unsigned (int_of_nat i) < Int.unsigned (int_of_nat j).
Proof.
  unfold int_of_nat. intros.
  destruct H. apply Nat2Z.inj_lt in H.
  apply Nat2Z.inj_le in H0. rewrite nat_of_Z_eq in H0.
  generalize Int.max_signed_unsigned; intros.
  repeat rewrite Int.unsigned_repr; try omega.
  unfold Int.max_signed. simpl. omega.
Qed.
