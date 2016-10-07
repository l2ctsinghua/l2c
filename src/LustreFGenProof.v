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

(** Correctness proof for translation of tempo statement. *)

Require Import Coqlib.
Require Import AST.
Require Import Errors.
Require Import Maps.
Require Import Integers.
Require Import Permutation.
Require Import List.
Require Import ExtraList.
Require Import Lident.
Require Import Cltypes.
Require Import Ltypes.
Require Import Lustre.
Require Import LustreR.
Require Import LustreF.
Require Import Lvalues.
Require Import Lenv.
Require Import Lenvmatch.
Require Import Lsem.
Require Import LsemR.
Require Import LsemF.
Require Import Lint.
Require Import LustreFGen.

Section CORRECTNESS.

Variable prog1: LustreR.program.
Variable prog2: program.

Hypothesis TRANS:
  trans_program prog1 = prog2.

Hypothesis ID_RANGE:
  LustreR.ids_range ACG_INIT (node_block prog1).

Hypothesis GID_RANGE:
  ids_plt ACG_EQU (map fst (const_block prog1)++ map fst (node_block prog1)).

Section NODE_CORRECT.

Variable gc: locenv.

Hypothesis GENV_NONE:
  gc ! ACG_J = None.

Definition locenv_matcht(l: list (ident*type))(te1 te2: locenv): Prop :=
  (forall id, id <> ACG_J -> te1 ! id = te2 ! id) /\
  locenv_range_perm_vars te2 l /\
  te1 ! ACG_J = None.

Lemma locenv_matcht_some:
  forall al te ta id mt,
  locenv_matcht al te ta ->
  te ! id = Some mt ->
  ta ! id = Some mt.
Proof.
  intros. destruct H as [? [? ?]].
  compare id ACG_J; intros; subst.
  congruence.
  rewrite <-H; auto.
Qed.

Lemma locenv_matcht_disjoint:
  forall al te ta,
  locenv_matcht al te ta ->
  locenv_disjoint gc te ta.
Proof.
  intros. red; intros.
  destruct H as [? [? ?]].
  compare id ACG_J; intros; subst.
  congruence.
  rewrite <-H; auto.
Qed.

Lemma eval_sexp_match:
  forall te1 e s v,
  eval_sexp gc te1 e s v ->
  forall te2 l, locenv_matcht l te1 te2 ->
  eval_sexp gc te2 e s v
with eval_lvalue_match:
  forall te1 e a id ofs k,
  eval_lvalue gc te1 e a id ofs k->
  forall te2 l, locenv_matcht l te1 te2 ->
  eval_lvalue gc te2 e a id ofs k.
Proof.
 +induction 1; intros.
  -constructor; auto.
  -constructor 2 with v1; eauto.
  -constructor 3 with v1 v2; eauto.
  -constructor 4 with v1; eauto.
  -apply eval_Rlvalue with id ofs k; auto.
   apply eval_lvalue_match with te1 l; auto.
   destruct k; simpl in *; auto;
   apply load_env_match with te1; auto;
   red; intros; eapply locenv_matcht_some; eauto.
 +induction 1; intros.
  -constructor 1 with m; auto.
   eapply locenv_matcht_some; eauto.
  -constructor 2 with m; auto.
   destruct H1 as [? [? ?]].
   compare id ACG_J; intros; subst.
   congruence. rewrite <-H1; auto.
  -constructor 3 with m; auto.
  -apply eval_Saryacc with aid z; eauto.
  -apply eval_Sfield with sid fld; eauto.
Qed.

Lemma eval_sexps_match:
  forall te1 e al vl,
  eval_sexps gc te1 e al vl ->
  forall te2 l, locenv_matcht l te1 te2 ->
  eval_sexps gc te2 e al vl.
Proof.
  induction 1; intros.
  constructor.
  constructor 2; auto.
  eapply eval_sexp_match; eauto.
  eapply IHForall2; eauto.
Qed.

Lemma locenv_setlvar_set_right:
  forall gc eh1 id t v eh2 te,
  Lsem.locenv_setlvar gc eh1 (Svar id t) v eh2 ->
  locenv_setvarf gc te eh1 (Ssvar id t) v te eh2.
Proof.
  intros. inv H. inv H0.
  constructor 2 with b Int.zero; auto.
  constructor 3 with m; auto.
Qed.

Lemma trans_call_func:
  forall nid cdef fd nd,
  Lustre.call_func (node_block prog1) cdef fd ->
  find_funct (node_block prog1) nid = Some nd ->
  callorder (nd_kind (snd nd)) (nd_kind (snd fd)) = true ->
  Lustre.call_node (node_block prog2) nid cdef (trans_node nd) (trans_node fd).
Proof.
  unfold Lustre.call_node, Lustre.call_func. intros.
  destruct H. subst.
  simpl. repeat (split; auto).
  +eapply trans_funcs_find; eauto.
  +eapply trans_funcs_find; eauto.
Qed.

Lemma alloc_variables_match_rec:
  forall eh1 l eh1',
  alloc_variables eh1 l eh1' ->
  ~ In ACG_J (map fst l) ->
  forall eh2, (forall id, (id <> ACG_J) -> eh1 ! id = eh2 ! id) ->
  eh1 ! ACG_J = None ->
  eh2 ! ACG_J = None ->
  exists eh2', alloc_variables eh2 ((ACG_J,type_int32s) :: l) eh2'
    /\ locenv_matcht ((ACG_J,type_int32s)::nil) eh1' eh2'.
Proof.
  induction 1; intros.
  +destruct alloc_variables_exists with ((ACG_J, type_int32s) :: nil) eh2 as [eh2' ?].
   exists eh2'. split; auto.
   repeat (split; eauto).
   -intros. symmetry.
    rewrite alloc_variables_notin_eq with (e:=eh2) (al:=(ACG_J, type_int32s) :: nil); auto.
    rewrite H0; auto. simpl; red; intros A.
    destruct A; subst; tauto.
   -eapply alloc_variables_range_perm; eauto.
    constructor; auto. constructor.
    simpl; intros. destruct H4; inv H4. simpl.
    unfold Int.max_signed. simpl; omega.
  +destruct IHalloc_variables with (PTree.set id (alloc (sizeof ty),ty) eh2) as [eh2' [? ?]]; auto.
   -red. intros. eapply H0; eauto. simpl; auto.
   -intros. compare id id0; intros; subst.
    repeat rewrite PTree.gss; auto.
    repeat rewrite PTree.gso; auto.
   -rewrite PTree.gso; auto. red; intros; subst. apply H0. simpl; auto.
   -rewrite PTree.gso; auto. red; intros; subst. apply H0. simpl; auto.
   -exists eh2'. split; auto.
    inv H4. constructor 2. constructor 2.
    rewrite ptree_set_swap; auto.
    red; intros; subst. apply H0. simpl; auto.
Qed.

Lemma locenv_matcht_refl:
  forall te, te ! ACG_J = None ->
  locenv_matcht nil te te.
Proof.
  intros. repeat (split; auto).
  red; intros; auto.
  red; simpl; intros; tauto.
Qed.

Lemma alloc_variables_match:
  forall f te,
  alloc_variables empty_locenv (allvarsof f) te ->
  ~ In ACG_J (map fst (allvarsof f)) ->
  LustreR.ids_norepet f ->
  exists ta, alloc_variables empty_locenv (allvarsof (trans_body f)) ta
    /\ locenv_matcht (mkloopid (fbyeqof (nd_stmt f))) te ta.
Proof.
  intros.
  unfold allvarsof in *. simpl.
  destruct mkloopid_idrange with (fbyeqof (nd_stmt f)) as [ A | A];
  rewrite A in *; simpl in *.
  +rewrite <-app_nil_end. exists te. split; auto.
   apply locenv_matcht_refl; auto.
   erewrite alloc_variables_notin_eq with (e:=empty_locenv); eauto.
  +apply alloc_variables_match_rec with (eh2:=empty_locenv) in H; eauto.
   destruct H as [ta [? ?]]. exists ta. split; auto.
   -apply alloc_variables_permut with ((ACG_J, type_int32s) :: (nd_vars f ++ nd_args f) ++ nd_rets f); auto.
    repeat rewrite app_ass. simpl.
    apply Permutation_middle. simpl.
    constructor; auto.
    destruct H1; auto.
Qed.

Lemma locenv_matcht_store_env_exists:
  forall l ty te id o v te' ta,
  store_env ty te id o v te' ->
  locenv_matcht l te ta ->
  exists ta', store_env ty ta id o v ta'
    /\ locenv_matcht l te' ta'.
Proof.
  unfold locenv_matcht.
  induction 1. intros. destruct H2 as [? [? ?]].
  exists (PTree.set id (m',t) ta). repeat split; auto.
  +constructor 1 with m; auto.
   rewrite <-H2; auto. intros. subst. congruence.
  +intros. compare id id0; intros; subst.
    repeat rewrite PTree.gss; auto.
    repeat rewrite PTree.gso; auto.
  +apply locenv_range_perm_vars_setid with (m:=m); eauto.
   rewrite <-H2; auto. congruence.
   eapply store_mvl_length; eauto.
  +rewrite PTree.gso; auto. red; intro; subst. congruence.
Qed.

Lemma locenv_setvars_exists:
  forall l1 eh1 l vl eh1',
  locenv_setvars eh1 l vl eh1' ->
  forall eh2, locenv_matcht l1 eh1 eh2 ->
  exists eh2', locenv_setvars eh2 l vl eh2'
    /\ locenv_matcht l1 eh1' eh2'.
Proof.
  induction 1; intros.
  +exists eh2. split; auto. constructor.
  +eapply locenv_matcht_store_env_exists in H0; eauto.
   destruct H0 as [eh21 [? ?]].
   destruct IHlocenv_setvars with eh21 as [eh2' [? ?]]; auto.
   exists eh2'. split; auto.
   constructor 2 with eh21 m; auto.
   eapply locenv_matcht_some; eauto.
Qed.

Lemma eval_sexp_gcempty:
  forall e a v,
  Lsem.eval_sexp empty_locenv e a v ->
  Lsem.eval_sexp gc e a v
with eval_lvalue_gcempty:
  forall e a b ofs k,
  Lsem.eval_lvalue empty_locenv e a b ofs k ->
  Lsem.eval_lvalue gc e a b ofs k.
Proof.
 +induction 1; simpl; intros.
  -constructor; auto.
  -constructor 2 with v1; auto.
  -constructor 3 with v1 v2; auto.
  -constructor 4 with v1; auto.
  -constructor 5 with id ofs k; auto.
   inv H0; destruct H2 as [m [t1 [? [? ?]]]].
   rewrite PTree.gempty in *. congruence.
   constructor 2. exists m, t1; split; auto.
 +induction 1; simpl; intros; auto.
  -constructor 1 with m; auto.
  -rewrite PTree.gempty in *. congruence.
  -eapply Lsem.eval_Saryacc; eauto.
  -apply Lsem.eval_Sfield with sid fld; auto.
Qed.

Lemma flag_set_correct:
  forall eh eh2 ta b,
  Lsem.eval_eqf empty_locenv eh eh2 (Svar ACG_INIT type_bool, Sconst (Cbool b) type_bool) ->
  eval_eqf gc ta eh ta eh2 (Ssvar ACG_INIT type_bool, Sconst (Cbool b) type_bool).
Proof.
  intros. inv H. constructor 1 with v v'; auto.
  +inv H2. constructor; auto. inv H.
  +econstructor 1; simpl; eauto.
  +eapply locenv_setlvar_set_right; eauto.
   inv H7. econstructor; eauto.
   eapply eval_lvalue_gcempty; eauto.
Qed.

Lemma locenv_matcht_setlvar_left_exists:
  forall te a v te1,
  Lsem.locenv_setlvar gc te a v te1 ->
  forall l ta eh, locenv_matcht l te ta ->
  exists ta1, locenv_setvarf gc ta eh a v ta1 eh
    /\ locenv_matcht l te1 ta1.
Proof.
  induction 1. intros.
  eapply eval_lvalue_lvalue with (eh:=eh) in H; eauto.
  eapply eval_lvalue_match in H; eauto.
  eapply locenv_matcht_store_env_exists in H0; eauto.
  destruct H0 as [ta1 [? ?]].
  exists ta1. split; auto.
  constructor 1 with b ofs; eauto.
Qed.

Lemma lvalue_disjoint_matchm:
  forall te eh a a1,
  lvalue_disjoint (eval_lvalue gc te eh) a a1 ->
  forall al ta, locenv_matcht al te ta ->
  lvalue_disjoint (eval_lvalue gc ta eh) a a1.
Proof.
  intros. inv H.
  constructor 1 with id1 id2 o1 o2 k1 k2; auto;
  eapply eval_lvalue_match; eauto.
Qed.

Lemma assign_disjoint_match:
  forall te eh a1 a2 al ta,
  assign_disjoint (eval_lvalue gc te eh) a1 a2 ->
  locenv_matcht al te ta ->
  assign_disjoint (eval_lvalue gc ta eh) a1 a2.
Proof.
  intros. inv H.
  constructor 1 with chunk; auto.
  constructor; auto.
  eapply lvalue_disjoint_matchm; eauto.
Qed.

Lemma eval_stmt_trans_peqs_app:
  forall nid l1 ta ta1 e e1,
  eval_stmt false prog2 gc nid ta e ta1 e1 (trans_peqs l1) ->
  forall ta' e' l2,
  eval_stmt false prog2 gc nid ta1 e1 ta' e' (trans_peqs l2) ->
  eval_stmt false prog2 gc nid ta e ta' e' (trans_peqs (l1 ++ l2)).
Proof.
  induction l1; simpl; intros.
  +inv H. auto.
  +destruct a; eauto; inv H; eapply eval_Sseq; eauto;
   eapply IHl1; eauto.
Qed.

Lemma eval_lvalue_field:
  forall ta eh id1 id2 sty ty b ofs,
  Lsem.eval_lvalue gc eh (Sfield (Svar id1 sty) id2 ty) b ofs Lid ->
  eval_lvalue gc ta eh (Sfield (Ssvar id1 sty) id2 ty) b ofs Sid.
Proof.
  intros.
  inv H. apply eval_Sfield with sid fld; auto.
  inv H3. constructor 3 with m; auto.
Qed.

Lemma eval_lvalue_aryacc_field:
  forall ta eh id1 i sty aty ty b ofs,
  Lsem.eval_lvalue gc eh (Saryacc (Sfield (Svar id1 sty) FBYITEM aty) (Sconst (Cint i) type_int32s) ty) b ofs Lid ->
  eval_lvalue gc ta eh (Saryacc (Sfield (Ssvar id1 sty) FBYITEM aty) (Sconst (Cint i) type_int32s) ty) b ofs Sid.
Proof.
  intros.
  inv H. apply eval_Saryacc with aid z;auto.
  eapply  eval_lvalue_field; eauto.
  inv H4. constructor ; auto. inv H.
Qed.

Lemma eval_lvalue_aryacc_field_index:
  forall ta eh id1 sty aty ty b ofs,
  Lsem.eval_lvalue empty_locenv eh (Saryacc (Sfield (Svar id1 sty) FBYITEM aty) (Sfield (Svar id1 sty) FBYIDX type_int32s) ty) b ofs Lid ->
  eval_lvalue gc ta eh (Saryacc (Sfield (Ssvar id1 sty) FBYITEM aty) (Sfield (Ssvar id1 sty) FBYIDX type_int32s) ty) b ofs Sid.
Proof.
  intros.
  inv H. apply eval_Saryacc with aid z;auto.
  eapply eval_lvalue_field; eauto.
  eapply eval_lvalue_gcempty; eauto.
  apply eval_field_field; auto.
Qed.

Lemma eval_fbyeqs_correct:
  forall te s eh eh',
  eval_fbyeqs gc te eh eh' (LustreR.fbyeqof s) ->
  forall al ta se nid, locenv_matcht al te ta ->
  eval_stmt false prog2 gc nid ta (mkenv eh se) ta (mkenv eh' se) (trans_peqs (fbyeqof s)).
Proof.
  induction s; simpl; intros; eauto; try (inv H; econstructor; eauto; fail).
  +eapply eval_fbyeqs_app_inv in H; eauto. destruct H as [eh1 [? ?]]; auto.
   eapply eval_stmt_trans_peqs_app; eauto.
  +inv H. inv H6. apply eval_Sseq with ta (mkenv eh' se); auto.
   constructor. simpl.
   -inv H5.
    cut(eval_sexp gc ta eh s0 v). intros A.
    cut(eval_lvalue gc ta eh (Ssvar i (typeof s0)) i Int.zero Sid). intros A1.
     constructor 1 with v v'; auto.
    *apply lids_disjoint_assign_disjoint with v i Int.zero Sid; auto.
    *inv H4.  econstructor; eauto. inv A1. inv H; eauto.
    *inv H4. inv H. econstructor; eauto.
    *eapply eval_sexp_match; eauto.
     eapply eval_sexp_sexp; eauto.
   -constructor.
  +destruct p. destruct p. inv H. simpl.
   inv H6. inv H7.
   apply eval_Sseq with ta (mkenv e1 se); auto.
   -constructor. simpl.
    inv H5.
    cut(eval_sexp gc ta eh s0 v). intros A1.
    constructor 1 with v v'; auto.
    *inv H6. apply lids_disjoint_assign_disjoint with v b ofs Sid; auto.
     eapply eval_lvalue_aryacc_field_index; eauto.
    *inv H6.  econstructor; eauto.
     eapply eval_lvalue_aryacc_field_index; eauto.
    *eapply eval_sexp_match; eauto.
     eapply eval_sexp_sexp; eauto.
   -inv H4. apply eval_Sseq with ta (mkenv eh' se); auto.
    constructor; auto. simpl.
    inv H3. constructor 1 with v v'; auto.
    *clear -H2. inv H2. econstructor; eauto.
     inv H4. econstructor; eauto.
     eapply eval_field_field; eauto.
     inv H6. constructor; simpl; auto. inv H.
     inv H.
     inv H5. constructor; simpl; auto. inv H.
     inv H.
    *constructor 1 with Mint32; auto.
    *clear -H9 H6. inv H9. econstructor; eauto.
     eapply eval_lvalue_field; eauto.
     eapply eval_lvalue_gcempty; eauto.
    *constructor.
  +inv H. inv H5. inv H6. constructor.
  +eapply eval_fbyeqs_app_inv in H; eauto.
   destruct H as [eh1 [? ?]].
   apply eval_stmt_trans_peqs_app with ta (mkenv eh1 se); eauto.
Qed.

Lemma eval_lvalue_aryacc_app1:
  forall ta e a id i ty b ofs k,
  eval_lvalue gc ta e (Saryacc a (Sconst (Cint i) type_int32s) ty) b ofs k ->
  eval_sexp gc ta e (Svar id type_int32s) (Vint i) ->
  eval_lvalue gc ta e (Saryacc a (Svar id type_int32s) ty) b ofs k.
Proof.
  intros. inv H.
  eapply eval_Saryacc; eauto.
  inv H5; auto. inv H.
Qed.

Lemma eval_poststmt_match:
  forall te eh eh' s l nid ta se,
  eval_poststmt gc te eh (LustreR.fbyeqof s) eh' ->
  locenv_matcht l te ta ->
  eval_stmt false prog2 gc nid ta (mkenv eh se) ta (mkenv eh' se)
          (mkpoststmt (fbyeqof s)).
Proof.
  intros. unfold mkpoststmt.
  rewrite <-fbyeqof_length. inversion H; simpl.
  destruct (le_lt_dec _ _).
  +subst. destruct (LustreR.fbyeqof s); simpl in *; try omega.
   inv H1. constructor.
  +apply eval_Sseq with ta (mkenv eh1 se); auto.
   -eapply eval_fbyeqs_correct; eauto.
   -unfold flag_incr. constructor; auto.
    eapply flag_set_correct; eauto.
Qed.

Lemma eval_eqf_trans:
  forall te te1 a,
  Lsem.eval_eqf gc te te1 a ->
  forall l eh ta, locenv_matcht l te ta ->
  exists ta1, eval_eqf gc ta eh ta1 eh a
    /\ locenv_matcht l te1 ta1.
Proof.
  induction 1; intros.
  apply locenv_matcht_setlvar_left_exists with (l:=l) (ta:=ta) (eh:=eh) in H2; eauto.
  destruct H2 as [ta1 [? ?]].
  exists ta1. split; auto.
  constructor 1 with v v'; auto.
  eapply eval_sexp_match; eauto.
  apply eval_sexp_sexp; auto.
  eapply assign_disjoint_match; eauto.
  eapply assign_disjoint_trans_left; eauto.
Qed.

Lemma locenv_setvarfs_exists:
  forall te l vl te',
  locenv_setlvars gc te l vl te' ->
  forall al ta eh, locenv_matcht al te ta ->
  exists ta', locenv_setvarfs gc ta eh l vl ta' eh
    /\ locenv_matcht al te' ta'.
Proof.
  induction 1; intros.
  +exists ta. split; auto. constructor.
  +eapply locenv_matcht_setlvar_left_exists with (eh:=eh) in H; eauto.
   destruct H as [ta1 [? ?]].
   destruct IHlocenv_setlvars with al ta1 eh as [ta' [? ?]]; auto.
   exists ta'. split; auto.
   econstructor 2; eauto.
Qed.

Lemma lvalue_list_norepet_matchm:
  forall te eh lhs,
  lvalue_list_norepet (eval_lvalue gc te eh) lhs ->
  forall al ta, locenv_matcht al te ta ->
  lvalue_list_norepet (eval_lvalue gc ta eh) lhs.
Proof.
  induction 1; intros.
  constructor.
  constructor 2; eauto.
  red; intros. apply H in H2.
  eapply lvalue_disjoint_matchm; eauto.
Qed.

Lemma locenv_getmvls_match:
  forall te lhs vl,
  locenv_getmvls gc te lhs vl ->
  forall al ta, locenv_matcht al te ta ->
  locenv_getmvls gc ta lhs vl.
Proof.
  induction 1; intros.
  constructor.
  constructor 2; eauto.
  inv H. constructor 1 with id ofs m t; auto.
  eapply Lenvmatch.eval_lvalue_match; eauto.
  red; intros. eapply locenv_matcht_some; eauto.
  eapply locenv_matcht_disjoint; eauto.
  eapply locenv_matcht_some; eauto.
  eapply IHForall2; eauto.
Qed.

Lemma loopid_disjioint_vars:
  forall nid f, In (nid, f) (node_block prog1) ->
  ~ In ACG_J (map fst (allvarsof f)).
Proof.
  intros. apply ID_RANGE in H.
  red. simpl. intros.
  apply ids_plt_le_notin with ACG_J _ _ in H; auto.
  apply H. simpl. apply in_or_app; auto.
  unfold Ple, ACG_J, ACG_INIT. omega.
Qed.

Lemma store_env_locenv_matcht:
  forall ta te ta1 v,
  store_env type_int32s ta ACG_J Int.zero v ta1 ->
  locenv_matcht ((ACG_J, type_int32s) :: nil) te ta ->
  locenv_matcht ((ACG_J, type_int32s) :: nil) te ta1.
Proof.
  intros. inv H.
  destruct H0 as [? [? ?]]. repeat (split; auto).
  +intros. rewrite PTree.gso; auto.
  +apply locenv_range_perm_vars_setid with m; auto.
   eapply store_mvl_length; eauto.
Qed.

Lemma load_env_eval_lvalue_loop:
  forall ta e j id,
  load_env type_int32s ta id Int.zero (Vint j) ->
  locenv_range_perm_vars ta ((id, type_int32s) :: nil) ->
  eval_lvalue gc ta e (Svar id type_int32s) id Int.zero Lid.
Proof.
  intros.
  destruct H0 with id type_int32s as [? [? ?]]; simpl; auto.
  destruct H as [? [? [? ?]]].
  rewrite H1 in H. inv H.
  constructor 1 with x0; auto.
Qed.

Lemma load_env_eval_sexp_loop:
  forall ta e j id,
  load_env type_int32s ta id Int.zero (Vint j) ->
  locenv_range_perm_vars ta ((id, type_int32s) :: nil) ->
  eval_sexp gc ta e (Svar id type_int32s) (Vint j).
Proof.
  intros.
  apply eval_Rlvalue with id Int.zero Lid; simpl; auto.
  eapply load_env_eval_lvalue_loop; eauto.
Qed.

Lemma eval_loop_init:
  forall te ta ta0 eh,
  store_env type_int32s ta ACG_J Int.zero (Vint Int.zero) ta0 ->
  locenv_matcht ((ACG_J, type_int32s) :: nil) te ta ->
  eval_eqf gc ta eh ta0 eh loop_init.
Proof.
  intros. constructor 1 with (Vint Int.zero) (Vint Int.zero); auto.
  +constructor; simpl; auto.
  +constructor 1 with Mint32; auto.
  +constructor 1 with Mint32; auto.
  +constructor 1 with ACG_J Int.zero; auto.
   destruct H0 as [? [? ?]].
   destruct H1 with ACG_J type_int32s as [? [? ?]]; simpl; auto.
   inv H. rewrite H5 in H3. inv H3.
   constructor 1 with x; auto.
Qed.

Lemma eval_loop_cond_false:
  forall eh ta ta' j,
  store_env type_int32s ta ACG_J Int.zero (Vint j) ta' ->
  locenv_range_perm_vars ta ((ACG_J, type_int32s) :: nil) ->
  eval_sexp gc ta' eh (loop_cond j) Vfalse.
Proof.
  intros. unfold loop_cond.
  eapply store_env_range_perm_vars in H0; eauto.
  apply store_env_load_int_eq in H.
  apply eval_Sbinop with (Vint j) (Vint j); simpl; auto.
  +eapply load_env_eval_sexp_loop;eauto.
  +constructor. simpl;auto.
  +unfold Int.lt. rewrite pred_dec_false; auto. omega.
Qed.

Lemma eval_loop_cond_true:
  forall eh ta ta' i j,
  store_env type_int32s ta ACG_J Int.zero (Vint i) ta' ->
  locenv_range_perm_vars ta ((ACG_J, type_int32s) :: nil) ->
  Int.lt i j = true ->
  eval_sexp gc ta' eh (loop_cond j) Vtrue.
Proof.
  intros. unfold loop_cond.
  eapply store_env_range_perm_vars in H0; eauto.
  apply store_env_load_int_eq in H.
  apply eval_Sbinop with (Vint i) (Vint j); simpl; auto.
  +eapply load_env_eval_sexp_loop;eauto.
  +constructor. simpl;auto.
  +rewrite H1. auto.
Qed.

Lemma eval_fbyn_init_correct:
  forall id1 id2 aid a2 i j v2 eh eh',
  eval_fbyn_init gc id1 id2 aid (typeof a2) i j v2 eh eh' ->
  forall nid aty te ta ta0 ta' se,
  store_env type_int32s ta ACG_J Int.zero (Vint j) ta' ->
  store_env type_int32s ta ACG_J Int.zero (Vint i) ta0 ->
  Lsem.eval_sexp gc te a2 v2 ->
  locenv_matcht ((ACG_J, type_int32s) :: nil) te ta ->
  Tarray aid (typeof a2) (Int.unsigned j) = aty ->
  ~ In id1 (get_lids a2) ->
  eval_stmt false prog2 gc nid ta0 (mkenv eh se) ta' (mkenv eh' se)
   (LustreF.Sfor None (loop_cond j) loop_add
      (LustreF.Sassign
           (Saryacc (Sfield (Ssvar id1 (make_fbyn_type id2 aty)) FBYITEM aty) (Svar ACG_J type_int32s)
              (typeof a2)) a2)).
Proof.
  induction 1; intros.
  +rewrite H9 in H0. subst aty0.
   generalize H8; intros A. destruct A as [A [A1 A2]].
   destruct has_type_store_env_exists with ta (Vint (Int.add i Int.one)) type_int32s ACG_J as [ta1 A4]; simpl; auto.
   apply eval_Sfor_loop with ta0 ta1 eh1 eh1 se; auto.
   -eapply eval_loop_cond_true; eauto.
   -eapply store_env_locenv_matcht with (ta1:=ta0) in H8; eauto.
    cut (eval_sexp gc ta0 eh a2 v). intros B.
    cut (eval_sexp gc ta0 eh (Svar ACG_J type_int32s) (Vint i)). intros B1.
    constructor. constructor 1 with v v'; auto.
    *inv H3. apply lids_disjoint_assign_disjoint with v b ofs Sid; auto.
     apply eval_lvalue_aryacc_app1 with i; auto.
     eapply eval_lvalue_aryacc_field;eauto.
     simpl. red; simpl; intros. destruct H1; subst; congruence.
    *subst. inv H3. econstructor; eauto.
     eapply eval_lvalue_aryacc_app1; eauto.
     eapply eval_lvalue_aryacc_field; eauto.
    *eapply load_env_eval_sexp_loop; eauto.
     eapply store_env_load_int_eq; eauto.
     eapply store_env_range_perm_vars; eauto.
    *eapply eval_sexp_match; eauto.
     eapply eval_sexp_sexp; eauto.
   -eapply store_env_range_perm_vars with (eh':=ta0) in A1; eauto.
    constructor 1 with (Vint (Int.add i Int.one)) (Vint (Int.add i Int.one)); auto.
    *apply eval_Sbinop with (Vint i) (Vint Int.one); auto.
     eapply load_env_eval_sexp_loop; eauto.
     apply store_env_load_int_eq with ta; eauto.
     constructor; simpl; auto. simpl; auto.
    *constructor 1 with Mint32; auto.
    *constructor 1 with Mint32; auto.
    *constructor 1 with ACG_J Int.zero;auto.
     eapply load_env_eval_lvalue_loop; eauto.
     apply store_env_load_int_eq with ta; eauto.
     eapply store_env_trans; eauto.
   -apply IHeval_fbyn_init with te ta0; auto.
    eapply store_env_trans; eauto.
    eapply store_env_trans; eauto.
    eapply store_env_locenv_matcht; eauto.
  +unfold Int.eq in *. destruct (zeq _ _); inv H.
   apply int_unsigned_inj in e. subst.
   apply store_env_determ with (e1:=ta0) in H0; auto. subst.
   apply eval_Sfor_false.
   apply eval_loop_cond_false with ta; auto.
   destruct H3 as [? [? ?]]; auto.
Qed.

Lemma eval_fbyn_index_init:
  forall eh1 eh2 id1 sty ta1,
  Lsem.eval_eqf gc eh1 eh2
       (Sfield (Svar id1 sty) FBYIDX type_int32s, Sconst (Cint Int.zero) type_int32s) ->
  eval_eqf gc ta1 eh1 ta1 eh2
       (Sfield (Ssvar id1 sty) FBYIDX type_int32s, Sconst (Cint Int.zero) type_int32s).
Proof.
  intros. inv H.
  constructor 1 with v v'; auto.
  +inv H2. constructor. simpl; auto. inv H.
  +constructor 1 with Mint32; auto.
  +inv H7. constructor 2 with b ofs; auto.
   inv H. apply eval_Sfield with sid fld; auto.
   inv H7. constructor 3 with m; auto.
Qed.

Lemma trans_node_all_correct:
  forall e e' fd vargs vrets,
  LsemR.eval_node false prog1 gc e e' fd vargs vrets ->
  find_funct (node_block prog1) (fst fd) = Some fd ->
  eval_node false prog2 gc e e' (trans_node fd) vargs vrets.
Proof.
  induction 1 using LsemR.eval_node_ind2 with
  ( P0 := fun nk te e te' e' s =>
      forall nid nd ta l, locenv_matcht (mkloopid l) te ta ->
      incl (fbyeqof s) l ->
      nk = nd_kind (snd nd) ->
      find_funct (node_block prog1) nid = Some nd ->
      exists ta', eval_stmt false prog2 gc nid ta e ta' e' (trans_stmt s)
        /\ locenv_matcht (mkloopid l) te' ta');
  simpl; intros.
 +(*node*)
  destruct alloc_variables_match with f te as [ta [A A1]]; auto.
    apply loopid_disjioint_vars with nid; eauto.
    eapply find_funct_in2; eauto.
  generalize H0 H1; intros B B1.
  apply locenv_setvars_exists with (l1:=mkloopid (fbyeqof (nd_stmt f))) (eh2:=ta) in H0; auto.
  destruct H0 as [ta1 [A2 A3]].
  eapply trans_body_ids_norepet in H1; eauto.
  unfold trans_body in *.
  destruct IHeval_node with nid (nid,f) ta1 (fbyeqof (nd_stmt f)) as [ta2 [A5 A6]]; auto.
    red; intros; auto.
  apply exec_node with ta ta1 ta2; simpl; auto.
  -eapply eval_Sseq with ta2 (mkenv eh1 se'); eauto.
   eapply eval_poststmt_match; eauto.
  -eapply locenv_match_getvars; eauto.
   red; intros. eapply locenv_matcht_some; eauto.
  -change f with (snd (nid, f)).
   apply eval_node_rets_cast with false prog1 gc (mkenv eh se) (mkenv eh3 se') vas; auto.
   econstructor 1; eauto.
  -apply find_funct_in2 in H6.
   apply ID_RANGE in H6; auto.
 +(*Sassign*)
  inv H2. destruct e as [eh se].
  eapply eval_eqf_trans with (eh:=eh) (ta:=ta) in H; eauto.
  destruct H as [te2' [? ?]].
  exists te2'. split; auto.
  constructor; auto.
 +(*Scall_node*)
  generalize H1; intros A.
  destruct A as [A [A1 A2]].
  eapply locenv_setvarfs_exists with (eh:=eh) in H6; eauto.
  destruct H6 as [ta' [B B1]].
  exists ta'. split; auto.
  apply eval_Scall with ef ef' (trans_node nd) (trans_node fd) vl vargs vargs' vrets i; auto.
  -inv H; constructor; auto.
   eapply Lenvmatch.eval_sexp_match; eauto.
   red; intros. eapply locenv_matcht_some; eauto.
   eapply locenv_matcht_disjoint; eauto.
  -simpl. subst nk. eapply trans_call_func; eauto.
  -eapply eval_sexps_match; eauto.
   eapply eval_sexps_sexps; eauto.
  -apply IHeval_node; auto. eapply find_funct_eq; eauto.
  -eapply locenv_getmvls_match; eauto.
  -eapply lvalue_list_norepet_matchm; eauto.
   eapply lvalue_list_norepet_trans_left; eauto.
  -red; intros. eapply assign_disjoint_match; eauto.
   eapply assign_disjoint_trans_left; eauto.
  -destruct H14. rewrite <-H6; auto.
   erewrite <-find_funct_fid with (fid:=callid cdef) (fd:=fd); eauto.
   apply ids_plt_le_notin with (id:=ACG_J) in GID_RANGE.
   red; intros. apply GID_RANGE. rewrite <-H18.
   apply in_or_app; right. apply in_map.
   eapply find_funct_in2; eauto.
   unfold Ple, ACG_J,ACG_EQU. omega.
 +(*Sfor_start*)
  destruct e as [eh se].
  eapply eval_eqf_trans in H; eauto.
  destruct H as [ta1 [? ?]].
  destruct IHeval_node with nid nd ta1 l as [ta' [? ?]]; simpl; auto.
  exists ta'. split; auto.
  eapply eval_Sfor_start; eauto.
 +(*Sfor_false*)
  exists ta. split; auto.
  destruct e as [eh se].
  eapply eval_Sfor_false; eauto.
  eapply eval_sexp_match; eauto.
  eapply eval_sexp_sexp; eauto.
 +(*Sfor_loop*)
  destruct IHeval_node with nid nd ta l as [ta1 [? ?]]; auto.
  destruct e as [eh se]. destruct e1 as [eh1 se1].
  eapply eval_eqf_trans in H1; eauto.
  destruct H1 as [ta2 [? ?]].
  destruct IHeval_node0 with nid nd ta2 l as [ta' [? ?]]; simpl; auto.
  exists ta'. split; auto.
  apply eval_Sfor_loop with ta1 ta2 eh1 eh1 se1; eauto.
  eapply eval_sexp_match; eauto.
  eapply eval_sexp_sexp; eauto.
 +(*Sskip*)
  exists ta. split; auto. constructor.
 +(*Sseq*)
  destruct IHeval_node with nid nd ta l as [ta1 [? ?]]; auto.
    red; intros. apply H2. apply in_or_app; auto.
  destruct IHeval_node0 with nid nd ta1 l as [ta' [? ?]]; auto.
    red; intros. apply H2. apply in_or_app; auto.
  exists ta'. split; auto.
  eapply eval_Sseq; eauto.
 +(*Sif*)
  destruct IHeval_node with nid nd ta l as [ta' [? ?]]; auto.
    red; intros. apply H3. destruct b; apply in_or_app; auto.
  exists ta'. split; auto.
  destruct e as [eh se].
  eapply eval_Sif; eauto.
  eapply eval_sexp_match; eauto.
  eapply eval_sexp_sexp; eauto.
  destruct b; auto.
 +(*Scase*)
  inv H1. destruct e as [eh se].
  eapply eval_eqf_trans with (eh:=eh) (ta:=ta) in H12; eauto.
  destruct H12 as [ta' [? ?]].
  exists ta'. split; auto.
  eapply eval_Scase; eauto.
  eapply eval_sexp_match; eauto.
  apply eval_sexp_sexp; eauto.
  apply eval_Sassign; auto.
 +(*Sfby_1*)
  eapply eval_eqf_trans with (eh:=eh) (ta:=ta) in H0; eauto.
  destruct H0 as [ta' [? ?]].
  exists ta'. split; auto.
  apply eval_Sif with Vtrue true; simpl; eauto.
  apply eval_var_svar; auto.
  apply eval_Sassign; auto.
 +(*Sfby_n*)
  assert(A: list_disjoint (get_lids lh) (id :: nil)).
    red; simpl; intros. destruct H10; auto. subst. congruence.
  generalize H3; intros A1.
  eapply locenv_matcht_setlvar_left_exists with (eh:=eh) in H3; eauto.
  destruct H3 as [ta' [? ?]].
  exists ta'. split; auto.
  apply eval_Sif with Vfalse false; simpl; eauto.
  apply eval_var_svar; auto.
  apply eval_Sassign; auto.
  constructor 1 with v1 v; auto.
  apply eval_var_svar; auto.
  eapply assign_disjoint_match; eauto.
  inv A1. apply lids_disjoint_assign_disjoint with v1 b ofs Lid; auto.
   apply eval_var_svar; auto.
   eapply eval_lvalue_lvalue; eauto.
 +(*Sfbyn_1*)
  assert(A: list_disjoint (get_lids lh) (id1 :: nil)).
    red; simpl; intros. destruct H16; auto. subst.
    red; intros. subst. apply H10. apply in_or_app; auto.
  assert(A1: mkloopid l = (ACG_J, type_int32s) :: nil).
    eapply mkloopid_in; eauto. eapply H12; simpl; eauto.
  rewrite A1 in *.
  destruct has_type_store_env_exists with ta (Vint i) type_int32s ACG_J as [ta1 A2]; simpl; auto.
    destruct H11 as [? [? ?]]; auto.
  assert(A3: locenv_matcht ((ACG_J, type_int32s) :: nil) te ta1).
    eapply store_env_locenv_matcht; eauto.
  generalize H9; intros A4.
  eapply locenv_matcht_setlvar_left_exists with (eh:=eh2) in A4; eauto.
  destruct A4 as [ta' [A4 ?]].
  exists ta'. split; auto.
  apply eval_Sseq with ta1 (mkenv eh2 se); auto.
  -apply eval_Sif with Vtrue true; simpl; eauto.
   apply eval_var_svar; auto.
   destruct has_type_store_env_exists with ta (Vint Int.zero) type_int32s ACG_J as [ta0 B]; simpl; auto.
   destruct H11 as [? [? ?]]; auto.
   apply eval_Sseq with ta1 (mkenv eh1 se).
   *apply eval_Sfor_start with ta0 eh; auto.
    apply eval_loop_init with te; auto.
    subst sa aty. eapply eval_fbyn_init_correct; eauto.
    congruence. red; intros. apply H10. apply in_or_app; auto.
   *constructor. subst. eapply eval_fbyn_index_init; eauto.
  -apply eval_Sassign; auto. constructor 1 with v1 v; auto.
   *rewrite <-H6, H7; auto. subst. eapply eval_aryacc_aryacc; eauto.
   *inv H9. apply lids_disjoint_assign_disjoint with v1 b ofs Lid; simpl; auto.
    rewrite <-H6, H7. eapply eval_aryacc_aryacc; eauto.
    eapply eval_lvalue_match; eauto.
    eapply eval_lvalue_lvalue; eauto.
 +(*Sfbyn_n*)
  assert(A: list_disjoint (get_lids lh) (id1 :: nil)).
    red; simpl; intros. destruct H13; auto. subst. congruence.
  generalize H6; intros A1.
  eapply locenv_matcht_setlvar_left_exists with (eh:=eh) in H6; eauto.
  destruct H6 as [ta' [? ?]].
  exists ta'. split; auto.
  apply eval_Sseq with ta (mkenv eh se); auto.
  -apply eval_Sif with Vfalse false; simpl; eauto.
   apply eval_var_svar; auto. constructor.
  -apply eval_Sassign; auto.
   constructor 1 with v1 v; auto.
   rewrite <-H3, H4. subst. eapply eval_aryacc_aryacc; eauto.
   inv A1. apply lids_disjoint_assign_disjoint with v1 b ofs Lid; simpl; auto.
   rewrite <-H3, H4. eapply eval_aryacc_aryacc; eauto.
   eapply eval_lvalue_match; eauto.
   eapply eval_lvalue_lvalue; eauto.
 +(*Sarrow*)
  eapply eval_eqf_trans with (eh:=eh) (ta:=ta) in H1; eauto.
  destruct H1 as [ta' [? ?]].
  exists ta'. split; auto.
  eapply eval_Sif; eauto.
  apply eval_var_svar; auto.
  destruct b; constructor; auto.
 +congruence.
Qed.

Lemma eval_init_correct:
  forall z svars eh1 vars,
  Lsem.eval_init z empty_locenv ((ACG_INIT,type_bool)::svars) eh1 ->
  (if lt_dec 0 z then vars = (ACG_INIT,type_bool)::svars else vars = nil) ->
  eval_init (length vars) empty_locenv vars eh1.
Proof.
  induction 1; simpl; intros.
  subst. constructor.
  rewrite H1. simpl.
  constructor 2 with eh1; auto.
Qed.

Lemma init_node_correct:
  forall e main,
  LsemR.init_node prog1 e main ->
  find_funct (node_block prog1) (fst main) = Some main ->
  LsemF.init_node false prog2 e (trans_node main).
Proof.
  induction 1 using LsemR.init_node_ind2 with
  ( P0 := fun nk e1 e2 l =>
      forall nid nd,
      (forall c, In c l -> cakind c = true) ->
      nk = nd_kind (snd nd) ->
      find_funct (node_block prog1) nid = Some nd ->
      LsemF.init_stmt false prog2 nid e1 e2 l
   ); intros.
 +(*init_node*)
  eapply trans_body_ids_norepet in H; eauto.
  unfold trans_body in *.
  apply init_node_ ; simpl; auto.
  -eapply eval_init_correct; eauto.
   rewrite fbyeqof_length.
   destruct (lt_dec 0 (length (fbyeqof (nd_stmt f)))); auto.
  -unfold svarsof. simpl. intros.
   rewrite map_app in *. apply in_app_or in H4. destruct H4.
   apply H1. apply in_or_app; auto.
   destruct (lt_dec _ _); try tauto.
   simpl in *. destruct H4; subst; simpl. omega.
   apply H1. apply in_or_app; auto.
  -rewrite mkpoststmt_instidof, <-app_nil_end.
   erewrite trans_stmt_instidof; eauto.
   apply IHinit_node with (nid,f); auto.
   rewrite <-trans_stmt_instidof; auto.
   apply instidof_cakind_true.
  -apply find_funct_in2 in H3.
   apply ID_RANGE in H3; auto.
 +(*nil*)
  constructor.
 +(*cons*)
  generalize H0; intros A. destruct A as [A [A1 A2]].
  constructor 2 with se1 (trans_node nd) (trans_node fd) ef; auto.
  -subst nk. eapply trans_call_func; eauto.
  -apply IHinit_node; auto.
   eapply find_funct_eq; eauto.
  -apply IHinit_node0 with nd; auto. intros. apply H4; simpl; auto.
Qed.

End NODE_CORRECT.

Lemma init_genvc_env_none:
  forall gc,
  init_genvc (const_block prog1) = Some gc ->
  gc ! ACG_J = None.
Proof.
  intros.
  eapply init_genvc_notin_none; eauto.
  apply ids_plt_le_notin with ACG_EQU; auto.
  unfold Ple, INSTRUCT,ACG_J, ACG_EQU; omega.
  red; intros. apply GID_RANGE.
  apply in_or_app; auto.
Qed.

Lemma initial_state_match:
  forall gc main e,
  Lenv.initial_state1 prog1 gc (fun p e fd => LsemR.init_node p e fd) main e ->
  exists main', Lenv.initial_state1 prog2 gc (fun p e fd => LsemF.init_node false p e fd) main' e
    /\ trans_node main = main'
    /\ gc ! ACG_J = None.
Proof.
  intros. generalize init_node_correct; intros.
  inv H. generalize H2; intros.
  eapply H0 in H4; eauto.
  exists (trans_node main). split; [| split]; auto. constructor 1; auto.
  +eapply trans_funcs_find; eauto.
  +apply init_genvc_env_none; auto.
  +eapply find_funct_eq; eauto.
Qed.

Lemma trans_program_general:
  forall gc main e maxn mass vrss,
  Lenv.exec_prog1 prog1 gc (LsemR.eval_node false) main e 1 maxn mass vrss ->
  find_funct (node_block prog1) (fst main) = Some main ->
  gc ! ACG_J = None ->
  Lenv.exec_prog1 prog2 gc (LsemF.eval_node false) (trans_node main) e 1 maxn mass vrss.
Proof.
  induction 1; intros.
  +constructor 1 with mrss; auto.
  +constructor 2 with e'; simpl; auto.
   eapply trans_node_all_correct; eauto.
Qed.

Lemma trans_program_correct:
  forall gc main e maxn mass vrss,
  Lenv.initial_state1 prog1 gc (fun p e fd => LsemR.init_node p e fd) main e ->
  Lenv.exec_prog1 prog1 gc (LsemR.eval_node false) main e 1 maxn mass vrss ->
  exists main', Lenv.initial_state1 prog2 gc (fun p e fd => LsemF.init_node false p e fd) main' e
    /\ Lenv.exec_prog1 prog2 gc (LsemF.eval_node false) main' e 1 maxn mass vrss
    /\ nd_rets (snd main') = nd_rets (snd main)
    /\ nd_kind (snd main') = nd_kind (snd main).
Proof.
  intros.
  destruct initial_state_match with gc main e as [? [? [? ?]]]; auto.
  exists x. subst x. intuition.
  eapply trans_program_general; eauto.
   inv H; try congruence.
   eapply find_funct_eq; eauto.
Qed.

End CORRECTNESS.
