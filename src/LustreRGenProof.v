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
Require Import Inclusion.
Require Import List.
Require Import ExtraList.
Require Import Ctypes.
Require Import Cltypes.
Require Import Cop.
Require Import Lident.
Require Import Ltypes.
Require Import Lop.
Require Import Lint.
Require Import Lustre.
Require Import LustreS.
Require Import LustreR.
Require Import Lint.
Require Import Lvalues.
Require Import Lenv.
Require Import LsemT.
Require Import Lsem.
Require Import Lenvmatch.
Require Import LsemS.
Require Import LsemR.
Require Import LustreRGen.
Require Import Permutation.

Section CORRECTNESS.

Variable progS: LustreS.program.
Variable progR: program.

Hypothesis TRANS:
  trans_program progS = OK progR.

Hypothesis ID_RANGE:
  LustreS.ids_range ACG_B (node_block progS).

Lemma eval_sexp_lvalue_assign_disjoint:
  forall gc eh a v s b o,
  eval_sexp gc eh a v ->
  eval_lvalue gc eh s b o Lid ->
  ~ In b (get_lids a) ->
  assign_disjoint (eval_lvalue gc eh) s a.
Proof.
  intros.
  destruct has_type_access_mode with v (typeof a) as [[chunk ?] | ?]; auto.
  +eapply eval_sexp_has_type; eauto.
  +constructor 1 with chunk; auto.
  +destruct has_type_access_mode_mvl with v (typeof a) as [mv [? ?]]; auto.
   eapply eval_sexp_has_type; eauto. subst.
   destruct eval_sexp_exists_lvalue with gc eh a mv as [id1 [o1 [k ?]]]; auto.
   constructor 2; auto.
   constructor 1 with b id1 o o1 Lid k; auto.
   left. red. intros. subst. apply H1; simpl; auto.
   erewrite eval_lvalue_get_lids; simpl; eauto.
Qed.

Lemma eval_sassign:
  forall gc nk te te1 e e1 lh a,
  LsemS.eval_stmt progS gc nk te e te1 e1 (LustreS.Sassign lh (Expr a)) ->
  eval_stmt true progR gc nk te e te1 e1 (Sassign (lvarof lh) a).
Proof.
  intros. inv H. inv H2. destruct e1 as [eh se].
  apply eval_Sassign; auto.
  constructor 1 with v v'; auto.
  inv H10.
  apply eval_sexp_lvalue_assign_disjoint with v b ofs; auto.
  inv H. auto.
Qed.

Lemma trans_finit_correct:
  forall s gc nk te e te1 e1,
  eval_stmts progS gc nk te e te1 e1 (initstmtsof2 s) ->
  eval_stmt true progR gc nk te e te1 e1 (trans_finit s).
Proof.
  intros.
  destruct s; simpl in *; try (inv H; constructor; fail).
  +inv H. inv H8. apply eval_sassign in H7; auto.
  +inv H. inv H8. apply eval_sassign; auto.
  +inv H. inv H8. apply eval_sassign; auto.
  +inv H. inv H8. apply eval_sassign; auto.
  +inv H. inv H8. apply eval_sassign; auto.
Qed.

Lemma find_funct_trans_exists:
  forall fid fdS, find_funct (node_block progS) fid = Some fdS ->
  exists fdR, trans_node fdS = OK fdR
   /\ find_funct (node_block progR) fid = Some fdR.
Proof.
  intros. monadInv TRANS. simpl.
  eapply find_funcs_monad_exits; eauto.
  intros. monadInv H0; auto.
Qed.

Lemma call_func_exists:
  forall cdef fdS,
  call_func (node_block progS) cdef fdS ->
  exists fdR, trans_node fdS = OK fdR
    /\ call_func (node_block progR) cdef fdR.
Proof.
  intros. destruct H as [? [? [? ?]]].
  destruct find_funct_trans_exists with (callid cdef) fdS as [fdR [? ?]]; auto.
  exists fdR. split; [| split]; auto.
  monadInv H3. monadInv EQ.
  repeat (split; auto).
Qed.

Lemma eval_map_args:
  forall gc e args vl,
  eval_sexps gc e args vl ->
  forall i vas tys al,
  locenv_getarys i (map typeof args) tys vl vas ->
  mmap trans_expr_proj args = OK al ->
  eval_sexp gc e (Svar ACG_I type_int32s) (Vint i) ->
  eval_sexps gc e al vas.
Proof.
  induction 1; simpl; intros; auto.
  +inv H0. inv H. constructor.
  +monadInv H2. inv H1. constructor.
   -monadInv EQ. rewrite <-H2 in EQ0. inv EQ0.
    eapply eval_sexp_aryacc; eauto.
    rewrite Z.max_r; try omega.
   -eapply IHForall2; eauto.
Qed.

Lemma set_map_rets:
  forall gc eh l tys vrs eh1,
  locenv_setarys gc (Svar ACG_I type_int32s) eh l tys vrs eh1 ->
  forall lvs, mmap trans_var_pary l = OK lvs ->
  locenv_setlvars gc eh lvs vrs eh1.
Proof.
  induction 1; simpl; intros; auto.
  +inv H. constructor.
  +monadInv H1. unfold lvarof. simpl.
   constructor 2 with e1; auto.
Qed.

Lemma setvars_lvars:
  forall eh lhs vrets eh' gc,
  locenv_setvars eh lhs vrets eh' ->
  locenv_setlvars gc eh (map lvarof lhs) vrets eh'.
Proof.
  induction 1; simpl; intros.
  constructor.
  unfold lvarof. simpl. constructor 2 with e1; auto.
  econstructor; eauto. constructor 1 with m; auto.
Qed.

Lemma eval_lindexs_disjoint:
  forall lis gc eh t ty z z',
  eval_lindexs gc eh t ty lis z z' ->
  forall id m, ~ In id (get_lindexids lis) ->
  eval_lindexs gc (PTree.set id m eh) t ty lis z z'.
Proof.
  induction lis; simpl; intros; inv H.
  constructor.
  constructor 2 with delta ty0; auto.
  eapply IHlis; eauto.
  apply not_in_app in H0. destruct H0; auto.
  apply not_in_app in H0. destruct H0; auto.
  constructor 3 with i; auto.
  eapply eval_sexp_setnew; eauto.
Qed.

Lemma ary_prj_size:
  forall t v i ty,
  ary_prj t v = OK (Some i, ty) ->
  Int.unsigned i + sizeof ty <= sizeof t.
Proof.
  destruct t, v; intros; inv H.
  destruct (zlt 0 (sizeof t)), (zlt 0 z); inv H1.
  destruct (negb _) eqn:?, (Int.lt _ (Int.repr z)) eqn:?; inv H0.
  apply array_ofs_add_le; auto.
  unfold Int.lt in *.
  destruct (zlt (Int.signed i0) (Int.signed Int.zero)); inv Heqb.
  destruct (zlt (Int.signed i0) (Int.signed (Int.repr z))); inv Heqb0.
  generalize Int.modulus_pos (sizeof_pos ty) (Int.unsigned_range i0); intros.
  rewrite Int.signed_zero in g. unfold Int.signed in g.
  destruct (zlt (Int.unsigned i0) Int.half_modulus); try omega.
  rewrite <-Int.signed_eq_unsigned.
  apply Zlt_le_trans with (Int.signed (Int.repr z)); try omega.
  rewrite Z.max_r; try omega.
  apply int_signed_repr_le; auto. omega.
  unfold Int.max_signed. omega.
Qed.

Lemma ary_prjs_size:
  forall vl t v i ty,
  ary_prjs t v vl = OK (Some i, ty) ->
  Int.unsigned i + sizeof ty <= sizeof t.
Proof.
  induction vl; simpl; intros; auto.
  apply ary_prj_size with v; auto.
  monadInv H. destruct x; destruct x1; inv EQ2.
  apply IHvl in EQ1. apply ary_prj_size in EQ.
  apply Zle_trans with (Int.unsigned i0 + sizeof x0); auto.
  apply Zle_trans with (Int.unsigned i0 + (Int.unsigned i1 + sizeof ty)); try omega.
  rewrite <-Zplus_assoc_reverse. apply Zplus_le_compat_r.
  apply int_add_le.
Qed.

Lemma cons_aryprj_typeof_eq:
  forall a ai c e vi oi ty,
  cons_aryprj a ai = OK (c, e) ->
  ary_prj (typeof a) vi = OK (oi, ty) ->
  ty = typeof e.
Proof.
  intros. monadInv H. simpl. destruct (typeof a); monadInv EQ.
  destruct vi; inv H0. destruct ((zlt _ _) && _); inv H1.
  destruct (_ && _); inv H0; auto.
Qed.

Lemma cons_aryprjs_typeof_eq:
  forall ids vl a ai c e vi oi ty,
  cons_aryprjs ids a ai = OK (c, e) ->
  length ids = length vl ->
  ary_prjs (typeof a) vi vl = OK (oi, ty) ->
  ty = typeof e.
Proof.
  induction ids; destruct vl; simpl; intros; monadInv H; inv H0.
  +simpl. destruct (typeof a); monadInv EQ. destruct vi; inv H1.
   destruct (zlt _ _ && _); inv H0.
   destruct (_ && _); inv H1; auto.
  +monadInv H1.
   eapply cons_aryprj_typeof_eq in EQ; eauto. subst x3.
   destruct x2, x4; inv EQ4; eauto.
Qed.

Lemma cons_aryprj_true_false:
  forall a vi oi ty ai c a1 gc e,
  cons_aryprj a ai = OK (c, a1) ->
  ary_prj (typeof a) vi = OK (oi, ty) ->
  typeof ai = type_int32s ->
  eval_sexp gc e ai vi ->
  match oi with
  | Some ofs => eval_sexp gc e c Vtrue
  | None => eval_sexp gc e c Vfalse
  end.
Proof.
  intros. monadInv H.
  destruct (typeof a); monadInv EQ.
  destruct vi; inv H0. destruct (zlt 0 (sizeof x)), (zlt 0 x0); inv H3.
  destruct (_ && _) eqn:?; inv H0.
  +apply andb_prop in Heqb; destruct Heqb.
   apply eval_Sbinop with Vtrue Vtrue; simpl; auto.
   -apply eval_Sbinop with (Vint Int.zero) (Vint i0); simpl; auto.
    constructor; simpl; auto. rewrite H. auto.
   -apply eval_Sbinop with (Vint i0) (Vint (Int.repr x0)); simpl; auto.
    constructor; simpl; auto. rewrite H1; simpl; auto. rewrite H0; auto.
  +apply andb_false_iff in Heqb; destruct Heqb.
   -econstructor; simpl; auto.
    *apply eval_Sbinop with (Vint Int.zero) (Vint i0); simpl; auto.
     constructor; simpl; auto.
     rewrite H. simpl. auto.
    *apply eval_Sbinop with (Vint i0) (Vint (Int.repr x0)); simpl; auto.
     constructor; simpl; auto. rewrite H1; simpl; auto.
     unfold of_bool. destruct (Int.lt i0 (Int.repr x0)); simpl; auto.
    *rewrite H. simpl. destruct (Int.lt i0 (Int.repr x0)); auto.
   -econstructor; simpl; auto.
    *apply eval_Sbinop with (Vint Int.zero) (Vint i0); simpl; auto.
     constructor; simpl; auto.
     unfold of_bool. destruct (Int.lt i0 Int.zero); simpl; auto.
    *apply eval_Sbinop with (Vint i0) (Vint (Int.repr x0)); simpl; auto.
     constructor; simpl; auto. rewrite H1; simpl; auto.
     rewrite H; simpl; auto.
    *rewrite H. simpl. destruct (negb (Int.lt i0 Int.zero)); auto.
Qed.

Lemma cons_aryprjs_true_false:
  forall l vl a vi oi ty ai c a1 gc e,
  ary_prjs (typeof a) vi vl = OK (oi, ty) ->
  eval_sexps gc e l vl ->
  eval_sexp gc e ai vi ->
  cons_aryprjs l a ai = OK (c, a1) ->
  (forall t, In t (map typeof (ai::l)) -> t = type_int32s) ->
  match oi with
  | Some ofs => eval_sexp gc e c Vtrue
  | None => eval_sexp gc e c Vfalse
  end.
Proof.
  induction l; destruct vl; intros; inv H0.
  +simpl in *. eapply cons_aryprj_true_false; eauto.
  +monadInv H2. simpl in *. monadInv H.
   assert (x3 = typeof x0).
    eapply cons_aryprj_typeof_eq; eauto.
   subst x3.
   assert (typeof x = type_bool /\ typeof x1 = type_bool).
    split. monadInv EQ. auto. eapply cons_aryprjs_typeof_bool; eauto.
   destruct H.
   eapply cons_aryprj_true_false in EQ0; eauto.
   eapply IHl in EQ1; eauto.
   destruct x2,x4; inv EQ4; simpl in *;
   econstructor; eauto; try rewrite H; try rewrite H0; simpl; auto.
Qed.

Lemma cons_aryproj_correct:
  forall gc e a m ai vi a1 a2 ofs ty v,
  eval_sexp gc e a (Vmvl m) ->
  eval_sexp gc e ai vi ->
  cons_aryprj a ai = OK (a1, a2) ->
  load_mvl ty m ofs v ->
  typeof ai = type_int32s ->
  ary_prj (typeof a) vi = OK (Some ofs, ty) ->
  has_type v ty ->
  eval_sexp gc e a1 (Vint Int.one) /\ eval_sexp gc e a2 v.
Proof.
  intros. monadInv H1. remember (typeof a).
  destruct t; monadInv EQ. destruct vi; inv H4.
  destruct (zlt 0 (sizeof x)),(zlt 0 x0); inv H6.
  destruct (negb _) eqn:?; destruct (Int.lt _ (Int.repr x0)) eqn:?; inv H4.
  split.
  apply eval_Sbinop with (Vint Int.one) (Vint Int.one); simpl; auto.
  apply eval_Sbinop with (Vint Int.zero) (Vint i0); simpl; auto.
  constructor; simpl; auto. rewrite Heqb. auto.
  apply eval_Sbinop with (Vint i0) (Vint (Int.repr x0)); simpl; auto.
  constructor; simpl; auto. rewrite H3. simpl. rewrite Heqb0; auto.
  eapply eval_sexp_aryacc; eauto.
  generalize (Int.unsigned_range i0). intros.
  destruct (Int.lt i0 Int.zero) eqn:?; simpl in *; try congruence.
  unfold Int.lt in *. rewrite Int.signed_zero in *.
  destruct (zlt _ 0); try congruence.
  destruct (zlt _ _); try congruence.
  split. omega.
  apply Zlt_le_trans with (Int.signed (Int.repr x0)); auto.
  cut (Int.unsigned (Int.repr x0) <= x0). intros.
  rewrite Z.max_r; try omega.
  unfold Int.signed. destruct (zlt _ _); try omega.
  apply int_repr_le. omega.
Qed.

Lemma ary_prj_alignof:
  forall v t i ty,
  ary_prj t v = OK (Some i, ty) ->
  (alignof ty | Int.unsigned i) /\ (alignof ty | alignof t).
Proof.
  intros. destruct t, v; simpl in *; try monadInv H.
  destruct (zlt _ _ && _); try congruence.
  destruct (_ && _); inv H. split.
  apply alignof_array_ofs; auto.
  exists 1; omega.
Qed.

Lemma ary_prjs_alignof:
  forall l v t i ty,
  ary_prjs t v l = OK (Some i, ty) ->
  (alignof ty | Int.unsigned i) /\ (alignof ty | alignof t).
Proof.
  induction l; simpl; intros.
  eapply ary_prj_alignof; eauto.
  monadInv H. destruct x,x1; inv EQ2.
  destruct IHl with a x0 i1 ty; auto.
  destruct ary_prj_alignof with v t i0 x0; auto. split.
  +apply Zdivides_plus_int; eauto.
   apply alignof_1248.
   apply Zdivides_trans with (alignof x0); auto.
  +apply Zdivides_trans with (alignof x0); auto.
Qed.

Lemma has_type_mvl:
  forall m ty,
  access_mode ty = By_copy \/ access_mode ty = By_reference ->
  mvl_type true m ty ->
  has_type (Vmvl m) ty.
Proof.
  destruct ty; simpl; intros; destruct H; try inv H; auto.
  +destruct i; destruct s; inv H2.
  +destruct i; destruct s; inv H2.
  +destruct f; inv H2.
  +destruct f; inv H2.
Qed.

Lemma mvl_type_array_getN:
  forall n i o m t,
  mvl_array true (getN (nat_of_Z (sizeof t) * n) o m) t n ->
  (i < n)%nat ->
  (o + (nat_of_Z (sizeof t) * n) <= length m)%nat ->
  mvl_type true (getN (nat_of_Z (sizeof t)) (o + (nat_of_Z (sizeof t)) * i) m) t.
Proof.
  induction n; intros; try omega.
  change (S n) with (1 + n)%nat in *.
  rewrite mult_plus_distr_l, mult_1_r in H.
  repeat rewrite getN_add in H. inv H.
  generalize H4 H6; intros A A1.
  apply mvl_type_length in A. apply mvl_type_length in A1.
  cut (length m0 = length (getN (nat_of_Z (sizeof t)) o m)). intros A4.
  apply app_length_equal_inv in H2.
  destruct H2. subst.
  destruct n.
  +destruct i; try omega.
   rewrite mult_0_r, plus_0_r in *; auto.
  +destruct i.
   -rewrite mult_0_r, plus_0_r in *; auto.
   -change (S i) with (1 + i)%nat.
    rewrite mult_plus_distr_l, mult_1_r, plus_assoc in *.
    apply IHn; auto. omega.
  +left. congruence.
  +rewrite <-nat_of_Z_of_nat with o.
   rewrite <-getN_length; try omega. rewrite <-A.
   rewrite nat_of_Z_of_nat; auto.
   generalize (sizeof_pos t); intros.
   rewrite mult_plus_distr_l, mult_1_r in H1.
   apply Nat2Z.inj_le in H1.
   repeat rewrite Nat2Z.inj_add in H1.
   rewrite nat_of_Z_eq in H1; try omega.
Qed.

Lemma load_mvl_has_type:
  forall t m i v,
  load_mvl t m (array_ofs i t) v ->
  forall z, mvl_array true m t (nat_of_Z z) ->
  0 <= Int.signed i < z ->
  has_type v t.
Proof.
  induction 1; intros.
  +eapply load_chunk_has_type; eauto.
  +eapply has_type_mvl; eauto.
   unfold loadbytes in *. destruct (range_perm_dec _ _ _); inv H0.
   generalize (Int.signed_range i) (sizeof_pos t) Int.max_signed_unsigned. intros.
   unfold array_ofs. rewrite Int.mul_signed.
   generalize H2. intros. apply mvl_type_length in H6.
   rewrite nat_of_Z_eq in H6; try omega.
   cut (sizeof t * z <= Int.max_signed). intros A.
   rewrite Int.signed_repr. rewrite Int.unsigned_repr.
   rewrite Z2Nat.inj_mul in *; try omega.
   replace (Z.to_nat (sizeof t) * Z.to_nat (Int.signed i))%nat with (0 + Z.to_nat (sizeof t) * Z.to_nat (Int.signed i))%nat by omega.
   apply mvl_type_array_getN with (Z.to_nat z).
   -change nat_of_Z with Z.to_nat.
    rewrite <-Z2Nat.inj_mul; try omega.
    rewrite <-H6. rewrite nat_of_Z_of_nat.
    rewrite getN_full. auto.
   -apply Z2Nat.inj_lt; try omega.
   -change nat_of_Z with Z.to_nat.
    rewrite <-Z2Nat.inj_mul; try omega.
    rewrite <-H6. rewrite nat_of_Z_of_nat. omega.
   -split. apply Zmult_le_0_compat; try omega.
    generalize Int.max_signed_unsigned. intros.
    apply Zle_trans with (sizeof t * z); try omega.
    apply Zmult_le_compat_l; try omega.
   -split. unfold Int.min_signed. simpl. omega.
    apply Zle_trans with (sizeof t * z); try omega.
    apply Zle_trans with (sizeof t * 1); try omega.
    apply Zmult_le_compat_l; try omega.
   -red in r. omega.
Qed.

Lemma load_mvl_ary_prj_has_type:
  forall t m i v vi,
  load_mvl t m i v ->
  forall ty, has_type (Vmvl m) ty ->
  ary_prj ty vi = OK (Some i, t) ->
  has_type v t.
Proof.
  intros. unfold ary_prj in H1.
  destruct ty; try congruence.
  destruct vi; try congruence.
  destruct (zlt _ (sizeof ty)),(zlt _ _); simpl in *; try congruence.
  destruct (Int.lt i1 Int.zero) eqn:?;
  destruct (Int.lt i1 (Int.repr z)) eqn:?; simpl in *; inv H1.
  unfold Int.lt in *. rewrite Int.signed_zero in Heqb.
  destruct (zlt _ 0); try congruence.
  destruct (zlt _ ); try congruence.
  inv H0; simpl in *; try congruence.
  eapply load_mvl_has_type; eauto.
  rewrite Z.max_r in *; try omega.
  split; try omega.
  apply signed_repr_lt_inv; try omega; auto.
Qed.

Lemma cons_aryprojs_correct:
  forall ids gc e a m vi vl a1 a2 ai ofs ty v,
  eval_sexp gc e a (Vmvl m) ->
  eval_sexp gc e ai vi ->
  eval_sexps gc e ids vl ->
  ary_prjs (typeof a) vi vl = OK (Some ofs, ty) ->
  cons_aryprjs ids a ai = OK (a1, a2) ->
  load_mvl ty m ofs v ->
  (forall t : type, In t (map typeof (ai :: ids)) -> t = type_int32s) ->
  eval_sexp gc e a1 (Vint Int.one)
    /\ eval_sexp gc e a2 v.
Proof.
  induction ids; simpl; intros.

  inv H1. inv H2.
  eapply cons_aryproj_correct; eauto.
  apply eval_sexp_has_type in H.

  eapply load_mvl_ary_prj_has_type; eauto.

  monadInv H3. inv H1. simpl in *. monadInv H2.
  destruct x2; destruct x4; inv EQ4.
  assert (A: exists j, vi = Vint j /\ typeof x0 = x3 /\ i = array_ofs j x3).
    monadInv EQ. destruct (typeof a0); inv EQ2.
    simpl in *. destruct vi; inv EQ0. destruct (zlt _ (sizeof _)),(zlt 0 x4); inv H2.
    destruct (negb (Int.lt i2 Int.zero) && Int.lt i2 (Int.repr x4)); inv H3; eauto.
  destruct A as [j [? [? A]]]. subst vi x3.
  assert (A2: exists aid t num, typeof x0 = Tarray aid t num).
    destruct ids; inv EQ1; monadInv H2.
    destruct (typeof x0); monadInv EQ1; eauto.
    monadInv EQ1. destruct (typeof x0); monadInv EQ2; eauto.
  destruct A2 as [aid [t [num A2]]].
  assert(A3: 0 < sizeof (typeof x0)).
    simpl. destruct (typeof a0); inv EQ0.
    destruct (zlt _ (sizeof t0)), (zlt 0 z); simpl in *; try congruence.
    destruct (_ && _); inv H2. auto.
  assert (A4: exists m1, loadbytes m (Int.unsigned i) (sizeof (typeof x0)) = Some m1).
    apply range_perm_loadbytes.
    apply load_mvl_range_perm in H4.
    apply ary_prj_size in EQ0.
    generalize (Int.unsigned_range i); intros.
    unfold range_perm in *. intuition.
    apply Zle_trans with (sizeof (typeof a0)); try omega.
    erewrite eval_sexp_size; eauto. omega.
  destruct A4 as [m1 A4].
  assert (B: (alignof (Tarray aid t num) | Int.unsigned i)).
    subst. rewrite A2. apply alignof_array_ofs.
  assert (A5: load_mvl (typeof x0) m i (Vmvl m1)).
    rewrite A2 in *. constructor 2; auto.
  destruct cons_aryproj_correct with gc e a0 m ai (Vint j) x x0 i (typeof x0) (Vmvl m1); auto.
    apply eval_sexp_has_type in H.
    eapply load_mvl_ary_prj_has_type; eauto.
  assert (A6: load_mvl ty m1 i0 v).
    eapply loadbytes_load_mvl; eauto.
    eapply ary_prjs_size; eauto.
    apply load_mvl_div_alignof in H4.
    rewrite Int.add_commut in H4.
    apply Zdivides_plus_int_inv with i0; auto.
    apply alignof_1248.
    eapply ary_prjs_alignof; eauto.
  destruct IHids with gc e x0 m1 y l' x1 a2 a i0 ty v; auto.
  split; auto. apply eval_Sbinop with (Vint Int.one) (Vint Int.one); simpl; auto.
  monadInv EQ. apply cons_aryprjs_typeof_bool in EQ1. rewrite EQ1; auto.
  monadInv EQ. simpl. auto.
Qed.

Lemma cons_prefix_correct:
  forall gc e al vl,
  eval_sexps gc e al vl ->
  forall a v ty v1 op,
  eval_sexp gc e a v ->
  (forall t, In t (map typeof (a::al)) -> t = ty) ->
  sem_fold_operation op ty v vl = Some v1 ->
  has_type v1 ty ->
  eval_sexp gc e (cons_prefix al a op ty) v1.
Proof.
  induction 1; simpl; intros; auto.
  inv H1; auto.

  destruct (sem_binary_operation _ _ _ _ _) eqn:?; try congruence.
  apply IHForall2 with v0; auto.
  apply eval_Sbinop with v y; simpl; auto.
  rewrite H2; auto.
  cut (typeof a = ty); intros; auto.
  rewrite H5. auto.
  eapply sem_fold_operation_has_type; eauto.
  simpl. intros. destruct H5; auto.
Qed.

Lemma cons_aryprjs_get_expids_incl:
  forall is a s x x0 b,
  cons_aryprjs is a s = OK (x, x0) ->
  In b (get_lids x0) ->
  In b (get_lids a).
Proof.
  induction is; simpl; intros.
  +monadInv H. auto.
  +monadInv H. monadInv EQ.
   eapply IHis in EQ1; eauto; simpl in *.
Qed.

Lemma lids_disjoint_assign_lidst_disjoint:
  forall gc eh lh vl args vargs,
  locenv_getmvls gc eh lh vl ->
  eval_sexps gc eh args vargs ->
  list_disjoint (flat_map get_lids lh) (flat_map get_lids (arystr_sexps args)) ->
  assign_list_disjoint (eval_lvalue gc eh) lh args.
Proof.
  intros. red. intros.
  apply in_split in H2. destruct H2 as [? [? ?]]. subst.
  apply in_split in H3. destruct H3 as [? [? ?]]. subst.
  apply Forall2_app_inv_l in H0. destruct H0 as [? [? [? [? ?]]]]. subst.
  apply Forall2_app_inv_l in H.
  destruct H as [? [? [? [? ?]]]]. subst.
  inv H3. inv H2. unfold arystr_sexps in *.
  rewrite filter_app, flat_map_app, flat_map_app in *.
  simpl in *. inv H6.
  erewrite eval_lvalue_get_lids in H1; eauto. simpl in *.
  destruct (is_arystr (typeof a2)) eqn:?.
  +apply eval_sexp_lvalue_assign_disjoint with y0 id ofs; eauto.
   red; intros. red in H1. red in H1.
    apply H1 with id id; eauto.
    apply in_or_app; simpl; auto.
    apply in_or_app. simpl. right. apply in_or_app; auto.
  +destruct is_arystr_by_value with y0 (typeof a2) as [chunk ?]; auto.
   eapply eval_sexp_has_type; eauto.
   constructor 1 with chunk; auto.
Qed.

Lemma eval_typecmp_assign_list_disjoint:
  forall gc eh eh' a a1 a2 b v,
  eval_typecmp gc (type_block progS) eh a1 a2 b ->
  locenv_setlvar gc eh a v eh' ->
  list_disjoint (get_lids a) (get_lids a1 ++ get_lids a2) ->
  assign_list_disjoint (eval_lvalue gc eh) (a::nil) (a1 :: a2 :: nil).
Proof.
  intros.
  eapply locenv_setlvar_getmvl_exists in H0; eauto.
  destruct H0 as [mv ?].
  inv H.
  +constructor 1 with chunk; auto. simpl in *.
   destruct H6 as [ | [ | ]]; try congruence. tauto.
  +apply lids_disjoint_assign_lidst_disjoint with (mv::nil) (v1::v2::nil); auto.
   -constructor 2; auto.
   -constructor 2; auto.
   -simpl. rewrite <-H2, H3. simpl.
    repeat rewrite <-app_nil_end; auto.
  +apply lids_disjoint_assign_lidst_disjoint with (mv::nil) (v1::v2::nil); auto.
   -constructor 2; auto.
   -constructor 2; auto.
   -simpl. rewrite <-H2, H3. simpl.
    repeat rewrite <-app_nil_end; auto.
Qed.

Lemma store_mvl_set_bool:
  forall t m ofs (b: bool) m',
  store_mvl t m ofs (if negb b then Vtrue else Vfalse) m' ->
  exists m1, store_mvl t m ofs (if b then Vtrue else Vfalse) m1.
Proof.
  intros.  inv H.
  +exists (setN (encode_val chunk (if b then Vtrue else Vfalse))
            (nat_of_Z (Int.unsigned ofs)) m).
   constructor 1 with chunk; auto.
   unfold store in *.
   destruct (valid_access_dec _ _ _) eqn:?; inv H1; auto.
  +destruct b; inv H0.
Qed.

Lemma locenv_setlvar_trans_exists:
  forall gc te a (b: bool) te1,
  locenv_setlvar gc te a (if negb b then Vtrue else Vfalse) te1 ->
  lid_disjoint a ->
  exists te0, locenv_setlvar gc te a (if b then Vtrue else Vfalse) te0
    /\ locenv_setlvar gc te0 a (if negb b then Vtrue else Vfalse) te1.
Proof.
  intros. inv H. inv H2.
  generalize H4; intros A.
  apply store_mvl_set_bool in A.
  destruct A as [m1 A].
  rewrite <-ptree_set_repeat with (v1:=(m1,t)).
  exists (PTree.set b0 (m1, t) te). split.
  +constructor 1 with b0 ofs; auto.
   constructor 1 with m; auto.
  +constructor 1 with b0 ofs; auto.
   -eapply eval_lvalue_setsame; eauto.
   -constructor 1 with m1; auto.
    rewrite PTree.gss; auto.
    eapply store_mvl_length in A. congruence.
    simpl. eapply store_mvl_trans; eauto.
Qed.

Lemma locenv_setbool_eval_sexp:
  forall gc eh id (b: bool) eh1,
  locenv_setlvar gc eh (Svar id type_bool) (if b then Vtrue else Vfalse) eh1 ->
  eval_sexp gc eh1 (Svar id type_bool) (if b then Vtrue else Vfalse).
Proof.
  intros. inv H.
  apply eval_Rlvalue with b0 ofs Lid; auto.
  +inv H1. inv H0.
   constructor 1 with m'; auto.
   rewrite PTree.gss. congruence.
  +constructor 2. inv H0. simpl.
   eapply store_env_load_bool_eq; eauto.
   destruct b; auto.
  +destruct b; simpl; auto.
Qed.

Lemma trans_expr_correct:
  forall a gc nk te te' e lh v v' s,
  eval_expr gc (type_block progS) te a (snd lh) v ->
  eval_cast v (snd lh) v' ->
  locenv_setlvar gc te (lvarof lh) v' te' ->
  trans_expr lh a = OK s ->
  ~ In (fst lh) (lids_of_e a) ->
  eval_stmt true progR gc nk te e te' e s.
Proof.
  intros; inv H; destruct lh.
  +monadInv H2. econstructor; eauto.
   econstructor; eauto. simpl in *. subst.
   inv H1. eapply eval_sexp_lvalue_assign_disjoint; eauto.
   inv H; auto.
  +(*eval_Saryprj_in*)
   simpl in *. destruct is; monadInv H2. inv H5.
   assert(eval_sexp gc te x Vtrue
           /\ eval_sexp gc te x0 v).
     eapply cons_aryprojs_correct; eauto.
   destruct H.
   apply eval_Sif with Vtrue true; simpl; auto.
   erewrite cons_aryprjs_typeof_bool; eauto.
   -apply eval_Sassign; eauto. econstructor; eauto.
    simpl. eapply cons_aryprjs_typeof_eq; eauto.
    eapply Forall2_length; eauto.
    inv H1. eapply eval_sexp_lvalue_assign_disjoint; eauto.
    inv H5. red; intros. apply H3. apply in_or_app. left.
    eapply cons_aryprjs_get_expids_incl; eauto.
  +(*eval_Saryprj_out*)
   simpl in *. destruct is; monadInv H2. inv H4.
   eapply eval_Sif with Vfalse false; simpl; eauto.
   eapply cons_aryprjs_true_false in EQ; eauto; simpl in *; auto.
   erewrite cons_aryprjs_typeof_bool; eauto.
   apply eval_Sassign; eauto.
   econstructor; eauto.
   inv H1. eapply eval_sexp_lvalue_assign_disjoint; eauto.
   inv H. red; intros. apply H3. apply in_or_app; auto.
  +(*eval_Scase*)
   monadInv H2. eapply eval_Scase; eauto.
   econstructor; eauto. econstructor; eauto.
   simpl in *. subst.
   inv H1. eapply eval_sexp_lvalue_assign_disjoint; eauto.
   inv H. red; intros. apply H3.
   apply in_flat_map; auto. apply select_case_in in H5.
   eapply in_map_iff in H5; eauto. destruct H5 as [? [? ?]].
   exists x. subst. split; auto.
  +(*eval_Sif*)
   simpl in *. inv H2.
   eapply eval_Sif with v0 b; eauto.
   rewrite H5; auto.
   simpl; auto.
   destruct b; eapply eval_Sassign; econstructor; eauto.
   -inv H1. eapply eval_sexp_lvalue_assign_disjoint; eauto.
    inv H. red; intros; simpl. apply H3. apply in_or_app; auto.
   -rewrite H7 in *. inv H1.
    eapply eval_sexp_lvalue_assign_disjoint; eauto.
    inv H. red; intros; simpl. apply H3. apply in_or_app; auto.
  +(*prefix*)
   inv H4. simpl in *. destruct l; monadInv H2. inv H11.
   eapply eval_Sassign; eauto. econstructor; eauto.
   -inv H6.
    destruct (sem_binary_operation _ _ _ _ _) eqn:?; try congruence.
    eapply cons_prefix_correct; eauto.
    *eapply eval_Sbinop; simpl; eauto. rewrite H5; auto.
     right. simpl; auto. rewrite H5 with (typeof x); auto.
     eapply sem_fold_operation_has_type; eauto.
    *simpl. intros. destruct H; eauto. apply H5; simpl; auto.
   -simpl. rewrite cons_prefix_typeof; auto.
   -apply sem_fold_operation_by_value in H6; auto.
    destruct H6 as [chunk ?]. constructor 1 with chunk; auto.
    rewrite cons_prefix_typeof; auto.
  +(*typecmp*)
   simpl in *.
   destruct (identeq _ _) eqn:?; inv H2.
   apply Pos.eqb_neq in Heqb0.
   cut (v' = if if k then b else negb b then Vtrue else Vfalse). intros.
   subst. destruct k.
   -apply eval_Stypecmp with b; simpl; auto.
    *monadInv TRANS. simpl in *; auto.
    *eapply eval_typecmp_assign_list_disjoint; eauto.
     red; simpl; intros. destruct H; try tauto. red; intros; subst. auto.
   -eapply locenv_setlvar_trans_exists in H1; simpl; eauto.
    destruct H1 as [te0 [? ?]].
    apply eval_Sseq with te0 e; auto.
    *apply eval_Stypecmp with b; simpl; auto.
     monadInv TRANS. simpl in *; auto.
     eapply eval_typecmp_assign_list_disjoint; eauto.
     red; simpl; intros. destruct H2; try tauto. red; intros; subst. auto.
    *constructor; auto. constructor 1 with (if negb b then Vtrue else Vfalse) (if negb b then Vtrue else Vfalse); auto.
     eapply eval_Sunop with (if b then Vtrue else Vfalse); eauto.
     eapply locenv_setbool_eval_sexp; eauto.
     destruct b; simpl; auto.
     destruct b; simpl; auto.
     constructor 1 with Mint8unsigned; auto.
   -inv H0; auto. unfold sem_cast in *. simpl in *.
    destruct k, b; simpl in *; inv H2; auto.
Qed.

Lemma trans_calldef_load_loopid:
  forall cdef x gc eh,
  trans_calldef cdef = OK x ->
  load_loopid gc eh None (callnum x) Int.zero.
Proof.
  unfold trans_calldef. intros.
  remember (callnum cdef). destruct o; inv H.
  rewrite <-Heqo. constructor 2.
Qed.

Lemma trans_hcalldef_load_loopid:
  forall cdef x gc eh i,
  trans_hcalldef cdef = OK x ->
  eval_sexp gc eh (Svar ACG_I type_int32s) (Vint i) ->
  load_loopid gc eh (Some (Svar ACG_I type_int32s)) (callnum x) i.
Proof.
  unfold trans_hcalldef. intros.
  remember (callnum cdef). destruct o; inv H.
  rewrite <-Heqo. constructor 1; auto.
Qed.

Lemma locenv_setvars_typeof:
  forall gc eh lhs l vrs eh',
  locenv_setarys gc (Svar ACG_I type_int32s) eh lhs l vrs eh' ->
  forall al, mmap trans_var_pary lhs = OK al ->
  map typeof al = l.
Proof.
  induction 1; simpl; intros.
  +monadInv H. auto.
  +monadInv H1. simpl. f_equal; auto.
Qed.

Lemma locenv_getmvls_setary_other:
  forall ty e id ofs v gc e1 al vl,
  locenv_getmvls gc e1 al vl ->
  store_env ty e id ofs v e1 ->
  forall l, ~ In id (map fst l) ->
  mmap trans_var_pary l = OK al ->
  id <> ACG_I ->
  locenv_getmvls gc e al vl.
Proof.
  induction 1; simpl; intros.
  +inv H1. constructor.
  +destruct l0; simpl in *; monadInv H3.
   simpl in H2. constructor 2; auto.
   -monadInv EQ. inv H. inv H1. inv H3. inv H11.
    rewrite PTree.gso in *; auto.
    rewrite H14 in H5. inv H5.
    unfold lvarof.
    constructor 1 with (fst p) (Int.add Int.zero (array_ofs i x0)) m (snd p); auto.
    destruct p. simpl in *. destruct t; monadInv EQ0.
    inv H13.
    apply eval_Saryacc with aid z; auto.
    constructor 1 with m; auto.
    inv H12. inv H1.
    *rewrite PTree.gso in *; auto.
     apply eval_Rlvalue with ACG_I Int.zero Lid; auto.
     constructor 1 with m1; auto. inv H3. constructor.
     destruct H1 as [m2 [t1 [A1 [A2 A3]]]]. rewrite PTree.gso in A1; auto.
     exists m2, t1; split; auto.
    *rewrite PTree.gso in *; auto.
     apply eval_Rlvalue with ACG_I Int.zero Gid; auto.
     constructor 2 with m1; auto. inv H3. constructor.
     destruct H1 as [m2 [t1 [A1 [A2 A3]]]].
     exists m2, t1; split; auto.
   -apply IHForall2 with l0; auto.
Qed.

Lemma locenv_setarys_getmvls:
  forall gc eh lhs tys vrets eh',
  locenv_setarys gc (Svar ACG_I type_int32s) eh lhs tys vrets eh' ->
  list_norepet (map fst lhs) ->
  forall al, mmap trans_var_pary lhs = OK al ->
  exists vl, locenv_getmvls gc eh al vl.
Proof.
  induction 1; simpl; intros.
  +inv H0. exists nil. constructor.
  +monadInv H2. inv H1. inv H. inv H1. inv H7.
   simpl in *. generalize H2; intros A. inv H2.
   eapply store_mvl_loadbytes_exists in H3; eauto.
   destruct H3 as [mv ?].
   destruct IHlocenv_setarys with x as [vl1 ?]; auto.
   rewrite H in H10. inv H10. inv H9.
   exists (mv :: vl1). constructor 2; auto.
   -constructor 1 with b (Int.add Int.zero (array_ofs i t)) m (Tarray aid0 t z); auto.
    apply eval_Saryacc with aid0 z ; auto.
    constructor 1 with m; auto.
   -eapply locenv_getmvls_setary_other; eauto.
    red. intros. subst.
    inv H8. inv H6. rewrite H in H16. inv H16. congruence.
Qed.

Lemma locenv_setarys_getmvls_mapw:
  forall gc eh id ty v eh1 lhs tys vrs eh2 al,
  locenv_setlvar gc eh (Svar id ty) v eh1 ->
  locenv_setarys gc (Svar ACG_I type_int32s) eh1 lhs tys vrs eh2 ->
  mmap trans_var_pary lhs = OK al ->
  list_norepet (id :: map fst lhs) ->
  id <> ACG_I ->
  exists vl, locenv_getmvls gc eh (Svar id ty :: al) vl.
Proof.
  intros. generalize H; intros. inv H2.
  apply locenv_setlvar_getmvl_exists in H4. destruct H4 as [v1 ?].
  eapply locenv_setarys_getmvls in H0; eauto.
  destruct H0 as [vl1 ?].
  exists (v1::vl1). constructor 2; auto.
  inv H. inv H4.
  eapply locenv_getmvls_setary_other; eauto.
Qed.

Lemma trans_expr_proj_typeof:
  forall l l' i tys vl vas,
  mmap trans_expr_proj l = OK l' ->
  locenv_getarys i (map typeof l) tys vl vas ->
  map typeof l' = tys.
Proof.
  induction l; simpl; intros; monadInv H; auto.
  +inv H0. auto.
  +inv H0. simpl in *. f_equal; eauto. monadInv EQ. simpl.
   rewrite <-H in *. simpl in *. congruence.
Qed.

Lemma lids_norepet_lvalues_norepet:
  forall gc eh l vl,
  locenv_getmvls gc eh l vl ->
  list_norepet (flat_map get_lids l) ->
  lvalue_list_norepet (eval_lvalue gc eh) l.
Proof.
  induction l; simpl; intros.
  +constructor.
  +inv H. inv H3. erewrite eval_lvalue_get_lids in H0; eauto.
   simpl in *. inv H0. constructor 2; eauto.
   red; intros. apply in_split in H0. destruct H0 as [? [? ?]].
   subst. rewrite flat_map_app in *.
   apply Forall2_app_inv_l in H5. destruct H5 as [? [? [? [? ?]]]].
   subst. inv H3. inv H8.
   econstructor 1; eauto.
   left. red; intros; subst.
   apply H6. apply in_or_app; simpl. right.
   erewrite eval_lvalue_get_lids; eauto. simpl. auto.
Qed.

Lemma trans_var_parys_get_lids:
  forall l l',
  mmap trans_var_pary l = OK l' ->
  flat_map get_lids l' = map fst l.
Proof.
  induction l; simpl; intros.
  inv H. auto.
  monadInv H. monadInv EQ. simpl.
  f_equal; auto.
Qed.

Lemma trans_expr_projs_get_lids:
  forall l l',
  mmap trans_expr_proj l = OK l' ->
  incl (flat_map get_lids (arystr_sexps l')) (flat_map get_lids (arystr_sexps l)) .
Proof.
  induction l; simpl; intros.
  inv H. simpl; red; auto.
  monadInv H. monadInv EQ. simpl.
  destruct (typeof a) eqn:?; simpl in *; inv EQ0.
  destruct (is_arystr x1); simpl; auto.
  +red; intros. apply in_app_or in H.
   destruct H; apply in_or_app; auto.
   right. eapply IHl; eauto.
  +red; intros. apply in_or_app; right.
   eapply IHl; eauto.
Qed.

Lemma loopid_notin_lid_disjoint:
  forall l, ~ In ACG_I (map fst l) ->
  Forall (lid_disjoint) (map lvarof l).
Proof.
  induction l; simpl; intros; auto.
  constructor 2 ;auto.
  destruct a. simpl. auto.
Qed.

Lemma trans_var_parys_lid_disjoint:
  forall l,  ~ In ACG_I (map fst l) ->
  forall l', mmap trans_var_pary l = OK l' ->
  Forall (lid_disjoint) l'.
Proof.
  induction l; simpl; intros; auto.
  inv H0. constructor.
  monadInv H0. constructor 2; auto.
  monadInv EQ. simpl. split; auto.
Qed.

Lemma cons_mixs_eval_cond:
  forall lis gc te o o' t ty cond ,
  eval_lindexs gc te t ty lis o o' ->
  cons_mixs_cond ty lis = OK cond ->
  eval_sexp gc te cond Vtrue.
Proof.
  induction lis; simpl; intros; inv H.
  +inv H0. constructor. simpl; auto.
  +destruct lis; monadInv H0.
   -simpl in *. rewrite H4 in *. inv EQ.
    constructor. simpl; auto.
   -simpl in EQ. rewrite H4 in *. simpl in EQ.
    inv EQ.
    apply IHlis with (Int.add o (Int.repr delta)) o' t x0; eauto.
  +simpl in *. rewrite Z.max_r in *; try omega.
   cut (0 < sizeof aty). intros A.
   destruct lis; monadInv H0.
   -apply eval_Sbinop with Vtrue Vtrue; simpl; auto.
    apply eval_Sbinop with (Vint Int.zero) (Vint i); simpl; auto.
    constructor; simpl; auto.
    unfold Int.lt. rewrite Int.signed_zero. rewrite pred_dec_false; auto. omega.
    apply eval_Sbinop with (Vint i) (Vint (Int.repr num)); simpl; auto.
    constructor; simpl; auto.
    rewrite H7. simpl; auto.
    unfold Int.lt. rewrite pred_dec_true; auto.
    rewrite Int.signed_repr; try omega.
    split. unfold Int.min_signed. simpl. omega.
    generalize (Int.unsigned_range o). intros.
    apply array_le_max_signed_inv with (Int.unsigned o) (sizeof aty); try xomega.
   -apply eval_Sbinop with Vtrue Vtrue; simpl; eauto.
    *apply eval_Sbinop with Vtrue Vtrue; simpl; auto.
     apply eval_Sbinop with (Vint Int.zero) (Vint i); simpl; auto.
     constructor; simpl; auto.
     unfold Int.lt. rewrite Int.signed_zero. rewrite pred_dec_false; auto. omega.
     apply eval_Sbinop with (Vint i) (Vint (Int.repr num)); simpl; auto.
     constructor; simpl; auto.
     rewrite H7. simpl; auto.
     unfold Int.lt. rewrite pred_dec_true; auto.
     rewrite Int.signed_repr; try omega.
     split. unfold Int.min_signed. simpl. omega.
     generalize (Int.unsigned_range o). intros.
     apply array_le_max_signed_inv with (Int.unsigned o) (sizeof aty); try xomega.
    *apply cons_mixs_cond_typeof in EQ. auto.
   -cut (0 < sizeof aty * num). intros.
    apply Zmult_lt_0_reg_r with num; try omega.
    omega.
Qed.

Lemma cons_mixs_correct:
  forall lis gc nk te te' e s s' o o' a v v' b,
  eval_lindexs gc te (typeof a) (typeof s) lis o o' ->
  eval_sexp gc te a v ->
  eval_cast v (typeof a) v' ->
  eval_lvalue gc te s b o Lid ->
  store_env (typeof a) te b o' v' te' ->
  ~ In b (get_expids a) ->
  cons_mixs_expr s lis = OK s' ->
  eval_stmt true progR gc nk te e te' e (Sassign s' a).
Proof.
  induction lis; simpl; intros; inv H.
  +inv H5. rewrite H7 in *.
   eapply eval_Sassign; eauto.
   constructor 1 with v v';auto.
   constructor 1 with b o'; auto.
   eapply eval_sexp_lvalue_assign_disjoint; eauto.
   red; simpl; intros. apply H4. apply get_lids_expids_incl; auto.
  +monadInv H5; simpl in *. rewrite <-H6 in *.
   simpl in *. rewrite H10 in *. simpl in *. inv EQ.
   apply IHlis with (Sfield s label ty) (Int.add o (Int.repr delta)) o' v v' b; eauto.
   eapply eval_Sfield; eauto.
   rewrite <-H6. auto.
  +monadInv H5; simpl in *. rewrite <-H6 in EQ.
   simpl in *. inv EQ.
   apply IHlis with (Saryacc s index aty) (Int.add o (array_ofs i aty)) o' v v' b; eauto.
   eapply eval_Saryacc; eauto.
   rewrite Z.max_r; try omega.
   rewrite <-H6. simpl. omega.
Qed.

Lemma locenv_setarybool_eval_sexp:
  forall gc eh id ty id2 (b: bool) eh1,
  locenv_setlvar gc eh (Saryacc (Svar id ty) (Svar id2 type_int32s) type_bool) (if b then Vtrue else Vfalse) eh1 ->
  eval_sexp gc eh1 (Saryacc (Svar id ty) (Svar id2 type_int32s) type_bool) (if b then Vtrue else Vfalse).
Proof.
  intros. inv H.
  apply eval_Rlvalue with b0 ofs Lid; auto.
  +inv H0.
   econstructor; eauto.
   inv H4. inv H1. constructor 1 with m'; auto.
   rewrite PTree.gss. congruence.
   inv H1. simpl in *. subst. eapply eval_sexp_setnew; simpl; eauto.
   red; simpl; intros. inv H4.
   destruct H1; subst; try tauto.
   rewrite H9 in H. inv H.
   inv H5. inv H. rewrite H9 in H12. inv H12.
   congruence.
  +constructor 2. inv H0. inv H4. simpl in *.
   eapply store_env_load_bool_eq; eauto.
   destruct b; auto.
  +destruct b; simpl; auto.
Qed.

Lemma trans_prefix_unary_expr_typeof:
  forall op a t,
  prefix_unary_type op (typeof a) t ->
  typeof (trans_prefix_unary_expr op a t) = t.
Proof.
  destruct op; auto.
Qed.

Lemma trans_node_all_correct:
  forall gc e e' nodeT vargs vrets,
  LsemS.eval_node progS gc e e' nodeT vargs vrets ->
  find_funct (node_block progS) (fst nodeT) = Some nodeT ->
  forall nodeR, trans_node nodeT = OK nodeR ->
  eval_node true progR gc e e' nodeR vargs vrets.
Proof.
  intros gc.
  induction 1 using LsemS.eval_node_ind2 with
  ( P0 := fun nk te e te' e' ss =>
      forall s, trans_stmts ss = OK s ->
      eval_stmt true progR gc nk te e te' e' s)
  ( P1 := fun nk te e te' e' s =>
      forall s', trans_stmt s = OK s' ->
      eval_stmt true progR gc nk te e te' e' s')
  ( P2 := fun nk te e te' e' f =>
      forall s, trans_hstmt f = OK s ->
      eval_stmt true progR gc nk te e te' e' s)
  ( P3 := fun nk te se se1 args atys vargs i cdef l rtys vrets =>
      exists fd' vargs' ef ef',
        callorder nk (nd_kind (snd fd')) = true
        /\ call_func (node_block progR) cdef fd'
        /\ map snd (nd_args (snd fd')) = atys
        /\ map snd (nd_rets (snd fd')) = rtys
        /\ eval_casts vargs atys vargs'
        /\ call_env cdef i se se1 ef ef'
        /\ eval_node true progR gc ef ef' fd' vargs' vrets
        /\ list_norepet (ACG_I::l)
        /\ list_disjoint l (flat_map get_lids (arystr_sexps args))
        /\ te ! (callid cdef) = None); intros.
+(*eval_node*)
   monadInv H7. simpl in *.
   generalize H0; intros B.
   eapply trans_body_ids_norepet in H0; eauto.
   monadInv EQ.
   eapply exec_node; eauto.
   -eapply alloc_variables_permut in H; eauto.
    apply allvarsof_permut.
    eapply trans_body_allidsof_norepet; eauto.
    apply find_funct_in2 in H6.
    apply ID_RANGE in H6; auto.
   -unfold allvarsof in *; simpl in *.
    repeat rewrite app_ass. rewrite app_ass in H; auto.
    simpl.
    erewrite trans_stmts_fby_eq; eauto.
   -apply find_funct_in2 in H6.
    apply ID_RANGE in H6; auto.
+(*eval_stmts_nil*)
   inv H. constructor.
+(*eval_stmts_cons*)
   monadInv H1. eapply eval_Sseq; eauto.
+(*eval_Sassign*)
   inv H3. eapply trans_expr_correct; eauto.
+(*eval_Scall*)
   monadInv H2.
   destruct IHeval_node as [fdR [vargs' [ef [ef' [A [A1 [A2 [A3 [A4 [A5 [A6 [A7 [A8 A9]]]]]]]]]]]]]; auto.
   generalize EQ; intros B.
   eapply trans_calldef_eq in B; eauto. subst.
   generalize H1; intros B1. inv A7.
   apply locenv_setlvars_getmvls with (gc:=gc) in B1; auto.
   destruct B1 as [vl B1].
   apply eval_Scall with ef ef' fdR vl vargs vargs' vrets Int.zero; simpl; auto.
   -eapply trans_calldef_load_loopid; eauto.
   -apply setvars_lvars; auto.
   -apply loopid_notin_lid_disjoint; auto.
   -rewrite map_lvarof_typeof; auto.
   -eapply lids_norepet_lvalues_norepet; eauto.
    rewrite flat_map_map; auto.
   -eapply lids_disjoint_assign_lidst_disjoint; eauto.
    rewrite flat_map_map; auto.
+(*eval_Sfor_start*)
   monadInv H2. generalize H0; intros A.
   eapply trans_finit_correct in H; eauto.
   apply eval_Sseq with te1 e; auto.
   apply eval_Sfor_start with te2; auto.
   simpl in *. rewrite EQ in *. simpl in *.
   eapply IHeval_node0; eauto.
+(*eval_Sfor_false*)
   monadInv H0. apply eval_Sfor_false; auto.
+(*eval_Sfor_loop*)
   monadInv H3. simpl in *. rewrite EQ in *. simpl in *.
   eapply eval_Sfor_loop; eauto.
+(*eval_Sarydif_nil*)
   monadInv H. constructor.
+(*eval_Sarydif_cons*)
   monadInv H5. apply eval_Sseq with te1 e; auto.
   constructor. constructor 1 with v v'; auto.
   unfold lvarof. simpl.
   inv H3. eapply eval_sexp_lvalue_assign_disjoint; eauto.
   inv H1. inv H8. simpl. red; intros.
   apply H0. apply get_lids_expids_incl; auto.
+(*eval_Smix *)
   simpl in *. monadInv H5.
   eapply eval_Sseq; eauto.
   inv H1. inv H15. inv H1.
   apply not_in_app in H4. destruct H4.
   assert(A: eval_lindexs gc te1 (typeof a3) ty lis Int.zero o).
     inv H5. eapply eval_lindexs_disjoint; eauto.
   apply eval_Sif with Vtrue true; simpl; auto.
   -apply cons_mixs_eval_cond with lis Int.zero o (typeof a3) ty; eauto.
   -erewrite cons_mixs_cond_typeof; eauto.
   -apply cons_mixs_correct with lis (Svar b ty) Int.zero o v3 v b; eauto.
    inv H5. eapply eval_sexp_setnew; eauto.
    inv H5. constructor 1 with m'; auto.
    rewrite PTree.gss; auto. simpl. congruence.
+(*eval_Sstruct_nil*)
   monadInv H. constructor.
+(*eval_Sstruct_cons*)
   monadInv H5.
   apply eval_Sseq with te1 e; auto.
   constructor. constructor 1 with v v'; auto.
   unfold lvarof. simpl.
   inv H1. eapply eval_sexp_lvalue_assign_disjoint; eauto.
   inv H3. inv H8. simpl. red; intros.
    apply H2. apply get_lids_expids_incl; auto.
+(*eval_Sskip*)
   inv H. constructor.
+(*fby_0*)
   monadInv H5.
   eapply eval_Sfby_cycle_1; eauto.
   econstructor; eauto.
   inv H4. apply eval_sexp_lvalue_assign_disjoint with v2 b ofs; eauto.
    inv H5; auto.
+(*fby_n*)
   monadInv H5. eapply eval_Sfby_cycle_n; eauto.
   simpl. red; intros. apply H4. destruct H5; auto. tauto.
+(*fbyn_0*)
   inv H11. eapply eval_Sfbyn_cycle_1; eauto.
+(*fbyn_n*)
   inv H8. eapply eval_Sfbyn_cycle_n; eauto.
   simpl. red; intros. apply H7. destruct H; auto. tauto.
+(*arrow*)
   inv H2. eapply eval_Sarrow; eauto.
   assert(trans_stmt (LustreS.Sassign lh (Expr (if b then a1 else a2))) =
            OK (Sassign (lvarof lh) (if b then a1 else a2))).
     destruct b; auto.
   apply IHeval_node in H2.
   destruct b; inv H2; auto.
+(*eval_Hmaptycmp*)
   monadInv H2.
   destruct (identeq _ _) eqn:?; destruct (in_list _ _) eqn:?; inv EQ0.
   rewrite H in *. inv EQ.
   apply in_list_false_notin in Heqb1.
   apply Pos.eqb_neq in Heqb0.
   destruct k.
   -apply eval_Stypecmp with b; simpl; auto.
    *monadInv TRANS. simpl in *; auto.
    *eapply eval_typecmp_assign_list_disjoint; eauto.
     simpl. red; simpl; intros. destruct H2; try tauto; subst.
     red; intros; subst. eapply Heqb1; eauto.
   -eapply locenv_setlvar_trans_exists in H1; simpl; eauto.
    destruct H1 as [te0 [? ?]].
    apply eval_Sseq with te0 e; auto.
    *apply eval_Stypecmp with b; simpl; auto.
     monadInv TRANS. simpl in *; auto.
     eapply eval_typecmp_assign_list_disjoint; eauto.
     red; simpl; intros. destruct H3; try tauto. red; intros; subst. auto.
    *constructor; auto. constructor 1 with (if negb b then Vtrue else Vfalse) (if negb b then Vtrue else Vfalse); auto.
     eapply eval_Sunop with (if b then Vtrue else Vfalse); eauto.
     eapply locenv_setarybool_eval_sexp; eauto.
     destruct b; simpl; auto.
     destruct b; simpl; auto.
     constructor 1 with Mint8unsigned; auto.
     destruct b; simpl; auto.
     constructor 1 with Mint8unsigned; auto.
+(*eval_Hmapary*)
   monadInv H2. unfold lvarof. simpl in *.
   apply eval_Sassign; auto. econstructor; eauto.
   apply eval_sbinop_by_value in H. destruct H as [chunk ?].
   constructor 1 with chunk; auto.
+(*eval_Hmapunary*)
   monadInv H5. rewrite H in *. unfold lvarof. simpl in *. inv EQ.
   apply eval_Sassign; econstructor; eauto.
   destruct op; simpl; auto.
   inv H4. eapply eval_sexp_lvalue_assign_disjoint; eauto.
   apply eval_sexp_has_type in H2.
   rewrite trans_prefix_unary_expr_typeof in *; auto.
   destruct op; simpl; auto.
   inv H5. inv H9; auto.
+(*eval_Hfoldary*)
   monadInv H0. econstructor; eauto.
+(*eval_Hfoldunary*)
   monadInv H0. econstructor; eauto.
+(*eval_Hfoldcast*)
   monadInv H0. econstructor; eauto.
+(*eval_Farydef*)
   monadInv H4. unfold lvarof. simpl in *.
   apply eval_Sassign; econstructor; eauto.
   inv H3. eapply eval_sexp_lvalue_assign_disjoint; eauto.
   inv H0. inv H7. red; simpl; intros.
   apply H1. eapply get_lids_expids_incl; eauto.
+(*eval_Haryslc*)
   monadInv H3. apply eval_Sassign; econstructor; eauto.
   inv H2. eapply eval_sexp_lvalue_assign_disjoint; eauto.
   inv H3. inv H7. simpl.
   red; simpl; intros. apply H.
   eapply get_lids_expids_incl; eauto.
+(*eval_Hboolred_true*)
   monadInv H1. apply eval_Sif with Vtrue true; auto.
   constructor; auto.
+(*eval_Hboolred_false*)
   monadInv H0. apply eval_Sif with Vfalse false; auto.
   constructor.
+(*eval_Hmapcall*)
   monadInv H4.
   destruct IHeval_node as [fdR [vargs' [ef [ef' [A [A1 [A2 [A3 [A4 [A5 [A6 [A7 [A8 A9]]]]]]]]]]]]]; auto.
   generalize EQ0; intros B.
   eapply trans_hcalldef_eq in B; eauto. subst.
   generalize H3; intros B. inv A7.
   apply locenv_setarys_getmvls with (al:=x) in B; auto.
   destruct B as [vl1 B].
   eapply eval_map_args in H; eauto.
   apply eval_Scall with ef ef' fdR vl1 vas vargs' vrs i; auto.
   -eapply trans_hcalldef_load_loopid; eauto.
   -erewrite trans_expr_proj_typeof; eauto.
   -eapply set_map_rets; eauto.
   -eapply trans_var_parys_lid_disjoint; eauto.
   -eapply locenv_setvars_typeof; eauto.
   -erewrite trans_expr_proj_typeof; eauto.
   -eapply lids_norepet_lvalues_norepet; eauto.
    erewrite trans_var_parys_get_lids; eauto.
   -eapply lids_disjoint_assign_lidst_disjoint; eauto.
    red; simpl; intros. eapply A8; eauto.
    erewrite <-trans_var_parys_get_lids; eauto.
    eapply trans_expr_projs_get_lids; eauto.
+(*eval_Hmapfoldcall*)
   monadInv H7.
   destruct IHeval_node0 as [fdR [vargs' [ef [ef' [A [A1 [A2 [A3 [A4 [A5 [A6 [A7 [A8 A9]]]]]]]]]]]]]; auto.
   generalize EQ0; intros B.
   eapply trans_hcalldef_eq in B; eauto. subst.
   generalize H6; intros B. inv A7. inv H10. simpl in *.
   eapply locenv_setarys_getmvls_mapw with (id:=lid) (ty:=ty) (v:=vret) (eh:=te1) in B; eauto.
   destruct B as [vl1 B]. eapply eval_map_args in H1; eauto.
   econstructor; eauto.
   apply eval_Scall with ef ef' fdR vl1 (v::vargs) vargs' (vret::vrs) i; simpl; auto.
   -eapply trans_hcalldef_load_loopid; eauto.
   -constructor 2; auto.
   -erewrite trans_expr_proj_typeof; eauto.
   -constructor 2 with te2; auto.
    eapply set_map_rets; eauto.
   -constructor 2; simpl; auto.
    eapply trans_var_parys_lid_disjoint; eauto.
   -erewrite locenv_setvars_typeof; eauto.
   -erewrite trans_expr_proj_typeof; eauto.
   -eapply lids_norepet_lvalues_norepet; eauto.
    simpl. erewrite trans_var_parys_get_lids; eauto.
    constructor; auto.
   -eapply lids_disjoint_assign_lidst_disjoint; eauto.
    econstructor; eauto.
    red; simpl; intros. eapply A8; simpl; eauto.
    destruct H7; auto. right. erewrite <-trans_var_parys_get_lids; eauto.
    destruct (is_arystr ty); simpl in *.
    destruct H8; auto. right. eapply trans_expr_projs_get_lids; eauto.
    eapply trans_expr_projs_get_lids; eauto.
   -constructor; auto.
+(*eval_apply*)
  destruct call_func_exists with cdef fd as [fdR [A A1]]; auto.
  destruct H0 as [? [? [? ?]]].
  exists fdR, vargs', ef, ef'. repeat (split; auto).
  -monadInv A. monadInv EQ; simpl; auto.
  -monadInv A. monadInv EQ; simpl; auto.
  -monadInv A. monadInv EQ; simpl; auto.
  -apply IHeval_node; auto.
   eapply find_funct_eq; eauto.
Qed.

Lemma init_node_correct:
  forall e fd,
  LsemT.init_node progS e fd ->
  find_funct (node_block progS) (fst fd) = Some fd ->
  forall fd', trans_node fd = OK fd' ->
  init_node progR e fd'.
Proof.
  induction 1 using LsemT.init_node_ind2 with
  ( P0 := fun e1 e2 l =>
      init_stmt progR e1 e2 l
   ); intros.
 +(*init_node*)
  monadInv H4. simpl in *.
  eapply trans_body_ids_norepet in H; eauto.
  monadInv EQ. constructor 1; simpl in *; auto.
  -erewrite trans_stmts_fby_eq; eauto.
   erewrite trans_body_fbyvarsof; eauto.
  -intros. apply H1. erewrite <-trans_body_fbyvarsof; eauto.
  -erewrite trans_stmts_instidof_eq; eauto.
  -apply find_funct_in2 in H3.
   apply ID_RANGE in H3; auto.
 +(*nil*)
  constructor.
 +(*cons*)
  destruct call_func_exists with c fd as [fd' [A A1]]; auto.
  destruct H0 as [? [? [? ?]]].
  constructor 2 with se1 fd' ef; auto.
  monadInv A. monadInv EQ; auto.
  apply IHinit_node; auto.
  eapply find_funct_eq; eauto.
Qed.

Theorem exec_prog_correct:
  forall gc e mainT vass vrss n maxn,
  exec_prog progS gc LsemS.eval_node mainT e n maxn vass vrss ->
  find_funct (node_block progS) (fst mainT) = Some mainT ->
  forall mainR, trans_node mainT = OK mainR ->
  exec_prog progR gc (eval_node true) mainR e n maxn vass vrss.
Proof.
  induction 1; intros.
  +constructor 1 with mrss; trivial.
   monadInv H2. monadInv EQ; auto.
  +constructor 2 with e'; auto.
   apply trans_node_all_correct with mainT; auto.
Qed.

Lemma initial_states_match:
  forall gc main1 e,
  Lenv.initial_state progS gc LsemT.init_node main1 e ->
  exists main2, Lenv.initial_state progR gc init_node main2 e
    /\ trans_node main1 = OK main2.
Proof.
  induction 1; intros.
  +destruct find_funcs_monad_exits with LustreS.node node (node_block progS) (node_block progR) trans_node (node_main progS) main1
     as [main2 [? ?]]; auto.
   -monadInv TRANS; auto.
   -intros. monadInv H2; auto.
   -exists main2. split; auto.
    constructor 1; auto.
    *monadInv TRANS; auto.
    *monadInv TRANS; auto.
    *eapply init_node_correct; eauto.
     eapply find_funct_eq; eauto.
Qed.

Theorem trans_program_correct:
  forall gc e main1 vass vrss maxn,
  Lenv.initial_state progS gc LsemT.init_node main1 e->
  exec_prog progS gc LsemS.eval_node main1 e 1 maxn vass vrss ->
  exists main2, Lenv.initial_state progR gc init_node main2 e
    /\ nd_args (snd main1) = nd_args (snd main2)
    /\ nd_rets (snd main2) = nd_rets (snd main1)
    /\ exec_prog progR gc (eval_node true) main2 e 1 maxn vass vrss.
Proof.
  intros.
  destruct initial_states_match with gc main1 e as [main2 [A A1]]; auto.
  exists main2. repeat (split; auto).
  monadInv A1. monadInv EQ. auto.
  monadInv A1. monadInv EQ. auto.
  eapply exec_prog_correct; eauto.
  inv H; eapply find_funct_eq; eauto.
Qed.

End CORRECTNESS.
