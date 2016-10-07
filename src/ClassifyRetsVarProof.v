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

(** Correctness proof for output parameters classification. *)

Require Import AST.
Require Import Coqlib.
Require Import Errors.
Require Import Maps.
Require Import Integers.
Require Import Memdata.
Require Import Ctypes.
Require Import Cltypes.
Require Import List.
Require Import Lint.
Require Import ExtraList.
Require Import Ltypes.
Require Import Lident.
Require Import Lustre.
Require Import LustreF.
Require Import Lvalues.
Require Import Lenv.
Require Import Lenvmatch.
Require Import Lsem.
Require Import LsemF.
Require Import LsemD.
Require Import LsemE.
Require Import ClassifyRetsVar.

Section CORRECTNESS.

Variable prog1 prog2: program.

Hypothesis TRANSL:
  trans_program prog1 = prog2.

Inductive mvl_match: mvl -> mvl -> type -> Prop :=
  | mvl_match_val: forall m ty,
     is_arystr ty = false ->
     Z_of_nat (length m) = sizeof ty ->
     mvl_match m m ty
  | mvl_match_undef: forall m1 m2 ty,
     is_arystr ty = false ->
     is_undefs m1 ->
     length m1 = length m2 ->
     Z_of_nat (length m1) = sizeof ty ->
     mvl_match m1 m2 ty
  | mvl_match_ary: forall m1 m2 aid aty num,
     mvl_array_match m1 m2 aty (nat_of_Z (Z.max 0 num)) ->
     mvl_match m1 m2 (Tarray aid aty num)
  | mvl_type_str: forall m1 m2 sid fld,
     mvl_struct_match m1 m2 fld fld 0 ->
     mvl_match m1 m2 (Tstruct sid fld)

with mvl_array_match: mvl -> mvl -> type -> nat -> Prop :=
  | mvl_array_match_nil: forall ty,
     mvl_array_match nil nil ty O
  | mvl_array_match_cons: forall m1 m2 ml1 ml2 ty n,
     mvl_match m1 m2 ty ->
     mvl_array_match ml1 ml2 ty n ->
     mvl_array_match (m1++ml1) (m2++ml2) ty (S n)

with mvl_struct_match: mvl -> mvl -> fieldlist -> fieldlist -> Z -> Prop :=
  | mvl_struct_match_nil: forall m fld pos,
     is_undefs m ->
     Z_of_nat (length m) = align pos (alignof_fields fld) - pos  ->
     mvl_struct_match m m Fnil fld pos
  | mvl_struct_match_cons: forall m m1 m2 ml1 ml2 pos i t ftl fld,
     is_undefs m ->
     Z_of_nat (length m) = align pos (alignof t) - pos ->
     mvl_match m1 m2 t ->
     mvl_struct_match ml1 ml2 ftl fld (align pos (alignof t) + sizeof t) ->
     mvl_struct_match (m++m1++ml1) (m++m2++ml2) (Fcons i t ftl) fld pos.

Scheme mvl_match_ind2 := Minimality for mvl_match Sort Prop
  with mvl_array_match_ind2 := Minimality for mvl_array_match Sort Prop
  with mvl_struct_match_ind2 := Minimality for mvl_struct_match Sort Prop.
Combined Scheme mvl_match_arystr_ind2 from mvl_match_ind2, mvl_array_match_ind2, mvl_struct_match_ind2.

Definition ptree_vars_some(l: list (ident*type))(e: locenv): Prop :=
  forall id ty, In (id,ty) l ->
  exists m, e ! id = Some (m,ty) /\ mvl_alloc m ty.

Definition locenv_mvl_alloc(te: locenv): Prop :=
  forall id m ty, te ! id = Some (m,ty) -> mvl_alloc m ty.

Lemma mvl_match_length:
(
  forall m1 m2 ty, mvl_match m1 m2 ty -> length m1 = length m2
)
/\
(
  forall m1 m2 ty n, mvl_array_match m1 m2 ty n -> length m1 = length m2
)
/\
(
  forall m1 m2 fld f pos, mvl_struct_match m1 m2 fld f pos -> length m1 = length m2
).
Proof.
  apply mvl_match_arystr_ind2; intros; auto.
  +repeat rewrite app_length. omega.
  +repeat rewrite app_length. omega.
Qed.

Lemma mvl_match_sizeof:
(
  forall m1 m2 ty, mvl_match m1 m2 ty -> Z_of_nat (length m1) = sizeof ty
)
/\
(
  forall m1 m2 ty n, mvl_array_match m1 m2 ty n ->
  Z_of_nat (length m1) = sizeof ty * (Z_of_nat n)
)
/\
(
  forall m1 m2 fld f pos, mvl_struct_match m1 m2 fld f pos -> Z_of_nat (length m1) =  align (sizeof_struct fld pos) (alignof_fields f) - pos
).
Proof.
  apply mvl_match_arystr_ind2; intros; auto.
  +simpl. rewrite nat_of_Z_eq in H0; try xomega.
  +simpl. omega.
  +simpl. omega.
  +rewrite app_length. rewrite Nat2Z.inj_add.
   rewrite Nat2Z.inj_succ.
   rewrite H0,H2. ring.
  +rewrite app_length. rewrite Nat2Z.inj_add.
   rewrite app_length. rewrite Nat2Z.inj_add.
   rewrite H0,H2,H4. simpl. ring.
Qed.

Lemma mvl_match_mvl_type_eq:
(
  forall m1 m2 t,
  mvl_match m1 m2 t ->
  mvl_type true m1 t ->
  m2 = m1
)
/\
(
  forall m1 m2 t i,
  mvl_array_match m1 m2 t i->
  mvl_array true m1 t i ->
  m2 = m1
)
/\
(
  forall m1 m2 fld f pos,
  mvl_struct_match m1 m2 fld f pos ->
  mvl_struct true m1 fld f pos ->
  m2 = m1
).
Proof.
  apply mvl_match_arystr_ind2; intros; auto.
  +inv H3; simpl in *; try congruence.
   destruct m1,m2; simpl in *; try omega; auto.
   inv H0. inv H5. destruct m; simpl in *; tauto.
  +inv H1; auto. simpl in *; congruence.
  +inv H1; auto. simpl in *; congruence.
  +inv H3. apply app_length_equal_inv in H4; auto.
   destruct H4; subst. f_equal; auto.
   left. apply mvl_match_sizeof in H.
   apply mvl_type_length in H6.
   apply Nat2Z.inj; congruence.
  +f_equal. inv H5. apply app_length_equal_inv in H6; auto.
   destruct H6; subst.
   apply app_length_equal_inv in H6; auto.
   destruct H6; subst. f_equal; auto.
   -left. apply mvl_match_sizeof in H1.
    apply mvl_type_length in H14.
    apply Nat2Z.inj. congruence.
   -left. apply Nat2Z.inj. congruence.
Qed.

Lemma mvl_match_self:
forall b,
(
  forall m t,
  mvl_type b m t ->
  mvl_match m m t
)
/\
(
  forall m t i,
  mvl_array b m t i->
  mvl_array_match m m t i
)
/\
(
  forall m fld f pos,
  mvl_struct b m fld f pos ->
  mvl_struct_match m m fld f pos
).
Proof.
  intros b. apply mvl_type_arystr_ind2; intros;
  try (econstructor; eauto; fail).
 +econstructor 3; eauto.
 +econstructor 4; eauto.
Qed.

Lemma mvl_match_mvl_alloc:
(
  forall m1 m2 t,
  mvl_match m1 m2 t ->
  mvl_type false m1 t /\ mvl_type false m2 t
)
/\
(
  forall m1 m2 t i,
  mvl_array_match m1 m2 t i ->
  mvl_array false m1 t i /\ mvl_array false m2 t i
)
/\
(
  forall m1 m2 fld f pos,
  mvl_struct_match m1 m2 fld f pos ->
  mvl_struct false m1 fld f pos /\ mvl_struct false m2 fld f pos
).
Proof.
  apply mvl_match_arystr_ind2; intros; split;
  try (econstructor; eauto; fail).
 +econstructor 1; eauto. congruence.
 +destruct H0. econstructor 2; eauto.
 +destruct H0. econstructor 2; eauto.
 +destruct H0. econstructor 3; eauto.
 +destruct H0. econstructor 3; eauto.
 +destruct H0,H2. econstructor 2; eauto.
 +destruct H0,H2. econstructor 2; eauto.
 +destruct H2, H4. econstructor 2; eauto.
 +destruct H2, H4. econstructor 2; eauto.
Qed.

Lemma mvl_match_alloc:
(
  forall m t,
  mvl_type false m t ->
  mvl_match (alloc (sizeof t)) m t
)
/\
(
  forall m t i,
  mvl_array false m t i ->
  mvl_array_match (alloc (sizeof t * (Z_of_nat i))) m t i
)
/\
(
  forall m fld f pos,
  mvl_struct false m fld f pos ->
  mvl_struct_match (alloc (align (sizeof_struct fld pos) (alignof_fields f) - pos)) m fld f pos
).
Proof.
  apply mvl_type_arystr_ind2; intros.
  +constructor 2; auto.
   apply is_undefs_alloc; auto.
   rewrite <-H1. unfold alloc.
   rewrite length_list_repeat, nat_of_Z_of_nat; auto.
   rewrite <-H1. unfold alloc.
   rewrite length_list_repeat, nat_of_Z_of_nat; auto.
  +econstructor 3; eauto. simpl.
   rewrite nat_of_Z_eq in H0; auto. xomega.
  +constructor 4; auto. simpl.
   rewrite Z.sub_0_r in H0. auto.
  +simpl. rewrite Zmult_0_r.
   unfold alloc. simpl. constructor.
  +rewrite Nat2Z.inj_succ.
   replace (sizeof ty * Z.succ (Z.of_nat n)) with (sizeof ty + sizeof ty * Z.of_nat n) by ring.
   generalize (sizeof_pos ty); intros.
   unfold alloc in *. rewrite Z2Nat.inj_add, list_repeat_app.
   econstructor; eauto.
   omega. apply Zmult_le_0_compat; omega.
  +simpl. rewrite <-H0.
   rewrite alloc_is_undefs; auto. econstructor; eauto.
  +assert (align (sizeof_struct (Fcons i t ftl) pos) (alignof_fields fld) - pos =
           Z_of_nat (length m) + Z_of_nat (length m1) + Z_of_nat (length ml)).
    apply mvl_type_length in H1. apply mvl_type_length in H3.
    rewrite H0, H1, H3. simpl. ring.
   rewrite H5.
   repeat rewrite Z2Nat.inj_add; try omega.
   repeat rewrite alloc_app; try omega.
   rewrite alloc_is_undefs; auto. rewrite app_ass.
   econstructor; eauto.
   apply mvl_type_length in H1. congruence.
   apply mvl_type_length in H3. congruence.
Qed.

Lemma mvl_array_match_getN:
  forall n i o m1 m2 t,
  mvl_array_match (getN (nat_of_Z (sizeof t) * n) o m1) (getN (nat_of_Z (sizeof t) * n) o m2) t n ->
  (i < n)%nat ->
  length m1 = length m2 ->
  (o + (nat_of_Z (sizeof t) * n) <= length m1)%nat ->
  mvl_match (getN (nat_of_Z (sizeof t)) (o + (nat_of_Z (sizeof t)) * i) m1) (getN (nat_of_Z (sizeof t)) (o + (nat_of_Z (sizeof t)) * i) m2) t.
Proof.
  induction n; intros; try omega.
  change (S n) with (1 + n)%nat in *.
  rewrite mult_plus_distr_l, mult_1_r in H.
  repeat rewrite getN_add in H. inv H.
  generalize H6 H6 H8 H8; intros A A1 A2 A3.
  apply mvl_match_length in A. apply mvl_match_length in A2.
  apply mvl_match_sizeof in A1. apply mvl_match_sizeof in A3.
  cut (length m3 = length (getN (nat_of_Z (sizeof t)) o m2)). intros A4.
  apply app_length_equal_inv in H3.
  apply app_length_equal_inv in H4; auto.
  destruct H3,H4. subst.
  destruct n.
  +destruct i; try omega.
   rewrite mult_0_r, plus_0_r in *; auto.
  +destruct i.
   -rewrite mult_0_r, plus_0_r in *; auto.
   -change (S i) with (1 + i)%nat.
    rewrite mult_plus_distr_l, mult_1_r, plus_assoc in *.
    apply IHn; auto. omega.
  +left. rewrite A, A4. unfold getN, getn.
   repeat rewrite firstn_length, skipn_length. congruence.
  +rewrite <-nat_of_Z_of_nat with o.
   rewrite <-getN_length; try omega. rewrite <-A1.
   rewrite nat_of_Z_of_nat; auto.
   generalize (sizeof_pos t); intros.
   rewrite mult_plus_distr_l, mult_1_r in H2.
   apply Nat2Z.inj_le in H2.
   repeat rewrite Nat2Z.inj_add in H2.
   rewrite nat_of_Z_eq in H2; try omega.
Qed.

Lemma mvl_struct_match_getN:
  forall f fld m1 m2 pos i delta t,
  mvl_struct_match m1 m2 fld f pos ->
  length m1 = length m2 ->
  0 <= pos ->
  field_offset_rec i fld pos = OK delta ->
  field_type i fld = OK t ->
  mvl_match (getN (nat_of_Z (sizeof t)) (nat_of_Z (delta-pos)) m1)
            (getN (nat_of_Z (sizeof t)) (nat_of_Z (delta-pos)) m2) t.
Proof.
  induction fld; simpl; intros; try congruence.
  compare i i0; intros; subst.
  +rewrite peq_true in *. inv H3. inv H2.
   inv H. rewrite <-H8. rewrite nat_of_Z_of_nat.
   replace (length m) with (0+length m)%nat by omega.
   repeat rewrite getN_app_skipn. rewrite skipn_length_app; try omega.
   rewrite minus_diag. simpl. rewrite skipn_length_app; try omega.
   rewrite minus_diag. simpl.
   unfold getN,getn. simpl. generalize H11 H11; intros A A1.
   apply mvl_match_sizeof in A1. apply mvl_match_length in A.
   rewrite <-A1. rewrite nat_of_Z_of_nat. rewrite A at 2.
   repeat rewrite firstn_length_app2; try omega.
   repeat rewrite minus_diag. simpl.
   repeat rewrite <-app_nil_end. auto.
  +rewrite peq_false in *; auto. inv H.
   generalize H13 H13; intros A A1.
   apply mvl_match_sizeof in A. apply mvl_match_length in A1.
   replace (delta - pos) with ((delta - (align pos (alignof t) + sizeof t)) + (align pos (alignof t) - pos + sizeof t)) by omega.
   rewrite <-H10. rewrite <-A. rewrite <-Nat2Z.inj_add.
   cut (0 <= delta - align pos (alignof t) - Z.of_nat (length m0)). intros A2.
   rewrite A1 at 4. repeat rewrite Z2Nat.inj_add; try omega.
   repeat rewrite nat_of_Z_of_nat, <-app_length.
   repeat rewrite getN_app_skipn, <-app_ass.
   repeat rewrite skipn_length_app; try omega.
   repeat rewrite minus_diag. simpl.
   apply IHfld with i0; try omega; try congruence.
   -eapply mvl_match_length in H14; eauto.
   -eapply field_offset_rec_in_range in H3; eauto. omega.
Qed.

Lemma eval_offset_mvl_match_sube:
  forall t a o,
  eval_offset t a o ->
  forall m1 m2,
  mvl_match m1 m2 t ->
  mvl_match (getN (nat_of_Z (sizeof (typeof a))) (nat_of_Z o) m1) (getN (nat_of_Z (sizeof (typeof a))) (nat_of_Z o) m2) (typeof a).
Proof.
  induction 1; intros.
  +simpl. generalize H H; intros. apply mvl_match_length in H.
   apply mvl_match_sizeof in H1.
   rewrite <-H1, nat_of_Z_of_nat.
   rewrite getN_full; auto.
   rewrite H. rewrite getN_full; auto.
  +simpl. generalize H H; intros. apply mvl_match_length in H.
   apply mvl_match_sizeof in H1.
   rewrite <-H1, nat_of_Z_of_nat.
   rewrite getN_full; auto.
   rewrite H. rewrite getN_full; auto.
  +rewrite H0 in *. simpl in *.
   generalize H. intros.
   generalize H2; intros.
   apply IHeval_offset in H2; auto.
   apply eval_offset_pos in H3.
   generalize (sizeof_pos t0). intros.
   rewrite H0 in *. simpl in *.
   generalize (Zle_max_l 1 z) (Zle_max_r 1 z); intros.
   rewrite Z2Nat.inj_add; try omega.
   rewrite Z2Nat.inj_mul in *; try omega.
   inv H2; simpl in *; try congruence.
   apply mvl_array_match_getN with (nat_of_Z (Z.max 0 z)); auto.
   apply Z2Nat.inj_lt; try omega.
   eapply mvl_match_length in H4; eauto.
   apply mvl_match_sizeof in H4. rewrite <-H4 in *.
   apply Nat2Z.inj_le. rewrite Nat2Z.inj_add, nat_of_Z_eq; try omega.
   rewrite Nat2Z.inj_mul; try omega. repeat rewrite nat_of_Z_eq; try omega.
   apply Zmult_le_0_compat; omega.
  +rewrite H0 in *. simpl typeof in *.
   generalize H; intros A. apply eval_offset_pos in A.
   apply IHeval_offset in H3; auto.
   change (sizeof (Tstruct sid fld)) with (sizeof_fld fld) in *.
   inv H3; simpl in *; try congruence.
   generalize H1; intros. eapply field_offset_in_range_simpl in H3; eauto.
   rewrite Z2Nat.inj_add; try omega.
   generalize (sizeof_pos t0). intros.
   cut ((Z.to_nat delta + nat_of_Z (sizeof t0) <= nat_of_Z (sizeof_fld fld))%nat). intros.
   repeat rewrite getN_app with (n1:=nat_of_Z (sizeof_fld fld)); auto.
   replace delta with (delta - 0) by omega.
   eapply mvl_struct_match_getN; eauto; try omega.
   -apply mvl_match_length in H7; auto.
   -apply Nat2Z.inj_le. rewrite Nat2Z.inj_add.
    repeat rewrite nat_of_Z_eq; try omega.
Qed.

Lemma eval_offset_mvl_alloc_sube:
  forall t a o,
  eval_offset t a o ->
  forall m,
  mvl_alloc m t ->
  mvl_alloc (getN (nat_of_Z (sizeof (typeof a))) (nat_of_Z o) m) (typeof a).
Proof.
  intros.
  apply mvl_match_mvl_alloc with (m1:=getN (nat_of_Z (sizeof (typeof a))) (nat_of_Z o) m).
  eapply eval_offset_mvl_match_sube; eauto.
  eapply mvl_match_self; eauto.
Qed.

Lemma getN_first_app:
  forall n1 n2 l1 l2, n1 = length l1 ->
  getN (n1+n2) 0 (l1 ++ l2) = l1 ++ getN n2 0 l2.
Proof.
  unfold getN, getn. intros. subst. simpl.
  rewrite firstn_length_app2; try omega.
  f_equal. f_equal. omega.
Qed.

Lemma getN_first_simpl:
  forall n l1 l2, n = length l1 ->
  getN n 0 (l1 ++ l2) = l1.
Proof.
  intros. replace n with (n + 0)%nat; try omega.
  rewrite getN_first_app; auto.
  unfold getN,getn. simpl. rewrite <-app_nil_end; auto.
Qed.

Lemma mvl_array_match_setn:
  forall m m' t n m1 m2 m3 m1' m2' m3' i,
  mvl_array_match (m1 ++ m2 ++ m3) (m1' ++ m2' ++ m3') t n ->
  mvl_match m m' t ->
  length m1 = length m1' ->
  length m2 = length m2' ->
  length m3 = length m3' ->
  length m2 = length m' ->
  (length m1 = nat_of_Z (sizeof t) * i)%nat ->
  mvl_array_match (m1 ++ m ++ m3) (m1' ++ m' ++ m3') t n.
Proof.
  induction n; simpl; intros; inv H; try omega.
  +destruct m1,m2,m3, m1', m2', m3'; simpl in *; try congruence.
   apply mvl_match_length in H0.
   destruct m, m'; simpl in *; try omega.
   constructor.
  +destruct i.
   -rewrite mult_0_r in H5.
    destruct m1,m1'; simpl in *; try omega.
    econstructor; eauto.
    apply app_length_equal_inv in H6. destruct H6. subst.
    apply app_length_equal_inv in H7. destruct H7. subst.
    auto.
    left. rewrite <-H2. apply mvl_match_length in H9; auto.
    left. apply mvl_match_sizeof in H9. generalize H0; intros A.
    apply mvl_match_sizeof in H0. apply mvl_match_length in A.
    rewrite <-H9 in H0. apply Nat2Z.inj in H0. congruence.
   -change (S i) with (1 + i)%nat in *.
    rewrite mult_plus_distr_l, mult_1_r in H5.
    generalize (firstn_skipn (nat_of_Z (sizeof t)) m1).
    generalize (firstn_skipn (nat_of_Z (sizeof t)) m1').
    intros A A1. rewrite <-A,<-A1. rewrite <-A in H7.
    rewrite <-A1 in H6. repeat rewrite app_ass in *.
    assert(A2: forall (l1:mvl) l2 l3 l4, l1++l2 ++ l3 ++ l4 = l1 ++ (l2++l3)++l4).
     intros. repeat rewrite <-app_ass. auto.
    repeat rewrite A2.
    apply app_length_equal_inv in H6. destruct H6. subst m0 ml1.
    apply app_length_equal_inv in H7. destruct H7. subst m4 ml2.
    econstructor 2; eauto.
    *repeat rewrite app_ass. apply IHn with m2 m2' i; auto.
     repeat rewrite skipn_length. congruence.
     rewrite skipn_length. rewrite min_l.
     rewrite H5. eauto with *.
     rewrite H5. eauto with *.
    *left. apply mvl_match_length in H9. rewrite <-H9.
     repeat rewrite firstn_length. congruence.
    *left. rewrite firstn_length. rewrite min_l; try omega.
     apply mvl_match_sizeof in H9. rewrite <-H9.
      rewrite nat_of_Z_of_nat. auto.
     rewrite H5. eauto with *.
Qed.

Lemma mvl_struct_match_setn:
  forall m m' f fld m1 m2 m3 m1' m2' m3' pos i t delta,
  mvl_struct_match (m1 ++ m2 ++ m3) (m1' ++ m2' ++ m3') fld f pos ->
  mvl_match m m' t ->
  field_offset_rec i fld pos = OK delta ->
  field_type i fld = OK t ->
  length m1 = length m1' ->
  length m2 = length m2' ->
  length m3 = length m3' ->
  length m2 = length m' ->
  (length m1 = nat_of_Z (delta - pos))%nat ->
  mvl_struct_match (m1 ++ m ++ m3) (m1' ++ m' ++ m3') fld f pos.
Proof.
  induction fld; simpl; intros; inv H; try congruence.
  generalize H17 H17 H0 H0. intros A A1 A2 A3.
  apply mvl_match_length in A. apply mvl_match_sizeof in A1.
  apply mvl_match_sizeof in A2. apply mvl_match_length in A3.
  compare i0 i; intros; subst.
  +rewrite peq_true in *. inv H1. inv H2.
   apply app_length_equal_inv in H8; auto. destruct H8. subst.
   apply app_length_equal_inv in H9; auto. destruct H9. subst.
   apply app_length_equal_inv in H1; auto. destruct H1. subst.
   apply app_length_equal_inv in H2; auto. destruct H2. subst.
   econstructor 2; eauto.
   -left. congruence.
   -left. rewrite <-A1 in A2. apply Nat2Z.inj in A2. congruence.
   -left. rewrite <-H14 in H7. rewrite nat_of_Z_of_nat in H7; auto.
  +rewrite peq_false in *; auto.
   generalize (firstn_skipn (length m0) m1).
   generalize (firstn_skipn (length m0) m1').
   intros A4 A5. rewrite <-A4,<-A5. rewrite <-A4 in H9.
   rewrite <-A5 in H8. repeat rewrite app_ass in *.
   generalize (firstn_skipn (length m4) (skipn (length m0) m1)).
   generalize (firstn_skipn (length m4) (skipn (length m0) m1')).
   intros A6 A7. rewrite <-A6,<-A7. rewrite <-A6 in H9.
   rewrite <-A7 in H8. repeat rewrite app_ass in *.
   assert(A8: forall (l1:mvl) l2 l3 l4 l5, l1++l2 ++ l3 ++ l4 ++ l5 = l1 ++ l2 ++(l3++l4++l5)).
     intros. repeat rewrite <-app_ass. auto.
   repeat rewrite A8.
   generalize H1; intros A9. eapply field_offset_rec_in_range in A9; eauto.
   cut ((length m0 + length m4 <= length m1)%nat). intros A10.
   apply app_length_equal_inv in H8. destruct H8. rewrite <-H in *.
   apply app_length_equal_inv in H9. destruct H9. rewrite <-H9 in *.
   apply app_length_equal_inv in H8. destruct H8. rewrite <-H8 in *.
   apply app_length_equal_inv in H10. destruct H10. rewrite <-H10 in *.
   repeat rewrite <-skipn_add in *.
   econstructor 2; eauto.
   -apply IHfld with m2 m2' i0 t0 delta; auto.
    *congruence.
    *repeat rewrite skipn_length. congruence.
    *rewrite skipn_length. rewrite min_l; try omega.
     apply Nat2Z.inj. rewrite nat_of_Z_eq.
     rewrite Nat2Z.inj_sub, Nat2Z.inj_add; try omega.
     rewrite H14,A1, H7. rewrite nat_of_Z_eq; try omega.
     omega.
   -left. rewrite firstn_length. rewrite min_l; auto.
    rewrite skipn_length. rewrite min_l; try omega.
   -left. rewrite firstn_length. rewrite min_l; auto.
    rewrite skipn_length. rewrite min_l; try omega.
   -left. rewrite firstn_length. rewrite min_l; omega.
   -left. rewrite firstn_length. rewrite min_l; omega.
   -apply Nat2Z.inj_le. rewrite Nat2Z.inj_add.
    rewrite H14,A1,H7. rewrite nat_of_Z_eq; try omega.
Qed.

Lemma mvl_match_setn_sube:
  forall t a ofs,
  eval_offset t a ofs ->
  forall m1 m2 m3 m1' m2' m3' m m',
  mvl_match (m1++m2++m3) (m1'++m2'++m3') t ->
  mvl_match m m' (typeof a) ->
  length m1 = length m1' ->
  length m2 = length m2' ->
  length m3 = length m3' ->
  length m2 = length m' ->
  length m1 = nat_of_Z ofs ->
  mvl_match (m1++m++m3) (m1'++m'++m3') t.
Proof.
  induction 1; simpl; intros.
  +destruct m1, m1'; simpl in *; try omega.
   generalize H H0 H0; intros. apply mvl_match_sizeof in H.
   apply mvl_match_sizeof in H0. apply mvl_match_length in H7.
   rewrite app_length,H4, <-H0 in *.
   apply Nat2Z.inj in H.
   destruct m3,m3'; simpl in *; try omega.
   repeat rewrite <-app_nil_end; auto.
  +destruct m1, m1'; simpl in *; try omega.
   generalize H H0 H0; intros. apply mvl_match_sizeof in H.
   apply mvl_match_sizeof in H0. apply mvl_match_length in H7.
   rewrite app_length,H4, <-H0 in *.
   apply Nat2Z.inj in H.
   destruct m3,m3'; simpl in *; try omega.
   repeat rewrite <-app_nil_end; auto.
  +rewrite H0 in *. generalize H. intros A.
   apply eval_offset_pos in A.
   generalize H3 H3 H2; intros B B1 B3.
   apply mvl_match_sizeof in B. apply mvl_match_length in B1.
   apply mvl_match_sizeof in B3. repeat rewrite app_length in B3.
   rewrite <-firstn_skipn with (l:=m1) (n:=nat_of_Z ofs).
   rewrite <-firstn_skipn with (l:=m1') (n:=nat_of_Z ofs).
   rewrite <-firstn_skipn with (l:=m3) (n:=nat_of_Z (sizeof t0 * Z.max 0 z - (sizeof t0 + sizeof t0 * i))).
   rewrite <-firstn_skipn with (l:=m3') (n:=nat_of_Z (sizeof t0 * Z.max 0 z - (sizeof t0 + sizeof t0 * i))).
   rewrite <-firstn_skipn with (l:=m1) (n:=nat_of_Z ofs) in H2.
   rewrite <-firstn_skipn with (l:=m1') (n:=nat_of_Z ofs) in H2.
   rewrite <-firstn_skipn with (l:=m3) (n:=nat_of_Z (sizeof t0 * Z.max 0 z - (sizeof t0 + sizeof t0 * i))) in H2.
   rewrite <-firstn_skipn with (l:=m3') (n:=nat_of_Z (sizeof t0 * Z.max 0 z - (sizeof t0 + sizeof t0 * i))) in H2.
   assert(A1: forall (l1:mvl) l2 l3 l4 l5, (l1++l2) ++ l3 ++ (l4++l5) = l1 ++ (l2++l3++l4) ++l5).
     intros. repeat rewrite <-app_ass. auto.
   repeat rewrite A1 in *.
   rewrite Z2Nat.inj_add in H8; try omega.
   cut (length (firstn (nat_of_Z ofs) m1) = nat_of_Z ofs).
   cut (length (firstn (nat_of_Z ofs) m1') = nat_of_Z ofs). intros A2 A3.
   cut (0 <= sizeof t0 * i). intros A4.
   generalize (sizeof_pos t0). intros A5.
   cut (sizeof t0 + sizeof t0 * i <= sizeof t0 * Z.max 0 z). intros A6.
   cut (Z.to_nat (sizeof t0 * Z.max 0 z) - Z.to_nat (sizeof t0 + sizeof t0 * i) <=length m3')%nat. intros A7.
   eapply IHeval_offset; eauto.
   -eapply eval_offset_mvl_match_sube in H2; eauto.
    rewrite H0 in *.
    rewrite <-plus_0_l with (nat_of_Z ofs) in H2.
    repeat rewrite getN_app_skipn in H2. simpl in *.
    rewrite skipn_length_app in H2; try omega. rewrite A3, minus_diag in H2. simpl in *.
    rewrite skipn_length_app in H2; try omega. rewrite A2, minus_diag in H2. simpl in *.
    inv H2; simpl in *; try congruence. constructor 3; auto.
    assert (A8: (nat_of_Z (sizeof t0 * Z.max 0 z) =
                nat_of_Z (sizeof t0 * i) + (nat_of_Z (sizeof t0) + nat_of_Z (sizeof t0 * Z.max 0 z - (sizeof t0 + sizeof t0 * i))))%nat).
      rewrite <-Z2Nat.inj_add; try omega.
      rewrite <-Z2Nat.inj_add; try omega.
      change nat_of_Z with Z.to_nat. f_equal. omega.
    rewrite A8 in H12. repeat rewrite app_ass in H12.
    change nat_of_Z with Z.to_nat in *.
    rewrite getN_first_app, getN_first_app, getN_first_app, getN_first_app in H12.
    rewrite getN_first_simpl, getN_first_simpl in H12.
    *eapply mvl_array_match_setn with (i:=nat_of_Z i); eauto.
     repeat rewrite skipn_length. congruence.
     repeat rewrite firstn_length. congruence.
     rewrite skipn_length.
     rewrite <-Z2Nat.inj_mul; try omega.
     rewrite min_l; try omega.
    *rewrite firstn_length. rewrite min_l; try omega.
     rewrite Z2Nat.inj_sub; try omega.
    *rewrite firstn_length. rewrite min_l; try omega.
     rewrite Z2Nat.inj_sub; try omega.
    *rewrite <-B. rewrite nat_of_Z_of_nat. congruence.
    *rewrite skipn_length. rewrite min_l; try omega.
    *rewrite H7. rewrite <-B. rewrite nat_of_Z_of_nat; try omega.
    *rewrite skipn_length. rewrite min_l; try omega.
   -repeat rewrite firstn_length. congruence.
   -repeat rewrite app_length. repeat rewrite firstn_length.
    repeat rewrite skipn_length. congruence.
   -repeat rewrite skipn_length. congruence.
   -repeat rewrite app_length. repeat rewrite firstn_length.
    repeat rewrite skipn_length. congruence.
   -rewrite H7, H8,<-B1 in B3.
    repeat rewrite Nat2Z.inj_add in B3; try omega.
    rewrite B in B3. rewrite <-B3, H0 in A.
    simpl in A.
    rewrite nat_of_Z_eq in A; try omega.
    rewrite nat_of_Z_eq in A; try omega.
    apply Nat2Z.inj_le. rewrite Nat2Z.inj_sub; try omega.
    rewrite nat_of_Z_eq; try omega.
    rewrite nat_of_Z_eq; try omega.
    apply Z2Nat.inj_le; auto; try omega.
   -apply Zle_trans with (sizeof t0 * (1 + i)).
    rewrite Z.mul_add_distr_l; omega.
    apply Zmult_le_compat_l; try omega.
   -apply Zmult_le_0_compat; omega.
   -rewrite firstn_length. rewrite min_l; try omega.
    change nat_of_Z with Z.to_nat. omega.
   -rewrite firstn_length. rewrite min_l; try omega.
    change nat_of_Z with Z.to_nat. omega.
   -apply Zmult_le_0_compat; omega.
  +rewrite H0 in *. generalize H. intros A.
   apply eval_offset_pos in A.
   generalize H4 H4 H3; intros B B1 B3.
   apply mvl_match_sizeof in B. apply mvl_match_length in B1.
   apply mvl_match_sizeof in B3. repeat rewrite app_length in B3.
   generalize H1; intros B4.
   eapply field_offset_in_range with (sid:=sid) in B4; eauto.
   rewrite <-firstn_skipn with (l:=m1) (n:=nat_of_Z ofs).
   rewrite <-firstn_skipn with (l:=m1') (n:=nat_of_Z ofs).
   rewrite <-firstn_skipn with (l:=m3) (n:=nat_of_Z (sizeof (Tstruct sid fld) - (delta + sizeof t0))).
   rewrite <-firstn_skipn with (l:=m3') (n:=nat_of_Z (sizeof (Tstruct sid fld) - (delta + sizeof t0))).
   rewrite <-firstn_skipn with (l:=m1) (n:=nat_of_Z ofs) in H3.
   rewrite <-firstn_skipn with (l:=m1') (n:=nat_of_Z ofs) in H3.
   rewrite <-firstn_skipn with (l:=m3) (n:=nat_of_Z (sizeof (Tstruct sid fld) - (delta + sizeof t0))) in H3.
   rewrite <-firstn_skipn with (l:=m3') (n:=nat_of_Z (sizeof (Tstruct sid fld) - (delta + sizeof t0))) in H3.
   assert(A1: forall (l1:mvl) l2 l3 l4 l5, (l1++l2) ++ l3 ++ (l4++l5) = l1 ++ (l2++l3++l4) ++l5).
     intros. repeat rewrite <-app_ass. auto.
   repeat rewrite A1 in *.
   rewrite Z2Nat.inj_add in H9; try omega.
   cut (length (firstn (nat_of_Z ofs) m1) = nat_of_Z ofs).
   cut (length (firstn (nat_of_Z ofs) m1') = nat_of_Z ofs). intros A2 A3.
   generalize (sizeof_pos t0). intros A5.
   cut (Z.to_nat (sizeof (Tstruct sid fld)) - Z.to_nat (delta + sizeof t0) <=length m3')%nat. intros A7.
   eapply IHeval_offset; eauto.
   -eapply eval_offset_mvl_match_sube in H3; eauto.
    rewrite H0 in *.
    rewrite <-plus_0_l with (nat_of_Z ofs) in H3.
    repeat rewrite getN_app_skipn in H3. rewrite plus_0_l in H3.
    rewrite skipn_length_app in H3; try omega. rewrite A3, minus_diag in H3. simpl in H3.
    rewrite skipn_length_app in H3; try omega. rewrite A2, minus_diag in H3. simpl in H3.
    inv H3; simpl in *; try congruence. constructor 4; auto.
    remember (align (sizeof_struct _ _) _).
    assert (A8: (nat_of_Z z =
                nat_of_Z delta + (nat_of_Z (sizeof t0) + nat_of_Z (z - (delta + (sizeof t0)))))%nat).
      rewrite <-Z2Nat.inj_add; try omega.
      rewrite <-Z2Nat.inj_add; try omega.
      change nat_of_Z with Z.to_nat. f_equal. omega.
    rewrite A8 in H13. repeat rewrite app_ass in H13.
    change nat_of_Z with Z.to_nat in *.
    rewrite getN_first_app, getN_first_app,getN_first_app,getN_first_app in H13.
    rewrite getN_first_simpl, getN_first_simpl in H13.
    *eapply mvl_struct_match_setn; eauto.
     repeat rewrite skipn_length. congruence.
     repeat rewrite firstn_length. congruence.
     rewrite skipn_length. rewrite min_l; try omega.
     rewrite Zminus_0_r. rewrite H9. eauto with *.
    *rewrite firstn_length. rewrite min_l; try omega.
     rewrite Z2Nat.inj_sub; try omega.
    *rewrite firstn_length. rewrite min_l; try omega.
     rewrite Z2Nat.inj_sub; try omega.
    *rewrite <-B. rewrite nat_of_Z_of_nat. congruence.
    *rewrite skipn_length. rewrite min_l; try omega.
    *rewrite H8. rewrite <-B. rewrite nat_of_Z_of_nat; try omega.
    *rewrite skipn_length. rewrite min_l; try omega.
   -repeat rewrite firstn_length. congruence.
   -repeat rewrite app_length. repeat rewrite firstn_length.
    repeat rewrite skipn_length. congruence.
   -repeat rewrite skipn_length. congruence.
   -repeat rewrite app_length. repeat rewrite firstn_length.
    repeat rewrite skipn_length. congruence.
   -rewrite H7, H8,H9,<-B1 in B3.
    repeat rewrite Nat2Z.inj_add in B3; try omega.
    rewrite B in B3. rewrite <-B3, H0 in A.
    rewrite nat_of_Z_eq in A; try omega.
    rewrite nat_of_Z_eq in A; try omega.
    apply Nat2Z.inj_le. rewrite Nat2Z.inj_sub; try omega.
    rewrite nat_of_Z_eq; try omega.
    rewrite nat_of_Z_eq; try omega.
    apply Z2Nat.inj_le; auto; try omega.
   -rewrite firstn_length. rewrite min_l; try omega.
    change nat_of_Z with Z.to_nat. omega.
   -rewrite firstn_length. rewrite min_l; try omega.
    change nat_of_Z with Z.to_nat. omega.
Qed.

Lemma mvl_match_setn:
  forall t a ofs,
  eval_offset t a ofs ->
  forall m1 m2 m',
  mvl_match m1 m2 t ->
  mvl_alloc m' (typeof a) ->
  mvl_match (setN m' (nat_of_Z ofs) m1) (setN m' (nat_of_Z ofs) m2) t.
Proof.
  unfold setN, replace_map. intros.
  generalize H0 H0 H1 H; intros A A1 A2 A3.
  apply mvl_match_length in A. apply mvl_match_sizeof in A1.
  apply mvl_type_length in A2. apply eval_offset_pos in A3.
  rewrite <-firstn_skipn with (l:=m1) (n:=nat_of_Z ofs) in H0.
  rewrite <-firstn_skipn with (l:=m2) (n:=nat_of_Z ofs) in H0.
  rewrite <-firstn_skipn with (l:=skipn (nat_of_Z ofs) m1) (n:=length m') in H0.
  rewrite <-firstn_skipn with (l:=skipn (nat_of_Z ofs) m2) (n:=length m') in H0.
  repeat rewrite <-skipn_add in H0.
  destruct A3 as [A3 A4]. rewrite <-A1 in A4.
  rewrite <-A2 in *. generalize A4; intros A5.
  apply Z2Nat.inj_le in A4; try omega.
  rewrite Z2Nat.inj_add, nat_of_Z_of_nat,nat_of_Z_of_nat in A4; try omega.
  eapply mvl_match_setn_sube; eauto.
  +eapply mvl_match_self; eauto.
  +repeat rewrite firstn_length. congruence.
  +repeat rewrite firstn_length.
   repeat rewrite skipn_length. congruence.
  +repeat rewrite skipn_length. congruence.
  +rewrite firstn_length, skipn_length.
   rewrite min_l; try omega.
   change nat_of_Z with Z.to_nat.
   rewrite min_l; try omega.
  +rewrite firstn_length.
   change nat_of_Z with Z.to_nat.
   rewrite min_l; try omega.
Qed.

Lemma mvl_alloc_setn:
  forall t a ofs m,
  eval_offset t a (Int.unsigned ofs) ->
  mvl_alloc m t ->
  forall m', mvl_alloc m' (typeof a) ->
  (nat_of_Z (Int.unsigned ofs) + length m' <= length m)%nat ->
  mvl_alloc (setN m' (nat_of_Z (Int.unsigned ofs)) m) t.
Proof.
  intros.
  eapply mvl_match_mvl_alloc with (m1:=setN m' (nat_of_Z (Int.unsigned ofs)) m); eauto.
  eapply mvl_match_setn; eauto.
  eapply mvl_match_self; eauto.
Qed.

Definition locenv_match_ret(te eh: locenv)(id: ident): Prop :=
  exists m1 m2 t, te ! id = Some (m1,t)
    /\ eh ! id = Some (m2,t)
    /\ mvl_match m1 m2 t.

Definition locenv_match_rets(te eh: locenv)(ids: list ident): Prop :=
  forall id, In id ids -> locenv_match_ret te eh id.


Definition subenv_ids(P: ident*func -> env -> Prop) (se: subenv)(l: list calldef): Prop :=
  forall c, In c l ->
    exists fd el,  find_funct (node_block prog1) (callid c) = Some fd
     /\ se ! (instid c) = Some el
     /\ Forall (P fd) el.

Inductive env_ids_none(nd: ident*func): env ->  Prop :=
  | env_ids_none_: forall eh1 se1,
     ptree_ids_none (map fst (nd_rets (snd nd))) eh1 ->
     subenv_ids env_ids_none se1 (if nd_kind (snd nd) then instidof (nd_stmt (snd nd)) else nil) ->
     env_ids_none nd (mkenv eh1 se1).

Inductive env_ids_some(nd: ident*func): env ->  Prop :=
  | env_ids_some_: forall eh2 se2,
     ptree_vars_some (nd_rets (snd nd)) eh2 ->
     subenv_ids env_ids_some se2 (if nd_kind (snd nd) then instidof (nd_stmt (snd nd)) else nil) ->
     env_ids_some nd (mkenv eh2 se2).

Lemma encode_val_mvl_type:
  forall ty chunk v,
  access_mode ty = By_value chunk ->
  mvl_alloc (encode_val chunk v) ty.
Proof.
  intros. constructor; auto.
  destruct ty; auto; inv H.
  rewrite encode_val_length. unfold size_chunk_nat.
  erewrite sizeof_chunk_eq;eauto.
  generalize (sizeof_pos ty). intros.
  rewrite nat_of_Z_eq; try omega.
Qed.

Lemma store_env_ptree_vars_some:
  forall gc eh2 id ofs v eh2' rets te2 a,
  store_env (typeof a) eh2 id ofs v eh2' ->
  ptree_vars_some rets eh2 ->
  has_type v (typeof a) ->
  eval_lvalue gc te2 eh2 a id ofs Sid ->
  ptree_vars_some rets eh2'.
Proof.
  intros. inv H. red; intros.
  apply H0 in H. destruct H as [m1 [? ?]].
  compare id id0; intros; subst.
  +rewrite PTree.gss. rewrite H3 in H. inv H.
   exists m'. split; auto.
   generalize (sizeof_pos ty) (Int.unsigned_range ofs). intros A A1.
   inv H5.
   -unfold store in *. destruct (valid_access_dec _ _ _); inv H7.
    apply mvl_alloc_setn with a; eauto.
    *eapply eval_lvalue_eval_offset; eauto.
    *eapply encode_val_mvl_type; eauto.
    *rewrite encode_val_length. unfold size_chunk_nat.
     destruct v0 as [[? [? ?]] ?].
     rewrite <-Z2Nat.inj_add; try omega.
     apply Nat2Z.inj_le. rewrite nat_of_Z_eq; try omega.
   -unfold storebytes in *. destruct (range_perm_dec _ _ _); inv H7.
    apply mvl_alloc_setn with a; auto.
    *eapply eval_lvalue_eval_offset; eauto.
    *eapply mvl_type_alloc; eauto.
     eapply has_type_mvl_inv; eauto.
    *destruct r as [? [? ?]].
     apply Nat2Z.inj_le; try omega.
     rewrite Nat2Z.inj_add.
     rewrite nat_of_Z_eq; try omega.
   +rewrite PTree.gso; eauto.
Qed.

Lemma alloc_variables_ptree_vars_some:
  forall e al e',
  alloc_variables e al e' ->
  list_norepet (map fst al) ->
  ptree_vars_some al e'.
Proof.
  induction 1; simpl; intros; auto.
  +red; intros. inv H0.
  +inv H0. red; simpl; intros. destruct H0.
   -inv H0. exists (alloc (sizeof ty0)).
    split. erewrite alloc_variables_notin_eq; eauto.
    rewrite PTree.gss; auto.
    apply mvl_alloc_self; auto.
   -eapply IHalloc_variables; eauto.
Qed.

Lemma mvl_match_is_byte_eq:
  forall m1 m2 t chunk,
  mvl_match m1 m2 t ->
  access_mode t = By_value chunk ->
  is_bytes m1 ->
  m2 = m1.
Proof.
  induction 1; simpl; intros; try congruence.
  destruct m1,m2; simpl in *; try omega.
  auto.
  inv H0. inv H4. destruct m; simpl in *; tauto.
Qed.

Lemma mvl_match_load_mvl:
  forall a m1 ofs v m2 t,
  load_mvl (typeof a) m1 ofs v ->
  eval_offset t a (Int.unsigned ofs) ->
  mvl_match m1 m2 t ->
  has_type v (typeof a) ->
  load_mvl (typeof a) m2 ofs v.
Proof.
  intros.
  eapply eval_offset_mvl_match_sube in H0; eauto.
  inv H.
  +constructor 1 with chunk;auto.
   unfold load in *.
   destruct (valid_access_dec m1 chunk _); try congruence.
   rewrite pred_dec_true; auto.
   -rewrite <-H4. f_equal.
    unfold size_chunk_nat in *. erewrite sizeof_chunk_eq in *; eauto.
    eapply mvl_match_is_byte_eq; eauto.
    unfold decode_val in *. destruct (proj_bytes _) eqn:?; try congruence.
    eapply proj_bytes_is_bytes; eauto.
   -eapply length_valid_access; eauto.
    eapply mvl_match_length in H1; eauto.
  +constructor 2; auto.
   unfold loadbytes in *.
   destruct (range_perm_dec m1 _ _); inv H4.
   rewrite pred_dec_true.
   -eapply has_type_mvl_inv in H2; eauto. destruct H2.
    f_equal. eapply mvl_match_mvl_type_eq in H0; eauto.
   -eapply length_range_perm; eauto.
    apply mvl_match_length with (ty:=t); eauto.
Qed.

Lemma locenv_match_rets_in:
  forall te1 eh2 ids id,
  locenv_match_rets te1 eh2 ids ->
  in_list id ids = true ->
  locenv_match_ret te1 eh2 id.
Proof.
  intros. apply H.
  apply in_list_true_in; auto.
Qed.

Lemma locenv_match_ret_set_same:
  forall id t m1 m2 te1 eh2,
  mvl_match m1 m2 t ->
  locenv_match_ret (PTree.set id (m1,t) te1) (PTree.set id (m2,t) eh2) id.
Proof.
  unfold locenv_match_ret. intros.
  repeat rewrite PTree.gss in *. exists m1,m2,t; eauto.
Qed.

Lemma locenv_match_rets_set_other_left:
  forall te1 eh2 ids b m,
  locenv_match_rets te1 eh2 ids ->
  in_list b ids = false ->
  locenv_match_rets (PTree.set b m te1) eh2 ids.
Proof.
  intros. red; intros.
  apply in_list_false_notin in H0.
  red; intros. rewrite PTree.gso.
  apply H; auto. congruence.
Qed.

Lemma locenv_match_rets_set_other_right:
  forall te1 eh2 ids b m,
  locenv_match_rets te1 eh2 ids ->
  in_list b ids = false ->
  locenv_match_rets te1 (PTree.set b m eh2) ids.
Proof.
  intros. red; intros.
  apply in_list_false_notin in H0.
  red; intros. rewrite PTree.gso.
  apply H; auto. congruence.
Qed.

Lemma store_env_locenv_match_ret:
  forall gc a te1 id ofs v te1' te2 eh2,
  store_env (typeof a) te1 id ofs v te1' ->
  locenv_match_ret te1 eh2 id ->
  has_type v (typeof a) ->
  eval_lvalue gc te2 eh2 a id ofs Sid ->
  exists eh2', store_env (typeof a) eh2 id ofs v eh2'
    /\ locenv_match_ret te1' eh2' id.
Proof.
  intros. inv H.
  destruct H0 as [m0 [m1 [? [? [? ?]]]]]; auto.
  generalize H6; intros.
  rewrite H in H3. inv H3.
  apply mvl_match_length in H6.
  generalize (Int.unsigned_range ofs) (sizeof_pos (typeof a)). intros A A1.
  inv H5.
  +destruct valid_access_store with m1 chunk (Int.unsigned ofs) v as [m1' ?]; auto.
   apply length_valid_access with m; auto.
   eapply store_valid_access_2;eauto.
   eapply store_valid_access;eauto.
   exists (PTree.set id (m1',t) eh2). split.
   -constructor 1 with m1; auto. congruence.
    constructor 1 with chunk; auto.
   -apply locenv_match_ret_set_same; auto.
    unfold store in *.
    destruct (valid_access_dec m chunk _); inv H8.
    destruct (valid_access_dec m1 chunk _); inv e.
    apply mvl_match_setn with a; auto.
    *eapply eval_lvalue_eval_offset; eauto.
    *econstructor; eauto.
     destruct (typeof a); auto; inv H3.
     rewrite encode_val_length.
     unfold size_chunk_nat. erewrite sizeof_chunk_eq; eauto.
     rewrite nat_of_Z_eq; try omega.
  +destruct range_perm_store_bytes with m1 (Int.unsigned ofs) m0 as [m1' ?];auto.
   apply length_range_perm with m; auto.
   eapply storebytes_range_perm_2;eauto.
   eapply storebytes_range_perm;eauto.
   exists (PTree.set id (m1',t) eh2). split.
   -constructor 1 with m1; auto. congruence.
    constructor 2; auto.
   -apply locenv_match_ret_set_same; auto.
    unfold storebytes in *.
    destruct (range_perm_dec m _ _); inv H8.
    destruct (range_perm_dec m1 _ _); inv e.
    apply mvl_match_setn with a; auto.
    *eapply eval_lvalue_eval_offset; eauto.
    *eapply mvl_type_alloc; eauto.
     apply has_type_mvl_inv; auto.
Qed.

Lemma loenv_match_rets_getvars:
  forall te rets vrs,
  Lsem.locenv_getvars te rets vrs ->
  has_types vrs (map snd rets) ->
  forall eh, locenv_match_rets te eh (map fst rets) ->
  Lsem.locenv_getvars eh rets vrs.
Proof.
  induction 1; simpl; intros.
  +constructor.
  +inv H1. constructor 2; auto.
   -destruct H as [m1 [? [? ?]]].
    destruct H2 with (id:=fst x) as [m0 [m2 [t0 [? [? ?]]]]]; simpl; auto.
    rewrite H4 in H. inv H.
    exists m2. repeat split; auto.
    apply mvl_match_length in H7. congruence.
    change (snd x) with (typeof (Svar (fst x) (snd x))); auto.
    eapply mvl_match_load_mvl; eauto.
    constructor 1; auto.
   -apply IHForall2; auto.
    red; intros. apply H2; simpl; auto.
Qed.

Lemma ptree_match_eval_lvalue:
  forall gc te1 id m ty ids te2 eh2,
  te1 ! id = Some (m, ty) ->
  ptree_noids_match ids te1 te2 ->
  locenv_match_rets te1 eh2 ids ->
  eval_lvalue gc te2 eh2 (trans_v ids id ty) id Int.zero (if in_list id ids then Sid else Lid).
Proof.
  unfold trans_v. intros. remember (in_list id ids).
  destruct b; symmetry in Heqb.
  +apply in_list_true_in in Heqb.
   apply H1 in Heqb.
   destruct Heqb as [m0 [m1 [? [? [? ?]]]]]; auto.
   rewrite H2 in H. inv H.
   constructor 3 with m1; auto.
  +constructor 1 with m; auto.
   rewrite <-H0; auto. apply in_list_false_notin; auto.
Qed.

Lemma eval_sexp_match:
forall gc te1 eh1,
(
  forall a v,
  eval_sexp gc te1 eh1 a v ->
  forall te2 eh2 ids, locenv_match eh1 eh2 ->
  ptree_noids_match ids te1 te2 ->
  locenv_match_rets te1 eh2 ids ->
  ptree_ids_none ids te2 ->
  eval_sexp gc te2 eh2 (trans_sexp (trans_v ids) a) v
)
/\
(
  forall a id o k,
  eval_lvalue gc te1 eh1 a id o k ->
  forall te2 eh2 ids, locenv_match eh1 eh2 ->
  ptree_noids_match ids te1 te2 ->
  locenv_match_rets te1 eh2 ids ->
  ptree_ids_none ids te2 ->
  match k with
  | Gid | Sid =>
    eval_lvalue gc te2 eh2 (trans_sexp (trans_v ids) a) id o k
  | Lid =>
    eval_lvalue gc te2 eh2 (trans_sexp (trans_v ids) a) id o (if in_list id ids then Sid else k)
  | Aid => False
  end
).
Proof.
 intros until eh1.
 apply eval_sexp_lvalue_ind; intros; simpl in *.
 +constructor; simpl; auto.
 +constructor 2 with v1; auto.
  rewrite trans_sexp_typeof; auto.
 +constructor 3 with v1 v2; auto;
  repeat rewrite trans_sexp_typeof; auto.
 +constructor 4 with v1; auto.
  rewrite trans_sexp_typeof; auto.
 +generalize H3; intros A1. eapply H0 in A1; eauto.
  assert(A: (k = Gid \/ k = Sid) \/ (k = Lid \/ k = Aid)).
     destruct k; auto.
  destruct A as [A | A].
  -apply eval_Rlvalue with id ofs k; auto;
   destruct A; subst; simpl in *; auto;
   rewrite trans_sexp_typeof; auto.
   eapply load_env_match; eauto.
  -destruct A; subst; simpl in *; try tauto.
   destruct H1 as [m [t [? [? ?]]]].
   apply eval_Rlvalue with id ofs (if in_list id ids then Sid else Lid); auto;
   rewrite trans_sexp_typeof; auto.
   destruct (in_list id ids) eqn:?.
   *eapply locenv_match_rets_in in Heqb; eauto.
    destruct Heqb as [m0 [m2 [t0 [? [? ?]]]]]; auto.
    rewrite H9 in H1. inv H1.
    exists m2, t. repeat split; auto.
    apply mvl_match_length in H11. congruence.
    eapply mvl_match_load_mvl; eauto.
    eapply eval_lvalue_eval_offset; eauto.
   *exists m, t; repeat split; simpl; auto.
    rewrite <-H4; auto. apply in_list_false_notin; auto.
 +apply ptree_match_eval_lvalue with te1 m; auto.
 +unfold trans_v. destruct (in_list id ids) eqn:?.
  -apply in_list_true_in in Heqb.
   destruct H3 with id as [m0 [m1 [? [? [? ?]]]]]; auto.
   congruence.
  -constructor 2 with m; auto.
   eapply ptree_noids_match_ids_none; eauto.
 +constructor 3 with m; auto.
 +generalize H6; intros A. eapply H0 in A; eauto.
  destruct k; try tauto; apply eval_Saryacc with aid z; auto;
  rewrite trans_sexp_typeof; auto.
 +eapply H0 in H5; eauto.
  destruct k; try tauto; apply eval_Sfield with sid fld; auto;
  rewrite trans_sexp_typeof; auto.
Qed.

Lemma eval_sexps_match:
  forall gc te1 eh1 al vl,
  eval_sexps gc te1 eh1 al vl ->
  forall te2 eh2 ids, locenv_match eh1 eh2 ->
  ptree_noids_match ids te1 te2 ->
  locenv_match_rets te1 eh2 ids ->
  ptree_ids_none ids te2 ->
  eval_sexps gc te2 eh2 (trans_sexps (trans_v ids) al) vl.
Proof.
  induction 1; simpl; intros.
  +constructor.
  +constructor 2; auto.
   eapply eval_sexp_match; eauto.
   eapply IHForall2; eauto.
Qed.

Lemma store_env_ptree_match_exists_right:
  forall gc a te1 b ofs v te1',
  store_env (typeof a) te1 b ofs v te1' ->
  forall ids te2 eh2, in_list b ids = true ->
  ptree_noids_match ids te1 te2 ->
  locenv_match_rets te1 eh2 ids ->
  has_type v (typeof a) ->
  eval_lvalue gc te2 eh2 a b ofs Sid ->
  exists eh2', store_env (typeof a) eh2 b ofs v eh2'
    /\ locenv_match_rets te1' eh2' ids
    /\ ptree_noids_match ids te1' te2.
Proof.
  intros. generalize H0; intros A.
  apply in_list_true_in in A.
  apply H2 in A.
  eapply store_env_locenv_match_ret in A; eauto.
  destruct A as [eh2' [A A1]].
  exists eh2'. split; [| split]; auto.
  +inv H. inv A. red; intros. apply H2 in H10.
   compare b id; intros; subst; auto.
   red; intros. repeat rewrite PTree.gso; auto.
  +inv H. inv A. red. intros. rewrite PTree.gso; auto.
   apply in_list_true_in in H0. red; intros; subst; auto.
Qed.

Lemma store_env_ptree_match_exists_left:
  forall a te1 b ofs v te1' gc eh1,
  store_env (typeof a) te1 b ofs v te1' ->
  forall ids te2 eh2, in_list b ids = false ->
  ptree_noids_match ids te1 te2 ->
  locenv_match_rets te1 eh2 ids ->
  locenv_mvl_alloc te2 ->
  has_type v (typeof a) ->
  eval_lvalue gc te1 eh1 a b ofs Lid ->
  exists te2', store_env (typeof a) te2 b ofs v te2'
    /\ locenv_match_rets te1' eh2 ids
    /\ ptree_noids_match ids te1' te2'
    /\ locenv_mvl_alloc te2'.
Proof.
  intros. inv H.
  exists (PTree.set b (m',t) te2). repeat (split; auto).
  +constructor 1 with m; eauto.
   rewrite <-H1; auto. apply in_list_false_notin; auto.
  +apply locenv_match_rets_set_other_left; auto.
  +apply ptree_noids_match_setsame; auto.
  +red; intros. compare b id; intros; subst.
   -rewrite PTree.gss in H. inv H.
    generalize H6; intros A.
    rewrite H1 in H6. eapply H3 in H6; eauto.
    eapply eval_lvalue_eval_offset in H5; eauto.
    inv H8.
    *unfold store in *. destruct (valid_access_dec _ _ _); inv H9.
     apply mvl_alloc_setn with a; auto.
     eapply encode_val_mvl_type; eauto.
     rewrite encode_val_length. unfold size_chunk_nat.
     destruct v0 as [[? [? ?]] ?].
     rewrite <-Z2Nat.inj_add; try omega.
     apply Nat2Z.inj_le. rewrite nat_of_Z_eq; try omega.
    *unfold storebytes in *. destruct (range_perm_dec _ _ _); inv H9.
     apply mvl_alloc_setn with a; auto.
     eapply mvl_type_alloc; eauto.
     eapply has_type_mvl_inv; eauto.
     destruct r as [? [? ?]].
     apply Nat2Z.inj_le; try omega.
     rewrite Nat2Z.inj_add.
     rewrite nat_of_Z_eq; try omega.
    *apply in_list_false_notin; auto.
   -rewrite PTree.gso in H; auto.
    eapply H3; eauto.
Qed.

Lemma locenv_setvarf_exists:
  forall gc te1 te1' eh1 eh1' a v,
  locenv_setvarf gc te1 eh1 a v te1' eh1' ->
  forall te2 eh2 ids, ptree_noids_match ids te1 te2 ->
  locenv_match_rets te1 eh2 ids ->
  locenv_match eh1 eh2 ->
  ptree_ids_none ids eh1 ->
  ptree_ids_none ids te2 ->
  has_type v (typeof a) ->
  locenv_mvl_alloc te2 ->
  exists te2' eh2', locenv_setvarf gc te2 eh2 (trans_sexp (trans_v ids) a) v te2' eh2'
    /\ ptree_noids_match ids te1' te2'
    /\ locenv_match_rets te1' eh2' ids
    /\ locenv_match eh1' eh2'
    /\ ptree_ids_none ids eh1'
    /\ ptree_ids_none ids te2'
    /\ locenv_mvl_alloc te2'.
Proof.
  intros. inv H.
  +generalize H7; intros A.
   eapply eval_sexp_match in H7; eauto.
   destruct (in_list id ids) eqn:?.
   -exists te2.
    rewrite <-trans_sexp_typeof with (ids:=ids) in H8.
    eapply store_env_ptree_match_exists_right in H8; eauto.
    destruct H8 as [eh2' [? [? ?]]].
    exists eh2'. repeat (split; auto).
    *constructor 2 with id ofs; auto.
    *inv H. eapply locenv_match_addnewid; eauto.
     apply H3. apply in_list_true_in; auto.
    *rewrite trans_sexp_typeof; auto.
   -eapply store_env_ptree_match_exists_left in H8; eauto.
    destruct H8 as [te2' [? [? [? ?]]]].
    exists te2', eh2. repeat (split; auto).
    constructor 1 with id ofs; auto.
    *rewrite trans_sexp_typeof; auto.
    *inv H. eapply ptree_ids_none_set_other; eauto.
  +exists te2.
   destruct locenv_match_store_env_exists with (typeof a) eh1 id ofs v eh1' eh2
    as [eh2' [? ?]]; auto.
   exists eh2'. repeat (split; auto).
   -constructor 2 with id ofs;auto.
    eapply eval_sexp_match in H7; eauto.
    rewrite trans_sexp_typeof; auto.
   -inv H. inv H8.
    eapply locenv_match_rets_set_other_right; eauto.
    eapply ptree_ids_none_in_list_false with (eh1:=eh1); eauto.
   -inv H8. eapply ptree_ids_none_set_other; eauto.
Qed.

Lemma lvalue_disjoint_match:
  forall gc te1 e1 a1 a2,
  lvalue_disjoint (eval_lvalue gc te1 e1) a1 a2 ->
  forall te2 e2 ids, locenv_match e1 e2 ->
  ptree_noids_match ids te1 te2 ->
  locenv_match_rets te1 e2 ids ->
  ptree_ids_none ids te2 ->
  lvalue_disjoint (eval_lvalue gc te2 e2) (trans_sexp (trans_v ids) a1) (trans_sexp (trans_v ids) a2).
Proof.
  induction 1. intros.
  eapply eval_sexp_match in H; eauto.
  eapply eval_sexp_match in H0; eauto.
  destruct H1, k2; subst; try tauto; destruct (in_list id1 ids);
  econstructor 1; try repeat rewrite trans_sexp_typeof; eauto.
Qed.

Lemma assign_disjoint_match:
  forall gc te1 e1 a1 a2,
  assign_disjoint (eval_lvalue gc te1 e1) a1 a2 ->
  forall te2 e2 ids, locenv_match e1 e2 ->
  ptree_noids_match ids te1 te2 ->
  locenv_match_rets te1 e2 ids ->
  ptree_ids_none ids te2 ->
  assign_disjoint (eval_lvalue gc te2 e2) (trans_sexp (trans_v ids) a1) (trans_sexp (trans_v ids) a2).
Proof.
  induction 1; intros.
  +constructor 1 with chunk; auto.
   rewrite trans_sexp_typeof; auto.
  +constructor 2; auto.
   rewrite trans_sexp_typeof; auto.
   eapply lvalue_disjoint_match; eauto.
Qed.

Lemma eval_eqf_exists:
  forall gc te1 eh1 te1' eh1' a,
  eval_eqf gc te1 eh1 te1' eh1' a ->
  forall te2 eh2 ids, ptree_noids_match ids te1 te2 ->
  locenv_match_rets te1 eh2 ids ->
  locenv_match eh1 eh2 ->
  ptree_ids_none ids eh1 ->
  ptree_ids_none ids te2 ->
  locenv_mvl_alloc te2 ->
  exists te2' eh2', eval_eqf gc te2 eh2 te2' eh2' (trans_eqf (trans_v ids) a)
    /\ ptree_noids_match ids te1' te2'
    /\ locenv_match_rets te1' eh2' ids
    /\ locenv_match eh1' eh2'
    /\ ptree_ids_none ids eh1'
    /\ ptree_ids_none ids te2'
    /\ locenv_mvl_alloc te2'.
Proof.
  intros. inv H. unfold trans_eqf. simpl.
  eapply locenv_setvarf_exists in H10; eauto.
  destruct H10 as [te2' [eh2' [? [? [? [? [? ?]]]]]]].
  exists te2', eh2'. repeat (split; auto).
  constructor 1 with v v'; auto.
  +eapply eval_sexp_match; eauto.
  +repeat rewrite trans_sexp_typeof; auto.
  +eapply assign_disjoint_match; eauto.
  +rewrite trans_sexp_typeof; auto.
  +eapply eval_cast_has_type; eauto.
   rewrite H7. eapply eval_sexp_has_type; eauto.
Qed.

Lemma locenv_setvarfs_exists:
  forall gc te1 te1' eh1 eh1' al vl,
  LsemF.locenv_setvarfs gc te1 eh1 al vl te1' eh1' ->
  forall te2 eh2 ids, ptree_noids_match ids te1 te2 ->
  locenv_match_rets te1 eh2 ids ->
  locenv_match eh1 eh2 ->
  ptree_ids_none ids eh1 ->
  ptree_ids_none ids te2 ->
  has_types vl (map typeof al) ->
  locenv_mvl_alloc te2 ->
  exists te2' eh2', LsemF.locenv_setvarfs gc te2 eh2 (trans_sexps (trans_v ids) al) vl te2' eh2'
    /\ ptree_noids_match ids te1' te2'
    /\ locenv_match_rets te1' eh2' ids
    /\ locenv_match eh1' eh2'
    /\ ptree_ids_none ids eh1'
    /\ ptree_ids_none ids te2'
    /\ locenv_mvl_alloc te2'.
Proof.
  induction 1; simpl; intros.
  +exists te2, eh2. repeat (split; auto).
   constructor.
  +inv H6.
   eapply locenv_setvarf_exists in H; eauto.
   destruct H as [te21 [eh21 [? [? [? [? [? [? ?]]]]]]]].
   destruct IHlocenv_setvarfs with te21 eh21 ids as [te2' [eh2' [? [? [? [? [? [? ?]]]]]]]]; auto.
   exists te2', eh2'. repeat (split; auto).
   constructor 2 with te21 eh21; auto.
Qed.

Lemma trans_call_node:
  forall nid cdef nd fd,
  call_node (node_block prog1) nid cdef nd fd ->
  call_node (node_block prog2) nid cdef (trans_node nd) (trans_node fd).
Proof.
  unfold call_node, call_func. intros.
  subst. intuition.
  eapply trans_funcs_find with _ func _ trans_node _ _   in H0; eauto.
  eapply trans_funcs_find with _ func _ trans_node _ _   in H4; eauto.
Qed.

Lemma trans_call_func:
  forall nid cdef nd fd,
  Lustre.call_node (node_block prog1) nid cdef nd fd ->
  Lustre.call_func (node_block prog2) cdef (trans_node fd).
Proof.
  unfold Lustre.call_node, Lustre.call_func. intros.
  subst. intuition.
  eapply trans_funcs_find with _ func _ trans_node _ _   in H1; eauto.
Qed.

Lemma env_ids_none_callnd_inst_env_match:
  forall nd fd le1 se1 c i ef1,
  env_ids_none nd (mkenv le1 se1) ->
  callnd_inst_env c i se1 ef1 ->
  In c (instidof (nd_stmt (snd nd))) ->
  nd_kind (snd nd) = true ->
  find_funct (node_block prog1) (callid c) = Some fd ->
  env_ids_none fd ef1.
Proof.
  intros. inv H.
  inv H0. destruct H7 with c as [fd1 [el1 [? [? ?]]]]; auto.
  rewrite H2; auto.
  rewrite H0 in H3. inv H3.
  rewrite H8 in H. inv H.
  eapply Forall_forall; eauto.
  eapply nth_error_in; eauto.
Qed.

Lemma env_ids_some_callnd_inst_env_match:
  forall nd fd le1 se1 c i ef1,
  env_ids_some nd (mkenv le1 se1) ->
  callnd_inst_env c i se1 ef1 ->
  In c (instidof (nd_stmt (snd nd))) ->
  nd_kind (snd nd) = true ->
  find_funct (node_block prog1) (callid c) = Some fd ->
  env_ids_some fd ef1.
Proof.
  intros. inv H. inv H0.
  destruct H7 with c as [fd1 [el1 [? [? ?]]]]; auto.
  rewrite H2; auto.
  rewrite H0 in H3. inv H3.
  rewrite H8 in H. inv H.
  eapply Forall_forall; eauto.
  eapply nth_error_in; eauto.
Qed.

Lemma env_ids_none_update:
  forall cdef i se se' ef ef' eh eh' nd fd,
  callnd_env cdef i se se' ef ef' ->
  env_ids_none nd (mkenv eh se) ->
  find_funct (node_block prog1) (callid cdef) = Some fd ->
  env_ids_none fd ef' ->
  ptree_ids_none (map fst (nd_rets (snd nd))) eh' ->
  list_norepet (map instid (instidof (nd_stmt (snd nd)))) ->
  In cdef (instidof (nd_stmt (snd nd))) ->
  nd_kind (snd nd) = true ->
  env_ids_none nd (mkenv eh' se').
Proof.
  intros. inv H. inv H0. constructor; auto.
  red; intros. rewrite H6 in *.
  compare (instid c) (instid cdef); intros.
  +eapply map_nodup_find_eq in e; eauto.
   subst. destruct H12 with cdef as [fd1 [el1 [? [? ?]]]]; auto.
   rewrite H0 in H1. inv H1. rewrite H9 in H7. inv H7.
   exists fd. rewrite PTree.gss.
   exists (replace_nth efs (nat_of_int i) ef'). repeat (split; auto).
   eapply Forall_replace; eauto.
   eapply list_norepet_nodup; eauto.
  +destruct H12 with c as [fd1 [el1 [? [? ?]]]]; auto.
   exists fd1. rewrite PTree.gso; auto.
   exists el1. repeat (split; auto).
Qed.

Lemma env_ids_some_update:
  forall cdef i se se' ef ef' eh eh' nd fd,
  callnd_env cdef i se se' ef ef' ->
  env_ids_some nd (mkenv eh se) ->
  find_funct (node_block prog1) (callid cdef) = Some fd ->
  env_ids_some fd ef' ->
  ptree_vars_some (nd_rets (snd nd)) eh' ->
  list_norepet (map instid (instidof (nd_stmt (snd nd)))) ->
  In cdef (instidof (nd_stmt (snd nd))) ->
  nd_kind (snd nd) = true ->
  env_ids_some nd (mkenv eh' se').
Proof.
  intros. inv H. inv H0; try congruence. constructor; auto.
  red; intros. rewrite H6 in *.
  compare (instid c) (instid cdef); intros.
  +eapply map_nodup_find_eq in e; eauto.
   subst. destruct H12 with cdef as [fd1 [el1 [? [? ?]]]]; auto.
   rewrite H0 in H1. inv H1. rewrite H9 in H7. inv H7.
   exists fd. rewrite PTree.gss.
   exists (replace_nth efs (nat_of_int i) ef'). repeat (split; auto).
   eapply Forall_replace; eauto.
   eapply list_norepet_nodup; eauto.
  +destruct H12 with c as [fd1 [el1 [? [? ?]]]]; auto.
   exists fd1. rewrite PTree.gso; auto.
   exists el1. repeat (split; auto).
Qed.

Lemma locenv_match_setvars_exists:
  forall te1 al vas te1',
  locenv_setvars te1 al vas te1' ->
  forall ids te2 eh2, ptree_noids_match ids te1 te2 ->
  locenv_match_rets te1 eh2 ids ->
  list_disjoint (map fst al) ids ->
  locenv_mvl_alloc te2 ->
  has_types vas (map snd al) ->
  exists te2', locenv_setvars te2 al vas te2'
     /\ ptree_noids_match ids te1' te2'
     /\ locenv_match_rets te1' eh2 ids
     /\ locenv_mvl_alloc te2'.
Proof.
  induction 1; simpl; intros.
  +exists te2. repeat (split; auto).
   constructor.
  +apply list_disjoint_appa_left in H4. destruct H4.
   apply in_list_false_notin in H4. inv H6.
   eapply store_env_ptree_match_exists_left with (gc:= empty_locenv) (eh1:=empty_locenv) (a:=Svar id ty) in H0; eauto.
   destruct H0 as [te21 [? [? [? ?]]]].
   destruct IHlocenv_setvars with ids te21 eh2 as [te2' [? [? [? ?]]]]; auto.
   exists te2'. repeat (split; auto).
   constructor 2 with te21 m; auto.
   rewrite <- H2; auto. apply in_list_false_notin; auto.
   constructor 1 with m; auto.
Qed.

Lemma alloc_variables_ptree_match:
  forall l1 l2 te1' te2' eh2,
  alloc_variables empty_locenv (l1++l2) te1' ->
  alloc_variables empty_locenv l1 te2' ->
  list_disjoint (map fst l1) (map fst l2) ->
  list_norepet (map fst l2) ->
  ptree_vars_some l2 eh2 ->
  ptree_noids_match (map fst l2) te1' te2'
    /\ locenv_match_rets te1' eh2 (map fst l2).
Proof.
  intros. apply alloc_variables_app in H.
  destruct H as [te1 [? ?]].
  eapply alloc_variables_determ in H; eauto.
  subst. split; red; intros.
  +eapply alloc_variables_notin_eq; eauto.
  +generalize H; intros.
   apply in_map_iff in H. destruct H as [? [? ?]].
   subst. destruct x. simpl in *.
   eapply alloc_variables_norepeat_in_eq in H4; eauto.
   apply H3 in H6. destruct H6 as [m [? ?]].
   red. intros. exists (alloc (sizeof t)), m, t.
   repeat split; auto.
   eapply mvl_match_alloc; eauto.
Qed.

Lemma alloc_variables_locenv_mvl_alloc:
  forall te l te',
  alloc_variables te l te' ->
  locenv_mvl_alloc te ->
  locenv_mvl_alloc te'.
Proof.
  induction 1; intros; auto.
  apply IHalloc_variables. red; intros.
  compare id id0; intros; subst.
  rewrite PTree.gss in H1. inv H1.
  apply mvl_alloc_self.
  rewrite PTree.gso in H1; auto. apply H0 in H1; auto.
Qed.

Lemma locenv_setvarf_ptree_vars_some:
  forall gc te2 eh2 a v te2' eh2' rets,
  locenv_setvarf gc te2 eh2 a v te2' eh2' ->
  ptree_vars_some rets eh2 ->
  has_type v (typeof a) ->
  ptree_vars_some rets eh2'.
Proof.
  intros. inv H; auto.
  eapply store_env_ptree_vars_some; eauto.
Qed.

Lemma locenv_setvarfs_ptree_vars_some:
  forall gc te2 eh2 al vl te2' eh2',
  LsemF.locenv_setvarfs gc te2 eh2 al vl te2' eh2' ->
  forall rets, ptree_vars_some rets eh2 ->
  has_types vl (map typeof al) ->
  ptree_vars_some rets eh2'.
Proof.
  induction 1; simpl; intros; auto.
  inv H2. apply IHlocenv_setvarfs; auto.
  eapply locenv_setvarf_ptree_vars_some; eauto.
Qed.

Lemma eval_eqf_ptree_vars_some:
  forall gc vars te2 te2' eh2 eh2' a,
  ptree_vars_some vars eh2 ->
  eval_eqf gc te2 eh2 te2' eh2' a ->
  ptree_vars_some vars eh2'.
Proof.
  intros. inv H0.
  eapply locenv_setvarf_ptree_vars_some; eauto.
  eapply eval_cast_has_type; eauto.
  rewrite H2. eapply eval_sexp_has_type; eauto.
Qed.

Lemma length_eq_loadbytes_exists:
  forall m1 m2 o size v1,
  length m1 = length m2 ->
  loadbytes m1 o size = Some v1 ->
  exists v2, loadbytes m2 o size = Some v2.
Proof.
  intros.
  apply loadbytes_range_perm in H0.
  econstructor. unfold loadbytes.
  rewrite pred_dec_true; auto.
  eapply length_range_perm; eauto.
Qed.

Lemma locenv_getmvl_match:
  forall gc te1 lh v1,
  Lsem.locenv_getmvl gc te1 lh v1 ->
  forall te2 e1 e2 ids, locenv_match e1 e2 ->
  ptree_noids_match ids te1 te2 ->
  locenv_match_rets te1 e2 ids ->
  ptree_ids_none ids te2 ->
  locenv_mvl_alloc te2 ->
  exists v2, locenv_getmvl gc te2 e2 (trans_sexp (trans_v ids) lh) v2
    /\ mvl_alloc v2 (typeof lh).
Proof.
  intros. inv H.
  generalize H5; intros A.
  apply eval_lvalue_lvalue with (eh:=e1) in A.
  eapply eval_sexp_match in A; eauto.
  destruct (in_list id ids) eqn:?.
  +destruct H2 with id as [? [? [? [? [? ?]]]]]; auto.
   apply in_list_true_in; auto.
   rewrite H in H6. inv H6.
   apply length_eq_loadbytes_exists with (m2:=x0) in H7.
   destruct H7 as [v2 ?].
   exists v2. split. constructor 1 with id ofs Sid x0 t; auto.
   -rewrite trans_sexp_typeof; auto.
   -erewrite loadbytes_contents with (bytes:=v2); eauto.
    apply eval_offset_mvl_alloc_sube with (t:=t); auto.
    eapply Lsem.eval_lvalue_eval_offset in H5; eauto.
    eapply mvl_match_mvl_alloc; eauto.
   -eapply mvl_match_length in H9; eauto.
  +exists v1. split; auto. constructor 1 with id ofs Lid m t; auto.
   -rewrite <-H1; auto.
    apply in_list_false_notin; auto.
   -rewrite trans_sexp_typeof; auto.
   -generalize H6; intros A1. rewrite H1 in H6. apply H4 in H6.
    erewrite loadbytes_contents with (bytes:=v1); eauto.
    eapply eval_offset_mvl_alloc_sube; eauto.
    eapply Lsem.eval_lvalue_eval_offset in H5; eauto.
    apply in_list_false_notin; auto.
Qed.

Lemma locenv_getmvls_match:
  forall gc te1 lhs vl1,
  Lsem.locenv_getmvls gc te1 lhs vl1 ->
  forall te2 e1 e2 ids, locenv_match e1 e2 ->
  ptree_noids_match ids te1 te2 ->
  locenv_match_rets te1 e2 ids ->
  ptree_ids_none ids te2 ->
  locenv_mvl_alloc te2 ->
  exists vl2, locenv_getmvls gc te2 e2 (trans_sexps (trans_v ids) lhs) vl2
    /\ Forall2 mvl_alloc vl2 (map typeof lhs).
Proof.
  induction 1; intros.
  +exists nil. split; constructor.
  +simpl. eapply locenv_getmvl_match in H; eauto.
   destruct H as [v2 [? ?]].
   destruct IHForall2 with te2 e1 e2 ids as [vl2 [? ?]]; auto.
   exists (v2::vl2). split; constructor 2; auto.
Qed.

Lemma locenv_setmvls_ptree_vars_some:
  forall e al vl e',
  locenv_setmvls e al vl e' ->
  list_norepet (map fst al) ->
  Forall2 mvl_alloc vl (map snd al) ->
  ptree_vars_some al e'.
Proof.
  induction 1; simpl; intros; auto.
  +red; simpl; intros. tauto.
  +inv H1. inv H2. red; simpl; intros. destruct H1.
   -inv H. inv H8. exists mv.
    split; auto. erewrite locenv_setmvls_notin_eq; eauto.
    rewrite PTree.gss; auto.
   -eapply IHlocenv_setmvls; eauto.
Qed.

Lemma lvalue_list_norepet_match:
  forall gc te1 e1 l,
  lvalue_list_norepet (eval_lvalue gc te1 e1) l ->
  forall te2 e2 ids, locenv_match e1 e2 ->
  ptree_noids_match ids te1 te2 ->
  locenv_match_rets te1 e2 ids ->
  ptree_ids_none ids te2 ->
  lvalue_list_norepet (eval_lvalue gc te2 e2) (trans_sexps (trans_v ids) l).
Proof.
  induction 1; simpl; intros.
  +constructor.
  +constructor 2; eauto.
   unfold trans_sexps. red; intros.
   apply in_map_iff in H5. destruct H5 as [? [? ?]].
   subst. apply in_split in H6. destruct H6 as [? [? ?]].
   subst. eapply lvalue_disjoint_match; eauto.
   apply H; apply in_or_app; simpl; auto.
Qed.

Lemma assign_list_disjoint_match:
  forall gc te1 e1 l al,
  assign_list_disjoint (eval_lvalue gc te1 e1) l al ->
  forall te2 e2 ids, locenv_match e1 e2 ->
  ptree_noids_match ids te1 te2 ->
  locenv_match_rets te1 e2 ids ->
  ptree_ids_none ids te2 ->
  assign_list_disjoint (eval_lvalue gc te2 e2) (trans_sexps (trans_v ids) l) (trans_sexps (trans_v ids) al).
Proof.
  intros.
  unfold trans_sexps. red; intros.
  apply in_map_iff in H4. destruct H4 as [? [? ?]].
  apply in_map_iff in H5. destruct H5 as [? [? ?]].
  subst. apply in_split in H6. destruct H6 as [? [? ?]].
  apply in_split in H7. destruct H7 as [? [? ?]].
  subst. eapply assign_disjoint_match; eauto.
  apply H; apply in_or_app; simpl; auto.
Qed.

Lemma trans_node_all_correct:
  forall gc eL eL' fd vargs vrets,
  LsemF.eval_node true prog1 gc eL eL' fd vargs vrets ->
  find_funct (node_block prog1) (fst fd) = Some fd ->
  forall eR,
  env_match eL eR ->
  env_ids_none fd eL ->
  env_ids_some fd eR ->
  has_types vargs (map snd (nd_args (snd fd))) ->
  exists eR', eval_node prog2 gc eR eR' (trans_node fd) vargs vrets
     /\ env_match eL' eR'
     /\ env_ids_none fd eL'
     /\ env_ids_some fd eR'.
Proof.
  intros gc.
  induction 1 using LsemF.eval_node_ind2 with
  ( P0 := fun nid teL eL teL' eL' s =>
      forall nd eR teR,
      find_funct (node_block prog1) nid = Some nd ->
      env_match eL eR ->
      env_ids_none nd eL ->
      ptree_noids_match (map fst (nd_rets (snd nd))) teL teR ->
      locenv_match_rets teL (le eR) (map fst (nd_rets (snd nd))) ->
      incl (instidof s) (instidof (nd_stmt (snd nd))) ->
      list_norepet (map instid (instidof (nd_stmt (snd nd)))) ->
      env_ids_some nd eR ->
      ptree_ids_none (map fst (nd_rets (snd nd))) teR ->
      ~ In ACG_I (map fst (nd_rets (snd nd))) ->
      locenv_mvl_alloc teR ->
      exists eR' teR',
         eval_stmt prog2 gc nid teR eR teR' eR'
            (trans_stmt (trans_v (map fst (nd_rets (snd nd)))) s)
      /\ env_ids_none nd eL'
      /\ env_match eL' eR'
      /\ ptree_noids_match (map fst (nd_rets (snd nd))) teL' teR'
      /\ locenv_match_rets teL' (le eR') (map fst (nd_rets (snd nd)))
      /\ env_ids_some nd eR'
      /\ ptree_ids_none (map fst (nd_rets (snd nd))) teR'
      /\ locenv_mvl_alloc teR'
   ); simpl; intros.
 +(*eval_node*)
  destruct alloc_variables_exists with (lvarsof f) empty_locenv as [teR A].
  assert (B: ptree_noids_match (map fst (nd_rets f)) te teR
             /\ locenv_match_rets te (le eR) (map fst (nd_rets f))).
    unfold allvarsof, lvarsof in *.
    eapply alloc_variables_ptree_match; eauto.
    apply ids_norepet_vars_args_rets_disjoint; auto.
    apply ids_norepet_rets_norepet; auto.
    inv H10; auto.
  destruct B as [B B1].
  destruct locenv_match_setvars_exists with te (nd_args f) vas te1 (map fst (nd_rets f)) teR (le eR)
    as [teR1 [A1 [? [? ?]]]]; auto.
    apply ids_norepet_args_rets_disjoint; auto.
    eapply alloc_variables_locenv_mvl_alloc; eauto.
     red; intros. rewrite PTree.gempty in *. congruence.
  destruct IHeval_node with (nid,f) eR teR1 as [eR' [teR' [A2 [A3 [A4 [A5 [A6 [A7 A8]]]]]]]]; simpl; auto.
    red; intros; auto.
    apply ids_norepet_instid; auto.
    eapply locenv_setvars_ptree_ids_none; eauto.
    eapply alloc_variables_ptree_ids_none; eauto.
    apply list_disjoint_sym.
    apply ids_norepet_vars_args_rets_disjoint; auto.
    apply list_disjoint_sym.
    apply ids_norepet_args_rets_disjoint; auto.
    eapply ids_norepet_loopid_notin_rets; eauto.
  exists eR'. split;[| split]; auto.
  destruct eR, eR'. econstructor; eauto.
  apply trans_body_ids_norepet; auto.
  eapply loenv_match_rets_getvars; eauto.
 +(*eval_Sassign*)
  eapply eval_eqf_exists in H; eauto.
  destruct H as [teR' [ehR' [? [? [? [? [? [? ?]]]]]]]]; auto.
  inv H1.
  exists (mkenv ehR' se2), teR'. split; [| split; [| split; [| split; [| split; [| split; [| split]]]]]]; auto.
  -apply eval_Sassign; auto.
  -inv H2. constructor; auto.
  -constructor; auto.
  -inv H7. constructor; auto.
   eapply eval_eqf_ptree_vars_some; eauto.
  -inv H1; auto.
  -inv H2; auto.
 +(*eval_Scall*)
  simpl in *.
  assert(nd0 = nd).
    destruct (cakind cdef); destruct H0 as [A1 [? [? ?]]];
    unfold func in *; rewrite H13 in A1; inv A1; auto.
  subst nd0. inversion H1; rewrite H24 in *.
  -(*node*)
   subst se1 se2 e1 e2.
   generalize H25 H0 H25; intros A A1 A5.
   apply callnd_inst_env_eq in A.
   eapply trans_call_node in H0; eauto.
   destruct A1 as [A1 [A2 [A3 [A4 [A6 [A7 [A8 A9]]]]]]].
   assert(A10: In cdef (instidof (nd_stmt (snd nd)))).
     eapply cons_inst_incl; eauto.
   destruct eR as [ehR seR].
   assert(A11: nd_kind (snd nd) = true).
     unfold func in *. rewrite <-A8, H24 in *.
     apply callorder_true; auto.
   assert (B: exists ef2, callnd_inst_env cdef i seR ef2).
     eapply env_match_callnd_inst_env_exists; eauto.
   destruct B as [ef2 B].
   assert (B1: env_match ef ef2).
     eapply env_match_callnd_inst_env_match; eauto.
   assert (B2: env_ids_none fd ef).
     eapply env_ids_none_callnd_inst_env_match with (nd:=nd); eauto.
   assert (B3: env_ids_some fd ef2).
     eapply env_ids_some_callnd_inst_env_match; eauto.
   destruct ef as [ehf sef]. destruct ef' as [ehf' sef'].
   destruct IHeval_node with ef2 as [efR' [? [? [? ?]]]]; auto.
     eapply find_funct_eq;eauto.
     rewrite <-H8.
     eapply eval_casts_has_types; eauto.
     eapply eval_sexps_has_types; eauto.
   eapply callnd_env_exists_se in H27; eauto.
   destruct H27 as [seR' [? ?]].
   cut(locenv_match eh ehR); intros C.
   eapply locenv_setvarfs_exists in H5; eauto.
   destruct H5 as [teR' [ehR' [? [? [? [? [? [? ?]]]]]]]].
   exists (mkenv ehR' seR'), teR'. split; [| split; [| split; [| split; [| split; [| split; [| split]]]]]]; auto.
   *eapply eval_Scall with _ _ (trans_node fd) (trans_node nd) vargs vargs' vrets i; eauto.
    inv H; simpl. constructor 1; auto.
     eapply eval_sexp_ptree_ids_match; eauto.
      red; simpl; intros ? C1. destruct C1; try tauto; subst; auto.
     constructor 2.
    eapply eval_sexps_match; eauto.
    rewrite trans_sexps_typeof; auto.
    eapply trans_sexps_lid_disjoint; eauto.
    rewrite trans_sexps_typeof; auto.
    rewrite trans_sexps_typeof; auto.
    eapply lvalue_list_norepet_match; eauto.
    eapply assign_list_disjoint_match; eauto.
    assert(D: In (callid cdef) (map fst (nd_rets (snd nd))) \/ ~ In (callid cdef) (map fst (nd_rets (snd nd)))) by tauto.
     destruct D. apply H21; simpl; auto. rewrite <-H16; auto.
   *eapply env_ids_none_update; eauto.
   *inv H30; constructor; auto.
   *eapply env_ids_some_update; eauto.
    eapply locenv_setvarfs_ptree_vars_some; eauto.
    inv H20; auto.
    rewrite trans_sexps_typeof. rewrite H7. inv H4; auto.
   *inv H15; auto.
   *rewrite H7. inv H4; auto.
   *inv H30; auto.
  -(*func*)
   subst se0 se ef ef'. generalize H0; intros A.
   destruct A as [A1 [A2 [A3 [A4 [A6 [A7 A8]]]]]].
   eapply trans_call_func in H0; eauto.
   cut (locenv_match eh (le eR)). intros C.
   eapply locenv_getmvls_match in H9; eauto.
   destruct H9 as [vl2 [A C2]].
   generalize H5; intros C1.
   eapply locenv_setvarfs_exists in H5; eauto.
   destruct H5 as [teR' [ehR' [? [? [? [? [? [? ?]]]]]]]].
   assert (A9: exists efR, locenv_setmvls empty_locenv (nd_rets (snd fd)) vl2 efR).
    eapply locenv_getmvls_set_mvls_exists; eauto.
    rewrite trans_sexps_typeof; auto.
   destruct A9 as [efR A9]. destruct eR as [ehR seR].
   cut (nd_kind (snd fd) = false); intros.
   destruct IHeval_node with (mkenv efR empty_subenv) as [efR' [? [? [? ?]]]]; auto.
     eapply find_funct_eq;eauto.
     constructor; auto; red; intros. rewrite PTree.gempty in *. congruence.
       split; intros; auto. rewrite PTree.gempty in *. congruence.
     constructor 1; auto; red; intros. rewrite PTree.gempty; auto.
       rewrite H30 in *. tauto.
     constructor 1; auto. eapply locenv_setmvls_ptree_vars_some; eauto.
       apply ids_norepet_rets_norepet; auto. inv H4; auto.
       congruence. red. rewrite H30. intros. tauto.
     rewrite <-H8. eapply eval_casts_has_types; eauto.
      eapply eval_sexps_has_types; eauto.
   exists (mkenv ehR' seR), teR'. split; [| split; [| split; [| split; [| split; [| split; [| split]]]]]]; auto.
   *apply eval_Fcall with efR efR' vl2 (trans_node fd) vargs vargs' vrets; auto.
    eapply eval_sexps_match; eauto.
    rewrite trans_sexps_typeof; auto.
    eapply trans_sexps_lid_disjoint; eauto.
    rewrite trans_sexps_typeof; auto.
    rewrite trans_sexps_typeof; auto.
    eapply lvalue_list_norepet_match; eauto.
    eapply assign_list_disjoint_match; eauto.
    assert(D: In (callid cdef) (map fst (nd_rets (snd nd))) \/ ~ In (callid cdef) (map fst (nd_rets (snd nd)))) by tauto.
     destruct D. apply H21; simpl; auto. rewrite <-H16; auto.
   *inv H15; constructor 1; auto.
   *inv H14; constructor; auto.
   *inv H20; constructor 1; auto;
    eapply locenv_setvarfs_ptree_vars_some; eauto;
    rewrite trans_sexps_typeof; rewrite H7; inv H4; auto.
   *unfold func in *. congruence.
   *inv H15; auto.
   *rewrite H7. inv H4; auto.
   *inv H14; auto.
 +(*eval_Sfor_start*)
  eapply eval_eqf_exists in H; eauto.
  destruct H as [teR1 [ehR1 [A [A1 [A2 [A3 [? [? ?]]]]]]]].
  destruct eR as [ehR seR].
  destruct IHeval_node with nd (mkenv ehR1 seR) teR1 as [eR' [teR' [A4 [A5 [A6 [A7 [A8 [? ?]]]]]]]]; auto.
    inv H2; constructor; auto.
    inv H3. constructor; auto.
    inv H8. constructor; auto.
    eapply eval_eqf_ptree_vars_some; eauto.
  exists eR', teR'. split; [| split; [| split]]; auto.
  apply eval_Sfor_start with teR1 ehR1; auto.
  inv H2; auto.
  inv H3; auto.
 +(*eval_Sfor_false*)
  exists eR, teR. repeat (split; auto).
  destruct eR as [ehR seR].
  apply eval_Sfor_false; auto.
  eapply eval_sexp_match; eauto.
  inv H1; auto.
 +(*eval_Sfor_loop*)
  destruct IHeval_node with nd eR teR
    as [eR1 [teR1 [? [? [? [? [? [? [? ?]]]]]]]]]; auto.
  destruct eR1 as [ehR1 seR1].
  eapply eval_eqf_exists with (eh1:=eh1) (eh2:=ehR1) in H1; eauto.
  destruct H1 as [teR2 [ehR2 [? [? [? [? [? [? ?]]]]]]]].
  destruct IHeval_node0 with nd (mkenv ehR2 seR1) teR2
    as [eR' [teR' [? [? [? [? [? [? [? ?]]]]]]]]]; auto.
    inv H16; constructor; auto.
    inv H15. constructor; auto.
    inv H19. constructor; auto.
    eapply eval_eqf_ptree_vars_some; eauto.
  exists eR', teR'. repeat (split; auto).
  destruct eR as [ehR seR].
  eapply eval_Sfor_loop; eauto.
  eapply eval_sexp_match; eauto.
  inv H4; auto.
  inv H16;auto.
  inv H15; auto.
 +(*eval_Sskip*)
  exists eR, teR. repeat (split; auto).
  constructor.
 +(*eval_Sseq *)
  destruct IHeval_node with nd eR teR as [eR1 [teR1 [? [? [? [? [? [? [? ?]]]]]]]]]; simpl; auto.
    eapply incl_app_inv_l; eauto.
  destruct IHeval_node0 with nd eR1 teR1 as [eR' [teR' [? [? [? [? [? [? [? ?]]]]]]]]]; simpl; auto.
    eapply incl_app_inv_r; eauto.
  exists eR', teR'. repeat (split; auto).
  apply eval_Sseq with teR1 eR1; auto.
 +(*eval_Sif*)
  destruct IHeval_node with nd eR teR as [eR1 [teR1 [? [? [? [? [? [? ?]]]]]]]]; simpl; auto.
    destruct b; [eapply incl_app_inv_l | eapply incl_app_inv_r]; eauto.
  exists eR1, teR1. split; [| split]; auto.
  destruct eR as [ehR seR].
  apply eval_Sif with v b; auto.
  -eapply eval_sexp_match; eauto.
   inv H3; auto.
  -rewrite trans_sexp_typeof; auto.
  -destruct b; auto.
 +(*eval_Scase*)
  inv H1. destruct eR as [ehR seR].
  eapply eval_eqf_exists in H18; eauto.
  destruct H18 as [teR' [ehR' [? [? [? [? [? [? ?]]]]]]]]; auto.
  exists (mkenv ehR' seR), teR'. split; [| split; [| split; [| split; [| split; [| split; [| split]]]]]]; auto.
  -apply eval_Scase with i (trans_sexp (trans_v (map fst (nd_rets (snd nd))))  a); eauto.
   *eapply eval_sexp_match; eauto.
    inv H3; auto.
   *eapply trans_select_case; eauto.
   *apply eval_Sassign; auto.
  -inv H3; constructor; auto.
  -inv H9. constructor; auto.
   eapply eval_eqf_ptree_vars_some; eauto.
  -inv H3; auto.
  -inv H4; auto.
Qed.

Lemma alloc_variables_locenv_match:
  forall e1 l e1',
  alloc_variables e1 l e1' ->
  forall e2 e2', locenv_match e1 e2 ->
  alloc_variables e2 l e2' ->
  locenv_match e1' e2'.
Proof.
  induction 1; simpl; intros.
  inv H0. auto.
  inv H1. eapply IHalloc_variables; eauto.
  apply locenv_match_addsameid; auto.
Qed.

Lemma alloc_variables_init_match:
  forall l1 l2 te1 te2,
  alloc_variables empty_locenv l2 te1 ->
  alloc_variables empty_locenv (l1++l2) te2 ->
  locenv_match te1 te2.
Proof.
  intros. apply alloc_variables_app in H0.
  destruct H0 as [te [? ?]].
  eapply alloc_variables_locenv_match; eauto.
  red; intros. rewrite PTree.gempty in H2. congruence.
Qed.

Lemma eval_init_exists:
  forall (f:func) eh1,
  eval_init (length (nd_svars f)) empty_locenv (nd_svars f) eh1 ->
  ids_norepet f ->
  exists eh eh2, alloc_variables empty_locenv (nd_rets f) eh
    /\ eval_init (length (nd_svars f)) eh (nd_svars f) eh2
    /\ locenv_match eh1 eh2
    /\ ptree_vars_some (nd_rets f) eh2.
Proof.
  intros.
  destruct alloc_variables_exists with (nd_rets (trans_body f)) empty_locenv as [eh A].
  exists eh. inv H.
  +exists eh. repeat split; auto.
   constructor 1; auto.
   red; intros. rewrite PTree.gempty in H. congruence.
   simpl in *. eapply alloc_variables_ptree_vars_some; eauto.
   eapply ids_norepet_rets_norepet; eauto.
  +destruct alloc_variables_exists with (nd_svars (trans_body f)) eh as [eh3 A1].
   cut (locenv_match eh2 eh3); intros.
   destruct locenv_match_store_env_exists with type_bool eh2 ACG_INIT Int.zero Vtrue eh1 eh3 as [eh3' [? ?]]; auto.
   exists eh3'. repeat split; auto. simpl in *.
   -constructor 2 with eh3; auto. congruence.
   -apply ids_norepet_rets_svars in H0. rewrite map_app in H0.
    apply list_norepet_app in H0. destruct H0 as [A2 [A3 A4]].
    eapply store_env_ptree_vars_some with (gc:=empty_locenv) (te2:=empty_locenv) (a:=Ssvar ACG_INIT type_bool); eauto.
    *simpl in *. eapply alloc_variables_ptree_vars_some in A; eauto.
     red; intros. destruct A with id ty as [m [? ?]]; auto.
     exists m; split; auto. apply in_map with (B:=ident) (f:=fst) in H0.
     erewrite alloc_variables_notin_eq; eauto.
     eapply list_disjoint_notin; eauto.
    *simpl; auto.
    *simpl in *. rewrite <-H2 in *. inv A1. inv H4.
     constructor 3 with (alloc (sizeof type_bool)); auto.
     erewrite alloc_variables_notin_eq; eauto.
     rewrite PTree.gss; auto.
     inv A3; auto.
   -apply alloc_variables_init_match with (nd_rets f) (nd_svars f); eauto.
    congruence.
    apply alloc_variables_trans with eh; auto.
Qed.

Lemma init_node_correct:
  forall eL fd,
  LsemF.init_node true prog1 eL fd ->
  exists eR, init_node prog2 eR (trans_node fd)
   /\ env_match eL eR
   /\ env_ids_none fd eL
   /\ env_ids_some fd eR.
Proof.
  intros gc.
  induction 1 using LsemF.init_node_ind2 with
  ( P0 := fun nid eL eL' l =>
      forall ehL seL seL' ehR seR,
      eL = mkenv ehL seL ->
      eL' = mkenv ehL seL' ->
      env_match eL (mkenv ehR seR)  ->
      list_norepet (map instid l) ->
      exists seR', init_stmt prog2 nid (mkenv ehR seR) (mkenv ehR seR') l
       /\ env_match eL' (mkenv ehR seR')
       /\ subenv_ids env_ids_none seL' l
       /\ subenv_ids env_ids_some seR' l
       /\ ptree_noids_match (map instid l) seL seL'
       /\ ptree_noids_match (map instid l) seR seR'
   ); intros.
 +(*init_node*)
  generalize H; intros B.
  apply trans_body_ids_norepet in H; auto.
  destruct eval_init_exists with f eh1 as [eh [eh2 [A [A1 [A2 A3]]]]]; auto.
  destruct IHinit_node with eh1 empty_subenv se eh2 empty_subenv as [seR' [? [? [? [? [? ?]]]]]]; auto.
    constructor; auto. apply subenv_match_empty.
    apply ids_norepet_instid; auto.
  exists (mkenv eh2 seR'). repeat (split; auto).
  constructor 1 with eh; simpl; auto.
  -rewrite trans_stmt_instidof_eq. auto.
  -red; intros.
   cut (~ In id (map fst (nd_svars f))). intros B1.
   inv H0. rewrite PTree.gempty; auto.
   inv H15. rewrite PTree.gso; auto.
   erewrite alloc_variables_notin_eq; eauto.
   rewrite PTree.gempty. auto.
   red; intros; subst. apply B1; simpl.
   rewrite <-H12. auto.
   red; intros. subst. apply B1. rewrite <-H12. simpl; auto.
   eapply list_disjoint_notin; eauto.
   eapply ids_norepet_rets_svars_disjoint; auto.
  -simpl. destruct (nd_kind f) eqn:?; auto. red; intros. tauto.
  -simpl. destruct (nd_kind f) eqn:?; auto. red; intros. tauto.
 +(*nil*)
  subst. inv H0.
  exists seR. repeat (split; auto).
  -constructor.
  -red. intros ? A. inv A.
  -red. intros ? A. inv A.
 +(*cons*)
  generalize H; intros A.
  destruct A as [A [A1 [A2 [A3 [A4 [A5 A6]]]]]].
  eapply trans_call_node in H; eauto.
  inv H3. inv H4. inv H6.
  destruct IHinit_node as [efR [? [? [? ?]]]]; auto.
  remember (PTree.set _ _ _) as se1.
  destruct IHinit_node0 with ehL se1 seL' ehR (PTree.set (instid c) (list_repeat (nat_of_int (intof_opti (callnum c))) efR) seR)
    as [seR' [? [? [? [? [? ?]]]]]]; auto.
    inv H5. constructor;auto. eapply subenv_match_setsame; eauto.
      eapply Forall2_list_repeat; eauto.
  exists seR'. split; [| split; [| split; [| split; [| split]]]]; auto.
  -econstructor 2 with _ (trans_node nd) (trans_node fd) efR; eauto.
  -red; simpl; intros ? B. destruct B; subst; auto.
   exists fd, (list_repeat (nat_of_int (intof_opti (callnum c0))) ef).
   repeat split; auto.
   rewrite <-H13; auto. rewrite PTree.gss; auto.
   eapply Forall_list_repeat; eauto.
  -red; simpl; intros ? B. destruct B; subst; auto.
   exists fd, (list_repeat (nat_of_int (intof_opti (callnum c0))) efR).
   repeat split; auto.
   rewrite <-H14; auto. rewrite PTree.gss; auto.
   eapply Forall_list_repeat; eauto.
  -simpl. red; simpl; intros. subst.
   rewrite <-H13; auto. rewrite PTree.gso; auto.
  -simpl. red; simpl; intros. subst.
   rewrite <-H14; auto. rewrite PTree.gso; auto.
Qed.

Lemma initial_states_match:
  forall gc main1 eL,
  Lenv.initial_state1 prog1 gc (fun p e fd => LsemF.init_node true p e fd) main1 eL ->
  exists main2 eR, Lenv.initial_state1 prog2 gc (fun p e fd => LsemE.init_node p e fd) main2 eR
    /\ trans_node main1 = main2
    /\ env_match eL eR
    /\ env_ids_none main1 eL
    /\ env_ids_some main1 eR.
Proof.
  intros. inversion_clear H.
  destruct init_node_correct with eL main1 as [eR [? [? [? ?]]]]; auto.
  exists (trans_node main1), eR. split; auto.
  subst. constructor 1; auto.
  eapply trans_funcs_find; eauto.
Qed.

Lemma exec_prog_correct:
  forall gc main1 eL n maxn vass vrss,
  Lenv.exec_prog1 prog1 gc (LsemF.eval_node true) main1 eL n maxn vass vrss ->
  forall eR, env_match eL eR ->
  env_ids_none main1 eL ->
  env_ids_some main1 eR ->
  find_funct (node_block prog1) (fst main1) = Some main1 ->
  Lenv.exec_prog1 prog2 gc eval_node (trans_node main1) eR n maxn vass vrss.
Proof.
  induction 1; intros; try congruence.
  +constructor 1 with mrss; auto.
  +destruct e as [ehL seL]. destruct e' as [ehL' seL'].
   destruct eR as [ehR seR].
   eapply trans_node_all_correct in H1; eauto.
   destruct H1 as [eR' [? [? [? ?]]]].
   econstructor 2; eauto.
Qed.

Theorem trans_program_correct:
  forall gc eL main1 vass vrss maxn,
  Lenv.initial_state1 prog1 gc (fun p e fd => LsemF.init_node true p e fd) main1 eL ->
  Lenv.exec_prog1 prog1 gc (LsemF.eval_node true) main1 eL 1 maxn vass vrss ->
  exists main2 eR, Lenv.initial_state1 prog2 gc (fun p e fd => LsemE.init_node p e fd) main2 eR
    /\ Lenv.exec_prog1 prog2 gc LsemE.eval_node main2 eR 1 maxn vass vrss
    /\ nd_rets (snd main2) = nd_rets (snd main1)
    /\ nd_fld (snd main2) = nd_fld (snd main1)
    /\ nd_kind (snd main2) = nd_kind (snd main1).
Proof.
  intros.
  destruct initial_states_match with gc main1 eL as [main2 [eR [? [? [? [? ?]]]]]]; auto.
  exists main2, eR; split; [| split]; auto.
  subst main2. apply exec_prog_correct with eL; auto.
  inv H; try congruence. eapply find_funct_eq; eauto.
  subst. auto.
Qed.

End CORRECTNESS.
