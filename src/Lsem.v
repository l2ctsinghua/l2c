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
Require Import Memdata.
Require Import Integers.
Require Import Lint.
Require Import List.
Require Import Permutation.
Require Import ExtraList.
Require Import Ctypes.
Require Import Cltypes.
Require Import Cop.
Require Import Lvalues.
Require Import Lenv.
Require Import Lident.
Require Import Ltypes.
Require Import Lop.
Require Import Lustre.
Require Import Lint.

Set Implicit Arguments.

Local Open Scope error_monad_scope.

Section EVAL_COMMON.

Variable gc: locenv.

Lemma load_mvl_range_perm:
  forall ty m ofs v,
  load_mvl ty m ofs v ->
  range_perm m (Int.unsigned ofs) (Int.unsigned ofs + sizeof ty).
Proof.
  intros. inv H.
  rewrite <-sizeof_chunk_eq with _ chunk; auto.
  eapply load_valid_access; eauto.
  apply loadbytes_range_perm with m1; auto.
Qed.

Lemma load_mvl_div_alignof:
  forall ty m ofs v,
  load_mvl ty m ofs v ->
  (alignof ty | Int.unsigned ofs).
Proof.
  intros. inv H; auto.
  apply load_valid_access in H1.
  destruct H1. erewrite alignof_chunk_eq; eauto.
Qed.

Lemma load_mvl_app:
  forall ty id o1 o2 m t v,
  load_mvl ty id o1 (Vmvl m) ->
  load_mvl t m o2 v ->
  (alignof t | alignof ty) ->
  load_mvl t id (Int.add o1 o2) v.
Proof.
  intros. inv H.
  apply load_vmvl_false in H3. inv H3.
  cut ((alignof t | Int.unsigned o1)). intros.
  inv H0; [constructor 1 with chunk | constructor 2]; auto.
  eapply loadbytes_load_app; eauto.
  rewrite <-alignof_chunk_eq with t chunk; auto.
  eapply loadbytes_loadbytes_app; eauto.
  apply Zdivides_plus_int; auto.
  apply alignof_1248.
  apply Zdivides_trans with (alignof ty); auto.
Qed.

Lemma loadbytes_load_mvl:
  forall m i t m1 i0 ty v,
  loadbytes m (Int.unsigned i) (sizeof t) = Some m1 ->
  Int.unsigned i0 + sizeof ty  <= sizeof t ->
  (alignof ty | Int.unsigned i) ->
  load_mvl ty m (Int.add i i0) v ->
  load_mvl ty m1 i0 v.
Proof.
  intros. inv H2.
  constructor 1 with chunk; auto.
  eapply loadbytes_load_app_inv; eauto.
  erewrite sizeof_chunk_eq; eauto.
  erewrite <-alignof_chunk_eq; eauto.
  constructor 2; auto.
  eapply loadbytes_loadbytes_app_inv; eauto.
  apply Zdivides_plus_int_inv with i; auto.
  apply alignof_1248.
Qed.

Lemma loadbytes_load_mvl_inv:
  forall m i t m1 i0 ty v,
  loadbytes m (Int.unsigned i) (sizeof t) = Some m1 ->
  load_mvl ty m1 i0 v ->
  (alignof ty | Int.unsigned i) ->
  load_mvl ty m (Int.add i i0) v.
Proof.
  intros.
  inv H0.
  constructor 1 with chunk; auto.
  eapply loadbytes_load_app; eauto.
  erewrite <-alignof_chunk_eq; eauto.
  constructor 2; auto.
  eapply loadbytes_loadbytes_app; eauto.
  apply Zdivides_plus_int; auto.
  apply alignof_1248.
Qed.

Lemma load_chunk_has_type:
  forall t chunk m o v,
  access_mode t = By_value chunk ->
  load chunk m o = Some v ->
  has_type v t.
Proof.
  unfold load, decode_val. intros.
  destruct (valid_access_dec m chunk o); inv H0.
  destruct (proj_bytes _); inv H2.
  destruct t; intros; inv H.
  +destruct i, s; inv H2; inv H1; simpl; auto.
  +destruct f; inv H2; inv H1; simpl; auto.
Qed.

Lemma getN_incl_eq_load_mvl:
  forall t m o v,
  load_mvl t m o v ->
  forall m', length m = length m' ->
  Int.unsigned o + sizeof t <= Z_of_nat (length m) ->
  getN (nat_of_Z (sizeof t)) (nat_of_Z (Int.unsigned o)) m' =
  getN (nat_of_Z (sizeof t)) (nat_of_Z (Int.unsigned o)) m ->
  load_mvl t m' o v.
Proof.
  induction 1; simpl; intros.
  +constructor 1 with chunk; auto.
   unfold load in *.
   destruct (valid_access_dec m chunk (Int.unsigned o)); inv H0.
   rewrite pred_dec_true.
   -unfold size_chunk_nat. rewrite sizeof_chunk_eq with t chunk; eauto.
    rewrite H3; auto.
   -eapply length_valid_access;eauto.
  +constructor 2; auto.
   unfold loadbytes in *. destruct (range_perm_dec m _ _); inv H0.
   rewrite pred_dec_true.
   -rewrite H4; auto.
   -eapply length_range_perm; eauto.
Qed.

Lemma load_mvl_full:
  forall t m m1,
  load_mvl t m Int.zero (Vmvl m1) ->
  sizeof t = Z.of_nat (length m) ->
  m1 = m.
Proof.
  intros. inv H.
  +apply load_vmvl_false in H2. inv H2.
  +rewrite Int.unsigned_zero, H0 in H3.
   symmetry. apply loadbytes_first with nil.
   rewrite <-app_nil_end; auto.
Qed.

Definition load_env(ty: type)(e: locenv)(b: ident)(ofs: int)(v: val): Prop :=
  exists m t, e ! b = Some (m,t)
    /\ sizeof t = Z_of_nat (length m)
    /\ load_mvl ty m ofs v.

Inductive store_mvl(ty: type)(m: mvl)(ofs: int): val -> mvl-> Prop :=
  | store_mvl_value: forall v chunk m',
      access_mode ty = By_value chunk ->
      store chunk m (Int.unsigned ofs) v = Some m' ->
      store_mvl ty m  ofs v m'
  | store_mvl_copy: forall m1 m',
      access_mode ty = By_copy \/ access_mode ty = By_reference ->
      storebytes m (Int.unsigned ofs) m1 = Some m' ->
      sizeof ty = Z_of_nat (length m1) ->
      (alignof ty | Int.unsigned ofs) ->
      store_mvl ty m ofs (Vmvl m1) m'.

Lemma store_mvl_div_alignof:
  forall ty m m' ofs v,
  store_mvl ty m ofs v m' ->
  (alignof ty | Int.unsigned ofs).
Proof.
  intros. inv H; auto.
  apply store_valid_access in H1.
  destruct H1. erewrite alignof_chunk_eq; eauto.
Qed.

Lemma store_mvl_range_perm:
  forall ty m m' ofs v,
  store_mvl ty m ofs v m' ->
  range_perm m' (Int.unsigned ofs) (Int.unsigned ofs + sizeof ty).
Proof.
  intros. inv H.
  erewrite <-sizeof_chunk_eq; eauto.
  eapply store_valid_access; eauto.
  rewrite H2. eapply storebytes_range_perm; eauto.
Qed.

Theorem store_mvl_range_perm_1:
  forall ty m m' ofs v,
  store_mvl ty m ofs v m' ->
  forall ofs' n,
  range_perm m ofs' (ofs' + n) ->
  range_perm m' ofs' (ofs' + n).
Proof.
  intros. inv H.
  eapply store_range_perm_1; eauto.
  eapply storebytes_range_perm_1; eauto.
Qed.

Theorem store_mvl_range_perm_2:
  forall ty m m' ofs v,
  store_mvl ty m ofs v m' ->
  forall ofs' n,
  range_perm m' ofs' (ofs' + n) ->
  range_perm m ofs' (ofs' + n).
Proof.
  intros. inv H.
  eapply store_range_perm_2; eauto.
  eapply storebytes_range_perm_2; eauto.
Qed.

Lemma store_mvl_sizeof:
  forall ty m ofs v m',
  store_mvl ty m ofs v m' ->
  sizeof ty <= Int.max_signed.
Proof.
  intros. eapply store_mvl_range_perm in H; eauto.
  red in H. omega.
Qed.

Lemma store_mvl_length:
  forall ty m m' ofs v,
  store_mvl ty m ofs v m' ->
  length m = length m'.
Proof.
  induction 1; intros.
  eapply store_length; eauto.
  eapply storebytes_length; eauto.
Qed.

Lemma store_mvl_range_perm2:
  forall ty m m' ofs v,
  store_mvl ty m ofs v m' ->
  range_perm m (Int.unsigned ofs) (Int.unsigned ofs + sizeof ty).
Proof.
  intros. generalize H. intros.
  apply store_mvl_range_perm in H.
  apply store_mvl_length in H0.
  red. rewrite H0; auto.
Qed.

Lemma loadbytes_store_mvl_other:
  forall t m1 ofs v m2 ofs' n,
  store_mvl t m1 ofs v m2 ->
  ofs' + n <= Int.unsigned ofs
  \/ Int.unsigned ofs + sizeof t <= ofs' ->
  loadbytes m2 ofs' n = loadbytes m1 ofs' n.
Proof.
  intros.
  destruct (zle n 0).
  +unfold loadbytes. repeat rewrite pred_dec_false; auto.
   red; intros. red in H1. omega.
   red; intros. red in H1. omega.
  +inv H.
   apply loadbytes_store_other with chunk (Int.unsigned ofs) v; auto.
   rewrite sizeof_chunk_eq with t _; auto.
   apply loadbytes_storebytes_other with (Int.unsigned ofs) m0; auto.
   omega.
Qed.

Lemma loadbytes_store_exists:
  forall chunk mv o v mv' m i size,
  store chunk mv (Int.unsigned o) v = Some mv' ->
  loadbytes m (Int.unsigned i) size = Some mv ->
  (align_chunk chunk | Int.unsigned i) ->
  exists m', store chunk m (Int.unsigned (Int.add i o)) v = Some m'
    /\ loadbytes m' (Int.unsigned i) size = Some mv'.
Proof.
  unfold store, loadbytes in *; intros.
  destruct (valid_access_dec mv chunk (Int.unsigned o)); try congruence.
  destruct (range_perm_dec m (Int.unsigned i) (Int.unsigned i + size)); try congruence.
  inv H. inv H0.

  exists (setN (encode_val chunk v) (nat_of_Z (Int.unsigned (Int.add i o))) m).
  destruct v0 as [[? [? ?]] ?]. unfold range_perm in *.
  rewrite <-getN_length in *; try omega.
  rewrite nat_of_Z_eq in *; try omega.
  unfold Int.add.
  generalize Int.max_signed_unsigned. intros.
  rewrite Int.unsigned_repr; try omega.
  repeat rewrite pred_dec_true; auto.
  +split;auto. f_equal. rewrite nat_of_Z_plus; try omega.
   apply getN_setN_swap; try omega.
   rewrite <-nat_of_Z_plus; try omega.
     apply Nat2Z.inj_le. rewrite nat_of_Z_eq; try omega.
     rewrite encode_val_length.
     apply Z2Nat.inj_le in H0; try omega.
       rewrite nat_of_Z_plus in H0; try omega.
       unfold size_chunk_nat; auto.
  +rewrite setN_length; try omega. rewrite encode_val_length; auto.
   rewrite nat_of_Z_plus; try omega.
   unfold size_chunk_nat in *.
   repeat rewrite <-nat_of_Z_plus; try omega.
   apply Nat2Z.inj_le. rewrite nat_of_Z_eq; try omega.
  +unfold valid_access, range_perm.
   repeat split; try omega.
   apply Zdivide_plus_r; auto.
Qed.

Lemma loadbytes_storebytes_exists:
  forall mv o v mv' m i size,
  storebytes mv (Int.unsigned o) v = Some mv' ->
  loadbytes m (Int.unsigned i) size = Some mv ->
  exists m', storebytes m (Int.unsigned (Int.add i o)) v = Some m'
    /\ loadbytes m' (Int.unsigned i) size = Some mv'.
Proof.
  unfold storebytes, loadbytes in *; intros.
  destruct (range_perm_dec mv _ _); try congruence.
  destruct (range_perm_dec m (Int.unsigned i) ); try congruence.
  inv H. inv H0.
  exists (setN v (nat_of_Z (Int.unsigned (Int.add i o))) m).
  unfold range_perm in *. rewrite <-getN_length in r; try omega.
  rewrite nat_of_Z_eq in r; try omega.
  unfold Int.add.
  generalize Int.max_signed_unsigned. intros.
  rewrite Int.unsigned_repr; try omega.
  repeat rewrite pred_dec_true; auto.
  +split;auto. f_equal.
   rewrite nat_of_Z_plus; try omega.
   apply getN_setN_swap.
   -rewrite <-nat_of_Z_plus; try omega.
    apply Nat2Z.inj_le. rewrite nat_of_Z_eq; try omega.
   -destruct r. destruct H1. apply Z2Nat.inj_le in H1; try omega.
    rewrite nat_of_Z_plus, nat_of_Z_of_nat in H1; try omega.
    auto.
  +rewrite setN_length; try omega.
   replace (length v) with (nat_of_Z (Z_of_nat (length v))).
   rewrite <- nat_of_Z_plus; try omega.
   apply Nat2Z.inj_le. rewrite nat_of_Z_eq; try omega.
    rewrite nat_of_Z_of_nat; try omega.
  +omega.
Qed.

Lemma loadbytes_store_mvl_exists:
  forall t mv o v mv',
  store_mvl t mv o v mv' ->
  forall m i size, loadbytes m (Int.unsigned i) size = Some mv ->
  (alignof t | Int.unsigned i) ->
  exists m', store_mvl t m (Int.add i o) v m'
    /\ loadbytes m' (Int.unsigned i) size = Some mv'.
Proof.
  induction 1; simpl; intros.
  +apply loadbytes_store_exists with _ _ _ _ _ m i size in H0; auto.
   destruct H0 as [m'0 [? ?]].
   exists m'0; split; auto.
   constructor 1 with chunk; auto.
   erewrite <-alignof_chunk_eq; eauto.
  +eapply loadbytes_storebytes_exists in H0; eauto.
   destruct H0 as [m'0 [? ?]].
   exists m'0; split; auto.
   constructor 2; auto.
   apply Zdivides_plus_int; auto.
   apply alignof_1248.
Qed.

Lemma store_mvl_load_arystr:
  forall ty m o v m1,
  store_mvl ty m o v m1 ->
  is_arystr ty = true ->
  load_mvl ty m1 o v.
Proof.
  induction 1; intros.
  +destruct ty; simpl in *; congruence.
  +constructor 2; auto. rewrite H1.
   eapply loadbytes_storebytes_same; eauto.
Qed.

Inductive store_env(ty: type)(e: locenv)(b: ident)(ofs: int): val -> locenv -> Prop :=
  | store_env_intro: forall m m' t v,
      e ! b = Some (m,t) ->
      sizeof t = Z_of_nat (length m) ->
      store_mvl ty m ofs v m'->
      store_env ty e b ofs v (PTree.set b (m',t) e).

Inductive vkind: Type := Gid | Lid | Sid | Aid.

Inductive eval_var(ty: type)(e: locenv)(id: ident)(ofs: int): vkind -> val ->Prop :=
  | eval_var_gid: forall v,
      load_env ty gc id ofs v->
      eval_var ty e id ofs Gid v
  | eval_var_vid: forall v,
      load_env ty e id ofs v->
      eval_var ty e id ofs Lid v.

Lemma load_env_eval_var_app:
  forall ty e id o1 o2 m t v,
  load_env ty e id o1 (Vmvl m) ->
  load_mvl t m o2 v ->
  (alignof t | alignof ty) ->
  load_env t e id (Int.add o1 o2) v.
Proof.
  intros. destruct H as [m1 [t1 [? [? ?]]]].
  exists m1, t1; repeat (split; auto).
  eapply load_mvl_app; eauto.
Qed.

Lemma load_mvl_eval_var_app:
  forall ty e id o1 o2 k m t v,
  eval_var ty e id o1 k (Vmvl m) ->
  load_mvl t m o2 v ->
  (alignof t | alignof ty) ->
  eval_var t e id (Int.add o1 o2) k v.
Proof.
  intros. inv H; [constructor 1 | constructor 2]; auto;
  eapply load_env_eval_var_app; eauto.
Qed.

Lemma load_env_app_inv:
  forall t e id o1 o2 m aty v,
  load_env t e id o1 (Vmvl m) ->
  load_env aty e id (Int.add o1 o2) v ->
  Int.unsigned o2 + sizeof aty <= sizeof t ->
  (alignof aty | alignof t) ->
  load_mvl aty m o2 v.
Proof.
  intros.
  destruct H as [? [? [? [? ?]]]].
  destruct H0 as [? [? [? [? ?]]]].
  rewrite H0 in H. inv H.
  apply loadbytes_load_mvl with x o1 t; auto.
  inv H4; auto.
  apply load_vmvl_false in H7. tauto.
  apply Zdivides_trans with (alignof t); auto.
  eapply load_mvl_div_alignof; eauto.
Qed.

Lemma eval_var_app_inv:
  forall e id t aty o1 o2 k m v,
  eval_var aty e id (Int.add o1 o2) k v ->
  eval_var t e id o1 k (Vmvl m) ->
  Int.unsigned o2 + sizeof aty <= sizeof t ->
  (alignof aty | alignof t) ->
  load_mvl aty m o2 v.
Proof.
  intros. inv H; inv H0; eapply load_env_app_inv; eauto.
Qed.

Lemma load_argv_loadbytes_app:
  forall ty m o v,
  load_argv ty m o v ->
  forall mv mv', store_mvl ty mv Int.zero v mv' ->
  length mv = nat_of_Z (sizeof ty) ->
  loadbytes m (Int.unsigned o) (sizeof ty) = Some mv'.
Proof.
  induction 1; intros.
  +inv H1.
   -rewrite H3 in H. inv H.
    rewrite Int.unsigned_zero in *.
    rewrite H0. f_equal.
    unfold store in H4.
    destruct (valid_access_dec mv chunk 0); inv H4.
    rewrite setN_encode_val; auto.
    apply sizeof_chunk_eq in H3.
    rewrite H2,<-H3; auto.
   -rewrite H in *. destruct H3; congruence.
  +inv H2.
   -rewrite H4 in *. destruct H; congruence.
   -rewrite Int.unsigned_zero in H6.
    generalize H6 H6;intros.
    apply storebytes_range_perm in H2.
    apply storebytes_length in H4.
    unfold range_perm in *.
    rewrite storebytes_full in H6; try omega.
    inv H6. auto.
    rewrite H7 in H3. rewrite nat_of_Z_of_nat in H3. auto.
Qed.

Lemma sem_cast_decode_encode_val:
  forall chunk v ty,
  access_mode ty = By_value chunk ->
  sem_cast v ty ty = Some v ->
  decode_val chunk (encode_val chunk v) = Some v.
Proof.
  unfold decode_val, encode_val, Lop.sem_cast. intros.
  destruct ty; simpl in *; try congruence.
  +destruct i,s; inv H; inv H0; destruct v;
   try congruence; rewrite Memdata.proj_inj_bytes.
   -rewrite decode_encode_int_1. rewrite Int.sign_ext_zero_ext; try omega; auto.
   -rewrite decode_encode_int_1. rewrite Int.zero_ext_idem; try omega. auto.
   -rewrite decode_encode_int_2. rewrite Int.sign_ext_zero_ext; try omega. auto.
   -rewrite decode_encode_int_2. rewrite Int.zero_ext_idem; try omega. auto.
   -rewrite decode_encode_int_4. auto.
   -rewrite decode_encode_int_4. auto.
   -rewrite decode_encode_int_1. rewrite Int.zero_ext_idem; try omega.
    destruct (Int.eq _ _); inv H1; auto.
   -rewrite decode_encode_int_1. rewrite Int.zero_ext_idem; try omega.
    destruct (Int.eq _ _); inv H1; auto.
  +destruct f; inv H; inv H0; destruct v;
   try congruence; rewrite Memdata.proj_inj_bytes.
   -rewrite decode_encode_int_4. rewrite Floats.Float32.of_to_bits; auto.
   -rewrite decode_encode_int_8. rewrite Floats.Float.of_to_bits; auto.
Qed.

Lemma store_storebytes_eq:
  forall chunk m o v m' mv,
  store chunk m o v = Some m' ->
  length mv = size_chunk_nat chunk ->
  load chunk mv 0 = Some v ->
  storebytes m o mv = Some m'.
Proof.
  unfold store, storebytes. intros.
  destruct (valid_access_dec _ _ _); inv H.
  unfold load in H1. simpl in *.
  destruct (valid_access_dec _ chunk 0); inv H1.
  destruct v0. destruct v1.
  rewrite <-H0 in H2. rewrite getN_full in H2.
  rewrite H0. unfold size_chunk_nat.
  generalize (size_chunk_pos chunk). intros.
  rewrite nat_of_Z_eq; try omega.
  rewrite pred_dec_true; auto.
  f_equal. f_equal.
  apply deconde_encode_inv; auto.
Qed.

Lemma store_mvl_storebytes_eq:
  forall ty m o' v m' mv,
  store_mvl ty m o' v m' ->
  load_mvl ty mv Int.zero v ->
  sizeof ty = Z.of_nat (length mv) ->
  storebytes m (Int.unsigned o') mv = Some m'.
Proof.
  intros. inv H.
  +inv H0.
   -rewrite H in H2. inv H2. rewrite Int.unsigned_zero in *.
    eapply store_storebytes_eq; eauto.
    unfold size_chunk_nat.
    rewrite sizeof_chunk_eq with (t:=ty); auto.
    rewrite H1. rewrite nat_of_Z_of_nat; auto.
   -destruct H; try congruence.
  +apply load_mvl_full in H0; subst; auto.
Qed.

Definition eval_const(c: const): val :=
  match c with
  | Cint i => Vint i
  | Cfloat f => Vfloat f
  | Csingle f => Vsingle f
  | Cbool b => if b then Vtrue else Vfalse
  end.

Definition eval_patn(p: patn): option int :=
  match p with
  | Paint i => Some i
  | Pachar c => Some c
  | Pabool b => Some (if b then Int.one else Int.zero)
  | Pany => None
  end.

Fixpoint select_case(A: Type)(i: int)(pl: list (patn*A)): option A :=
  match pl with
  | nil => None
  | (p,a) :: pal =>
     match (eval_patn p) with
     | None => Some a
     | Some i1 => if (Int.eq i1 i) then Some a else select_case i pal
     end
  end.

Lemma select_case_in:
  forall (A: Type) i l (a: A),
  select_case i l = Some a ->
  In a (map (@snd patn A) l).
Proof.
  induction l; simpl; intros.
  congruence.
  destruct a. destruct (eval_patn p).
  destruct (Int.eq i0 i). inv H; auto.
  apply IHl in H; auto. inv H; auto.
Qed.

Lemma trans_select_case:
  forall pl i a f,
  select_case i pl = Some a ->
  select_case i (trans_patns f pl) = Some (f a).
Proof.
  induction pl; simpl; intros.
  congruence.
  destruct a. simpl in *.
  destruct (eval_patn p); auto.
  destruct (Int.eq i0 i); auto.
  inv H; auto. inv H; auto.
Qed.

Inductive eval_field(m: mvl)(fld: fieldlist): ident*type -> val-> Prop :=
  | eval_field_: forall id ty delta v,
      field_offset id fld = OK delta ->
      field_type id fld = OK ty ->
      load_mvl ty m (Int.repr delta) v ->
      eval_field m fld (id,ty) v.

Definition array_ofs(i: int)(aty: type): int :=
  Int.mul (Int.repr (sizeof aty)) i.

Lemma alignof_array_ofs:
  forall t j,
  (alignof t | Int.unsigned (array_ofs j t)).
Proof.
  unfold array_ofs. intros.
  apply Zdivides_mul_int; auto.
  apply sizeof_alignof_compat.
  apply alignof_1248.
Qed.

Lemma array_ofs_add_le:
  forall i num aid aty,
  Int.unsigned i < Z.max 0 num ->
  Int.unsigned (array_ofs i aty) + sizeof aty <= sizeof (Tarray aid aty num).
Proof.
  intros. simpl sizeof.
  generalize (Int.unsigned_range i) (sizeof_pos aty); intros.
  unfold array_ofs. rewrite int_mul_repr.
  apply Zle_trans with (sizeof aty * Int.unsigned i + sizeof aty).
  apply Zplus_le_compat_r. apply int_repr_le.
  apply Zmult_le_0_compat; try omega.
  apply zmul_add_le_mul_lt; omega.
Qed.

Lemma signed_repr_lt_inv:
  forall i z,
  0 <= z ->
  0 <= i < Int.signed (Int.repr z) ->
  i < z.
Proof.
  unfold Int.signed. intros.
  generalize Int.modulus_pos. intros.
  cut (0 <= z / Int.modulus * Int.modulus). intros.
  rewrite Int.unsigned_repr_eq in *.
  rewrite Zmod_eq_full in H0; try omega.
  destruct (zlt _ Int.half_modulus); omega.
  apply Z.mul_nonneg_nonneg; try omega.
  apply Z.div_pos; try omega.
Qed.

Lemma array_le_max_signed_inv:
  forall num o size,
  0 <= o ->
  o + size * num <= Int.max_signed ->
  size > 0 ->
  num <= Int.max_signed.
Proof.
  intros.
  destruct (zle num 0).
  unfold Int.max_signed. simpl. omega.
  apply Zle_trans with (o + 1 * num); try omega.
  apply Zle_trans with (o + size * num); try omega.
  apply Zplus_le_compat_l. apply Zmult_le_compat_r; omega.
Qed.

Definition mvl_mapping (m m': mvl)(o: int)(ty: type): Prop :=
  forall o' n,
  o' + n <= Int.unsigned o \/ Int.unsigned o + sizeof ty <= o' ->
  loadbytes m' o' n = loadbytes m o' n.

Lemma store_mvl_mapping:
  forall m m' ty o v,
  store_mvl ty m o v m' ->
  mvl_mapping m m' o ty.
Proof.
  unfold mvl_mapping. intros.
  eapply loadbytes_store_mvl_other; eauto; try omega.
Qed.

Section LVALUE_DISJOINT.

Variable eval_lvalue: sexp -> ident -> int -> vkind -> Prop.

Inductive lvalue_disjoint(a1 a2: sexp): Prop :=
  | lvalue_disjoint_arystr: forall id1 id2 o1 o2 k1 k2,
     eval_lvalue a1 id1 o1 k1 ->
     eval_lvalue a2 id2 o2 k2 ->
     k1 = Lid \/ k1 = Sid ->
     id1 <> id2 \/ Int.unsigned o1 + sizeof (typeof a1) <= Int.unsigned o2 \/
       Int.unsigned o2 + sizeof (typeof a2) <= Int.unsigned o1 ->
     lvalue_disjoint a1 a2.

Inductive assign_disjoint(a1 a2: sexp): Prop :=
  | assign_disjoint_val: forall chunk,
     access_mode (typeof a2) = By_value chunk ->
     assign_disjoint a1 a2
  | assign_disjoint_arystr:
     access_mode (typeof a2) = By_copy \/ access_mode (typeof a2) = By_reference ->
     lvalue_disjoint a1 a2 ->
     assign_disjoint a1 a2.

Definition assign_list_disjoint(l1 l2: list sexp): Prop :=
  forall a1 a2, In a1 l1 -> In a2 l2 -> assign_disjoint a1 a2.

Definition lvalue_disjoints(a: sexp)(l: list sexp): Prop :=
  forall a1, In a1 l -> lvalue_disjoint a a1.

Inductive lvalue_list_norepet: list sexp -> Prop :=
  | lvalue_list_norepet_nil:
     lvalue_list_norepet nil
  | lvalue_list_norepet_cons: forall a al,
     lvalue_disjoints a al ->
     lvalue_list_norepet al ->
     lvalue_list_norepet (a::al).

End LVALUE_DISJOINT.

Inductive eval_sexp(e: locenv): sexp -> val -> Prop :=
  | eval_Sconst: forall c ty,
      has_type (eval_const c) ty ->
      eval_sexp e (Sconst c ty) (eval_const c)
  | eval_Sunop: forall op a ty v1 v,
      eval_sexp e a v1 ->
      sem_unary_operation op v1 (typeof a) = Some v ->
      has_type v ty ->
      eval_sexp e (Sunop op a ty) v
  | eval_Sbinop: forall op a1 a2 ty v1 v2 v,
      eval_sexp e a1 v1 ->
      eval_sexp e a2 v2 ->
      typeof a1 = typeof a2 ->
      sem_binary_operation op v1 v2 (typeof a1) ty = Some v ->
      has_type v ty ->
      eval_sexp e (Sbinop op a1 a2 ty) v
  | eval_Scast: forall a ty v v1,
      eval_sexp e a v1 ->
      sem_cast v1 (typeof a) ty = Some v ->
      eval_sexp e (Scast a ty) v
  | eval_Rlvalue: forall a id ofs k v,
      eval_lvalue e a id ofs k->
      eval_var (typeof a) e id ofs k v ->
      has_type v (typeof a) ->
      eval_sexp e a v

with eval_lvalue(e: locenv): sexp -> ident -> int -> vkind -> Prop :=
  | eval_Svar: forall id ty m,
     e ! id = Some (m, ty) ->
     eval_lvalue e (Svar id ty) id Int.zero Lid
  | eval_Scvar: forall id ty m,
     e ! id = None ->
     gc ! id = Some (m, ty) ->
     eval_lvalue e (Svar id ty) id Int.zero Gid
  | eval_Saryacc: forall a a1 ty l ofs vk i aid z,
     eval_lvalue e a l ofs vk ->
     eval_sexp e a1 (Vint i) ->
     typeof a = Tarray aid ty z ->
     0 <= Int.signed i < Z.max 0 z ->
     Int.unsigned ofs + sizeof (typeof a) <= Int.max_signed ->
     eval_lvalue e (Saryacc a a1 ty) l (Int.add ofs (array_ofs i ty)) vk
  | eval_Sfield: forall a i ty l sid fld ofs vk delta,
     eval_lvalue e a l ofs vk->
     typeof a = Tstruct sid fld ->
     field_offset i fld = OK delta ->
     field_type i fld = OK ty ->
     Int.unsigned ofs + sizeof (typeof a) <= Int.max_signed ->
     eval_lvalue e (Sfield a i ty) l (Int.add ofs (Int.repr delta)) vk.

Scheme eval_sexp_ind2 := Minimality for eval_sexp Sort Prop
  with eval_lvalue_ind2 := Minimality for eval_lvalue Sort Prop.
Combined Scheme eval_sexp_lvalue_ind from eval_sexp_ind2, eval_lvalue_ind2.

Definition eval_sexps(e: locenv)(al: list sexp)(vl: list val):=
  Forall2 (eval_sexp e) al vl.

Inductive eval_cast: val -> type -> val -> Prop :=
  | eval_cast_val: forall ty chunk v1 v2,
     access_mode ty = By_value chunk ->
     sem_cast v1 ty ty = Some v2 ->
     eval_cast v1 ty v2
  | eval_cast_arystr: forall ty v,
     access_mode ty = By_copy \/ access_mode ty = By_reference ->
     eval_cast v ty v.

Inductive eval_casts: list val -> list type -> list val -> Prop :=
  | eval_casts_nil:
      eval_casts nil nil nil
  | eval_casts_cons:  forall  ty tyl v1 v2 vl1 vl2,
      eval_cast v1 ty v2 ->
      eval_casts vl1 tyl vl2 ->
      eval_casts (v1 :: vl1) (ty :: tyl) (v2 :: vl2).

Lemma sem_cast_idem:
  forall v1 ty v2,
  sem_cast v1 ty ty = Some v2 ->
  sem_cast v2 ty ty = Some v2.
Proof.
  unfold sem_cast.
  destruct ty; simpl; intros; try congruence.
  +destruct i, s, v1; inv H; simpl;
   try rewrite Int.sign_ext_idem; try omega; auto;
   try rewrite Int.zero_ext_idem; try omega; auto;
   destruct (Int.eq i Int.zero); simpl; auto.
  +destruct f, v1; inv H; simpl; auto.
Qed.

Lemma eval_cast_idem:
  forall v ty v',
  eval_cast v ty v' ->
  eval_cast v' ty v'.
Proof.
  induction 1; intros.
  +constructor 1 with chunk; auto.
   eapply sem_cast_idem; eauto.
  +constructor 2; auto.
Qed.

Lemma eval_cast_int32s:
  forall v v',
  eval_cast v type_int32s v' ->
  v' = v.
Proof.
  intros. inv H; auto.
  unfold sem_cast in H1. simpl in *.
  destruct v; inv H1. auto.
Qed.

Lemma eval_casts_length_l:
  forall vl1 tyl vl2,
  eval_casts vl1 tyl vl2 ->
  length vl1 = length vl2.
Proof.
  induction 1; simpl; intros; omega.
Qed.

Lemma eval_casts_length_r:
  forall vl1 tyl vl2,
  eval_casts vl1 tyl vl2 ->
  length tyl = length vl2.
Proof.
  induction 1; simpl; intros; omega.
Qed.

Lemma eval_casts_app:
  forall vl1 tl1,
  eval_casts vl1 tl1 vl1 ->
  forall vl2 tl2,
  eval_casts vl2 tl2 vl2 ->
  eval_casts (vl1 ++ vl2) (tl1 ++ tl2) (vl1 ++ vl2).
Proof.
  induction vl1; simpl; intros; inv H; auto.
  constructor 2; auto.
Qed.

Lemma eval_casts_app_inv_r:
  forall vl tyl1 tyl2 vl1 vl2,
  eval_casts (vl1++vl2) (tyl1++tyl2) vl ->
  length tyl1 = length vl1 ->
  exists vl1' vl2', eval_casts vl1 tyl1 vl1'
    /\ eval_casts vl2 tyl2 vl2'
    /\ vl = vl1' ++ vl2'.
Proof.
  induction vl; simpl; intros; inv H; auto.
  +exists nil, nil. symmetry in H2. symmetry in H3.
   apply app_eq_nil in H2. apply app_eq_nil in H3.
   destruct H2. destruct H3. subst.
   repeat (split; auto); constructor.
  +destruct tyl1, vl1; simpl in *; try (inv H0; fail).
   -subst. exists nil, (a :: vl). repeat (split; auto).
    constructor. constructor 2; auto.
   -inv H1. inv H2.
    destruct IHvl with tyl1 tyl2 vl1 vl2 as [vl1' [vl2' [? [? ?]]]]; auto.
    subst. exists (a::vl1'), vl2'. repeat (split; auto).
    constructor 2; auto.
Qed.

Lemma sem_cast_has_type:
  forall t1 t2 v1 v2,
  sem_cast v1 t1 t2 = Some v2 ->
  has_type v1 t1 ->
  has_type v2 t2.
Proof.
  unfold sem_cast. intros.
  destruct v1, t1; simpl; try tauto;
  destruct t2; simpl; intros; inv H; auto.
  +destruct i1; inv H2; auto.
  +destruct f; inv H2; auto.
  +destruct f0; try tauto.
   destruct i; try congruence;
   destruct (cast_float_int s f); inv H2; auto.
  +destruct f0, f1; inv H2; auto.
  +destruct i, f0; inv H2; destruct (cast_single_int _ _); inv H1; auto.
  +destruct f0, f1; inv H2; auto.
  +destruct i0; inv H2; auto.
  +destruct f; inv H2.
  +destruct i0; inv H2.
  +destruct f0; inv H2.
Qed.

Lemma eval_cast_has_type:
  forall v ty,
  has_type v ty ->
  forall v', eval_cast v ty v' ->
  has_type v' ty.
Proof.
  intros. inv H0; auto.
  eapply sem_cast_has_type; eauto.
Qed.

Lemma eval_casts_has_types:
  forall vl tys,
  has_types vl tys ->
  forall vl', eval_casts vl tys vl' ->
  has_types vl' tys.
Proof.
  induction 1; intros.
  inv H. constructor.
  inv H1. constructor 2.
  eapply eval_cast_has_type; eauto.
  eapply IHForall2; eauto.
Qed.

Inductive load_loopid(e: locenv): option sexp -> option int -> int -> Prop :=
  | load_loopid_some: forall j i,
      eval_sexp e (Svar ACG_I type_int32s) (Vint i) ->
      load_loopid e (Some (Svar ACG_I type_int32s)) (Some j) i
  | load_loopid_none:
      load_loopid e None None Int.zero.

Inductive option_match: option sexp -> option int -> Prop :=
  | option_match_some: forall j,
      option_match (Some (Svar ACG_I type_int32s)) (Some j)
  | option_match_none:
      option_match None None.

Lemma load_loopid_option_match:
  forall te oa oj i,
  load_loopid te oa oj i ->
  option_match oa oj.
Proof.
  induction 1; constructor; auto.
Qed.

Lemma load_mvl_determ:
  forall t id ofs v1,
  load_mvl t id ofs v1 ->
  forall v2, load_mvl t id ofs v2 ->
  v1 = v2.
Proof.
  induction 1; intros.
  +inv H1; auto; try congruence.
   destruct H2; congruence.
  +inv H2; auto; try congruence.
   destruct H; congruence.
Qed.

Lemma load_env_determ:
  forall t e id ofs v1,
  load_env t e id ofs v1 ->
  forall v2, load_env t e id ofs v2 ->
  v1 = v2.
Proof.
  intros. destruct H as [m1 [t1 [? [? ?]]]].
  destruct H0 as [m2 [t2 [? [? ?]]]].
  rewrite H in H0. inv H0.
  eapply load_mvl_determ; eauto.
Qed.

Lemma eval_var_determ:
  forall t e id ofs k v1,
  eval_var t e id ofs k v1 ->
  forall v2, eval_var t e id ofs k v2 ->
  v1 = v2.
Proof.
  induction 1; intros; inv H0; auto;
  eapply load_env_determ; eauto.
Qed.

Lemma eval_sexp_determ:
forall e,
(
  forall s v1,
  eval_sexp e s v1 ->
  forall v2, eval_sexp e s v2 ->
  v1 = v2
)
/\
(
  forall a id1 ofs1 k1,
  eval_lvalue e a id1 ofs1 k1->
  forall id2 ofs2 k2, eval_lvalue e a id2 ofs2 k2 ->
  id1 = id2 /\ ofs1 = ofs2 /\ k1 = k2
).
Proof.
  intros e. apply eval_sexp_lvalue_ind; intros.
  +inv H0; auto. destruct c; inv H1.
  +inv H3. apply H0 in H7. congruence. inv H4.
  +inv H6. apply H0 in H11. apply H2 in H12.
    congruence. inv H7.
  +inv H2. apply H0 in H5. congruence. inv H3.
  +inv H3; try (inv H; fail).
   apply H0 with id0 ofs0 k0 in H4. destruct H4 as [? [? ?]]; subst.
   apply eval_var_determ with (typeof a) e id0 ofs0 k0; auto.
  +inv H0; auto. congruence.
  +inv H1; auto. congruence.
  +inv H6. apply H0 in H10; auto. destruct H10 as [? [? ?]].
    apply H2 with (Vint i0) in H11; auto. inv H11. auto.
  +inv H5. apply H0 in H9. intuition. subst. congruence.
Qed.

Lemma eval_sexp_lvalue_var:
  forall e s v,
  eval_sexp e s v ->
  forall id ofs k, eval_lvalue e s id ofs k ->
  eval_var (typeof s) e id ofs k v.
Proof.
  induction 1; intros.
  inv H0.
  inv H2.
  inv H4.
  inv H1.
  eapply eval_sexp_determ in H; eauto.
  intuition. subst. auto.
Qed.

Lemma eval_sexp_exists_lvalue:
  forall e a m,
  eval_sexp e a (Vmvl m) ->
  exists id ofs k, eval_lvalue e a id ofs k.
Proof.
  induction a; intros;
  try (inv H; eauto; fail).
  +destruct c; inv H; try inv H0.
   destruct b; inv H3.
  +inv H. apply sem_cast_not_mvl in H4. inv H4. inv H0.
  +inv H. apply sem_unary_operation_not_mvl in H5.
   inv H5. inv H0.
  +inv H. apply sem_binary_operation_not_mvl in H8.
   inv H8. inv H0.
Qed.

Lemma eval_lvalue_env_some:
  forall e a id ofs k,
  eval_lvalue e a id ofs k ->
  match k with
  | Gid => exists mv, gc ! id = Some mv
  | Lid => exists mv, e ! id = Some mv
  | _ => False
  end.
Proof.
  induction 1; simpl; intros; eauto.
Qed.

Lemma load_mvl_size:
  forall ty m ofs m1,
  load_mvl ty m ofs (Vmvl m1) ->
  sizeof ty = Z.of_nat (length m1).
Proof.
  intros. inv H.
  apply load_vmvl_false in H1. tauto.
  eapply loadbytes_length2; eauto.
Qed.

Lemma load_env_size:
  forall ty e id ofs m,
  load_env ty e id ofs (Vmvl m) ->
  sizeof ty = Z.of_nat (length m).
Proof.
  intros. destruct H as [m1 [t1 [? [? ?]]]].
  eapply load_mvl_size; eauto.
Qed.

Lemma eval_var_size:
  forall ty e id ofs k m,
  eval_var ty e id ofs k (Vmvl m) ->
  sizeof ty = Z.of_nat (length m).
Proof.
  intros. inv H; eapply load_env_size; eauto.
Qed.

Lemma eval_sexp_size:
  forall e a m,
  eval_sexp e a (Vmvl m) ->
  sizeof (typeof a) = Z_of_nat (length m).
Proof.
  intros. subst.
  destruct eval_sexp_exists_lvalue with e a m as [? [? [? ?]]]; auto.
  eapply eval_sexp_lvalue_var in H0; eauto.
  eapply eval_var_size; eauto.
Qed.

Lemma load_env_range_perm:
  forall t e id o v,
  load_env t e id o v ->
  sizeof t > 0 /\ Int.unsigned o + sizeof t <= Int.max_signed.
Proof.
  intros.
  destruct H as [m [ty [? [? ?]]]].
  apply load_mvl_range_perm in H1.
  red in H1. omega.
Qed.

Lemma eval_var_range_perm:
  forall t e id o k v,
  eval_var t e id o k v ->
  sizeof t > 0 /\ Int.unsigned o + sizeof t <= Int.max_signed.
Proof.
  intros. inv H;
  eapply load_env_range_perm; eauto.
Qed.

Lemma eval_sexp_aryacc:
  forall e a m ai i aid t n v,
  eval_sexp e a (Vmvl m) ->
  eval_sexp e ai (Vint i) ->
  typeof a = Tarray aid t n ->
  load_mvl t m (array_ofs i t) v ->
  has_type v t ->
  0 <= Int.signed i < Z.max 0 n ->
  eval_sexp e (Saryacc a ai t) v.
Proof.
  intros.
  destruct eval_sexp_exists_lvalue with e a m as [id [o [k ?]]]; auto.
  apply eval_Rlvalue with id (Int.add o (array_ofs i t)) k; simpl; auto.
  eapply eval_Saryacc; eauto.
  eapply eval_sexp_lvalue_var in H; eauto.
  eapply eval_var_range_perm; eauto.
  eapply eval_sexp_lvalue_var in H; eauto.
  eapply load_mvl_eval_var_app; eauto.
  rewrite H1. simpl. exists 1; omega.
Qed.

Lemma eval_aryacc_app1:
  forall e a ai j ty v,
  eval_sexp e (Saryacc a (Sconst (Cint j) type_int32s) ty) v ->
  eval_sexp e ai (Vint j) ->
  eval_sexp e (Saryacc a ai ty) v.
Proof.
  intros. inv H. inv H1. inv H7.
  apply eval_Rlvalue with id (Int.add ofs0 (array_ofs i ty)) k; auto.
  eapply eval_Saryacc; eauto.
  inv H.
Qed.

Lemma eval_sexp_field:
  forall e a m f i t v sid,
  eval_sexp e a (Vmvl m) ->
  eval_field m f (i,t) v ->
  typeof a = Tstruct sid f ->
  has_type v t ->
  eval_sexp e (Sfield a i t) v.
Proof.
  intros. inv H0.
  destruct eval_sexp_exists_lvalue with e a m as [id1 [o [k ?]]]; auto.
  eapply eval_sexp_lvalue_var in H; eauto.
  apply eval_Rlvalue with id1 (Int.add o (Int.repr delta)) k; simpl; auto.
  apply eval_Sfield with sid f; eauto.
  eapply eval_var_range_perm; eauto.
  eapply load_mvl_eval_var_app; eauto.
  rewrite H1. simpl.
  eapply field_type_alignof; eauto.
Qed.

Lemma eval_lvalue_id_in_expids:
  forall e a id ofs k,
  eval_lvalue e a id ofs k ->
  In id (get_expids a).
Proof.
  induction 1; simpl; auto.
  apply in_or_app; auto.
Qed.

Lemma eval_lvalue_get_lids:
  forall e a id ofs k,
  eval_lvalue e a id ofs k ->
  get_lids a = id :: nil.
Proof.
  induction 1; simpl; auto.
Qed.

Lemma eval_sexp_eval_lvalue:
  forall te a v,
  eval_sexp te a v ->
  forall id, In id (get_lids a) ->
  exists ofs k, eval_lvalue te a id ofs k.
Proof.
  induction 1; simpl; intros; try tauto.
  exists ofs, k. cut (id = id0). intros. subst. auto.
  apply eval_lvalue_get_lids in H.
  rewrite H in *. simpl in *. destruct H2; tauto.
Qed.

Lemma eval_sbinop_by_value:
  forall e op a1 a2 t v,
  eval_sexp e (Sbinop op a1 a2 t) v ->
  exists chunk, access_mode t = By_value chunk.
Proof.
  intros. inv H.
  eapply sem_binary_by_value; eauto.
  inv H0.
Qed.

Lemma eval_sunop_by_value:
  forall e op a t v,
  eval_sexp e (Sunop op a t) v ->
  exists chunk, access_mode t = By_value chunk.
Proof.
  intros. inv H.
  eapply sem_unary_by_value; eauto.
  inv H0.
Qed.

Lemma eval_scast_by_value:
  forall e a t v,
  eval_sexp e (Scast a t) v ->
  exists chunk, access_mode t = By_value chunk.
Proof.
  intros. inv H.
  eapply sem_cast_by_value; eauto.
  inv H0.
Qed.

Lemma eval_sexp_const:
  forall eh1 eh2 c ty v,
  eval_sexp eh1 (Sconst c ty) v ->
  eval_sexp eh2 (Sconst c ty) v.
Proof.
  intros. inv H. constructor; auto. inv H0.
Qed.

Lemma eval_sexp_has_type:
  forall e a v,
  eval_sexp e a v ->
  has_type v (typeof a).
Proof.
  induction 1; simpl; auto.
  eapply sem_cast_has_type; eauto.
Qed.

Lemma eval_lvalue_by_value_lid:
  forall  e a id o k mv t,
  eval_lvalue e a id o k ->
  forall chunk,
  k = Lid ->
  e ! id = Some (mv, t) ->
  access_mode t = By_value chunk ->
  a = Svar id t.
Proof.
  induction 1; simpl; intros; subst; try congruence.
  -(*Sarray*)
   erewrite IHeval_lvalue in H1; eauto.
   simpl in *. subst. inv H6.
  -(*Sfield*)
   erewrite IHeval_lvalue in H0; eauto.
   simpl in *. subst. inv H6.
Qed.

Lemma eval_lvalue_lid_disjoint_not_loopid:
  forall te a id o k,
  eval_lvalue te a id o k ->
  lid_disjoint a ->
  id <> ACG_I.
Proof.
  induction 1; simpl; intros; auto.
  destruct a1; auto. destruct H4; auto.
Qed.

Lemma eval_lvalue_some_alignof:
  forall e a id ofs m ty,
  eval_lvalue e a id ofs Lid ->
  e ! id = Some (m, ty) ->
  (alignof (typeof a) | alignof ty).
Proof.
  induction a; simpl; intros; inv H.
  +rewrite H5 in H0. inv H0. exists 1. omega.
  +apply Zdivide_trans with (alignof (typeof a1)); eauto.
   rewrite H6. simpl. exists 1. omega.
  +apply Zdivide_trans with (alignof (typeof a)); eauto.
   rewrite H5. simpl.
   eapply field_type_alignof; eauto.
Qed.

Lemma eval_sexp_type_size:
  forall e a v,
  eval_sexp e a v ->
  0 < sizeof (typeof a) <= Int.max_signed.
Proof.
  intros. generalize H; intros.
  apply eval_sexp_has_type in H0.
  destruct has_type_access_mode with v (typeof a) as [[? ?] | ]; auto.
  +unfold Int.max_signed. simpl.
   destruct (typeof a); simpl in *; try congruence; try omega.
   destruct i; omega. destruct f; omega.
  +destruct has_type_access_mode_mvl with v (typeof a) as [? [? ?]]; auto.
   subst. generalize H; intros.
   apply eval_sexp_exists_lvalue in H2; auto. destruct H2 as [? [? [? ?]]].
   eapply eval_sexp_lvalue_var in H; eauto.
   apply eval_var_range_perm in H.
   generalize (Int.unsigned_range x1). omega.
Qed.

Inductive eval_offset(ty: type): sexp -> Z -> Prop :=
  | eval_offset_Svar: forall id,
     eval_offset ty (Svar id ty) 0
  | eval_offset_Ssvar: forall id,
     eval_offset ty (Ssvar id ty) 0
  | eval_offset_Saryacc: forall a a1 t ofs i aid z,
     eval_offset ty a ofs ->
     typeof a = Tarray aid t z ->
     0 <= i < Z.max 0 z ->
     eval_offset ty (Saryacc a a1 t) (ofs + (sizeof t * i))
  | eval_offset_Sfield: forall a i t sid fld ofs delta,
     eval_offset ty a ofs->
     typeof a = Tstruct sid fld ->
     field_offset i fld = OK delta ->
     field_type i fld = OK t ->
     eval_offset ty (Sfield a i t) (ofs + delta).

Lemma eval_offset_pos:
  forall t a o,
  eval_offset t a o ->
  0 <= o /\ o + sizeof (typeof a) <= sizeof t.
Proof.
  induction 1; simpl; intros; try omega.
  +rewrite H0 in *. simpl in *.
   generalize (sizeof_pos t0). intros.
   cut (0 <= sizeof t0 * i). intros.
   split; try omega.
   apply Zle_trans with (ofs + sizeof t0 * Z.max 0 z); try omega.
   replace (Z.max 0 z) with ((Z.max 0 z -1)+1) by omega.
   rewrite Zmult_plus_distr_r, Zmult_1_r.
   rewrite <-Zplus_assoc. apply Zplus_le_compat_l.
   apply Zplus_le_compat_r. apply Zmult_le_compat_l; try omega.
   apply Zmult_le_0_compat; omega.
  +eapply field_offset_in_range with (sid:=sid) (ty:=t0) in H1; eauto.
   split. omega.
   apply Zle_trans with (ofs + sizeof (typeof a)); try omega.
   rewrite H0. omega.
Qed.

Lemma eval_lvalue_eval_offset:
  forall e a id ofs k,
  eval_lvalue e a id ofs k ->
  forall m ty,
  match k with
  | Lid =>
    e ! id = Some (m, ty) ->
    eval_offset ty a (Int.unsigned ofs)
  | Gid =>
    gc ! id = Some (m, ty) ->
    eval_offset ty a (Int.unsigned ofs)
  | _ => False
  end.
Proof.
  induction 1; simpl; intros.
  +rewrite H0 in H. inv H. rewrite Int.unsigned_zero. constructor.
  +rewrite H1 in H0. inv H0. rewrite Int.unsigned_zero. constructor.
  +generalize Int.max_signed_unsigned (Int.unsigned_range i)
    (Int.unsigned_range ofs) (sizeof_pos ty). intros.
   unfold array_ofs. rewrite int_mul_repr.
   cut (0 <= Int.unsigned i < Z.max 0 z); intros.
   rewrite <-repr_add_int_r. rewrite Int.unsigned_repr.
   destruct vk; try tauto; intros; econstructor; eauto.
   -split.
    *apply Zle_trans with (Int.unsigned ofs + sizeof ty * 0); try omega.
     apply Zplus_le_compat_l.
     apply Zmult_le_compat_l; try omega.
    *apply Zle_trans with (Int.unsigned ofs + sizeof (typeof a)); try omega.
     apply Zplus_le_compat_l.
     rewrite H1. simpl.
     apply Zmult_le_compat_l; omega.
   -split; try omega. apply signed_unsigned_range; auto.
  +generalize Int.max_signed_unsigned (Int.unsigned_range ofs) (sizeof_pos ty). intros.
   cut (0 <= Int.unsigned ofs + delta <= Int.max_unsigned). intros.
   rewrite <-repr_add_int_r. rewrite Int.unsigned_repr; auto.
   destruct vk; try tauto; intros; econstructor; eauto.
   eapply field_offset_in_range with (sid:=sid) in H1; eauto.
   split; try omega. rewrite H0 in *. omega.
Qed.

Inductive locenv_setlvar: locenv -> sexp -> val -> locenv -> Prop :=
  | locenv_setlvar_vid: forall e e' var b ofs v,
      eval_lvalue e var b ofs Lid ->
      store_env (typeof var) e b ofs v e' ->
      locenv_setlvar e var v e'.

Inductive eval_typecmp(tyl: list (ident*type))(te: locenv)(a1 a2: sexp) : bool -> Prop :=
  | eval_typecmp_chunk: forall chunk v b,
      typeof a1 = typeof a2 ->
      access_mode (typeof a1) = By_value chunk ->
      eval_sexp te (Sbinop Oeq a1 a2 type_bool) v ->
      bool_val v type_bool = Some b ->
      eval_typecmp tyl te a1 a2 b
  | eval_typecmp_array: forall aid aty num b v1 v2,
      typeof a1 = typeof a2 ->
      typeof a1 = Tarray aid aty num ->
      find_funct tyl aid = Some (aid, Tarray aid aty num) ->
      eval_sexp te a1 v1 ->
      eval_sexp te a2 v2 ->
      eval_arycmp tyl te a1 a2 num aty Int.zero b ->
      te ! (comp_funcs_id aid) = None ->
      eval_typecmp tyl te a1 a2 b
  | eval_typecmp_struct: forall sid fld b v1 v2,
      typeof a1 = typeof a2 ->
      typeof a1 = Tstruct sid fld ->
      find_funct tyl sid = Some (sid, Tstruct sid fld) ->
      eval_sexp te a1 v1 ->
      eval_sexp te a2 v2 ->
      eval_strcmp tyl te a1 a2 fld fld b ->
      te ! (comp_funcs_id sid) = None ->
      eval_typecmp tyl te a1 a2 b

with eval_arycmp(tyl: list (ident*type))(te: locenv)(a1 a2: sexp): Z -> type -> int ->  bool -> Prop :=
  | eval_arycmp_loop: forall num aty i b1 b2,
      Int.unsigned i < num <= Int.max_signed ->
      eval_typecmp tyl te (Saryacc a1 (Sconst (Cint i) type_int32s) aty) (Saryacc a2 (Sconst (Cint i) type_int32s) aty) b1 ->
      eval_arycmp tyl te a1 a2 num aty (Int.add i Int.one) b2 ->
      eval_arycmp tyl te a1 a2 num aty i (b1 && b2)
  | eval_arycmp_false: forall aty i,
      eval_arycmp tyl te a1 a2 (Int.unsigned i) aty i true

with eval_strcmp(tyl: list (ident*type))(te: locenv)(a1 a2: sexp): fieldlist -> fieldlist ->  bool -> Prop :=
  | eval_strcmp_cons: forall fld id ty ftl b1 b2,
      eval_typecmp tyl te (Sfield a1 id ty) (Sfield a2 id ty) b1 ->
      field_type id fld = OK ty ->
      eval_strcmp tyl te a1 a2 fld ftl b2 ->
      eval_strcmp tyl te a1 a2 fld (Fcons id ty ftl) (b1 && b2)
  | eval_strcmp_nil: forall fld,
      eval_strcmp tyl te a1 a2 fld Fnil true.

Scheme eval_typecmp_ind2 := Minimality for eval_typecmp Sort Prop
  with eval_arycmp_ind2 := Minimality for eval_arycmp Sort Prop
  with eval_strcmp_ind2 := Minimality for eval_strcmp Sort Prop.
Combined Scheme eval_arystr_cmp_ind from eval_typecmp_ind2, eval_arycmp_ind2, eval_strcmp_ind2.

Inductive eval_lindexs(te: locenv)(t: type): type -> list lindex -> int -> int  -> Prop:=
  | eval_Lnil: forall o,
      eval_lindexs te t t nil o o
  | eval_Lcons_label: forall sid fld label lis o o' delta ty,
      field_offset label fld = OK delta ->
      field_type label fld = OK ty ->
      Int.unsigned o + sizeof (Tstruct sid fld) <= Int.max_signed ->
      eval_lindexs te t ty lis (Int.add o (Int.repr delta)) o' ->
      eval_lindexs te t (Tstruct sid fld) ((Label label)::lis) o o'
  | eval_Econs_index: forall aid aty num index lis o o' i,
      eval_sexp te index (Vint i) ->
      eval_lindexs te t aty lis (Int.add o (array_ofs i aty)) o'  ->
      0 <= Int.signed i < num ->
      typeof index = type_int32s ->
      Int.unsigned o < Int.unsigned o + sizeof (Tarray aid aty num) <= Int.max_signed ->
      eval_lindexs te t (Tarray aid aty num) ((Index index)::lis) o o'.

Lemma eval_aryacc_app3:
  forall e a1 a2 ai ty v,
  (forall v, eval_sexp e a1 v -> eval_sexp e a2 v) ->
  (forall id o k, eval_lvalue e a1 id o k -> eval_lvalue e a2 id o k) ->
  typeof a1 = typeof a2 ->
  eval_sexp e (Saryacc a1 ai ty) v ->
  eval_sexp e (Saryacc a2 ai ty) v.
Proof.
  intros. inv H2.
  apply eval_Rlvalue with id ofs k; auto.
  inv H3. apply eval_Saryacc with aid z; auto.
  congruence. congruence.
Qed.

Lemma eval_field_app3:
  forall e a1 a2 fid ty v,
  (forall id o k, eval_lvalue e a1 id o k -> eval_lvalue e a2 id o k) ->
  typeof a1 = typeof a2 ->
  eval_sexp e (Sfield a1 fid ty) v ->
  eval_sexp e (Sfield a2 fid ty) v.
Proof.
  intros. inv H1.
  apply eval_Rlvalue with id ofs k; auto.
  inv H2. apply eval_Sfield with sid fld; eauto.
  congruence. congruence.
Qed.

Definition ary_prj (ty: type)(v: val): res (option int * type) :=
  match ty, v with
  | Tarray _ ty1 z, Vint i =>
     if zlt 0 (sizeof ty1) && zlt 0 z then
       if (negb (Int.lt i Int.zero)) && (Int.lt i (Int.repr z)) then
         OK (Some (array_ofs i ty1), ty1)
       else OK (None,ty1)
     else Error (MSG "num is le zero " :: nil)
  | _, _ => Error (MSG "Not Tarray " :: nil)
  end.

Fixpoint ary_prjs(ty: type)(vi: val)(vl: list val){struct vl}: res (option int * type) :=
  match vl with
  | nil => ary_prj ty vi
  | v :: tl =>
     do (oi1,ty1) <- ary_prj ty vi;
     do (oi2,ty2) <- ary_prjs ty1 v tl;
     match oi1, oi2 with
     | Some pos1, Some pos2 => OK (Some (Int.add pos1 pos2),ty2)
     | _, _ => OK (None,ty2)
     end
  end.

Inductive alloc_variables: locenv -> list (ident*type) -> locenv ->  Prop :=
  | alloc_variables_nil: forall e,
      alloc_variables e nil e
  | alloc_variables_cons: forall e id ty vars e2,
      alloc_variables (PTree.set id (alloc (sizeof ty), ty) e) vars e2 ->
      alloc_variables e ((id, ty) :: vars) e2.

Definition locenv_getvar(e: locenv)(lh: ident*type)(v: val): Prop :=
  exists m, e ! (fst lh) = Some (m,snd lh)
    /\ sizeof (snd lh) = Z_of_nat (length m)
    /\ load_mvl (snd lh) m Int.zero v.

Definition locenv_getvars(e: locenv)(ls: list (ident*type))(vl: list val): Prop :=
  Forall2 (locenv_getvar e) ls vl.

Inductive locenv_setvars: locenv -> list (ident*type) -> list val-> locenv -> Prop :=
  | locenv_setvars_nil: forall e,
      locenv_setvars e nil nil e
  | locenv_setvars_cons_id: forall e e1 e' id dl v vl ty m,
      e ! id = Some (m, ty) ->
      store_env ty e id Int.zero v e1 ->
      locenv_setvars e1 dl vl e' ->
      locenv_setvars e ((id, ty) :: dl) (v :: vl) e'.

Inductive locenv_setlvars: locenv -> list sexp -> list val-> locenv -> Prop :=
  | locenv_setlvars_nil: forall e,
      locenv_setlvars e nil nil e
  | locenv_setlvars_cons: forall e e1 e' lhs dl v vl,
      locenv_setlvar e lhs v e1 ->
      locenv_setlvars e1 dl vl e' ->
      locenv_setlvars e (lhs :: dl) (v :: vl) e'.

Inductive eval_fbyn_init(id1 id2 aid: ident)(ty: type)(i j: int)(v: val): locenv -> locenv -> Prop :=
  | eval_fbyn_init_loop: forall aty sa eh eh1 eh2 v',
     Int.lt i j = true ->
     Tarray aid ty (Int.unsigned j) = aty ->
     Svar id1 (make_fbyn_type id2 aty) = sa ->
     eval_cast v ty v' ->
     locenv_setlvar eh (Saryacc (Sfield sa FBYITEM aty) (Sconst (Cint i) type_int32s) ty) v' eh1 ->
     eval_fbyn_init id1 id2 aid ty (Int.add i Int.one) j v eh1 eh2 ->
     eval_fbyn_init id1 id2 aid ty i j v eh eh2
  | eval_fbyn_init_false: forall eh,
     Int.eq i j = true ->
     eval_fbyn_init id1 id2 aid ty i j v eh eh.

Inductive locenv_getarys(i:int): list type -> list type -> list val -> list val -> Prop :=
  | locenv_getarys_nil:
      locenv_getarys i nil nil nil nil
  | locenv_getarys_cons: forall m aid aty num pl tyl vpl v vl,
      load_mvl aty m (array_ofs i aty) v ->
      has_type v aty ->
      0 <= Int.signed i < num ->
      locenv_getarys i pl tyl vpl vl ->
      locenv_getarys i ((Tarray aid aty num) :: pl) (aty::tyl) ((Vmvl m) :: vpl) (v:: vl).

Inductive locenv_setarys(ai: sexp): locenv -> list (ident*type) -> list type -> list val-> locenv -> Prop :=
  | locenv_setarys_nil: forall e,
      locenv_setarys ai e nil nil nil e
  | locenv_setarys_cons_id: forall e e1 e' id aid t num dl tl v vl,
      locenv_setlvar e (Saryacc (Svar id (Tarray aid t num)) ai t) v e1 ->
      locenv_setarys ai e1 dl tl vl e' ->
      locenv_setarys ai e ((id, Tarray aid t num) :: dl) (t::tl) (v :: vl) e'.

Inductive eval_eqf: locenv -> locenv -> eqf -> Prop :=
  | eval_Eqf: forall e e' a1 a2 v v',
      eval_sexp e a2 v ->
      typeof a1 = typeof a2 ->
      eval_cast v (typeof a1) v' ->
      locenv_setlvar e a1 v' e' ->
      assign_disjoint (eval_lvalue e) a1 a2 ->
      eval_eqf e e' (a1,a2).

Inductive locenv_getmvl(e: locenv)(lh: sexp)(mv: mvl): Prop :=
  | locenv_getmvl_lid: forall id ofs m t,
      eval_lvalue e lh id ofs Lid ->
      e ! id = Some (m, t) ->
      loadbytes m (Int.unsigned ofs) (sizeof (typeof lh)) = Some mv ->
      locenv_getmvl e lh mv.

Definition locenv_getmvls(e: locenv)(l: list sexp)(vl: list mvl): Prop :=
  Forall2 (locenv_getmvl e) l vl.

Lemma store_mvl_loadbytes_exists:
  forall ty m ofs v m',
  store_mvl ty m ofs v m' ->
  exists mv, loadbytes m (Int.unsigned ofs) (sizeof ty) = Some mv.
Proof.
  intros. unfold loadbytes.
  econstructor. rewrite pred_dec_true; auto.
  eapply store_mvl_range_perm2; eauto.
Qed.

Lemma store_env_getmvl_exists:
  forall ty e id v e1 m,
  store_env ty e id Int.zero v e1 ->
  e ! id = Some (m, ty) ->
  exists v1, locenv_getmvl e (lvarof (id, ty)) v1.
Proof.
  intros. inv H.
  rewrite H0 in H1. inv H1.
  apply store_mvl_loadbytes_exists in H3.
  destruct H3 as [mv ?].
  exists mv. constructor 1 with id Int.zero m0 t; auto.
  constructor 1 with m0; auto.
Qed.

Lemma locenv_getmvl_set_other_exists:
  forall ty id ofs v e e1 id1 ty1 v1,
  locenv_getmvl e1 (Svar id1 ty1) v1 ->
  store_env ty e id ofs v e1 ->
  id <> id1 ->
  locenv_getmvl e (Svar id1 ty1) v1.
Proof.
  intros. inv H0. inv H. inv H0.
  rewrite PTree.gso in *; auto.
  rewrite H10 in H5. inv H5.
  constructor 1 with id0 Int.zero m0 t0; auto.
  constructor 1 with m0; auto.
Qed.

Lemma locenv_getmvls_set_other_exists:
  forall ty id ofs v e e1 l vl,
  locenv_getmvls e1 (map lvarof l) vl ->
  store_env ty e id ofs v e1 ->
  ~ In id (map fst l) ->
  locenv_getmvls e (map lvarof l) vl.
Proof.
  induction l, vl; simpl; intros; inv H.
  +constructor.
  +constructor 2; auto.
   eapply locenv_getmvl_set_other_exists; eauto.
   apply IHl; auto.
Qed.

Lemma locenv_setlvar_getmvl_exists:
  forall e lh v e1,
  locenv_setlvar e lh v e1 ->
  exists v1, locenv_getmvl e lh v1.
Proof.
  intros. inv H. inv H1.
  apply store_mvl_loadbytes_exists in H3.
  destruct H3 as [mv ?].
  exists mv. constructor 1 with b ofs m t; auto.
Qed.

Lemma locenv_setlvars_getmvls:
  forall eh lhs vrets eh',
  locenv_setvars eh lhs vrets eh' ->
  list_norepet (map fst lhs) ->
  exists vl, locenv_getmvls eh (map lvarof lhs) vl.
Proof.
  induction 1; simpl; intros.
  +exists nil. constructor.
  +inv H. inv H2.
   destruct IHlocenv_setvars as [vl1 ?]; auto.
   destruct store_env_getmvl_exists with ty e id v e1 m as [v1 ?]; auto.
   exists (v1::vl1). constructor 2; auto.
   eapply locenv_getmvls_set_other_exists; eauto.
Qed.

Lemma locenv_setlvars_app:
  forall e l1 vl1 e1,
  locenv_setlvars e l1 vl1 e1 ->
  forall l2 vl2 e2,
  locenv_setlvars e1 l2 vl2 e2 ->
  locenv_setlvars e (l1 ++ l2) (vl1 ++ vl2) e2.
Proof.
  induction 1; simpl; intros; auto.
  constructor 2 with e1; auto.
Qed.

Lemma locenv_setvars_sizeof:
  forall te l vas te',
  locenv_setvars te l vas te' ->
  forall id ty, In (id, ty) l -> 0 < sizeof ty.
Proof.
  induction 1; simpl; intros; try tauto.
  destruct H2.
  inv H2. inv H0. apply store_mvl_range_perm2 in H4.
  red in H4. omega.
  apply IHlocenv_setvars with id0; auto.
Qed.

End EVAL_COMMON.

Inductive eval_init: nat -> locenv -> list (ident*type)-> locenv ->  Prop :=
  | eval_init_none: forall eh svars,
     eval_init O eh svars eh
  | eval_init_some: forall n svars eh eh1 eh2,
     alloc_variables eh ((ACG_INIT,type_bool)::svars) eh1 ->
     store_env type_bool eh1 ACG_INIT Int.zero (Vint Int.one) eh2 ->
     eval_init (S n) eh ((ACG_INIT,type_bool)::svars) eh2.

Inductive eval_fbyeq(gc te: locenv): locenv -> locenv -> eqt -> Prop :=
  | eval_eqt_assign: forall e e' a1 a2 v v',
      eval_sexp gc te a2 v ->
      eval_cast v (typeof a1) v' ->
      locenv_setlvar empty_locenv e a1 v' e' ->
      typeof a1 = typeof a2 ->
      list_disjoint (get_lids a1) (get_lids a2) ->
      eval_fbyeq gc te e e' (Eqt_assign (a1,a2))
  | eval_eqt_counter: forall e e' eq,
      eval_eqf empty_locenv e e' eq ->
      eval_fbyeq gc te e e' (Eqt_counter eq)
  | eval_eqt_skip: forall e,
      eval_fbyeq gc te e e Eqt_skip.

Inductive eval_fbyeqs(gc te: locenv): locenv -> locenv -> list eqt -> Prop :=
  | eval_fbyeqs_nil: forall e,
      eval_fbyeqs gc te e e nil
  | eval_fbyeqs_cons: forall e e1 e2 eq eql,
      eval_fbyeq gc te e e1 eq ->
      eval_fbyeqs gc te e1 e2 eql ->
      eval_fbyeqs gc te e e2 (eq :: eql).

Inductive eval_poststmt(gc te eh: locenv): list eqt -> locenv ->  Prop :=
  | eval_poststmt_: forall eqs eh1 eh2,
     eval_fbyeqs gc te eh eh1 eqs ->
     (if le_lt_dec (length eqs) O then eh2 = eh1
      else eval_eqf empty_locenv eh1 eh2 (Svar ACG_INIT type_bool, Sconst (Cbool false) type_bool)) ->
     eval_poststmt gc te eh eqs eh2.

Lemma eval_fbyeqs_app:
  forall gc te e e1 eql1,
  eval_fbyeqs gc te e e1 eql1 ->
  forall e2 eql2, eval_fbyeqs gc te e1 e2 eql2 ->
  eval_fbyeqs gc te e e2 (eql1 ++ eql2).
Proof.
  induction 1; simpl; intros; auto.
  constructor 2 with e1; auto.
Qed.

Lemma eval_fbyeqs_app_inv:
  forall gc te l1 l2 e e2,
  eval_fbyeqs gc te e e2 (l1 ++ l2) ->
  exists e1, eval_fbyeqs gc te e e1 l1
    /\ eval_fbyeqs gc te e1 e2 l2.
Proof.
  induction l1; simpl; intros; auto.
  exists e. split; auto. constructor.
  inv H. destruct IHl1 with l2 e1 e2 as [e' [? ?]]; auto.
  exists e'. split; auto. econstructor; eauto.
Qed.

Lemma store_mvl_trans:
  forall t m m1 m' ofs v1 v2,
  store_mvl t m ofs v1 m' ->
  store_mvl t m ofs v2 m1 ->
  store_mvl t m1 ofs v1 m'.
Proof.
  intros.
  inv H; inv H0; simpl in *.
  *rewrite H in H1. inv H1. constructor 1 with chunk; auto.
   eapply store_trans; eauto.
  *destruct H; congruence.
  *destruct H1; congruence.
  *constructor 2; auto.
   eapply storebytes_trans; eauto.
   apply Nat2Z.inj; auto. congruence.
Qed.

Lemma store_env_trans:
  forall ty te te0 te1 id o v1 v2,
  store_env ty te id o v1 te1 ->
  store_env ty te id o v2 te0 ->
  store_env ty te0 id o v1 te1.
Proof.
  intros. inv H. inv H0. rewrite H in H1. inv H1.
  rewrite <-ptree_set_repeat with _ te id (m',t) (m'0,t).
  generalize H3, H5. intros.
  apply store_mvl_length in H0. apply store_mvl_length in H1.
  constructor 1 with m'0; auto.
  +rewrite PTree.gss; auto.
  +congruence.
  +eapply store_mvl_trans; eauto.
Qed.

Lemma store_mvl_determ:
  forall ty m ofs v m1 m2,
  store_mvl ty m ofs v m1 ->
  store_mvl ty m ofs v m2 ->
  m1 = m2.
Proof.
  induction 1; intros.
  inv H1. congruence. destruct H2; congruence.
  inv H3. destruct H; congruence. congruence.
Qed.

Lemma eval_cast_determ:
  forall v t v1 v2,
  eval_cast v t v1 ->
  eval_cast v t v2 ->
  v1 = v2.
Proof.
  intros. inv H; inv H0; auto.
  congruence.
  destruct H; congruence.
  destruct H1; congruence.
Qed.

Lemma store_env_determ:
  forall ty e id ofs v e1 e2,
  store_env ty e id ofs v e1 ->
  store_env ty e id ofs v e2 ->
  e1 = e2.
Proof.
  induction 1. induction 1.
  f_equal. rewrite H in H2. inv H2.
  f_equal. eapply store_mvl_determ; eauto.
Qed.

Lemma locenv_setvars_determ:
  forall te l vrets te1',
  locenv_setvars te l vrets te1' ->
  forall te2',
  locenv_setvars te l vrets te2' ->
  te1' = te2'.
Proof.
  induction 1; intros.
  inv H; auto.
  inv H2. eapply store_env_determ in H0; eauto.
  subst; auto.
Qed.

Lemma locenv_setlvar_determ:
  forall gc e a v e1,
  locenv_setlvar gc e a v e1 ->
  forall e2, locenv_setlvar gc e a v e2 ->
  e1 = e2.
Proof.
  intros. inv H. inv H0.
  eapply eval_sexp_determ in H1; eauto.
  destruct H1 as [? [? ?]]. subst.
  eapply store_env_determ; eauto.
Qed.

Lemma eval_eqf_determ:
  forall gc e e1 eq,
  eval_eqf gc e e1 eq ->
  forall e2, eval_eqf gc e e2 eq ->
  e1 = e2.
Proof.
  intros. inv H. inv H0.
  eapply eval_sexp_determ in H1; eauto.
  subst. eapply eval_cast_determ in H3; eauto.
  subst. eapply locenv_setlvar_determ; eauto.
Qed.

Lemma locenv_getvar_determ:
  forall te lh v1,
  locenv_getvar te lh v1 ->
  forall v2, locenv_getvar te lh v2 ->
  v1 = v2.
Proof.
  intros. destruct H as [m1 [? [? ?]]].
  destruct H0 as [m2 [? [? ?]]].
  rewrite H in H0. inv H0.
  eapply load_mvl_determ; eauto.
Qed.

Lemma locenv_getvars_determ:
  forall te l vl1,
  locenv_getvars te l vl1 ->
  forall vl2, locenv_getvars te l vl2 ->
  vl1 = vl2.
Proof.
  induction 1; intros.
  inv H; auto.
  inv H1. f_equal; auto.
  eapply locenv_getvar_determ in H; eauto.
Qed.

Lemma eval_casts_determ:
  forall vargs tyl vargs1,
  eval_casts vargs tyl vargs1 ->
  forall vargs2, eval_casts vargs tyl vargs2 ->
  vargs1 = vargs2.
Proof.
  induction 1; intros.
  inv H; auto.
  inv H1. f_equal; auto.
  eapply eval_cast_determ; eauto.
Qed.

Lemma locenv_getarys_determ:
  forall i tyl atys1 vl vas1,
  locenv_getarys i tyl atys1 vl vas1 ->
  forall atys2 vas2, locenv_getarys i tyl atys2 vl vas2 ->
  atys1 = atys2 /\ vas1 = vas2.
Proof.
  induction 1; intros.
  inv H. auto.
  inv H3. eapply load_mvl_determ in H; eauto. subst.
  eapply IHlocenv_getarys in H15; eauto.
  destruct H15; subst;auto.
Qed.

Lemma locenv_setarys_determ:
  forall gc i te l rtys vrs te1',
  locenv_setarys gc i te l rtys vrs te1' ->
  forall te2', locenv_setarys gc i te l rtys vrs te2' ->
  te1' = te2'.
Proof.
  induction 1; intros.
  inv H. auto.
  inv H1. eapply locenv_setlvar_determ in H; eauto. subst. eauto.
Qed.

Lemma int_eq_lt_false:
  forall i j,
  Int.eq i j = true ->
  Int.lt i j = false.
Proof.
  intros. generalize (Int.eq_spec i j); intros.
  rewrite H in H0. subst.
  unfold Int.lt. destruct (zlt _ _) eqn:?; try omega. auto.
Qed.

Lemma eval_fbyn_init_determ:
  forall gc id1 id2 aid t i i1 v eh eh1,
  eval_fbyn_init gc id1 id2 aid t i i1 v eh eh1 ->
  forall eh2, eval_fbyn_init gc id1 id2 aid t i i1 v eh eh2 ->
  eh1 = eh2.
Proof.
  induction 1; intros.
  +inv H5.
   -eapply eval_cast_determ in H2; eauto. subst.
    eapply locenv_setlvar_determ in H3; eauto.
    subst. eauto.
   -rewrite int_eq_lt_false in H; auto. congruence.
  +inv H0; auto.
   rewrite int_eq_lt_false in H1; auto. congruence.
Qed.

Lemma alloc_variables_determ:
  forall e al e1,
  alloc_variables e al e1 ->
  forall e2, alloc_variables e al e2 ->
  e1 = e2.
Proof.
  induction 1; simpl; intros.
  inv H; auto.
  inv H0. eauto.
Qed.

Lemma eval_sexps_determ:
  forall gc e l vl1,
  eval_sexps gc e l vl1 ->
  forall vl2, eval_sexps gc e l vl2 ->
  vl1 = vl2.
Proof.
  induction 1; intros.
  inv H; auto.
  inv H1. f_equal; auto.
  eapply eval_sexp_determ; eauto.
Qed.

Lemma eval_fbyeqs_determ:
  forall gc te eh eh1 l,
  eval_fbyeqs gc te eh eh1 l ->
  forall eh2, eval_fbyeqs gc te eh eh2 l ->
  eh1 = eh2.
Proof.
  induction 1; intros.
  inv H; auto.
  inv H1. inv H; inv H6; auto.
  eapply eval_sexp_determ in H1; eauto. subst.
  eapply eval_cast_determ in H2; eauto. subst.
  apply locenv_setlvar_determ with (e1:=e1) in H11; auto.
  subst; auto.
  eapply eval_eqf_determ in H1; eauto. subst; auto.
Qed.

Lemma eval_poststmt_determ:
  forall gc te eh l eh1',
  eval_poststmt gc te eh l eh1' ->
  forall eh2',
  eval_poststmt gc te eh l eh2' ->
  eh1' = eh2'.
Proof.
  induction 1; intros.
  inv H1.
  eapply eval_fbyeqs_determ in H; eauto. subst.
  destruct (le_lt_dec _ _); subst; auto.
  eapply eval_eqf_determ; eauto.
Qed.

Lemma eval_typecmp_determ:
  forall gc eh l a1 a2 b1,
  eval_typecmp gc l eh a1 a2 b1 ->
  forall b2, eval_typecmp gc l eh a1 a2 b2 ->
  b1 = b2.
Proof.
  intros until l.
  induction 1 using eval_typecmp_ind2 with
  ( P0 := fun a1 a2 num aty i b1 =>
      forall b2, eval_arycmp gc l eh a1 a2 num aty i b2 ->
      b1 = b2)
  ( P1 := fun a1 a2 fld ftl b1 =>
      forall b2, eval_strcmp gc l eh a1 a2 fld ftl b2 ->
      b1 = b2); intros.
 +inv H3. eapply eval_sexp_determ in H1; eauto. subst.
  congruence.
  rewrite H5 in *. simpl in *. congruence.
  rewrite H5 in *. simpl in *. congruence.
 +inv H6. rewrite H0 in *. simpl in *. congruence.
  rewrite H8 in H0. inv H0. auto.
  rewrite H0 in *. simpl in *. congruence.
 +inv H6. rewrite H0 in *. simpl in *. congruence.
  rewrite H0 in *. simpl in *. congruence.
  rewrite H8 in H0. inv H0. auto.
 +inv H2. f_equal; eauto. omega.
 +inv H. omega. auto.
 +inv H2. f_equal; eauto.
 +inv H. auto.
Qed.

Lemma eval_lindexs_determ:
  forall gc te t ty lis i o1,
  eval_lindexs gc te t ty lis i o1 ->
  forall o2, eval_lindexs gc te t ty lis i o2 ->
  o1 = o2.
Proof.
  induction 1; intros.
  inv H. auto.
  inv H3. rewrite H8,H9 in *. inv H. inv H0. auto.
  inv H4. eapply eval_sexp_determ in H; eauto.
  inv H. eauto.
Qed.

Lemma alloc_variables_trans:
  forall e al1 e1,
  alloc_variables e al1 e1 ->
  forall al2 e', alloc_variables e1 al2 e'->
  alloc_variables e (al1++al2) e'.
Proof.
  induction 1; simpl; intros; auto.
  constructor 2; eauto.
Qed.

Lemma alloc_variables_exists:
  forall al e, exists e', alloc_variables e al e'.
Proof.
  induction al; simpl; intros.
  exists e. constructor.
  destruct a.
  destruct IHal with (PTree.set i (alloc (sizeof t),t) e) as [e' ?]; auto.
  exists e'. econstructor 2; eauto.
Qed.

Lemma alloc_variables_app:
  forall al1 al2 e e',
  alloc_variables e (al1++al2) e' ->
  exists e1, alloc_variables e al1 e1
    /\ alloc_variables e1 al2 e'.
Proof.
  induction al1; simpl; intros.
  +exists e. split; auto. constructor.
  +inv H. apply IHal1 in H4.
   destruct H4 as [e1 [? ?]].
   exists e1; split; auto.
   constructor 2; auto.
Qed.

Lemma alloc_variables_notin_eq:
  forall e al e',
  alloc_variables e al e' ->
  forall id, ~ In id (map fst al) ->
  e' ! id = e ! id.
Proof.
  induction 1; simpl; intros; auto.
  rewrite IHalloc_variables; auto.
  rewrite PTree.gso; auto.
Qed.

Lemma alloc_variables_norepeat_in_eq:
  forall e al e1',
  alloc_variables e al e1' ->
  forall id ty, In (id,ty) al ->
  list_norepet (map fst al) ->
  e1' ! id = Some (alloc (sizeof ty),ty).
Proof.
  induction 1; simpl; intros.
  destruct H.
  inv H1. destruct H0; eauto.
  inv H0. apply alloc_variables_notin_eq with _ _ _ id0 in H; auto.
  rewrite H; auto. rewrite PTree.gss; auto.
Qed.

Lemma alloc_variables_exists_in:
  forall e al e',
  alloc_variables e al e' ->
  forall id, In id (map fst al) ->
  exists m, e' ! id = Some m.
Proof.
  induction 1; simpl; intros; try tauto.
  destruct H0; eauto.
  subst.
  assert(In id0 (map fst vars) \/ ~ In id0 (map fst vars)).
    tauto.
  destruct H0; auto.
  exists (alloc (sizeof ty), ty).
  erewrite alloc_variables_notin_eq; eauto.
  rewrite PTree.gss; auto.
Qed.

Lemma alloc_variables_norepeat_ptree_in_exists:
  forall e al e1',
  alloc_variables e al e1' ->
  forall id m,
  e1' ! id = Some m ->
  e ! id = None ->
  list_norepet (map fst al) ->
  exists ty, In (id,ty) al /\ m = (alloc (sizeof ty),ty).
Proof.
  induction 1; simpl; intros.
  +congruence.
  +inv H2. compare id0 id; intros; subst.
   -exists ty. split; auto.
    eapply alloc_variables_notin_eq in H; eauto.
    rewrite PTree.gss in H. congruence.
   -destruct IHalloc_variables with id0 m as [ty1 [? ?]]; auto.
    rewrite PTree.gso; auto.
    exists ty1; split; auto.
Qed.

Lemma alloc_variables_permut:
  forall l1 l2, Permutation l1 l2 ->
  forall e e', alloc_variables e l1 e' ->
  list_norepet (map fst l1) ->
  alloc_variables e l2 e'.
Proof.
  induction 1; simpl; intros.
  +inv H. constructor.
  +inv H0. inv H1. constructor 2; auto.
  +inv H. inv H5. inv H0. simpl in *.
   constructor 2; auto. constructor 2; auto.
   rewrite ptree_set_swap; auto.
  +apply IHPermutation2; auto.
   eapply list_norepet_permut; eauto.
   apply Permutation_map; auto.
Qed.

Lemma set_new_vars_getid_eq:
  forall lhs vl eh eh',
  locenv_setvars eh lhs vl eh' ->
  forall id, ~ In id (map fst lhs) ->
  eh' ! id = eh ! id .
Proof.
  induction 1; simpl; intros; auto.
  rewrite IHlocenv_setvars; auto.
  inv H0. rewrite PTree.gso; auto.
Qed.

Lemma locenv_setvars_type_determ:
  forall ta al vas ta',
  locenv_setvars ta al vas ta' ->
  forall id m t m' t',
  ta' ! id = Some (m', t') ->
  ta ! id = Some (m, t) ->
  t' = t.
Proof.
  induction 1; simpl; intros.
  +congruence.
  +inv H0. rewrite H4 in H. inv H.
   compare id id0; intros; subst.
   -rewrite H3 in H4. inv H4.
    eapply IHlocenv_setvars; eauto.
    rewrite PTree.gss; auto.
   -apply IHlocenv_setvars with id0 m0 m'; auto.
    rewrite PTree.gso; auto.
Qed.

Lemma locenv_setvars_length_eq:
  forall lhs vl e e',
  locenv_setvars e lhs vl e' ->
  length lhs = length vl.
Proof.
  induction 1; simpl; auto.
Qed.

Lemma locenv_setvars_trans_rev:
  forall lhs1 v1 e e1 lhs2 v2 e2,
  locenv_setvars e (lhs1 ++ lhs2) (v1 ++ v2) e2 ->
  locenv_setvars e lhs1 v1 e1 ->
  locenv_setvars e1 lhs2 v2 e2.
Proof.
  induction lhs1; induction v1; simpl; intros; inv H0; auto.
  inv H. apply IHlhs1 with v1 e3; auto.
  apply store_env_determ with _ _ _ _ _ e3 _ in H11; eauto.
  subst. auto.
Qed.

Lemma locenv_setvars_trans_exists:
  forall lhs1 v1 lhs2 v2 e e2,
  locenv_setvars e (lhs1 ++ lhs2) (v1 ++ v2) e2 ->
  length lhs1 = length v1 ->
  exists e1, locenv_setvars e lhs1 v1 e1.
Proof.
  induction lhs1; induction v1; simpl; intros; inv H0.
  exists e; constructor.
  inv H. eapply IHlhs1 in H9; eauto.
  destruct H9 as [e01 A]. exists e01. econstructor; eauto.
Qed.

Lemma locenv_setvars_in_exists:
  forall eh lhs vrets eh',
  locenv_setvars eh lhs vrets eh' ->
  forall id, In id (map fst lhs) ->
  exists m, eh ! id = Some m.
Proof.
  induction 1; simpl; intros.
  +inv H.
  +destruct H2; subst.
   -inv H. eauto.
   -destruct IHlocenv_setvars with id0 as [m1 ?]; auto.
    inv H0. compare id id0; intros; subst.
    *rewrite PTree.gss in H3; eauto.
    *rewrite PTree.gso in H3; eauto.
Qed.

Lemma store_env_load_int_eq:
  forall i id eh eh1,
  store_env type_int32s eh id Int.zero (Vint i) eh1 ->
  load_env type_int32s eh1 id Int.zero (Vint i).
Proof.
  intros. inv H.
  generalize H2. intros.
  apply store_mvl_length in H2.
  exists m',t. rewrite PTree.gss; repeat (split; auto).
  congruence.
  inv H3. constructor 1 with chunk; auto.
  rewrite Int.unsigned_zero in *.
  eapply store_decode_encode_val_load; eauto.
  simpl in *. inv H. simpl. unfold decode_val.
  rewrite proj_inj_bytes.
  rewrite decode_encode_int; auto.
  rewrite Zmod_small. rewrite Int.repr_unsigned. auto.
  simpl. apply Int.unsigned_range.
Qed.

Lemma store_env_load_bool_eq:
  forall v id o eh eh1,
  store_env type_bool eh id o v eh1 ->
  v = Vint Int.zero \/ v = Vint Int.one ->
  load_env type_bool eh1 id o v.
Proof.
  intros. inv H.
  generalize H3. intros.
  apply store_mvl_length in H3.
  exists m',t. rewrite PTree.gss; repeat (split; auto).
  congruence.
  inv H4. constructor 1 with chunk; auto.
  eapply store_decode_encode_val_load; eauto.
  simpl in *. inv H.
  destruct H0; subst; simpl; unfold decode_val;
  rewrite proj_inj_bytes;
  rewrite decode_encode_int; auto.
  destruct H0; congruence.
Qed.

Lemma load_env_int_store_exists:
  forall e id v i,
  load_env type_int32s e id Int.zero v ->
  exists e', store_env type_int32s e id Int.zero (Vint i) e'.
Proof.
  intros. destruct H as [m [t [? [? ?]]]].
  inv H1. rewrite Int.unsigned_zero in H3.
  apply load_valid_access in H3.
  destruct valid_access_store with m chunk 0 (Vint i) as [m2 ?]; auto.
  exists (PTree.set id (m2,t) e). exists m; simpl; auto.
  constructor 1 with chunk; auto.
  destruct H2; inv H1.
Qed.
