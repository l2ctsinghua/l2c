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
Require Import Memdata.
Require Import Integers.

Section Z.

Lemma zmax_l_le:
  forall m n p, p <= m -> p <= Z.max m n.
Proof.
  intros. apply Zle_trans with m; auto.
  apply Zle_max_l; auto.
Qed.

Lemma zmax_r_le:
  forall m n p, p <= n -> p <= Z.max m n.
Proof.
  intros. apply Zle_trans with n; auto.
  apply Zle_max_r; auto.
Qed.

Lemma zmul_add_le_mul_lt:
  forall i j size, 0 <= size -> j < i ->
  size * j + size <= size * i.
Proof.
  intros.
  replace i with ((i -1) + 1); try omega.
  rewrite Z.mul_add_distr_l, Z.mul_1_r.
  apply Zplus_le_compat_r. apply Zmult_le_compat_l; try omega.
Qed.

Lemma Zdivides_one:
  forall x, (1 | x).
Proof.
  intros. exists x. omega.
Qed.

Lemma Zdivides_plus_inv:
  forall x y z, (x | y) -> (x | y + z) -> (x | z).
Proof.
  intros. replace z with ( y+z -y); try omega.
  apply Zdivide_minus_l; auto.
Qed.

End Z.

Section INT.

Transparent Int.repr Int64.repr Byte.repr.

Lemma signed_unsigned_range:
  forall i z,
  0 <= Int.signed i < z ->
  Int.unsigned i < z.
Proof.
  unfold Int.signed. intros.
  generalize (Int.unsigned_range i). intros.
  destruct (zlt _ _); try omega.
Qed.

Lemma int_unsigned_inj:
  forall i j, Int.unsigned i = Int.unsigned j ->
  i = j.
Proof.
  destruct i,j. simpl. intros.
  subst. apply Int.mkint_eq; auto.
Qed.

Lemma repr_add_int:
  forall i j,
  Int.repr (i + j) = Int.add (Int.repr i) (Int.repr j).
Proof.
  intros. apply int_unsigned_inj.
  unfold Int.add. simpl. repeat rewrite Int.Z_mod_modulus_eq.
  apply Zplus_mod.
Qed.

Lemma repr_add_int_r:
  forall o j,
  Int.repr (Int.unsigned o + j) = Int.add o (Int.repr j).
Proof.
  intros. apply int_unsigned_inj.
  simpl. repeat rewrite Int.Z_mod_modulus_eq.
  rewrite Zplus_mod_idemp_r; auto.
Qed.

Lemma int_repr_le:
  forall z, 0 <= z ->
  Int.unsigned (Int.repr z) <= z.
Proof.
  intros. unfold Int.repr. simpl.
  generalize Int.modulus_pos. intros.
  rewrite Int.Z_mod_modulus_eq.
  apply Z.mod_le; try omega.
Qed.

Lemma int_signed_repr_le:
  forall z, 0 <= z ->
  Int.signed (Int.repr z) <= z.
Proof.
  unfold Int.signed. intros.
  cut (Int.unsigned (Int.repr z) <= z). intros.
  destruct (zlt _ _); auto.
  unfold Int.half_modulus in *.
  generalize Int.modulus_pos. intros.
  apply Zle_trans with (z- Int.modulus); try omega.
  apply int_repr_le; auto.
Qed.

Lemma int_add_le:
  forall i j, Int.unsigned (Int.add i j) <= Int.unsigned i + Int.unsigned j.
Proof.
  intros.
  destruct Int.unsigned_add_either with i j.
  omega.
  rewrite H. generalize Int.modulus_pos. omega.
Qed.

Lemma Zdivide_1248_modulus:
  forall x,
  x = 1 \/ x = 2 \/ x = 4 \/ x = 8 ->
  (x | Int.modulus).
Proof.
  intros. rewrite Int.modulus_power.
  simpl. destruct H as [ | [ | [ | ]]]; subst.
  apply Zdivides_one.
  exists (two_power_pos 31). change 2 with (two_power_pos 1).
   rewrite <-two_power_pos_is_exp. auto.
  exists (two_power_pos 30). change 4 with (two_power_pos 2).
   rewrite <-two_power_pos_is_exp. auto.
  exists (two_power_pos 29). change 8 with (two_power_pos 3).
   rewrite <-two_power_pos_is_exp. auto.
Qed.

Lemma Zdivide_unsigned_repr:
  forall x y,
  (x | y) ->
  x = 1 \/ x = 2 \/ x = 4 \/ x = 8 ->
  (x | Int.unsigned (Int.repr y)).
Proof.
  simpl. intros.
  rewrite Int.Z_mod_modulus_eq.
  cut (0 < x). intros.
  generalize Int.modulus_pos. intros.
  apply Zmod_divide; try omega.
  apply Zdivide_mod in H.
  rewrite <-Zmod_div_mod; try omega.
  apply Zdivide_1248_modulus; auto.
  destruct H0 as [ | [ | [ | ]]]; subst; omega.
Qed.

Lemma Zdivide_unsigned_repr_inv:
  forall x y,
  x = 1 \/ x = 2 \/ x = 4 \/ x = 8 ->
  (x | Int.unsigned (Int.repr y)) ->
  (x | y).
Proof.
  simpl. intros.
  rewrite Int.Z_mod_modulus_eq in *.
  generalize Int.modulus_pos. intros.
  apply Zmod_divide.
  destruct H as [ | [ | [ | ]]]; subst; omega.
  apply Zdivide_mod in H0.
  rewrite <-Zmod_div_mod in H0; try omega.
  apply Zdivide_1248_modulus; auto.
Qed.

Lemma Zdivides_plus_int:
  forall z o1 o2,
  z = 1 \/ z = 2 \/ z = 4 \/ z = 8 ->
  (z | Int.unsigned o1) ->
  (z | Int.unsigned o2) ->
  (z | Int.unsigned (Int.add o1 o2)).
Proof.
  intros. unfold Int.add.
  apply Zdivide_unsigned_repr; auto.
  apply Zdivide_plus_r; auto.
Qed.

Lemma Zdivides_plus_int_inv:
  forall z o1 o2,
  z = 1 \/ z = 2 \/ z = 4 \/ z = 8 ->
  (z | Int.unsigned o1) ->
  (z | Int.unsigned (Int.add o1 o2)) ->
  (z | Int.unsigned o2).
Proof.
  intros. unfold Int.add in *.
  apply Zdivide_unsigned_repr_inv in H1; auto.
  apply Zdivides_plus_inv with (y:=Int.unsigned o1); auto.
Qed.

Lemma Zdivides_mul_int:
  forall x y j,
  (x | y) ->
  x = 1 \/ x = 2 \/ x = 4 \/ x = 8 ->
  (x | Int.unsigned (Int.mul (Int.repr y) j)).
Proof.
  intros. unfold Int.mul.
  apply Zdivide_unsigned_repr; auto.
  apply Zdivide_mult_l.
  apply Zdivide_unsigned_repr; auto.
Qed.

Lemma int_mul_repr:
  forall z i, Int.mul (Int.repr z) i = Int.repr (z * Int.unsigned i).
Proof.
  unfold Int.mul, Int.repr. simpl. intros.
  apply Int.mkint_eq. repeat rewrite Int.Z_mod_modulus_eq.
  symmetry. rewrite Zmult_mod; auto.
  f_equal. f_equal. rewrite Zmod_small; try omega.
  apply Int.unsigned_range.
Qed.

End INT.
