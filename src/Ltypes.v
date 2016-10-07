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
Require Import Memdata.
Require Import Lint.
Require Import Integers.
Require Import Ctypes.
Require Import Cltypes.

Definition sizeof_fld(fld: fieldlist):=
  align (sizeof_struct fld 0) (alignof_fields fld).

Lemma sizeof_fld_pos:
  forall fld, 0 <= sizeof_fld fld.
Proof.
  unfold sizeof_fld. intros.
  apply Zle_trans with (sizeof_struct fld 0); try omega.
  apply sizeof_struct_incr; auto.
  apply align_le. apply alignof_fields_pos.
Qed.

Lemma field_offset_in_range_simpl:
  forall id fld delta ty,
  field_offset id fld = OK delta ->
  field_type id fld = OK ty ->
  0 <= delta /\ delta + sizeof ty <= sizeof_fld fld.
Proof.
  intros.
  apply field_offset_in_range with (sid:=xH) (ty:=ty) in H; auto.
Qed.

Lemma field_offset_unsigned_repr:
  forall id fld z ty,
  field_offset id fld = OK z ->
  field_type id fld = OK ty ->
  sizeof_fld fld <= Int.max_unsigned ->
  Int.unsigned (Int.repr z) = z.
Proof.
  intros.
  eapply field_offset_in_range_simpl in H; eauto.
  generalize (sizeof_pos ty); intros.
  rewrite Int.unsigned_repr; try omega.
Qed.

Lemma field_offset_rec_type_exists:
  forall fld fid ofs pos,
  field_offset_rec fid fld pos = OK ofs ->
  exists ty, field_type fid fld = OK ty.
Proof.
  induction fld; simpl; intros.
  inv H.
  destruct (ident_eq _ _); eauto.
Qed.

Lemma field_offset_type_exists:
  forall fld fid ofs,
  field_offset fid fld = OK ofs ->
  exists ty, field_type fid fld = OK ty.
Proof.
  unfold field_offset. intros.
  eapply field_offset_rec_type_exists; eauto.
Qed.

Lemma field_type_offset_rec_exists:
  forall fld fid ty pos,
  field_type fid fld = OK ty ->
  exists ofs, field_offset_rec fid fld pos = OK ofs.
Proof.
  induction fld; simpl; intros.
  congruence.
  destruct (ident_eq fid i).
  inv H. eauto.
  eapply IHfld; eauto.
Qed.

Lemma field_type_offset_exists:
  forall fld fid ty,
  field_type fid fld = OK ty ->
  exists ofs, field_offset fid fld = OK ofs.
Proof.
  unfold field_offset. intros.
  eapply field_type_offset_rec_exists; eauto.
Qed.

Definition fieldlist_of(vas: list (ident*type)): fieldlist :=
  fold_right (fun p=> Fcons (fst p) (snd p)) Fnil vas.

Lemma fieldlist_list_in:
  forall al id ty,
  field_type id (fieldlist_of al) = OK ty ->
  In (id, ty) al.
Proof.
  induction al; simpl; intros.
  inv H.
  destruct a. simpl in *.
  compare id i; intros.
  subst. rewrite peq_true in *. inv H; auto.
  rewrite peq_false in *; eauto.
Qed.

Lemma list_in_fieldlist:
  forall al id ty,
  In (id, ty) al ->
  list_norepet (map fst al) ->
  field_type id (fieldlist_of al) = OK ty.
Proof.
  induction al; intros.
  +inv H.
  +inv H0. destruct H; subst; simpl.
   -rewrite peq_true; auto.
   -assert(id <> fst a).
      apply in_map with _ _ fst _ _ in H; eauto.
      simpl in H. red; intros. subst. auto.
    repeat rewrite peq_false; auto.
Qed.

Lemma fieldlist_list_in_offset_exists:
  forall al id pos,
  In id (map fst al) ->
  exists delta, field_offset_rec id (fieldlist_of al) pos = OK delta.
Proof.
  induction al; simpl; intros.
  +inv H.
  +destruct H; subst; simpl.
   -rewrite peq_true; eauto.
   -destruct (ident_eq id (fst a)) eqn:?; eauto.
Qed.

Lemma fieldlist_list_id_in:
  forall al id delta pos,
  field_offset_rec id (fieldlist_of al) pos = OK delta ->
  In id (map fst al).
Proof.
  induction al; simpl; intros.
  inv H.
  compare id (fst a); intros.
  subst. rewrite peq_true in *. inv H; auto.
  rewrite peq_false in *; eauto.
Qed.

Lemma fieldlist_list_notin:
  forall al id pos msg,
  field_offset_rec id (fieldlist_of al) pos = Error msg ->
  ~ In id (map fst al).
Proof.
  induction al; simpl; intros; auto.
  compare (fst a) id; intros; subst.
  rewrite peq_true in H. inv H.
  rewrite peq_false in H; auto.
  red. intros. destruct H0; auto.
  eapply IHal; eauto.
Qed.

Lemma field_type_notin_app:
  forall l1 l2 id,
  ~ In id (map fst l1) ->
  field_type id (fieldlist_of (l1++l2)) = field_type id (fieldlist_of l2).
Proof.
  induction l1; simpl; intros; eauto.
  rewrite peq_false; auto.
Qed.

Lemma fieldlist_list_notin_inv:
  forall al id pos,
  ~ In id (map fst al) ->
  exists msg, field_offset_rec id (fieldlist_of al) pos = Error msg.
Proof.
  induction al; simpl; intros; eauto.
  rewrite peq_false; auto.
Qed.

Lemma field_type_offset_error_rec:
  forall fld id msg1 pos,
  field_type id fld = Error msg1 ->
  exists msg2, field_offset_rec id fld pos = Error msg2.
Proof.
  induction fld; simpl; intros; eauto.
  destruct (ident_eq _ _); try congruence.
  eauto.
Qed.

Lemma field_type_offset_error:
  forall fld id msg1,
  field_type id fld = Error msg1 ->
  exists msg2, field_offset id fld = Error msg2.
Proof.
  intros. apply field_type_offset_error_rec with msg1; auto.
Qed.

Lemma field_type_ok_app:
  forall l1 l2 id ty,
  field_type id (fieldlist_of l1) = OK ty ->
  field_type id (fieldlist_of (l1 ++ l2))  = OK ty.
Proof.
  induction l1; simpl; intros.
  congruence.

  destruct a; simpl in *.
  compare id i; intros ; subst.
  rewrite peq_true in *; auto.
  rewrite peq_false in *; auto.
Qed.

Lemma field_offset_rec_fieldlist_of_notin_app_cons:
  forall id ty l1 l2 z,
  ~ In id (map fst l1) ->
  field_offset_rec id (fieldlist_of (l1 ++ (id, ty) :: l2)) z = OK (align (sizeof_struct (fieldlist_of l1) z) (alignof ty)).
Proof.
  induction l1; simpl; intros; auto.
  +rewrite peq_true; auto.
  +rewrite peq_false; auto.
Qed.

Lemma sizeof_struct_fieldlist_of_app_cons:
  forall l id ty z,
  sizeof_struct (fieldlist_of (l ++ (id, ty) :: nil)) z =
  align (sizeof_struct (fieldlist_of l) z) (alignof ty) + sizeof ty.
Proof.
  induction l; simpl; auto.
Qed.

Definition access_mode (ty: type) : mode :=
  match ty with
  | Tint I8 Signed => By_value Mint8signed
  | Tint I8 Unsigned => By_value Mint8unsigned
  | Tint I16 Signed => By_value Mint16signed
  | Tint I16 Unsigned => By_value Mint16unsigned
  | Tint I32 _ => By_value Mint32
  | Tint IBool _ => By_value Mint8unsigned
  | Tfloat F32 => By_value Mfloat32
  | Tfloat F64 => By_value Mfloat64
  | Tvoid => By_nothing
  | Tpointer _ => By_nothing
  | Tarray _ _ _ => By_reference
  | Tfunction _ _ _ => By_nothing
  | Tstruct _ _ => By_copy
end.

Definition typeof_array(t: type): res (type*Z) :=
  match t with
  | Tarray _ ty num => OK (ty,num)
  | _ => Error (MSG "Not Tarray " :: nil)
  end.

Definition fieldof_struct(t: type): res fieldlist :=
  match t with
  | Tstruct _ fld => OK fld
  | _ => Error (MSG "Not Tstruct " :: nil)
  end.

Lemma access_mode_eq:
  forall t, (exists c, access_mode t = By_value c) \/ access_mode t = By_copy \/ access_mode t = By_reference ->
  access_mode t = Cltypes.access_mode t.
Proof.
  destruct t; simpl; intros; auto;
  destruct H as [? | [? | ?]]; inv H; inv H0.
Qed.

Lemma sizeof_chunk_eq:
  forall t chunk,
  access_mode t = By_value chunk ->
  size_chunk chunk = sizeof t.
Proof.
  destruct t; intros; inv H; simpl; auto.
  destruct i; destruct s; inv H1; auto.
  destruct f; inv H1; auto.
Qed.

Lemma alignof_chunk_eq:
  forall ty chunk,
  access_mode ty = By_value chunk ->
  alignof ty = align_chunk chunk.
Proof.
  induction ty; simpl; intros; try congruence; auto.
  destruct i,s; inv H; auto.
  destruct f; inv H; auto.
Qed.

Lemma field_type_alignof_le:
  forall i f t,
  field_type i f = OK t ->
  alignof t <= alignof_fields f.
Proof.
  induction f; simpl; intros.
  congruence.
  destruct (ident_eq _ _).
  +inv H. apply zmax_l_le. omega.
  +apply zmax_r_le. auto.
Qed.

Lemma field_type_alignof:
  forall i f t,
  field_type i f = OK t ->
  (alignof t | alignof_fields f).
Proof.
  intros. generalize (alignof_1248 t).
  generalize (alignof_fields_1248 f).
  apply field_type_alignof_le in H. intros.
  destruct H0 as [ | [ | [ | ]]]; destruct H1 as [ | [ | [ | ]]];
  rewrite H0,H1 in *; try omega; try (exists 1; omega; fail);
  try (exists 2; omega; fail) .
  exists 4; omega. exists 8. omega. exists 4. omega.
Qed.

Definition is_arystr(t: type): bool :=
  match t with
  | Tarray _ _ _ => true
  | Tstruct _ _ => true
  | _ => false
  end.
