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

(** Type expressions for the Compcert C and Clight languages *)

Require Import Coqlib.
Require Import AST.
Require Import Errors.
Require Import Ctypes.
Require Archi.

(** * Syntax of types *)

(** The syntax of type expressions.  Some points to note:
- Array types [Tarray n] carry the size [n] of the array.
  Arrays with unknown sizes are represented by pointer types.
- Function types [Tfunction targs tres] specify the number and types
  of the function arguments (list [targs]), and the type of the
  function result ([tres]).  Variadic functions and old-style unprototyped
  functions are not supported.
- In C, struct and union types are named and compared by name.
  This enables the definition of recursive struct types such as
<<
  struct s1 { int n; struct * s1 next; };
>>
  Note that recursion within types must go through a pointer type.
  For instance, the following is not allowed in C.
<<
  struct s2 { int n; struct s2 next; };
>>
*)

Inductive type : Type :=
  | Tvoid: type                                    (**r the [void] type *)
  | Tint: intsize -> signedness -> type    (**r integer types *)
  | Tfloat: floatsize -> type              (**r floating-point types *)
  | Tpointer: type -> type                 (**r pointer types ([*ty]) *)
  | Tarray: ident -> type -> Z -> type              (**r array types ([ty[len]]) *)
  | Tfunction: typelist -> type -> calling_convention -> type    (**r function types *)
  | Tstruct: ident -> fieldlist -> type    (**r struct types *)

with typelist : Type :=
  | Tnil: typelist
  | Tcons: type -> typelist -> typelist

with fieldlist : Type :=
  | Fnil: fieldlist
  | Fcons: ident -> type -> fieldlist -> fieldlist.

Lemma type_eq: forall (ty1 ty2: type), {ty1=ty2} + {ty1<>ty2}
with typelist_eq: forall (tyl1 tyl2: typelist), {tyl1=tyl2} + {tyl1<>tyl2}
with fieldlist_eq: forall (fld1 fld2: fieldlist), {fld1=fld2} + {fld1<>fld2}.
Proof.
  assert (forall (x y: intsize), {x=y} + {x<>y}) by decide equality.
  assert (forall (x y: signedness), {x=y} + {x<>y}) by decide equality.
  assert (forall (x y: floatsize), {x=y} + {x<>y}) by decide equality.
  assert (forall (x y: attr), {x=y} + {x<>y}).
  { decide equality. decide equality. apply N.eq_dec. apply bool_dec. }
  generalize ident_eq zeq bool_dec. intros E1 E2 E3.
  decide equality.
  decide equality.
  decide equality.
  generalize ident_eq. intros E1. decide equality.
Defined.

Opaque type_eq typelist_eq fieldlist_eq.

Definition type_int32s := Tint I32 Signed.
Definition type_bool := Tint IBool Signed.
Definition type_pvoid := Tpointer Tvoid.

(** The usual unary conversion.  Promotes small integer types to [signed int32]
  and degrades array types and function types to pointer types. *)

Definition typeconv (ty: type) : type :=
  match ty with
  | Tint (I8 | I16 | IBool) _ => Tint I32 Signed
  | Tarray _ t sz       => Tpointer t
  | Tfunction _ _ _     => Tpointer ty
  | _                   => ty
  end.

(** * Operations over types *)

(** Natural alignment of a type, in bytes. *)

Fixpoint alignof (t: type) : Z :=
  match t with
  | Tvoid => 1
  | Tint I8 _ => 1
  | Tint I16 _ => 2
  | Tint I32 _ => 4
  | Tint IBool _ => 1
  | Tfloat F32 => 4
  | Tfloat F64 => Archi.align_float64
  | Tpointer _ => 4
  | Tarray _ t' _ => alignof t'
  | Tfunction _ _ _ => 1
  | Tstruct _ fld => alignof_fields fld
  end

with alignof_fields (f: fieldlist) : Z :=
  match f with
  | Fnil => 1
  | Fcons id t f' => Zmax (alignof t) (alignof_fields f')
  end.

Scheme type_ind2 := Induction for type Sort Prop
  with fieldlist_ind2 := Induction for fieldlist Sort Prop.

Lemma alignof_1248:
  forall t, alignof t = 1 \/ alignof t = 2 \/ alignof t = 4 \/ alignof t = 8
with alignof_fields_1248:
  forall f, alignof_fields f = 1 \/ alignof_fields f = 2 \/ alignof_fields f = 4 \/ alignof_fields f = 8.
Proof.
  induction t; simpl; auto.
  destruct i; auto.
  destruct f; auto.
  induction f; simpl; auto.
  rewrite Zmax_spec. destruct (zlt (alignof_fields f) (alignof t)); auto.
Qed.

Lemma alignof_pos:
  forall t, alignof t > 0.
Proof.
  intros. generalize (alignof_1248 t). omega.
Qed.

Lemma alignof_fields_pos:
  forall f, alignof_fields f > 0.
Proof.
  intros. generalize (alignof_fields_1248 f). omega.
Qed.

(** Size of a type, in bytes. *)

Fixpoint sizeof (t: type) : Z :=
  match t with
  | Tvoid => 1
  | Tint I8 _ => 1
  | Tint I16 _ => 2
  | Tint I32 _ => 4
  | Tint IBool _ => 1
  | Tfloat F32 => 4
  | Tfloat F64 => 8
  | Tpointer _ => 4
  | Tarray _ t' n => sizeof t' * Zmax 0 n
  | Tfunction _ _ _ => 1
  | Tstruct _ fld => align (sizeof_struct fld 0) (alignof t)
  end

with sizeof_struct (fld: fieldlist) (pos: Z) {struct fld} : Z :=
  match fld with
  | Fnil => pos
  | Fcons id t fld' => sizeof_struct fld' (align pos (alignof t) + sizeof t)
  end

with sizeof_union (fld: fieldlist) : Z :=
  match fld with
  | Fnil => 0
  | Fcons id t fld' => Zmax (sizeof t) (sizeof_union fld')
  end.

Lemma sizeof_pos:
  forall t, sizeof t >= 0.
Proof.
  intro t0.
  apply (type_ind2 (fun t => sizeof t >= 0)
                   (fun f => sizeof_union f >= 0 /\ forall pos, pos >= 0 -> sizeof_struct f pos >= 0));
  intros; simpl; auto; try omega.
  destruct i; omega.
  destruct f; omega.
  change 0 with (0 * Z.max 0 z) at 2. apply Zmult_ge_compat_r. auto. xomega.
  destruct H.
  generalize (align_le (sizeof_struct f 0) (alignof_fields f) (alignof_fields_pos f)).
  generalize (H0 0). intros. apply Zle_ge.
  apply Zle_trans with 0; try xomega.
  split. omega. auto.
  destruct H0. split; intros.
  generalize (Zmax2 (sizeof t) (sizeof_union f)). omega.
  apply H1.
  generalize (align_le pos (alignof t) (alignof_pos t)). omega.
Qed.

Lemma sizeof_struct_incr:
  forall fld pos, pos <= sizeof_struct fld pos.
Proof.
  induction fld; intros; simpl. omega.
  eapply Zle_trans. 2: apply IHfld.
  apply Zle_trans with (align pos (alignof t)).
  apply align_le. apply alignof_pos.
  assert (sizeof t >= 0) by apply sizeof_pos. omega.
Qed.

Lemma sizeof_alignof_compat:
  forall t, (alignof t | sizeof t).
Proof.
  induction t; simpl; try (apply Zdivide_refl).
  destruct f. exists 1. omega. exists 2. omega.
  apply Zdivide_mult_l. auto.
  apply align_divides. apply alignof_fields_pos.
Qed.

(** Byte offset for a field in a struct or union.
  Field are laid out consecutively, and padding is inserted
  to align each field to the natural alignment for its type. *)

Open Local Scope string_scope.

Fixpoint field_offset_rec (id: ident) (fld: fieldlist) (pos: Z)
                              {struct fld} : res Z :=
  match fld with
  | Fnil => Error (MSG "Unknown field " :: CTX id :: nil)
  | Fcons id' t fld' =>
      if ident_eq id id'
      then OK (align pos (alignof t))
      else field_offset_rec id fld' (align pos (alignof t) + sizeof t)
  end.

Definition field_offset (id: ident) (fld: fieldlist) : res Z :=
  field_offset_rec id fld 0.

Fixpoint field_type (id: ident) (fld: fieldlist) {struct fld} : res type :=
  match fld with
  | Fnil => Error (MSG "Unknown field " :: CTX id :: nil)
  | Fcons id' t fld' => if ident_eq id id' then OK t else field_type id fld'
  end.

(** Some sanity checks about field offsets.  First, field offsets are
  within the range of acceptable offsets. *)

Remark field_offset_rec_in_range:
  forall id ofs ty fld pos,
  field_offset_rec id fld pos = OK ofs -> field_type id fld = OK ty ->
  pos <= ofs /\ ofs + sizeof ty <= sizeof_struct fld pos.
Proof.
  intros until ty. induction fld; simpl.
  congruence.
  destruct (ident_eq id i); intros.
  inv H. inv H0. split. apply align_le. apply alignof_pos. apply sizeof_struct_incr.
  exploit IHfld; eauto. intros [A B]. split; auto.
  eapply Zle_trans; eauto. apply Zle_trans with (align pos (alignof t)).
  apply align_le. apply alignof_pos. generalize (sizeof_pos t). omega.
Qed.

Lemma field_offset_in_range:
  forall sid fld fid ofs ty,
  field_offset fid fld = OK ofs -> field_type fid fld = OK ty ->
  0 <= ofs /\ ofs + sizeof ty <= sizeof (Tstruct sid fld).
Proof.
  intros. exploit field_offset_rec_in_range; eauto. intros [A B].
  split. auto.  simpl. eapply Zle_trans. eauto.
  apply align_le. apply alignof_fields_pos.
Qed.

(** Second, two distinct fields do not overlap *)

Lemma field_offset_no_overlap:
  forall id1 ofs1 ty1 id2 ofs2 ty2 fld,
  field_offset id1 fld = OK ofs1 -> field_type id1 fld = OK ty1 ->
  field_offset id2 fld = OK ofs2 -> field_type id2 fld = OK ty2 ->
  id1 <> id2 ->
  ofs1 + sizeof ty1 <= ofs2 \/ ofs2 + sizeof ty2 <= ofs1.
Proof.
  intros until ty2. intros fld0 A B C D NEQ.
  assert (forall fld pos,
  field_offset_rec id1 fld pos = OK ofs1 -> field_type id1 fld = OK ty1 ->
  field_offset_rec id2 fld pos = OK ofs2 -> field_type id2 fld = OK ty2 ->
  ofs1 + sizeof ty1 <= ofs2 \/ ofs2 + sizeof ty2 <= ofs1).
  induction fld; intro pos; simpl. congruence.
  destruct (ident_eq id1 i); destruct (ident_eq id2 i).
  congruence.
  subst i. intros. inv H; inv H0.
  exploit field_offset_rec_in_range. eexact H1. eauto. tauto.
  subst i. intros. inv H1; inv H2.
  exploit field_offset_rec_in_range. eexact H. eauto. tauto.
  intros. eapply IHfld; eauto.

  apply H with fld0 0; auto.
Qed.

(** Third, if a struct is a prefix of another, the offsets of common fields
    are the same. *)

Fixpoint fieldlist_app (fld1 fld2: fieldlist) {struct fld1} : fieldlist :=
  match fld1 with
  | Fnil => fld2
  | Fcons id ty fld => Fcons id ty (fieldlist_app fld fld2)
  end.

Lemma field_offset_prefix:
  forall id ofs fld2 fld1,
  field_offset id fld1 = OK ofs ->
  field_offset id (fieldlist_app fld1 fld2) = OK ofs.
Proof.
  intros until fld2.
  assert (forall fld1 pos,
    field_offset_rec id fld1 pos = OK ofs ->
    field_offset_rec id (fieldlist_app fld1 fld2) pos = OK ofs).
  induction fld1; intros pos; simpl. congruence.
  destruct (ident_eq id i); auto.
  intros. unfold field_offset; auto.
Qed.

(** Fourth, the position of each field respects its alignment. *)

Lemma field_offset_aligned:
  forall id fld ofs ty,
  field_offset id fld = OK ofs -> field_type id fld = OK ty ->
  (alignof ty | ofs).
Proof.
  assert (forall id ofs ty fld pos,
          field_offset_rec id fld pos = OK ofs -> field_type id fld = OK ty ->
          (alignof ty | ofs)).
  induction fld; simpl; intros.
  discriminate.
  destruct (ident_eq id i). inv H; inv H0.
  apply align_divides. apply alignof_pos.
  eapply IHfld; eauto.
  intros. eapply H with (pos := 0); eauto.
Qed.

(** The [access_mode] function describes how a l-value of the given
type must be accessed:
- [By_value ch]: access by value, i.e. by loading from the address
  of the l-value using the memory chunk [ch];
- [By_reference]: access by reference, i.e. by just returning
  the address of the l-value (used for arrays and functions);
- [By_copy]: access is by reference, assignment is by copy
  (used for [struct] and [union] types)
- [By_nothing]: no access is possible, e.g. for the [void] type.
*)

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
  | Tpointer _ => By_value Mint32
  | Tarray _ _ _ => By_reference
  | Tfunction _ _ _ => By_reference
  | Tstruct _ _ => By_copy
end.

(** A variant of [alignof] for use in block copy operations.
  Block copy operations do not support alignments greater than 8,
  and require the size to be an integral multiple of the alignment. *)

Fixpoint alignof_blockcopy (t: type) : Z :=
  match t with
  | Tvoid => 1
  | Tint I8 _ => 1
  | Tint I16 _ => 2
  | Tint I32 _ => 4
  | Tint IBool _ => 1
  | Tfloat F32 => 4
  | Tfloat F64 => 8
  | Tpointer _ => 4
  | Tarray _ t' _ => alignof_blockcopy t'
  | Tfunction _ _ _ => 1
  | Tstruct _ fld => alignof t
  end.

Lemma alignof_range:
  forall t, alignof t <=8.
Proof.
  intros.
  destruct alignof_1248 with t as [ | [ | [ | ]]]; omega.
Qed.

Lemma alignof_fields_range:
  forall f, alignof_fields f <=8.
Proof.
  intros.
  destruct alignof_fields_1248 with f as [ | [ | [ | ]]]; omega.
Qed.

Lemma alignof_blockcopy_1248:
  forall ty, let a := alignof_blockcopy ty in a = 1 \/ a = 2 \/ a = 4 \/ a = 8.
Proof.
  induction ty; simpl; auto.
  destruct i; auto.
  destruct f; auto.
  destruct alignof_fields_1248 with f as [ | [ | [ | ]]]; xomega.
Qed.

Lemma alignof_blockcopy_pos:
  forall ty, alignof_blockcopy ty > 0.
Proof.
  intros. generalize (alignof_blockcopy_1248 ty). simpl. intuition omega.
Qed.

Lemma sizeof_alignof_blockcopy_compat:
  forall ty, (alignof_blockcopy ty | sizeof ty).
Proof.
  induction ty; simpl.
  apply Zdivide_refl.
  destruct i; apply Zdivide_refl.
  apply Zdivide_refl.
  apply Zdivide_refl.
  apply Z.divide_mul_l. auto.
  apply Zdivide_refl.
  apply align_divides. apply alignof_fields_pos.
Qed.

(** Extracting a type list from a function parameter declaration. *)

Fixpoint type_of_params (params: list (ident * type)) : typelist :=
  match params with
  | nil => Tnil
  | (id, ty) :: rem => Tcons ty (type_of_params rem)
  end.
