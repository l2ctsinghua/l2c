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
Require Import Memory.
Require Import Ctypes.
Require Import Cltypes.
Require Import Ltypes.
Require Import Integers.
Require Import Floats.
Require Import Lint.
Require Import ExtraList.

(** store value of the variable in memval list. *)

Definition mvl := list memval.

(** Reading N adjacent bytes in mvl. *)

Definition getN(n p: nat)(m: mvl) := getn n p m.

(** Writing N adjacent bytes in mvl. *)

Definition setN(m1: mvl)(p: nat)(m: mvl):= replace_map m m1 p.

(** accessible range of mvl. *)

Definition range_perm(m: mvl)(lo hi: Z) : Prop :=
  0 <= lo < hi /\ hi <= Z_of_nat (length m) <= Int.max_signed.

Definition is_byte(v: memval) : Prop :=
  match v with
  | Byte b => True
  | _ => False
  end.

Lemma is_byte_dec:
  forall v, {is_byte v} + {~ is_byte v}.
Proof.
  destruct v; simpl; intuition.
Qed.

Definition is_bytes (vl: list memval) : Prop :=
  Forall is_byte vl.

Lemma inj_bytes_is_bytes:
  forall m, is_bytes (inj_bytes m).
Proof.
  induction m; simpl; constructor; simpl; auto.
Qed.

Lemma is_bytes_dec:
  forall vl, {is_bytes vl} + {~ is_bytes vl}.
Proof.
  induction vl; simpl; intros.
  left. constructor.
  destruct (is_byte_dec a); destruct IHvl;
  try (right; red; intros; inv H; auto; fail).
  left. constructor; auto.
Qed.

Definition is_undef(v: memval) : Prop :=
  match v with
  | Undef => True
  | _ => False
  end.

Lemma is_undef_dec:
  forall v, {is_undef v} + {~ is_undef v}.
Proof.
  destruct v; simpl; intuition.
Qed.

Definition is_undefs (vl: list memval) : Prop :=
  Forall is_undef vl.

Inductive mvl_type(b: bool): mvl -> type -> Prop :=
  | mvl_type_val: forall m ty,
     is_arystr ty = false ->
     (if b then is_bytes m else True) ->
     Z_of_nat (length m) = sizeof ty ->
     mvl_type b m ty
  | mvl_type_ary: forall m aid aty num,
     mvl_array b m aty (nat_of_Z (Z.max 0 num)) ->
     mvl_type b m (Tarray aid aty num)
  | mvl_type_str: forall m sid fld,
     mvl_struct b m fld fld 0 ->
     mvl_type b m (Tstruct sid fld)

with mvl_array(b: bool): mvl -> type -> nat -> Prop :=
  | mvl_array_nil: forall ty,
     mvl_array b nil ty O
  | mvl_array_cons: forall m ml ty n,
     mvl_type b m ty ->
     mvl_array b ml ty n ->
     mvl_array b (m++ml) ty (S n)

with mvl_struct(b: bool): mvl -> fieldlist -> fieldlist -> Z -> Prop :=
  | mvl_struct_nil: forall m fld pos,
     is_undefs m ->
     Z_of_nat (length m) = align pos (alignof_fields fld) - pos  ->
     mvl_struct b m Fnil fld pos
  | mvl_struct_cons: forall m m1 ml pos i t ftl fld,
     is_undefs m ->
     Z_of_nat (length m) = align pos (alignof t) - pos ->
     mvl_type b m1 t ->
     mvl_struct b ml ftl fld (align pos (alignof t) + sizeof t) ->
     mvl_struct b (m++m1++ml) (Fcons i t ftl) fld pos.

Scheme mvl_type_ind2 := Minimality for mvl_type Sort Prop
  with mvl_array_ind2 := Minimality for mvl_array Sort Prop
  with mvl_struct_ind2 := Minimality for mvl_struct Sort Prop.
Combined Scheme mvl_type_arystr_ind2 from mvl_type_ind2, mvl_array_ind2, mvl_struct_ind2.

Lemma mvl_type_length:
forall b,
(
  forall m ty, mvl_type b m ty -> Z_of_nat (length m) = sizeof ty
)
/\
(
  forall m ty n, mvl_array b m ty n ->
  Z_of_nat (length m) = sizeof ty * (Z_of_nat n)
)
/\
(
  forall m fld f pos, mvl_struct b m fld f pos -> Z_of_nat (length m) =  align (sizeof_struct fld pos) (alignof_fields f) - pos
).
Proof.
  intros b. apply mvl_type_arystr_ind2; intros; auto.
  +simpl. generalize (Zle_max_l 0 num). intros.
   rewrite nat_of_Z_eq in H0; try omega.
  +simpl. omega.
  +simpl. omega.
  +rewrite app_length. rewrite Nat2Z.inj_add.
   rewrite Nat2Z.inj_succ.
   rewrite H0,H2. ring.
  +rewrite app_length. rewrite Nat2Z.inj_add.
   rewrite app_length. rewrite Nat2Z.inj_add.
   rewrite H0,H2,H4. simpl. ring.
Qed.

Definition mvl_alloc (m: mvl)(ty: type) : Prop :=
  mvl_type false m ty.

Lemma mvl_type_alloc:
(
  forall m ty, mvl_type true m ty -> mvl_type false m ty
)
/\
(
  forall m ty n, mvl_array true m ty n -> mvl_array false m ty n
)
/\
(
  forall m fld f pos, mvl_struct true m fld f pos -> mvl_struct false m fld f pos
).
Proof.
  apply mvl_type_arystr_ind2; intros;
  try (econstructor; eauto; fail).
 +econstructor 2; eauto.
 +econstructor 3; eauto.
Qed.

Lemma range_perm_dec:
  forall m lo hi, {range_perm m lo hi} + {~ range_perm m lo hi}.
Proof.
  unfold range_perm. intros.
  destruct (Z_le_dec 0 lo);
  destruct (Z_lt_dec lo hi);
  destruct (Z_le_dec hi (Z_of_nat (length m)));
  destruct (Z_le_dec (Z_of_nat (length m)) Int.max_signed);
  try (right; omega; fail); intuition.
Defined.

Lemma length_range_perm:
  forall m1 lo hi m2,
  range_perm m1 lo hi ->
  length m1 = length m2->
  range_perm m2 lo hi.
Proof.
  unfold range_perm. intros.
  rewrite <-H0. auto.
Qed.

Lemma getN_length:
  forall m ofs n,
  n + ofs <= Z_of_nat (length m) ->
  ofs >= 0 ->
  nat_of_Z n = length (getN (nat_of_Z n) (nat_of_Z ofs) m).
Proof.
  unfold getN. intros.
  destruct (zle n 0).
  +destruct n; simpl; auto.
   generalize (Pos2Z.is_pos p). omega.
  +rewrite getn_length; try omega.
   rewrite <- nat_of_Z_plus; try omega.
   apply <-Nat2Z.inj_le. rewrite nat_of_Z_eq; try omega.
Qed.

Lemma setN_length:
  forall m s m1,
  (s + length m <= length m1)%nat ->
  length (setN m s m1) = length m1.
Proof.
  unfold setN. intros.
  rewrite replace_map_length_eq; try omega.
  rewrite max_r; auto.
Qed.

Lemma getN_full:
  forall m,
  getN (length m) 0 m = m.
Proof.
  unfold getN,getn. intros.
  simpl. rewrite <-firstn_bign; auto.
Qed.

Lemma getN_add:
  forall i j o m,
  getN (i+j) o m = getN i o m ++ getN j (o+i) m.
Proof.
  unfold getN, getn. intros.
  rewrite firstn_app, skipn_add. auto.
Qed.

Lemma setN_full:
  forall m m1,
  length m = length m1 ->
  setN m1 0 m = m1.
Proof.
  unfold setN, replace_map. intros. simpl.
  rewrite skipn_bign; try omega.
  rewrite app_nil_r; auto.
Qed.

Lemma setN_same:
  forall m m1 m2 o,
  length m1 = length m2 ->
  (o <= length m)%nat ->
  setN m2 o (setN m1 o m) = setN m2 o m.
Proof.
  unfold setN, replace_map. intros. simpl.
  rewrite <-H. f_equal.
  +rewrite firstn_length_app1.
   rewrite firstn_firstn; auto.
   rewrite min_l; auto.
   rewrite firstn_length.
   rewrite min_l; auto.
  +f_equal. rewrite <-app_ass.
   rewrite skipn_length_app; rewrite app_length, firstn_length;
   rewrite min_l; auto.
   rewrite minus_diag. simpl. auto.
Qed.

Remark getN_setN_outside:
  forall vl q c n p,
  (p +  n <= q <= length c \/ q + (length vl) <= p <= length c)%nat ->
  getN n p (setN vl q c) = getN n p c.
Proof.
  intros. unfold getN, getn, setN, replace_map.
  destruct H.
  +rewrite skipn_length_app2.
   rewrite firstn_length_app1.
   replace q with (p + (q-p))%nat by omega.
   rewrite firstn_skipn_swap.
   rewrite firstn_firstn, Min.min_l; try omega; auto.
   rewrite skipn_length, firstn_length.
    rewrite Min.min_l,Min.min_l; try omega.
   rewrite firstn_length. rewrite Min.min_l; try omega.
  +rewrite skipn_length_app; rewrite firstn_length; rewrite Min.min_l; try omega.
   rewrite skipn_length_app; try omega.
   rewrite <-skipn_add. f_equal. f_equal. omega.
Qed.

Lemma getN_setN_same:
  forall vl o c,
  (o + length vl <= length c)%nat ->
  getN (length vl) o (setN vl o c) = vl.
Proof.
  unfold getN,getn,setN, replace_map. intros.
  rewrite skipn_length_app; rewrite firstn_length, Min.min_l; try omega.
  replace (o-o)%nat with 0%nat by omega.
  simpl. rewrite firstn_length_app1; try omega.
  rewrite <-firstn_bign; try omega. auto.
Qed.

Lemma getN_setN_swap:
  forall n p q v c,
  (p + n <= length c)%nat ->
  (q + length v <= n)%nat ->
  getN n p (setN v (p + q) c) = setN v q (getN n p c).
Proof.
  unfold getN,getn,setN,replace_map. intros.
  rewrite skipn_length_app2; try omega.
  rewrite firstn_skipn_swap.
  rewrite firstn_firstn. rewrite Min.min_l; try omega.
  rewrite firstn_length_app2; try omega; rewrite firstn_length; try omega.
  rewrite Min.min_l; try omega. f_equal.
  rewrite firstn_length_app2; try omega. f_equal.
  symmetry. rewrite <- firstn_skipn_swap.
  rewrite <-skipn_add. symmetry.
  rewrite <-firstn_skipn_swap. f_equal; try omega.
  f_equal; try omega.
  rewrite skipn_length. rewrite Min.min_l; try omega.
  rewrite skipn_length. rewrite Min.min_l; try omega.
    rewrite Min.min_l; try omega.
  rewrite firstn_length; try omega. rewrite Min.min_l; try omega.
Qed.

Lemma getN_app:
  forall n1 n2 o1 o2 m,
  (o2 + n2 <= n1)%nat ->
  getN n2 (o1 + o2) m = getN n2 o2 (getN n1 o1 m).
Proof.
  unfold getN. unfold getn. intros.
  rewrite skipn_add.
  replace n1 with (o2 + (n1-o2))%nat by omega.
  rewrite firstn_skipn_swap. rewrite firstn_firstn.
  rewrite min_l; auto. omega.
Qed.

Lemma getN_app_skipn:
  forall n o1 o2 l,
  getN n (o1 + o2) l = getN n o1 (skipn o2 l).
Proof.
  unfold getN, getn. intros.
  replace (o1 + o2)%nat with (o2 + o1)%nat; try omega.
  rewrite skipn_add. auto.
Qed.

Lemma getN_offset_incl_eq:
  forall m m' o1 o2 o n1 n2,
  0 <= o ->
  0 <= o1 ->
  0 <= o2 ->
  o + n2 <= n1 ->
  getN (nat_of_Z n1) (nat_of_Z o1) m' = getN (nat_of_Z n1) (nat_of_Z o2) m ->
  getN (nat_of_Z n2) (nat_of_Z (o1+ o)) m' = getN (nat_of_Z n2) (nat_of_Z (o2+o)) m.
Proof.
  unfold getN, getn. intros.
  destruct (zle n2 0).
  +destruct n2; simpl; auto.
   generalize (Pos2Z.is_pos p). omega.
  +repeat rewrite nat_of_Z_plus; try omega.
   repeat rewrite <-firstn_skipn_swap.
   repeat rewrite skipn_add. f_equal.
   repeat rewrite <-plus_assoc.
   repeat rewrite firstn_skipn_swap.
   apply firstn_sube with (nat_of_Z n1); auto.
   rewrite <-nat_of_Z_plus; try omega.
   apply Z2Nat.inj_le; try omega.
Qed.

Lemma getN_incl_eq:
  forall m m' o1 o2 n1 n2,
  0 <= o1 <= o2 ->
  o2 + n2 <= o1 + n1 ->
  getN (nat_of_Z n1) (nat_of_Z o1) m' = getN (nat_of_Z n1) (nat_of_Z o1) m ->
  getN (nat_of_Z n2) (nat_of_Z o2) m' = getN (nat_of_Z n2) (nat_of_Z o2) m.
Proof.
  intros. replace o2 with (o1 + (o2-o1)); try omega.
  apply getN_offset_incl_eq with n1; auto; try omega.
Qed.

Lemma range_perm_add_skipn:
  forall o o1 n m,
  0 <= o /\ 0 <= o1 ->
  range_perm m (o + o1) (o + o1 + n) ->
  range_perm (skipn (nat_of_Z o1) m) o (o + n).
Proof.
  unfold range_perm. intros. rewrite skipn_length.
  assert(nat_of_Z o1 <= length m)%nat.
    apply Nat2Z.inj_le. rewrite nat_of_Z_eq; try omega.
  rewrite min_l; try omega.
  rewrite Nat2Z.inj_sub; try omega.
  rewrite nat_of_Z_eq; try omega.
Qed.

(** value of Lustre. *)

Inductive val: Type :=
  | Vint: int -> val  (**r integer*)
  | Vfloat: float -> val (**r float-point*)
  | Vsingle: float32 -> val (**r single floating-point*)
  | Vmvl: mvl -> val. (**r value of stuct and array *)

Definition Vzero: val := Vint Int.zero.
Definition Vone: val := Vint Int.one.
Definition Vmone: val := Vint Int.mone.

Definition Vtrue: val := Vint Int.one.
Definition Vfalse: val := Vint Int.zero.

(** value match with type. *)

Definition has_type(v: val)(t: type) :=
  match v, t with
  | Vint _, Tint _ _ => True
  | Vfloat _, Tfloat F64 => True
  | Vsingle _, Tfloat F32 => True
  | Vmvl m, (Tstruct _ _ | Tarray _ _ _) => mvl_type true m t
  | _, _ => False
  end.

Definition has_types(vl: list val)(ts: list type) :=
  Forall2 has_type vl ts.

Lemma has_type_access_mode:
  forall v ty,
  has_type v ty ->
  (exists chunk, access_mode ty = By_value chunk) \/ access_mode ty = By_copy \/ access_mode ty = By_reference.
Proof.
  destruct v, ty; intros; try inv H; simpl; auto.
  left. destruct i0, s; eauto.
  left. destruct f0; eauto.
  left. destruct f0; eauto.
Qed.

Lemma has_type_access_mode_mvl:
  forall v ty,
  has_type v ty ->
  access_mode ty = By_copy \/ access_mode ty = By_reference ->
  exists m, v = Vmvl m /\ mvl_type true m ty.
Proof.
  destruct v, ty; simpl; intros; try tauto; eauto.
  destruct i0,s, H0; congruence.
  destruct f0, H0; congruence.
  destruct f0, H0; congruence.
Qed.

Lemma has_type_mvl_inv:
  forall ty m,
  has_type (Vmvl m) ty ->
  mvl_type true m ty /\ is_arystr ty = true.
Proof.
  destruct ty; simpl; intros; try tauto; split; auto.
Qed.

Lemma is_arystr_by_value:
  forall v t, is_arystr t = false ->
  has_type v t ->
  exists chunk, access_mode t = By_value chunk.
Proof.
  unfold is_arystr.
  destruct t, v; simpl; intros; try (inv H0;fail); try congruence.
  destruct i, s; eauto.
  destruct f; eauto.
  destruct f; eauto.
Qed.

Definition encode_val (chunk: memory_chunk) (v: val) : mvl :=
  match v, chunk with
  | Vint n, (Mint8signed | Mint8unsigned) => inj_bytes (encode_int 1%nat (Int.unsigned n))
  | Vint n, (Mint16signed | Mint16unsigned) => inj_bytes (encode_int 2%nat (Int.unsigned n))
  | Vint n, Mint32 => inj_bytes (encode_int 4%nat (Int.unsigned n))
  | Vsingle n, Mfloat32 => inj_bytes (encode_int 4%nat (Int.unsigned (Float32.to_bits n)))
  | Vfloat n, Mfloat64 => inj_bytes (encode_int 8%nat (Int64.unsigned (Float.to_bits n)))
  | _, _ => list_repeat (size_chunk_nat chunk) Undef
  end.

Lemma encode_val_length:
  forall chunk v, length(encode_val chunk v) = size_chunk_nat chunk.
Proof.
  destruct v, chunk; simpl;
  try rewrite length_inj_bytes;
  try apply encode_int_length;
  try apply length_list_repeat; auto.
Qed.

Lemma encode_val_is_bytes:
  forall ty chunk v,
  has_type v ty ->
  access_mode ty = By_value chunk ->
  is_bytes (encode_val chunk v).
Proof.
  unfold encode_val. intros.
  destruct ty, v; try tauto; inv H0; simpl.
  destruct i,s; inv H2; apply inj_bytes_is_bytes.
  destruct f; inv H2; inv H; apply inj_bytes_is_bytes.
  destruct f; inv H2; inv H; apply inj_bytes_is_bytes.
Qed.

Definition decode_val (chunk: memory_chunk) (vl: mvl) : option val :=
  match proj_bytes vl with
  | Some bl =>
      match chunk with
      | Mint8signed => Some (Vint(Int.sign_ext 8 (Int.repr (decode_int bl))))
      | Mint8unsigned => Some (Vint(Int.zero_ext 8 (Int.repr (decode_int bl))))
      | Mint16signed => Some (Vint(Int.sign_ext 16 (Int.repr (decode_int bl))))
      | Mint16unsigned => Some (Vint(Int.zero_ext 16 (Int.repr (decode_int bl))))
      | Mint32 => Some (Vint(Int.repr(decode_int bl)))
      | Mint64 => None
      | Mfloat32 => Some (Vsingle(Float32.of_bits (Int.repr (decode_int bl))))
      | Mfloat64 => Some (Vfloat(Float.of_bits (Int64.repr (decode_int bl))))
      | Many32 => None
      | Many64 => None
      end
  | None => None
  end.

Lemma proj_bytes_is_bytes:
  forall m l,
  proj_bytes m = Some l ->
  is_bytes m.
Proof.
  induction m; simpl; intros.
  constructor.
  destruct a; try congruence.
  remember (proj_bytes m). destruct o; try congruence.
  constructor; simpl; auto.
  inv H. apply IHm with l0; auto.
Qed.

Lemma decode_val_is_bytes:
  forall chunk m v,
  decode_val chunk m = Some v ->
  is_bytes m.
Proof.
  unfold decode_val. intros.
  remember (proj_bytes m). destruct o; try congruence.
  eapply proj_bytes_is_bytes; eauto.
Qed.

Definition valid_access (m: mvl) (chunk: memory_chunk)(ofs: Z): Prop :=
  range_perm m ofs (ofs + size_chunk chunk)
  /\ (align_chunk chunk | ofs).

Lemma valid_access_dec:
  forall m chunk ofs,
  {valid_access m chunk ofs} + {~ valid_access m chunk ofs}.
Proof.
  intros.
  destruct (range_perm_dec m ofs (ofs + size_chunk chunk)).
  destruct (Zdivide_dec (align_chunk chunk) ofs (align_chunk_pos chunk)).
  left; constructor; auto.
  right; red; intro V; inv V; contradiction.
  right; red; intro V; inv V; contradiction.
Defined.

Lemma length_valid_access:
  forall m1 chunk o m2,
  valid_access m1 chunk o ->
  length m1 = length m2->
  valid_access m2 chunk o.
Proof.
  unfold valid_access, range_perm. intros.
  rewrite <-H0. auto.
Qed.

(** [load chunk m ofs] perform a read in mvl [m], at offset [ofs].
  It returns the value of the memory chunk at that offset.
 [None] is returned if the accessed bytes are not readable. *)

Definition load(chunk: memory_chunk)(m: mvl)(ofs: Z): option val :=
  if valid_access_dec m chunk ofs
  then decode_val chunk (getN (size_chunk_nat chunk) (nat_of_Z ofs) m)
  else None.

Lemma load_valid_access:
  forall chunk m ofs v,
  load chunk m ofs = Some v ->
  valid_access m chunk ofs.
Proof.
  intros until v. unfold load.
  destruct (valid_access_dec m _ _); intros.
  auto.
  congruence.
Qed.

Lemma byte_unsigned_div_256:
  forall a, Byte.unsigned a / 256 = 0.
Proof.
  intros. generalize (Byte.unsigned_range a).
  intros. rewrite Z.div_small; auto.
Qed.

Lemma repr_add_mult:
  forall a b,  Byte.repr (Byte.unsigned a + b * 256) = a.
Proof.
  intros. apply Byte.eqm_repr_eq.
  unfold Byte.eqm, Byte.eqmod. exists b.
  unfold Byte.modulus, Byte.wordsize, Wordsize_8.wordsize.
  unfold two_power_nat, shift_nat. simpl. omega.
Qed.

Lemma bytes_of_int_of_bytes:
  forall l, bytes_of_int (length l) (int_of_bytes l) = l.
Proof.
  induction l; simpl; intros; auto.
  rewrite repr_add_mult.
  rewrite Z_div_plus_full; try omega.
  rewrite byte_unsigned_div_256. simpl.
  f_equal; auto.
Qed.

Lemma encode_decode_int:
  forall l,
  encode_int (length l) (decode_int l) = l.
Proof.
  unfold encode_int, decode_int, rev_if_be.
  intros. destruct Archi.big_endian.
  rewrite <-rev_length.
  rewrite bytes_of_int_of_bytes.
  apply rev_involutive.
  apply bytes_of_int_of_bytes; auto.
Qed.

Lemma decode_int_range:
  forall l, 0 <= decode_int l < two_p (Z.of_nat (length l) * 8).
Proof.
  unfold decode_int. intros.
  generalize (int_of_bytes_range (rev_if_be l)). intros.
  rewrite rev_if_be_length in H. auto.
Qed.

Lemma deconde_encode_inv:
  forall chunk v vl,
  decode_val chunk vl = Some v ->
  length vl = size_chunk_nat chunk ->
  vl = encode_val chunk v.
Proof.
  unfold encode_val, decode_val, size_chunk_nat. intros.
  destruct (proj_bytes vl) eqn:?; try congruence.
  apply inj_proj_bytes in Heqo. subst.
  rewrite length_inj_bytes in H0.
  destruct chunk; inv H; simpl in *; f_equal.
  +transitivity (encode_int 1 (decode_int l)).
   replace 1%nat with (length l); auto.
   rewrite encode_decode_int; auto.
   apply encode_int_8_mod; auto. apply Int.eqmod_sym.
   remember (Int.repr (decode_int l)) as x.
   replace (decode_int l) with (Int.unsigned x).
   apply Int.eqmod_sign_ext'.
   unfold Int.zwordsize, Int.wordsize. simpl. omega.
   subst. rewrite Int.unsigned_repr; auto.
   generalize (decode_int_range l) (Int.two_p_range 8). rewrite H0.
   simpl. intros. unfold Int.zwordsize, Int.wordsize in *.
   simpl in *. xomega.
  +rewrite <-decode_encode_int_1.
   cut (0 <= decode_int l <= Int.max_unsigned). intros.
   rewrite Int.unsigned_repr with (decode_int l); auto.
   replace 1%nat with (length l); auto.
   rewrite encode_decode_int.
   rewrite Int.unsigned_repr; auto.
   rewrite encode_decode_int; auto.
   generalize (decode_int_range l) (Int.two_p_range 8). rewrite H0.
   simpl. intros. unfold Int.zwordsize, Int.wordsize in *.
   simpl in *. xomega.
  +transitivity (encode_int 2 (decode_int l)).
   replace 2%nat with (length l); auto.
   rewrite encode_decode_int; auto.
   apply encode_int_16_mod; auto. apply Int.eqmod_sym.
   remember (Int.repr (decode_int l)) as x.
   replace (decode_int l) with (Int.unsigned x).
   apply Int.eqmod_sign_ext'.
   unfold Int.zwordsize, Int.wordsize. simpl. omega.
   subst. rewrite Int.unsigned_repr; auto.
   generalize (decode_int_range l) (Int.two_p_range 16). rewrite H0.
   simpl. intros. unfold Int.zwordsize, Int.wordsize in *.
   simpl in *. xomega.
  +rewrite <-decode_encode_int_2.
   cut (0 <= decode_int l <= Int.max_unsigned). intros.
   rewrite Int.unsigned_repr with (decode_int l); auto.
   replace 2%nat with (length l); auto.
   rewrite encode_decode_int.
   rewrite Int.unsigned_repr; auto.
   rewrite encode_decode_int; auto.
   generalize (decode_int_range l) (Int.two_p_range 16). rewrite H0.
   simpl. intros. unfold Int.zwordsize, Int.wordsize in *.
   simpl in *. xomega.
  +rewrite Int.unsigned_repr.
   replace 4%nat with (length l); auto.
   rewrite encode_decode_int; auto.
   generalize (decode_int_range l). rewrite H0.
   simpl. unfold Int.max_unsigned, two_power_pos, shift_pos.
   simpl. xomega.
  +rewrite Float32.to_of_bits. rewrite Int.unsigned_repr.
   replace 4%nat with (length l); auto.
   rewrite encode_decode_int; auto.
   generalize (decode_int_range l). rewrite H0.
   simpl. unfold Int.max_unsigned, two_power_pos, shift_pos.
   simpl. xomega.
  +rewrite Float.to_of_bits. rewrite Int64.unsigned_repr.
   replace 8%nat with (length l); auto.
   rewrite encode_decode_int; auto.
   generalize (decode_int_range l) . rewrite H0.
   unfold Int64.max_unsigned. simpl.
   unfold two_power_pos, shift_pos. simpl. omega.
Qed.

Lemma decode_val_vmvl_false:
  forall chunk m1 m2, decode_val chunk m1 = Some (Vmvl m2) -> False.
Proof.
  unfold decode_val. intros.
  destruct (proj_bytes m1); try congruence.
  destruct chunk; try congruence.
Qed.

Lemma load_vmvl_false:
  forall chunk id ofs m,
  load chunk id ofs = Some (Vmvl m) -> False.
Proof.
  unfold load. intros.
  destruct (valid_access_dec _ _ _); try congruence.
  inv H. apply decode_val_vmvl_false in H1; auto.
Qed.

(** [loadbytes m ofs n] reads [n] consecutive bytes starting at
  offset [ofs].  Returns [None] if the accessed offset are not accessible. *)

Definition loadbytes(m: mvl)(ofs n: Z): option mvl:=
  if range_perm_dec m ofs (ofs + n)
  then Some (getN (nat_of_Z n) (nat_of_Z ofs) m)
  else None.

Theorem range_perm_loadbytes:
  forall m ofs len,
  range_perm m ofs (ofs + len) ->
  exists bytes, loadbytes m ofs len = Some bytes.
Proof.
  intros. econstructor. unfold loadbytes. rewrite pred_dec_true; eauto.
Qed.

Theorem loadbytes_range_perm:
  forall m ofs len bytes,
  loadbytes m ofs len = Some bytes ->
  range_perm m ofs (ofs + len).
Proof.
  intros until bytes. unfold loadbytes.
  destruct (range_perm_dec m ofs (ofs + len)). auto. congruence.
Qed.

Lemma range_perm_false_loadbytes:
  forall m b ofs len,
  ~ Mem.range_perm m b ofs (ofs + len) Cur Readable ->
  Mem.loadbytes m b ofs len = None.
Proof.
  intros.
  destruct (Mem.loadbytes m b ofs len) eqn:?; auto.
  apply Mem.loadbytes_range_perm in Heqo. congruence.
Qed.

Lemma loadbytes_none_range_perm:
  forall m b ofs len,
  Mem.loadbytes m b ofs len = None ->
  ~ Mem.range_perm m b ofs (ofs + len) Cur Readable.
Proof.
  intros.
  destruct (Mem.range_perm_dec m b ofs (ofs + len) Cur Readable); auto.
  apply Mem.range_perm_loadbytes in r. destruct r. congruence.
Qed.

Theorem loadbytes_contents:
  forall m ofs len bytes,
  loadbytes m ofs len = Some bytes ->
  bytes = getN (nat_of_Z len) (nat_of_Z ofs) m.
Proof.
  unfold loadbytes. intros.
  destruct (range_perm_dec m ofs (ofs + len)); inv H; auto.
Qed.

Theorem loadbytes_length:
  forall m ofs n bytes,
  loadbytes m ofs n = Some bytes ->
  nat_of_Z n = length bytes.
Proof.
  unfold loadbytes; intros.
  destruct (range_perm_dec m ofs (ofs + n)); try congruence.
  inv H. red in r. apply getN_length; try omega.
Qed.

Theorem loadbytes_length2:
  forall m ofs n bytes,
  loadbytes m ofs n = Some bytes ->
  n = Z_of_nat (length bytes).
Proof.
  unfold loadbytes; intros.
  destruct (range_perm_dec m ofs (ofs + n)); try congruence.
  inv H. red in r. rewrite <-getN_length; try omega.
  rewrite nat_of_Z_eq; omega.
Qed.

Theorem loadbytes_length_le:
  forall m ofs n bytes,
  loadbytes m ofs n = Some bytes ->
  (length bytes <= length m)%nat.
Proof.
  intros. generalize H. intros.
  apply loadbytes_range_perm in H.
  erewrite <-loadbytes_length; eauto.
  red in H. apply <-Nat2Z.inj_le.
  rewrite nat_of_Z_eq; omega.
Qed.

Lemma loadbytes_first:
  forall l1 l2 l3,
  loadbytes (l1 ++ l2) 0 (Z.of_nat (length l1)) = Some l3 ->
  l1 = l3.
Proof.
  unfold loadbytes. simpl. intros.
  destruct (range_perm_dec (l1 ++ l2) 0 (Z.of_nat (length l1))); try congruence.
  inv H. rewrite nat_of_Z_of_nat.
  unfold getN,getn. simpl.
  rewrite firstn_length_app2; try omega.
  replace (length l1 - length l1)%nat with O; try omega.
  simpl. rewrite app_nil_r; auto.
Qed.

Lemma loadbytes_getN_eq:
  forall m m' o n,
  loadbytes m' o n = loadbytes m o n ->
  length m = length m' ->
  0 <= o ->
  o + n <= Z_of_nat (length m) <= Int.max_signed ->
  getN (nat_of_Z n) (nat_of_Z o) m' = getN (nat_of_Z n) (nat_of_Z o) m.
Proof.
  unfold loadbytes. intros.
  destruct (zle n 0).
  +destruct n; simpl; auto.
   generalize (Pos2Z.is_pos p). omega.
  +rewrite pred_dec_true, pred_dec_true in H.
   congruence.
   unfold range_perm. omega.
   unfold range_perm. omega.
Qed.

Lemma loadbytes_load_app:
  forall m m1 o1 o2 chunk size v,
  loadbytes m (Int.unsigned o1) size = Some m1 ->
  load chunk m1 (Int.unsigned o2) = Some v ->
  (align_chunk chunk | Int.unsigned o1) ->
  load chunk m (Int.unsigned (Int.add o1 o2)) = Some v.
Proof.
  intros. generalize H; intros.
  apply loadbytes_length in H2.
  unfold load, loadbytes in *.
  destruct (range_perm_dec m _ _) eqn:?; try congruence.
  destruct (valid_access_dec _ chunk (Int.unsigned o2)) eqn:?; try congruence.
  inv H. clear Heqs Heqs0.
  destruct r as [? [? ?]]. destruct v0 as [[? [? ?]] ?].
  rewrite <-H2 in *. rewrite nat_of_Z_eq in * by omega.
  unfold Int.add. rewrite Int.unsigned_repr; try omega.
  rewrite pred_dec_true; eauto.
  +rewrite <-H0. f_equal. rewrite nat_of_Z_plus by omega.
   rewrite <-getN_app; auto.
   apply Z2Nat.inj_le in H6; try omega.
   rewrite nat_of_Z_plus in H6; auto; omega.
  +repeat split; auto; try omega.
   apply Zdivide_plus_r; auto.
  +split. omega. apply Zle_trans with Int.max_signed; try omega.
   generalize Int.max_signed_unsigned. omega.
Qed.

Lemma loadbytes_load_app_inv:
  forall m m1 o1 o2 chunk size v,
  loadbytes m (Int.unsigned o1) size = Some m1 ->
  load chunk m (Int.unsigned (Int.add o1 o2)) = Some v ->
  Int.unsigned o2 + size_chunk chunk  <= size ->
  (align_chunk chunk | Int.unsigned o1) ->
  load chunk m1 (Int.unsigned o2) = Some v .
Proof.
  intros. generalize H; intros.
  apply loadbytes_length in H3.
  unfold load, loadbytes in *.
  destruct (range_perm_dec m _ _) eqn:?; try congruence.
  destruct (valid_access_dec m _ _) eqn:?; try congruence.
  inv H. clear Heqs Heqs0.
  generalize (Int.unsigned_range o1) (Int.unsigned_range o2) ; intros.
  generalize Int.max_signed_unsigned; intros.
  destruct r as [? [? ?]]. destruct v0 as [[? [? ?]] ?].
  unfold Int.add in *. rewrite Int.unsigned_repr in *; try omega.
  rewrite pred_dec_true; eauto.
  +rewrite <-H0. f_equal.
   rewrite nat_of_Z_plus by omega.
   rewrite <-getN_app; auto.
   apply Z2Nat.inj_le in H1; try omega.
   rewrite nat_of_Z_plus in H1; auto; omega.
  +repeat split; auto; try omega.
   -rewrite <-H3. rewrite nat_of_Z_max.
    rewrite Z.max_l; try omega.
   -rewrite <-H3. rewrite nat_of_Z_max.
    rewrite Z.max_l; try omega.
   -eapply Zdivides_plus_inv; eauto.
Qed.

Lemma loadbytes_loadbytes_app:
  forall m m1 m2 o1 o2 s1 s2,
  loadbytes m (Int.unsigned o1) s1 = Some m1 ->
  loadbytes m1 (Int.unsigned o2) s2 = Some m2 ->
  loadbytes m (Int.unsigned (Int.add o1 o2)) s2 = Some m2.
Proof.
  intros. generalize H; intros.
  apply loadbytes_length in H1.
  unfold loadbytes in *.
  destruct (range_perm_dec m (Int.unsigned o1) _); inv H.
  destruct (range_perm_dec _ (Int.unsigned o2) _); inv H0.
  destruct r as [? [? ?]]. destruct r0 as [? [? ?]].
  rewrite <-H1 in *. rewrite nat_of_Z_eq in * by omega.
  unfold Int.add. rewrite Int.unsigned_repr; try omega.
  rewrite pred_dec_true; eauto.
  +f_equal. rewrite nat_of_Z_plus by omega.
   rewrite <-getN_app; auto.
   apply Z2Nat.inj_le in H4; try omega.
   rewrite nat_of_Z_plus in H4; auto; omega.
  +repeat split; auto; omega.
  +split. omega. generalize Int.max_signed_unsigned. omega.
Qed.

Lemma loadbytes_app_getn:
  forall m m2 o1 o2 s1 s2,
  loadbytes m (Int.unsigned (Int.add o1 o2)) s2 = Some m2 ->
  Int.unsigned o2 + s2  <= s1 ->
  Int.unsigned o1 + s1 <= Z.of_nat (length m) ->
  loadbytes (getN (nat_of_Z s1) (nat_of_Z (Int.unsigned o1)) m) (Int.unsigned o2) s2 = Some m2.
Proof.
  intros. generalize H; intros.
  apply loadbytes_length in H2.
  unfold loadbytes in *.
  destruct (range_perm_dec m _ _); try congruence.
  generalize (Int.unsigned_range o1) (Int.unsigned_range o2) Int.max_signed_unsigned; intros.
  destruct r as [? [? ?]].
  unfold Int.add in *. rewrite Int.unsigned_repr in *; try omega.
  inv H. rewrite pred_dec_true; eauto.
  +f_equal. symmetry. rewrite nat_of_Z_plus by omega.
   apply getN_app; auto.
   rewrite <-nat_of_Z_plus by omega.
   apply Z2Nat.inj_le; omega.
  +red. rewrite <-getN_length; try omega.
   rewrite nat_of_Z_eq; try omega.
Qed.

Lemma loadbytes_loadbytes_app_inv:
  forall m m1 m2 o1 o2 s1 s2,
  loadbytes m (Int.unsigned o1) s1 = Some m1 ->
  loadbytes m (Int.unsigned (Int.add o1 o2)) s2 = Some m2 ->
  Int.unsigned o2 + s2  <= s1 ->
  loadbytes m1 (Int.unsigned o2) s2 = Some m2.
Proof.
  intros. generalize H; intros.
  apply loadbytes_range_perm in H.
  apply loadbytes_contents in H2. subst.
  eapply loadbytes_app_getn; eauto.
  red in H. omega.
Qed.

Lemma loadbytes_full:
  forall m, 0 < Z.of_nat (length m) <= Int.max_signed ->
  loadbytes m 0 (Z.of_nat (length m))= Some m.
Proof.
  unfold loadbytes. intros.
  rewrite pred_dec_true; eauto.
  simpl. rewrite nat_of_Z_of_nat.
  rewrite getN_full; auto.
  red. simpl. split; try omega.
Qed.

Lemma loadbytes_eq_app_inv:
  forall m1 m2 b ofs n1 n2,
  Mem.loadbytes m1 b ofs n1 = Mem.loadbytes m2 b ofs n1 ->
  Mem.loadbytes m1 b (ofs+n1) n2 = Mem.loadbytes m2 b (ofs+n1) n2 ->
  0 <= n1 -> 0 <= n2 ->
  Mem.loadbytes m1 b ofs (n1 + n2) = Mem.loadbytes m2 b ofs (n1 + n2).
Proof.
  intros.
  destruct (Mem.loadbytes m1 b ofs n1) eqn:?;
  destruct (Mem.loadbytes m2 b ofs n1) eqn:?; inv H.
  +destruct (Mem.loadbytes m1 b (ofs + n1) n2) eqn:?;
   destruct (Mem.loadbytes m2 b (ofs + n1) n2) eqn:?; inv H0.
   -repeat erewrite Mem.loadbytes_concat; eauto; try omega.
   -repeat rewrite range_perm_false_loadbytes; auto.
    apply loadbytes_none_range_perm in Heqo2.
    red; intros. apply Heqo2. red; intros.
    apply H. omega.
    apply loadbytes_none_range_perm in Heqo1.
    apply Mem.loadbytes_range_perm in Heqo.
    red; intros. apply Heqo1. red; intros.
    apply H. omega.
  +repeat rewrite range_perm_false_loadbytes; auto.
   -apply loadbytes_none_range_perm in Heqo0.
    red; intros. apply Heqo0. red; intros.
    apply H. omega.
   -apply loadbytes_none_range_perm in Heqo.
    red; intros. apply Heqo. red; intros.
    apply H. omega.
Qed.

(** [store chunk m ofs v] perform a write in mvl [m].
  Value [v] is stored at offset [ofs]. Return the updated mvl store,
  or [None] if the accessed bytes are not accessible. *)

Definition store(chunk: memory_chunk)(m: mvl)(ofs: Z) (v: val): option mvl :=
  if valid_access_dec m chunk ofs
  then Some (setN (encode_val chunk v) (nat_of_Z ofs) m)
  else None.

Theorem valid_access_store:
  forall m1 chunk ofs v,
  valid_access m1 chunk ofs ->
  { m2: mvl | store chunk m1 ofs v = Some m2 }.
Proof.
  intros.
  unfold store.
  destruct (valid_access_dec _ _ _).
  eauto.
  contradiction.
Defined.

Lemma store_trans:
  forall t m m0 m1 o v1 v2,
  store t m o v1 = Some m1 ->
  store t m o v2 = Some m0 ->
  store t m0 o v1 = Some m1.
Proof.
  unfold store. simpl; intros.
  destruct (valid_access_dec m t o); inv H. inv H0.
  destruct v as [[? [? ?]] ?].
  rewrite pred_dec_true.
  +rewrite setN_same; auto.
   repeat rewrite encode_val_length; auto.
   apply Nat2Z.inj_le. rewrite nat_of_Z_eq; omega.
  +split; auto. red. rewrite setN_length; auto;
   rewrite encode_val_length; auto;
   unfold size_chunk_nat; simpl.
   apply Nat2Z.inj_le.
   rewrite Nat2Z.inj_add, nat_of_Z_eq, nat_of_Z_eq; simpl; try omega.
Qed.

Section STORE.

Variable chunk: memory_chunk.
Variable m1: mvl.
Variable ofs: Z.
Variable v: val.
Variable m2: mvl.
Hypothesis STORE: store chunk m1 ofs v = Some m2.

Lemma store_mem_contents: m2 = setN (encode_val chunk v) (nat_of_Z ofs) m1.
Proof.
  unfold store in STORE. destruct (valid_access_dec m1 _ _); inv STORE.
  auto.
Qed.

Theorem store_length: length m1 = length m2.
Proof.
  unfold store in STORE. destruct (valid_access_dec m1 _ _); inv STORE.
  destruct v0 as [[? [? ?]] ?].
  generalize (size_chunk_pos chunk); intros.
  rewrite setN_length; auto. rewrite encode_val_length; unfold size_chunk_nat.
  apply Z2Nat.inj_le in H0; try omega. rewrite Z2Nat.inj_add in H0; try omega.
  rewrite Nat2Z.id in H0; auto.
Qed.

Theorem store_valid_access: valid_access m2 chunk ofs.
Proof.
  assert (length m1 = length m2).
    eapply store_length; eauto.
  unfold store in STORE.
  destruct (valid_access_dec _ _ _); inv STORE.
  destruct v0 as [[? [? ?]] ?].
  repeat (split; auto); try omega.
Qed.

Theorem store_valid_access_1:
  forall chunk' ofs',
  valid_access m1 chunk' ofs' ->
  valid_access m2 chunk' ofs'.
Proof.
  unfold valid_access, range_perm.
  intuition; rewrite <-store_length; auto.
Qed.

Theorem store_valid_access_2:
  forall chunk' ofs',
  valid_access m2 chunk' ofs' ->
  valid_access m1 chunk' ofs'.
Proof.
  unfold valid_access, range_perm.
  intuition; rewrite store_length; auto.
Qed.

Theorem store_range_perm_1:
  forall ofs' n,
  range_perm m1 ofs' (ofs' + n) ->
  range_perm m2 ofs' (ofs' + n).
Proof.
  unfold range_perm. intros.
  rewrite <-store_length; auto.
Qed.

Theorem store_range_perm_2:
  forall ofs' n,
  range_perm m2 ofs' (ofs' + n)->
  range_perm m1 ofs' (ofs' + n).
Proof.
  unfold range_perm. intros.
  rewrite store_length; auto.
Qed.

Theorem store_decode_encode_val_load:
  forall v', decode_val chunk (encode_val chunk v) = Some v' ->
  load chunk m2 ofs = Some v'.
Proof.
  generalize store_valid_access; intros.
  unfold load. rewrite pred_dec_true; auto.
  rewrite store_mem_contents; auto.
  assert(size_chunk_nat chunk = length (encode_val chunk v)).
    rewrite encode_val_length; auto.
  rewrite H1. rewrite getN_setN_same; auto.
  apply store_valid_access_2 in H.
  rewrite <-H1. destruct H as [[? [? ?]] ?].
  apply Z2Nat.inj_le in H2; try omega.
  rewrite nat_of_Z_of_nat in H2.
  unfold size_chunk_nat.
  rewrite Z2Nat.inj_add in H2; try omega.
  unfold Z.to_nat, nat_of_Z in *; auto.
Qed.

Theorem load_store_other:
  forall chunk' ofs',
  ofs' + size_chunk chunk' <= ofs
  \/ ofs + size_chunk chunk <= ofs' ->
  load chunk' m2 ofs' = load chunk' m1 ofs'.
Proof.
  intros. unfold load.
  assert(valid_access m2 chunk ofs).
    eapply store_valid_access; eauto.
  apply store_valid_access_2 in H0.
  destruct (valid_access_dec m1 chunk' ofs').
  +rewrite pred_dec_true; auto.
   rewrite store_mem_contents. decEq.
   destruct v0 as [[? [? ?]] ?].
   destruct H0 as  [[? [? ?]] ?].
   apply getN_setN_outside.
   rewrite encode_val_length. unfold size_chunk_nat.
   repeat rewrite <-nat_of_Z_plus; try omega.
   -destruct H; [left | right];
    split; apply Nat2Z.inj_le; auto; repeat rewrite nat_of_Z_eq; try omega.
   -apply store_valid_access_1; auto.
  +rewrite pred_dec_false;auto.
   red; intros. elim n.
   apply store_valid_access_2; auto.
Qed.

Theorem loadbytes_store_other:
  forall ofs' n,
  n <= 0
  \/ ofs' + n <= ofs
  \/ ofs + size_chunk chunk <= ofs' ->
  loadbytes m2 ofs' n = loadbytes m1 ofs' n.
Proof.
  intros. unfold loadbytes.
  assert(range_perm m2 ofs (ofs + size_chunk chunk)).
    eapply store_valid_access; eauto.
  apply store_range_perm_2 in H0.
  destruct (range_perm_dec m1 ofs' (ofs' + n)).
  +rewrite pred_dec_true; auto.
   rewrite store_mem_contents. decEq.
   destruct (zle n 0).
   rewrite (nat_of_Z_neg _ l). auto.
   destruct H. omegaContradiction.
   unfold range_perm in *. apply getN_setN_outside.
   rewrite encode_val_length. unfold size_chunk_nat.
   repeat rewrite <-nat_of_Z_plus; try omega.
   -destruct H; [left | right];
    split; apply Nat2Z.inj_le; auto; repeat rewrite nat_of_Z_eq; try omega.
   -apply store_range_perm_1; auto.
  +rewrite pred_dec_false;auto.
   red; intros; elim n0.
   apply store_range_perm_2; auto.
Qed.

End STORE.

Lemma setN_encode_val:
 forall mv chunk v,
 length mv = size_chunk_nat chunk ->
 setN (encode_val chunk v) 0 mv = encode_val chunk v.
Proof.
  intros. apply setN_full; auto.
  rewrite encode_val_length. omega.
Qed.

(** [storebytes m ofs bytes] stores the given list of bytes [bytes]
  starting at offset [ofs].  Returns updated mvl or [None]
  if the offset are not accessible. *)

Definition storebytes(m: mvl)(ofs: Z)(bytes: mvl): option mvl :=
  if range_perm_dec m ofs (ofs + Z_of_nat (length bytes))
  then Some (setN bytes (nat_of_Z ofs) m)
  else None.

Theorem range_perm_store_bytes:
  forall m1 ofs bytes,
  range_perm m1 ofs (ofs + (Z_of_nat (length bytes))) ->
  { m2: mvl | storebytes m1 ofs bytes = Some m2 }.
Proof.
  intros.
  unfold storebytes.
  destruct (range_perm_dec m1 ofs (ofs + Z.of_nat (length bytes))).
  eauto.
  contradiction.
Defined.

Lemma storebytes_trans:
  forall m m0 m1 o mv1 mv2,
  storebytes m o mv1 = Some m1 ->
  storebytes m o mv2 = Some m0 ->
  length mv1 = length mv2 ->
  storebytes m0 o mv1 = Some m1.
Proof.
  unfold storebytes. simpl; intros.
  rewrite H1 in *.
  destruct (range_perm_dec m _ _); inv H. inv H0.
  rewrite pred_dec_true; unfold range_perm in *.
  +rewrite setN_same; auto.
   repeat rewrite encode_val_length; auto.
   apply Nat2Z.inj_le. rewrite nat_of_Z_eq; omega.
  +rewrite setN_length; auto.
   apply Nat2Z.inj_le.
   rewrite Nat2Z.inj_add, nat_of_Z_eq; simpl; try omega.
Qed.

Section STOREBYTES.

Variable m1: mvl.
Variable ofs: Z.
Variable bytes: mvl.
Variable m2: mvl.
Hypothesis STORE: storebytes m1 ofs bytes = Some m2.

Theorem storebytes_length: length m1 = length m2.
Proof.
  unfold storebytes in STORE.
  remember (range_perm_dec m1 ofs (ofs + Z.of_nat (length bytes))).
  destruct s; inv STORE. destruct r as [? [? ?]]. clear Heqs.
  rewrite setN_length; auto.
   apply Z2Nat.inj_le in l; try omega. rewrite Z2Nat.inj_add in l; try omega.
    repeat rewrite Nat2Z.id in l at 1; auto.
Qed.

Theorem storebytes_range_perm:
  range_perm m2 ofs (ofs + Z.of_nat (length bytes)).
Proof.
  assert (length m1 = length m2).
    eapply storebytes_length; eauto.
  intros. unfold storebytes in STORE.
  destruct (range_perm_dec m1 ofs (ofs + Z.of_nat (length bytes))); inv STORE.
  destruct r as [? [? ?]]. split; [| split]; auto; try omega.
Qed.

Lemma storebytes_mem_contents:
   m2 = setN bytes (nat_of_Z ofs) m1.
Proof.
  unfold storebytes in STORE.
  destruct (range_perm_dec m1 ofs (ofs + Z_of_nat (length bytes)));
  inv STORE.
  auto.
Qed.

Theorem storebytes_valid_access_1:
  forall chunk' ofs',
  valid_access m1 chunk' ofs' ->
  valid_access m2 chunk' ofs'.
Proof.
  unfold valid_access, range_perm.
  intuition; rewrite <-storebytes_length; auto.
Qed.

Theorem storebytes_valid_access_2:
  forall chunk' ofs',
  valid_access m2 chunk' ofs' ->
  valid_access m1 chunk' ofs'.
Proof.
  unfold valid_access, range_perm.
  intuition; rewrite storebytes_length; auto.
Qed.

Theorem storebytes_range_perm_1:
  forall ofs' n,
  range_perm m1 ofs' (ofs' + n) ->
  range_perm m2 ofs' (ofs' + n).
Proof.
  unfold range_perm. intros.
  rewrite <-storebytes_length; auto.
Qed.

Theorem storebytes_range_perm_2:
  forall ofs' n,
  range_perm m2 ofs' (ofs' + n) ->
  range_perm m1 ofs' (ofs' + n).
Proof.
  unfold range_perm. intros.
  rewrite storebytes_length; auto.
Qed.

Theorem loadbytes_storebytes_same:
  loadbytes m2 ofs (Z_of_nat (length bytes)) = Some bytes.
Proof.
  intros. unfold storebytes in STORE. unfold loadbytes.
  destruct (range_perm_dec m1 ofs (ofs + Z_of_nat (length bytes)));
  try discriminate.
  rewrite pred_dec_true.
  decEq. inv STORE; simpl. rewrite nat_of_Z_of_nat.
  rewrite getN_setN_same; auto.
  unfold range_perm in *. destruct r. destruct H0.
  apply Z2Nat.inj_le in H0; try omega.
  rewrite nat_of_Z_plus, nat_of_Z_of_nat,nat_of_Z_of_nat in H0; try omega.
  apply storebytes_range_perm; auto.
Qed.

Theorem load_storebytes_other:
  forall chunk ofs',
  ofs' + size_chunk chunk <= ofs
  \/ ofs + Z_of_nat (length bytes) <= ofs' ->
  load chunk m2 ofs' = load chunk m1 ofs'.
Proof.
  intros. unfold load.
  assert(range_perm m2 ofs (ofs + Z.of_nat (length bytes))).
    eapply storebytes_range_perm ; eauto.
  apply storebytes_range_perm_2 in H0.
  destruct (valid_access_dec m1 chunk ofs').
  +rewrite pred_dec_true; auto.
   rewrite storebytes_mem_contents. decEq.
   destruct H0 as [? [? ?]]. destruct v as [[? [? ?]] ?].
   apply getN_setN_outside.
   replace (length bytes) with (nat_of_Z (Z_of_nat (length bytes))).
   unfold size_chunk_nat.
   -repeat rewrite <-nat_of_Z_plus; try omega.
    destruct H; [left | right];
    split; apply Nat2Z.inj_le; auto; repeat rewrite nat_of_Z_eq; try omega.
   -rewrite nat_of_Z_of_nat. auto.
   -apply storebytes_valid_access_1; auto.
  +rewrite pred_dec_false;auto.
   red; intros; elim n.
   apply storebytes_valid_access_2; auto.
Qed.

Theorem loadbytes_storebytes_other:
  forall ofs' len,
  ofs' + len <= ofs
  \/ ofs + Z_of_nat (length bytes) <= ofs' ->
  loadbytes m2 ofs' len = loadbytes m1 ofs' len.
Proof.
  intros. unfold loadbytes.
  destruct (zle len 0).
  +repeat rewrite pred_dec_false; auto.
   red; intros. red in H0. omega.
   red; intros. red in H0. omega.
  +assert(range_perm m2 ofs (ofs + Z.of_nat (length bytes))).
    eapply storebytes_range_perm ; eauto.
   apply storebytes_range_perm_2 in H0.
   destruct (range_perm_dec m1 ofs' (ofs' + len)).
   -rewrite pred_dec_true; auto.
    rewrite storebytes_mem_contents. decEq.
    unfold range_perm in *. apply getN_setN_outside.
    replace (length bytes) with (nat_of_Z (Z_of_nat (length bytes))).
    *destruct H; [left | right]; rewrite <-nat_of_Z_plus; try omega;
     split; apply Nat2Z.inj_le; auto; repeat rewrite nat_of_Z_eq; try omega.
    *rewrite nat_of_Z_of_nat. auto.
    *apply storebytes_range_perm_1; auto.
   -rewrite pred_dec_false;auto.
    red; intros; elim n.
    apply storebytes_range_perm_2; auto.
Qed.

Lemma storebytes_full:
  forall m m',
  length m = length m' ->
  0 < Z_of_nat (length m') ->
  Z.of_nat (length m) <= Int.max_signed ->
  storebytes m 0 m' = Some m'.
Proof.
  unfold storebytes. intros.
  rewrite pred_dec_true.
  +simpl. unfold setN, replace_map.
   simpl. rewrite skipn_bign; try omega.
   rewrite app_nil_r; auto.
  +unfold range_perm.
   simpl. split; try omega.
Qed.

End STOREBYTES.

Definition alloc(hi: Z) :=
  list_repeat (nat_of_Z hi) Undef.

Lemma alloc_range_perm:
  forall n, 0 < n <= Int.max_signed ->
  range_perm (alloc n) 0 n.
Proof.
  intros. red. unfold alloc.
  rewrite length_list_repeat.
  rewrite nat_of_Z_eq; try omega.
Qed.

Lemma is_undefs_repeat:
  forall n, is_undefs (list_repeat n Undef).
Proof.
  induction n; simpl.
  constructor 1.
  constructor 2; auto. constructor.
Qed.

Lemma is_undefs_alloc:
  forall n, is_undefs (alloc n).
Proof.
  unfold alloc. intros.
  apply is_undefs_repeat; auto.
Qed.

Lemma repeat_is_undefs:
  forall m, is_undefs m ->
  list_repeat (length m) Undef = m.
Proof.
  induction m; simpl; intros; inv H; auto.
  destruct a; simpl in *; try tauto.
  f_equal; auto.
Qed.

Lemma alloc_is_undefs:
  forall m,
  is_undefs m ->
  alloc (Z.of_nat (length m)) = m.
Proof.
  unfold alloc. intros m. rewrite nat_of_Z_of_nat.
  apply repeat_is_undefs; auto.
Qed.

Lemma length_alloc:
  forall n, length (alloc n) = (nat_of_Z n).
Proof.
  unfold alloc. intros. rewrite length_list_repeat; auto.
Qed.

Lemma firstn_list_repeat:
  forall (A: Type) m n (a: A),
  (n <= m)%nat ->
  firstn n (list_repeat m a) = list_repeat n a.
Proof.
  induction m, n; intros; auto.
  +inv H.
  +simpl. f_equal. rewrite IHm; auto.
   omega.
Qed.

Lemma list_repeat_app:
  forall (A: Type) m n (a: A), list_repeat (m + n) a = list_repeat m a ++ list_repeat n a.
Proof.
  induction m; simpl; intros; auto.
  f_equal; auto.
Qed.

Lemma alloc_app:
  forall m n, 0 <= m -> 0 <= n ->
  alloc (m + n) = alloc m ++ alloc n.
Proof.
  unfold alloc. intros.
  rewrite Z2Nat.inj_add; auto.
  apply list_repeat_app.
Qed.

Lemma skipn_list_repeat:
  forall (A: Type) m n (a: A),
  (n <= m)%nat ->
  skipn n (list_repeat m a) = list_repeat (m-n) a.
Proof.
  induction m, n; intros; auto.
  simpl. rewrite IHm; auto.
   omega.
Qed.

Lemma getN_alloc_eq:
  forall o s1 s2,
  o + s2 <= s1 ->
  0 <= o ->
  getN (nat_of_Z s2) (nat_of_Z o) (alloc s1) = alloc s2.
Proof.
  unfold alloc, getN, getn. intros.
  destruct (zle s2 0).
  +destruct s2; simpl in *; auto.
   generalize (Pos2Z.is_pos p). omega.
  +rewrite skipn_list_repeat; try omega.
   rewrite firstn_list_repeat; auto.
   rewrite <-Z2Nat.inj_sub; auto.
   apply Z2Nat.inj_le; try omega.
   apply Z2Nat.inj_le; omega.
Qed.

Lemma loadbytes_alloc:
  forall o s1 s2,
  o + s2 <= s1 <= Int.max_signed ->
  0 <= o -> 0 < s2 ->
  loadbytes (alloc s1) o s2 = Some (alloc s2).
Proof.
  unfold loadbytes,alloc. intros.
  rewrite pred_dec_true.
  +f_equal.
   apply getN_alloc_eq; try omega.
  +unfold range_perm. rewrite length_list_repeat.
   rewrite nat_of_Z_eq; try omega.
Qed.

Lemma decode_val_alloc_none:
  forall t chunk,
  access_mode t = By_value chunk ->
  decode_val chunk (alloc (sizeof t)) = None.
Proof.
  destruct t; simpl; intros; try congruence.
  +destruct i, s; inv H; simpl; auto.
  +destruct f; inv H; simpl; auto.
Qed.

Lemma mvl_array_alloc:
  forall n t,
  mvl_type false (alloc (sizeof t)) t ->
  mvl_array false (list_repeat (nat_of_Z (sizeof t) * n) Undef) t n.
Proof.
  induction n; intros.
  replace (nat_of_Z (sizeof t) * 0)%nat with 0%nat; try omega.
  simpl. constructor.
  change (S n) with (1 + n)%nat. rewrite mult_plus_distr_l.
  rewrite mult_1_r, list_repeat_app. econstructor; eauto.
Qed.

Lemma mvl_alloc_self:
  forall t, mvl_type false (alloc (sizeof t)) t.
Proof.
  intro t.
  apply (type_ind2
    (fun t => mvl_type false (alloc (sizeof t)) t)
    (fun f => forall fld pos,
     mvl_struct false (alloc (align (sizeof_struct f pos) (alignof_fields fld) - pos)) f fld pos)); intros;
  try (econstructor; simpl; eauto; fail).
 +econstructor; eauto. rewrite length_alloc.
  rewrite nat_of_Z_eq; auto. destruct i; simpl; omega.
 +econstructor; eauto. rewrite length_alloc.
  rewrite nat_of_Z_eq; auto. destruct f; simpl; omega.
 +generalize (zmax_l_le 0 z 0). intros.
  constructor 2; auto. generalize (sizeof_pos t0); intros.
  unfold alloc. simpl. rewrite Z2Nat.inj_mul; try omega.
  eapply mvl_array_alloc; eauto.
 +constructor 3; auto. simpl.
  generalize (H f 0). rewrite Zminus_0_r. auto.
 +simpl. constructor. apply is_undefs_alloc.
  rewrite length_alloc.
  rewrite nat_of_Z_eq; simpl; try omega.
  generalize (alignof_fields_pos fld). intros.
  generalize (align_le pos (alignof_fields fld) H).
  intros. omega.
 +remember (align _ _).
  assert (z - pos = (align pos (alignof t0) - pos) + (sizeof t0) + (z - (align pos (alignof t0) + sizeof t0))).
    subst. ring.
  generalize (sizeof_pos t0) (alignof_pos t0). intros.
  generalize (align_le pos (alignof t0) H3); intros.
  rewrite H1. repeat rewrite alloc_app; try omega.
  rewrite app_ass. econstructor; eauto.
  -apply is_undefs_alloc.
  -rewrite length_alloc. rewrite nat_of_Z_eq; try omega.
  -subst. apply H0.
  -subst. simpl. generalize (align pos (alignof t0) + sizeof t0). intros.
   generalize (sizeof_struct_incr f z). intros.
   generalize (alignof_fields_pos fld); intros.
   generalize (align_le (sizeof_struct f z) (alignof_fields fld) H6).
   intros. omega.
Qed.

Lemma loadbytes_offset_add_skipn:
  forall m o o1 n mv,
  0 <= o /\ 0 <= o1 ->
  loadbytes m (o + o1) n = Some mv ->
  loadbytes (skipn (nat_of_Z o1) m) o n = Some mv.
Proof.
  unfold loadbytes. intros.
  destruct (range_perm_dec m (o + o1) (o + o1 + n)); inv H0.
  rewrite pred_dec_true; eauto.
  +f_equal. rewrite nat_of_Z_plus; try omega.
   rewrite getN_app_skipn; auto.
  +apply range_perm_add_skipn; auto.
Qed.

Lemma storebytes_split_right:
  forall l1 l2 l3 l,
  storebytes (l1 ++ l2) (Z.of_nat (length l1)) l3 = Some l ->
  exists l', storebytes l2 0 l3 = Some l' /\ l = l1 ++ l'.
Proof.
  unfold storebytes. intros.
  destruct (range_perm_dec _ _ _) in H; inv H.
  rewrite nat_of_Z_of_nat.
  exists (setN l3 0 l2). rewrite pred_dec_true; simpl.
  +split; auto. unfold setN, replace_map. simpl.
   rewrite firstn_length_app1; try omega.
   rewrite skipn_length_app; try omega.
   rewrite <-firstn_bign; try omega. repeat f_equal. omega.
  +red in r. red. rewrite app_length, Nat2Z.inj_add in r. omega.
Qed.

Lemma storebytes_split_left:
  forall l l3 l',
  storebytes l 0 l3 = Some l' ->
  exists l1 l2, l = l1 ++ l2 /\ l' = l3 ++ l2.
Proof.
  unfold storebytes. intros.
  destruct (range_perm_dec _ _ _) in H; inv H.
  unfold setN, replace_map. red in r. simpl in *.
  exists (firstn (length l3) l), (skipn (length l3) l).
  split. rewrite firstn_skipn; auto.
  f_equal.
Qed.

Lemma store_split_right:
  forall chunk l1 l2 v l,
  store chunk (l1 ++ l2) (Z.of_nat (length l1)) v = Some l ->
  exists l', store chunk l2 0 v = Some l' /\ l = l1 ++ l'.
Proof.
  unfold store. intros.
  destruct (valid_access_dec _ _ _) in H; inv H.
  rewrite nat_of_Z_of_nat.
  exists (setN (encode_val chunk v) 0 l2). rewrite pred_dec_true; simpl.
  +split; auto. unfold setN, replace_map. simpl.
   rewrite firstn_length_app1; try omega.
   rewrite encode_val_length.
   rewrite skipn_length_app; try omega.
   rewrite <-firstn_bign; try omega. repeat f_equal. omega.
  +destruct v0 as [[? [? ?]] ?].
   rewrite app_length, Nat2Z.inj_add in *.
   unfold valid_access, range_perm.
   split. omega. red. exists 0. simpl. auto.
Qed.

Lemma store_split_left:
  forall chunk l l' v,
  store chunk l 0 v = Some l' ->
  exists l1 l2, store chunk l1 0 v = Some (encode_val chunk v)
    /\ l = l1 ++ l2
    /\ l' = encode_val chunk v ++ l2
    /\ Z_of_nat (length l1) = size_chunk chunk.
Proof.
  unfold store. intros.
  destruct (valid_access_dec _ _ _) in H; inv H.
  unfold setN, replace_map. destruct v0 as [[? [? ?]] ?]. simpl in *.
  exists (firstn (size_chunk_nat chunk) l), (skipn (size_chunk_nat chunk) l).
  assert(size_chunk_nat chunk <= length l)%nat.
    apply Nat2Z.inj_le; auto. unfold size_chunk_nat. rewrite nat_of_Z_eq; try omega.
  rewrite pred_dec_true; auto.
  rewrite encode_val_length. repeat (split; auto).
  +rewrite skipn_bign. rewrite app_nil_r; auto.
   rewrite firstn_length. rewrite min_l; try omega.
  +rewrite firstn_skipn; auto.
  +rewrite firstn_length.
   rewrite min_l; try omega.
   unfold size_chunk_nat. rewrite nat_of_Z_eq; try omega.
  +red. unfold range_perm. rewrite firstn_length.
   rewrite min_l; try omega. unfold size_chunk_nat.
   split. rewrite nat_of_Z_eq; try omega.
   red. exists 0. auto.
Qed.

(** value of Lustre match with value of Clight. *)

Inductive val_match(m: mem)(ty: type): val -> Values.val -> Prop :=
  | val_match_int: forall i,
     val_match m ty (Vint i) (Values.Vint i)
  | val_match_float: forall f,
     val_match m ty (Vfloat f) (Values.Vfloat f)
  | val_match_single: forall f,
     val_match m ty (Vsingle f) (Values.Vsingle f)
  | val_match_copy: forall m1 b ofs,
     Mem.loadbytes m b (Int.unsigned ofs) (Z_of_nat (length m1)) = Some m1 ->
     Int.unsigned ofs + Z_of_nat (length m1) <= Int.max_signed ->
     (alignof ty | Int.unsigned ofs) ->
     val_match m ty (Vmvl m1) (Values.Vptr b ofs).

Inductive vals_match(m: mem): list type -> list val -> list Values.val -> Prop :=
  | vals_match_nil:
    vals_match m nil nil nil
  | vals_match_cons: forall ty tys v vl vc vcl,
    val_match m ty v vc ->
    vals_match m tys vl vcl ->
    vals_match m (ty::tys) (v::vl) (vc::vcl).

Lemma decode_val_match:
  forall m ty chunk l v,
  decode_val chunk l = Some v ->
  val_match m ty v (Memdata.decode_val chunk l).
Proof.
  unfold decode_val, Memdata.decode_val. intros.
  destruct (proj_bytes l); try congruence.
  destruct chunk; inv H; try constructor 1; try constructor 2; try constructor 3; try constructor 4.
Qed.

Lemma load_decode_match:
  forall l v chunk ty m,
  load chunk l 0 = Some v ->
  length l = nat_of_Z (size_chunk chunk) ->
  val_match ty m v (Memdata.decode_val chunk l).
Proof.
  unfold load. intros.
  destruct (valid_access_dec l chunk 0); try congruence.
  unfold getN, getn, size_chunk_nat in H.
  rewrite <-H0 in *. simpl in *. rewrite <-firstn_bign in H; try omega.
  apply decode_val_match; auto.
Qed.

Lemma vals_match_length:
  forall m tys vl vcl,
  vals_match m tys vl vcl ->
  length tys = length vl /\ length vl = length vcl.
Proof.
  induction 1; simpl; omega.
Qed.

Lemma vals_match_app_inv_r:
  forall m tyl1 tyl2 vl vcl1 vcl2,
  vals_match m (tyl1 ++ tyl2) vl (vcl1 ++ vcl2) ->
  length tyl1 = length vcl1 ->
  exists vl1 vl2, vals_match m tyl1 vl1 vcl1
    /\ vals_match m tyl2 vl2 vcl2
    /\ vl = vl1 ++ vl2.
Proof.
  induction tyl1; destruct vcl1; simpl; intros; try omega.
  exists nil,vl. split; auto. constructor.
  inv H. destruct IHtyl1 with tyl2 vl0 vcl1 vcl2 as [vl1 [vl2 [? [? ?]]]]; auto.
  exists (v0::vl1), vl2. subst. repeat (split; auto). constructor 2; auto.
Qed.

Definition valof(v: val): Values.val :=
  match v with
  | Vint i => Values.Vint i
  | Vfloat f => Values.Vfloat f
  | Vsingle f => Values.Vsingle f
  | Vmvl _ => Values.Vundef
  end.
