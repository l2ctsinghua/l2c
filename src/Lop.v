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
Require Import Integers.
Require Import Floats.
Require Import Cop.
Require Import Ctypes.
Require Import Clop.
Require Import Cltypes.
Require Import Lvalues.
Require Import Ltypes.

(** The following [sem_] functions compute the result of an operator
  application.  The result depends on their run-time values.
  Unlike in C, automatic conversions are not performed. For instance,
  [e1 + e2] is undefined if [e1] is a float and [e2] an integer.
  The Lustre code must explicitly convert [e2] to a float. *)

Inductive binary_operationL : Type :=
  | Oadd : binary_operationL             (* addition (binary [+]) *)
  | Osub : binary_operationL             (* subtraction (binary [-]) *)
  | Omul : binary_operationL             (* multiplication (binary [*]) *)
  | Odivreal : binary_operationL         (* division real ([/]) *)
  | Odivint : binary_operationL          (* division integer ([div]) *)
  | Omod : binary_operationL             (* remainder ([mod]) *)
  | Oand : binary_operationL             (* and ([and]) *)
  | Oor : binary_operationL              (* or ([or]) *)
  | Oxor : binary_operationL             (* xor ([xor]) *)
  | Oeq: binary_operationL               (* comparison ([=]) *)
  | One: binary_operationL               (* comparison ([<>]) *)
  | Olt: binary_operationL               (* comparison ([<]) *)
  | Ogt: binary_operationL               (* comparison ([>]) *)
  | Ole: binary_operationL               (* comparison ([<=]) *)
  | Oge: binary_operationL.              (* comparison ([>=]) *)

Definition of_bool (b: bool): val := if b then Vtrue else Vfalse.

Function bool_val (v: val) (t: type) : option bool :=
  match v, t with
  | Vint n, Tint _ _ => Some (negb (Int.eq n Int.zero))
  | _, _ => None
  end.

Function sem_neg (v: val) (ty: type): option val :=
  match v, ty with
  | Vint n, Tint _ _ => Some (Vint (Int.neg n))
  | Vfloat f, Tfloat F64 => Some (Vfloat (Float.neg f))
  | Vsingle f, Tfloat F32 => Some (Vsingle (Float32.neg f))
  | _, _ => None
  end.

Function sem_notbool (v: val) (ty: type): option val :=
  match v, ty with
  | Vint n, Tint IBool _ => Some (of_bool (Int.eq n Int.zero))
  | _, _ => None
  end.

Function sem_add (v1 v2: val) (ty: type): option val :=
  match v1, v2, ty with
  | Vint n1, Vint n2, Tint _ _ => Some (Vint (Int.add n1 n2))
  | Vfloat f1, Vfloat f2, Tfloat F64 => Some (Vfloat (Float.add f1 f2))
  | Vsingle f1, Vsingle f2, Tfloat F32 => Some(Vsingle(Float32.add f1 f2))
  | _, _, _ => None
  end.

Function sem_sub (v1 v2: val) (ty: type): option val :=
  match v1, v2, ty with
  | Vint n1,  Vint n2, Tint _ _ => Some (Vint (Int.sub n1 n2))
  | Vfloat f1, Vfloat f2, Tfloat F64 => Some (Vfloat(Float.sub f1 f2))
  | Vsingle f1, Vsingle f2, Tfloat F32 => Some(Vsingle(Float32.sub f1 f2))
  | _, _, _=> None
  end.

Function sem_mul (v1 v2: val) (ty: type): option val :=
  match v1, v2, ty with
  | Vint n1, Vint n2, Tint _ _ => Some (Vint (Int.mul n1 n2))
  | Vfloat f1, Vfloat f2, Tfloat F64 => Some (Vfloat (Float.mul f1 f2))
  | Vsingle f1, Vsingle f2, Tfloat F32 => Some(Vsingle(Float32.mul f1 f2))
  | _, _, _ => None
  end.

Definition div_sign(n1 n2: int)(sz: intsize)(sg: signedness): option val :=
  match sz, sg with
  | I32, Unsigned =>
     if Int.eq n2 Int.zero
     then None else Some(Vint(Int.divu n1 n2))
  | _, _ =>
     if Int.eq n2 Int.zero
     || Int.eq n1 (Int.repr Int.min_signed) && Int.eq n2 Int.mone
     then None else Some(Vint(Int.divs n1 n2))
  end.

Function sem_div (v1 v2: val) (ty: type): option val :=
  match v1, v2, ty with
  | Vint n1, Vint n2, Tint sz sg => div_sign n1 n2 sz sg
  | Vfloat f1, Vfloat f2, Tfloat F64 => Some (Vfloat(Float.div f1 f2))
  | Vsingle f1, Vsingle f2, Tfloat F32 => Some(Vsingle(Float32.div f1 f2))
  | _, _, _ => None
  end.

Definition mod_sign(n1 n2: int)(sz: intsize)(sg: signedness): option val :=
  match sz, sg with
  | I32, Unsigned =>
     if Int.eq n2 Int.zero
     then None else Some(Vint(Int.modu n1 n2))
  | _, _ =>
     if Int.eq n2 Int.zero
     || Int.eq n1 (Int.repr Int.min_signed) && Int.eq n2 Int.mone
     then None else Some(Vint(Int.mods n1 n2))
  end.

Function sem_mod (v1 v2: val) (ty: type): option val :=
  match v1, v2, ty with
  | Vint n1, Vint n2, Tint sz sg => mod_sign n1 n2 sz sg
  | _, _, _=> None
  end.

Function sem_and (v1 v2: val) (ty: type): option val :=
  match v1, v2, ty with
  | Vint n1, Vint n2, Tint _ _ => Some (Vint (Int.and n1 n2))
  | _, _, _ => None
  end.

Function sem_or (v1 v2: val) (ty: type) : option val :=
  match v1, v2, ty with
  | Vint n1, Vint n2, Tint _ _ => Some (Vint (Int.or n1 n2))
  | _, _, _ => None
  end.

Function sem_xor (v1 v2: val) (ty: type): option val :=
  match v1, v2, ty with
  | Vint n1, Vint n2, Tint _ _ => Some (Vint (Int.xor n1 n2))
  | _, _, _ => None
  end.

Definition cmp_sign(op: comparison)(n1 n2: int)(sz: intsize)(sg: signedness): bool :=
  match sz, sg with
  | I32, Unsigned => Int.cmpu op n1 n2
  | _, _ => Int.cmp op n1 n2
  end.

Function sem_cmp (op: comparison) (v1 v2: val) (ty: type): option val :=
  match v1, v2, ty with
  | Vint n1, Vint n2, Tint sz sg => Some (of_bool (cmp_sign op n1 n2 sz sg))
  | Vfloat f1, Vfloat f2, Tfloat F64 => Some (of_bool (Float.cmp op f1 f2))
  | Vsingle f1, Vsingle f2, Tfloat F32 => Some(of_bool (Float32.cmp op f1 f2))
  | _, _, _ => None
  end.

Function classify_cast (tfrom tto: type) : classify_cast_cases :=
  match tto, tfrom with
  | Tint IBool _, Tfloat _ => cast_case_default
  | Tint sz2 si2, Tint sz1 si1 => cast_case_i2i sz2 si2
  | Tint sz2 si2, Tfloat F64 => cast_case_f2i sz2 si2
  | Tint sz2 si2, Tfloat F32 => cast_case_s2i sz2 si2
  | Tfloat F64, Tfloat F64 => cast_case_f2f
  | Tfloat F32, Tfloat F32 => cast_case_s2s
  | Tfloat F64, Tfloat F32 => cast_case_s2f
  | Tfloat F32, Tfloat F64 => cast_case_f2s
  | Tfloat F64, Tint sz1 si1 => cast_case_i2f si1
  | Tfloat F32, Tint sz1 si1 => cast_case_i2s si1
  | _, _ => cast_case_default
  end.

Definition sem_cast(v: val)(t1 t2: type): option val :=
  match classify_cast t1 t2 with
  | cast_case_i2i sz2 si2 =>
      match v with
      | Vint i => Some (Vint (cast_int_int sz2 si2 i))
      | _ => None
      end
  | cast_case_f2f =>
      match v with
      | Vfloat f => Some (Vfloat f)
      | _ => None
      end
  | cast_case_s2s =>
      match v with
      | Vsingle f => Some (Vsingle f)
      | _ => None
      end
  | cast_case_s2f =>
      match v with
      | Vsingle f => Some (Vfloat (Float.of_single f))
      | _ => None
      end
  | cast_case_f2s =>
      match v with
      | Vfloat f => Some (Vsingle (Float.to_single f))
      | _ => None
      end
  | cast_case_i2f si1 =>
      match v with
      | Vint i => Some (Vfloat (cast_int_float si1 i))
      | _ => None
      end
  | cast_case_i2s si1 =>
      match v with
      | Vint i => Some (Vsingle (cast_int_single si1 i))
      | _ => None
      end
  | cast_case_f2i sz2 si2 =>
      match v with
      | Vfloat f =>
          match cast_float_int si2 f with
          | Some i => Some (Vint (cast_int_int sz2 si2 i))
          | None => None
          end
      | _ => None
      end
  | cast_case_s2i sz2 si2 =>
      match v with
      | Vsingle f =>
          match cast_single_int si2 f with
          | Some i => Some (Vint (cast_int_int sz2 si2 i))
          | None => None
          end
      | _ => None
      end
  | _ => None
  end.

Definition sem_unary_operation (op: unary_operation) (v: val) (ty: type): option val :=
  match op with
  | Onotbool => sem_notbool v ty
  | Oneg => sem_neg v ty
  | Onotint => None
  | Oabsfloat => None
  end.

Inductive classify_binop_case: Type :=
  | binop_case_normal
  | binop_case_divint
  | binop_case_divreal.

Definition classify_binop(ty: type)(op: binary_operationL) :=
  match op with
  | Odivint =>
    match ty with
    | Tint I32 Signed => binop_case_normal
    | _ => binop_case_divint
    end
  | Odivreal =>
    match ty with
    | Tfloat _ => binop_case_normal
    | _ =>  binop_case_divreal
    end
  | _ => binop_case_normal
  end.

Definition sem_div_operation(op: binary_operationL)(v1 v2: val)(t tto: type): option val :=
  match classify_binop t op with
  | binop_case_normal => sem_div v1 v2 t
  | binop_case_divint =>
    match sem_div v1 v2 t with
    | Some v => sem_cast v t tto
    | None => None
    end
  | binop_case_divreal =>
    match (sem_cast v1 t (Tfloat F64)), (sem_cast v2 t (Tfloat F64)) with
    | Some v1', Some v2' => sem_div v1' v2' (Tfloat F64)
    | _, _ => None
    end
  end.

Definition sem_binary_operation (op: binary_operationL) (v1 v2: val)(t tto: type) : option val :=
  match op with
  | Oadd => sem_add v1 v2 t
  | Osub => sem_sub v1 v2 t
  | Omul => sem_mul v1 v2 t
  | Odivint => sem_div_operation Odivint v1 v2 t tto
  | Odivreal => sem_div_operation Odivreal v1 v2 t tto
  | Omod => sem_mod v1 v2 t
  | Oand => sem_and v1 v2 t
  | Oor => sem_or v1 v2 t
  | Oxor => sem_xor v1 v2 t
  | Oeq => sem_cmp Ceq v1 v2 t
  | One => sem_cmp Cne v1 v2 t
  | Olt => sem_cmp Clt v1 v2 t
  | Ogt => sem_cmp Cgt v1 v2 t
  | Ole => sem_cmp Cle v1 v2 t
  | Oge => sem_cmp Cge v1 v2 t
  end.

Fixpoint sem_fold_operation (op: binary_operationL)
    (ty: type) (v: val) (vl: list val): option val :=
  match vl with
  | nil => Some v
  | cons v1 vl1 =>
    match (sem_binary_operation op v v1 ty ty) with
    | Some v2 => sem_fold_operation op ty v2 vl1
    | None => None
    end
  end.

Lemma sem_unary_operation_not_mvl:
  forall op v1 t m,
  sem_unary_operation op v1 t = Some (Vmvl m) -> False.
Proof.
  destruct op; destruct v1; destruct t; intros; inv H.
  destruct i0; inv H1.
  destruct (Int.eq i Int.zero); inv H0.
  destruct f0; congruence.
  destruct f0; congruence.
Qed.

Lemma sem_div_not_mvl:
  forall v1 v2 t m,
  sem_div v1 v2 t = Some (Vmvl m) -> False.
Proof.
  intros. destruct v1,v2,t; inv H.
  destruct i1, s; intros; inv H1;
  destruct (Int.eq i0 Int.zero || Int.eq i (Int.repr Int.min_signed) && Int.eq i0 Int.mone); inv H0;
  destruct (Int.eq i0 Int.zero); inv H1.
  destruct f1; congruence.
  destruct f1; congruence.
Qed.

Lemma sem_cast_not_mvl:
  forall v1 t ty m,
  sem_cast v1 t ty = Some (Vmvl m) -> False.
Proof.
  unfold sem_cast. intros.
  destruct (classify_cast _ _); try congruence;
  destruct v1; try congruence.
  destruct (cast_float_int _ _); congruence.
  destruct (cast_single_int _ _); congruence.
Qed.

Lemma sem_div_operation_not_mvl:
  forall op v1 v2 t tto m,
  sem_div_operation op v1 v2 t tto = Some (Vmvl m) -> False.
Proof.
  unfold sem_div_operation. intros.
  destruct (classify_binop _ _); try congruence.
  +eapply sem_div_not_mvl; eauto.
  +destruct (sem_div _ _ _); try congruence.
   eapply sem_cast_not_mvl; eauto.
  +destruct (sem_cast v1 _ _); try congruence.
   destruct (sem_cast v2 _ _); try congruence.
   eapply sem_div_not_mvl; eauto.
Qed.

Lemma sem_cmp_not_mvl:
  forall op v1 v2 t m,
  sem_cmp op v1 v2 t = Some (Vmvl m) -> False.
Proof.
  destruct op, v1,v2,t; intros; inv H;
  try (destruct (cmp_sign _ _ _ _ _); inv H1; fail);
  destruct f1; try congruence;
  try destruct (Floats.Float.cmp _ _ _); inv H1;
  destruct (Floats.Float32.cmp _ _ _); inv H0.
Qed.

Lemma sem_binary_operation_not_mvl:
  forall op v1 v2 t tto m,
  sem_binary_operation op v1 v2 t tto = Some (Vmvl m) -> False.
Proof.
  destruct op; simpl; intros;
  try (destruct v1, v2, t; inv H;destruct f1; congruence; fail);
  try (eapply sem_cmp_not_mvl; eauto; fail).
  +eapply sem_div_operation_not_mvl; eauto.
  +eapply sem_div_operation_not_mvl; eauto.
  +destruct v1,v2,t; inv H.
   destruct i1; destruct s; inv H1;
    destruct (Int.eq i0 Int.zero || Int.eq i (Int.repr Int.min_signed) && Int.eq i0 Int.mone); inv H0;
    destruct (Int.eq i0 Int.zero); inv H1.
Qed.

Lemma sem_binary_operation_has_type:
  forall op v1 v2 ty tto v,
  sem_binary_operation op v1 v2 ty tto = Some v ->
  has_type v1 ty.
Proof.
  unfold has_type.
  destruct op, v1, v2, ty; simpl; intros; try inv H; auto;
  unfold sem_div_operation in *; simpl in *;
  try (destruct f1; inv H1; auto; fail);
  try (destruct i0,s; congruence; fail);
  try (destruct i,s; congruence; fail).
Qed.

Lemma sem_fold_operation_has_type:
  forall vl op ty v v1,
  sem_fold_operation op ty v vl = Some v1 ->
  has_type v1 ty ->
  has_type v ty.
Proof.
  destruct vl; simpl; intros.
  inv H. auto.
  destruct (sem_binary_operation _ _ _ _ _) eqn:?; try congruence.
  eapply sem_binary_operation_has_type; eauto.
Qed.

Lemma sem_binary_by_value:
  forall op v1 v2 v t1 t2 tto,
  sem_binary_operation op v1 v2 t1 tto = Some v ->
  has_type v t2 ->
  exists chunk, access_mode t2 = By_value chunk.
Proof.
  intros. destruct v,t2; try tauto; simpl; eauto.
  +destruct i0, s; eauto.
  +destruct f0; eauto.
  +destruct f0; eauto.
  +eapply sem_binary_operation_not_mvl in H; tauto.
  +eapply sem_binary_operation_not_mvl in H; tauto.
Qed.

Lemma sem_fold_operation_by_value:
  forall op v1 v2 v t l,
  sem_fold_operation op t v1 (v2::l)  = Some v ->
  has_type v t ->
  exists chunk, access_mode t = By_value chunk.
Proof.
  intros. inv H.
  destruct (sem_binary_operation _ _ _ _ _) eqn:?; try congruence.
  eapply sem_binary_by_value; eauto.
  eapply sem_fold_operation_has_type; eauto.
Qed.

Lemma sem_unary_by_value:
  forall op v1 v t1 t2,
  sem_unary_operation op v1 t1 = Some v ->
  has_type v t2 ->
  exists chunk, access_mode t2 = By_value chunk.
Proof.
  intros. destruct v,t2; try tauto; simpl; eauto.
  +destruct i0, s; eauto.
  +destruct f0; eauto.
  +destruct f0; eauto.
  +eapply sem_unary_operation_not_mvl in H; tauto.
  +eapply sem_unary_operation_not_mvl in H; tauto.
Qed.

Lemma sem_cast_by_value:
  forall v1 v t1 t2,
  sem_cast v1 t1 t2 = Some v ->
  exists chunk, access_mode t2 = By_value chunk.
Proof.
  unfold sem_cast, classify_cast. intros.
  destruct t1, t2; try congruence;
  try (destruct i; congruence; fail);
  try (destruct i0; congruence; fail);
  try (destruct f; congruence; fail); simpl.
  +destruct i0,s0; eauto.
  +destruct f; eauto.
  +destruct i,s; eauto.
  +destruct f0; eauto.
  +destruct f0; eauto.
Qed.
