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

(** Arithmetic and logical operators for the Compcert C and Clight languages *)

Require Import Coqlib.
Require Import AST.
Require Import Integers.
Require Import Floats.
Require Import Values.
Require Import Memory.
Require Import Cop.
Require Import Ctypes.
Require Import Cltypes.

(** * Type classification and semantics of operators. *)

(** Most C operators are overloaded (they apply to arguments of various
  types) and their semantics depend on the types of their arguments.
  The following [classify_*] functions take as arguments the types
  of the arguments of an operation.  They return enough information
  to resolve overloading for this operator applications, such as
  ``both arguments are floats'', or ``the first is a pointer
  and the second is an integer''.  This classification is used in the
  compiler (module [Cshmgen]) to resolve overloading statically.

  The [sem_*] functions below compute the result of an operator
  application.  Since operators are overloaded, the result depends
  both on the static types of the arguments and on their run-time values.
  The corresponding [classify_*] function is first called on the
  types of the arguments to resolve static overloading.  It is then
  followed by a case analysis on the values of the arguments. *)

(** ** Casts and truth values *)

Inductive classify_cast_cases : Type :=
  | cast_case_neutral                   (**r int|pointer -> int32|pointer *)
  | cast_case_i2i (sz2:intsize) (si2:signedness)   (**r int -> int *)
  | cast_case_f2f                                  (**r double -> double *)
  | cast_case_s2s                                  (**r single -> single *)
  | cast_case_f2s                                  (**r double -> single *)
  | cast_case_s2f                                  (**r single -> double *)
  | cast_case_i2f (si1: signedness)                (**r int -> double *)
  | cast_case_i2s (si1: signedness)                (**r int -> single *)
  | cast_case_f2i (sz2:intsize) (si2:signedness)   (**r double -> int *)
  | cast_case_s2i (sz2:intsize) (si2:signedness)   (**r single -> int *)
  | cast_case_l2l                       (**r long -> long *)
  | cast_case_i2l (si1: signedness)     (**r int -> long *)
  | cast_case_l2i (sz2: intsize) (si2: signedness) (**r long -> int *)
  | cast_case_l2f (si1: signedness)                (**r long -> double *)
  | cast_case_l2s (si1: signedness)                (**r long -> single *)
  | cast_case_f2l (si2:signedness)                 (**r double -> long *)
  | cast_case_s2l (si2:signedness)                 (**r single -> long *)
  | cast_case_f2bool                               (**r double -> bool *)
  | cast_case_s2bool                               (**r single -> bool *)
  | cast_case_l2bool                               (**r long -> bool *)
  | cast_case_p2bool                               (**r pointer -> bool *)
  | cast_case_struct (id1: ident) (fld1: fieldlist) (id2: ident) (fld2: fieldlist) (**r struct -> struct *)
  | cast_case_union (id1: ident) (fld1: fieldlist) (id2: ident) (fld2: fieldlist) (**r union -> union *)
  | cast_case_void                                 (**r any -> void *)
  | cast_case_default.

Definition classify_cast (tfrom tto: type) : classify_cast_cases :=
  match tto, tfrom with
  | Tint I32 si2 , (Tint _ _ | Tpointer _ | Tarray _ _ _ | Tfunction _ _ _) => cast_case_neutral
  | Tint IBool _, Tfloat F64 => cast_case_f2bool
  | Tint IBool _, Tfloat F32 => cast_case_s2bool
  | Tint IBool _, (Tpointer _ | Tarray _ _ _ | Tfunction _ _ _) => cast_case_p2bool
  | Tint sz2 si2, Tint sz1 si1 => cast_case_i2i sz2 si2
  | Tint sz2 si2, Tfloat F64 => cast_case_f2i sz2 si2
  | Tint sz2 si2, Tfloat F32 => cast_case_s2i sz2 si2
  | Tfloat F64, Tfloat F64 => cast_case_f2f
  | Tfloat F32, Tfloat F32 => cast_case_s2s
  | Tfloat F64, Tfloat F32 => cast_case_s2f
  | Tfloat F32, Tfloat F64 => cast_case_f2s
  | Tfloat F64, Tint sz1 si1 => cast_case_i2f si1
  | Tfloat F32, Tint sz1 si1 => cast_case_i2s si1
  | Tpointer _ , (Tint _ _ | Tpointer _ | Tarray _ _ _ | Tfunction _ _ _) => cast_case_neutral
  | Tstruct id2 fld2, Tstruct id1 fld1 => cast_case_struct id1 fld1 id2 fld2
  | Tvoid, _ => cast_case_void
  | _, _ => cast_case_default
  end.

(** Semantics of casts.  [sem_cast v1 t1 t2 = Some v2] if value [v1],
  viewed with static type [t1], can be converted  to type [t2],
  resulting in value [v2].  *)

Definition sem_cast (v: val) (t1 t2: type) : option val :=
  match classify_cast t1 t2 with
  | cast_case_neutral =>
      match v with
      | Vint _ | Vptr _ _ => Some v
      | _ => None
      end
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
  | cast_case_f2bool =>
      match v with
      | Vfloat f =>
          Some(Vint(if Float.cmp Ceq f Float.zero then Int.zero else Int.one))
      | _ => None
      end
  | cast_case_s2bool =>
      match v with
      | Vsingle f =>
          Some(Vint(if Float32.cmp Ceq f Float32.zero then Int.zero else Int.one))
      | _ => None
      end
  | cast_case_p2bool =>
      match v with
      | Vint i => Some (Vint (cast_int_int IBool Signed i))
      | Vptr _ _ => Some (Vint Int.one)
      | _ => None
      end
  | cast_case_l2l =>
      match v with
      | Vlong n => Some (Vlong n)
      | _ => None
      end
  | cast_case_i2l si =>
      match v with
      | Vint n => Some(Vlong (cast_int_long si n))
      | _ => None
      end
  | cast_case_l2i sz si =>
      match v with
      | Vlong n => Some(Vint (cast_int_int sz si (Int.repr (Int64.unsigned n))))
      | _ => None
      end
  | cast_case_l2bool =>
      match v with
      | Vlong n =>
          Some(Vint(if Int64.eq n Int64.zero then Int.zero else Int.one))
      | _ => None
      end
  | cast_case_l2f si1 =>
      match v with
      | Vlong i => Some (Vfloat (cast_long_float si1 i))
      | _ => None
      end
  | cast_case_l2s si1 =>
      match v with
      | Vlong i => Some (Vsingle (cast_long_single si1 i))
      | _ => None
      end
  | cast_case_f2l si2 =>
      match v with
      | Vfloat f =>
          match cast_float_long si2 f with
          | Some i => Some (Vlong i)
          | None => None
          end
      | _ => None
      end
  | cast_case_s2l si2 =>
      match v with
      | Vsingle f =>
          match cast_single_long si2 f with
          | Some i => Some (Vlong i)
          | None => None
          end
      | _ => None
      end
  | cast_case_struct id1 fld1 id2 fld2 =>
      match v with
      | Vptr b ofs =>
          if ident_eq id1 id2 && fieldlist_eq fld1 fld2 then Some v else None
      | _ => None
      end
  | cast_case_union id1 fld1 id2 fld2 =>
      match v with
      | Vptr b ofs =>
          if ident_eq id1 id2 && fieldlist_eq fld1 fld2 then Some v else None
      | _ => None
      end
  | cast_case_void =>
      Some v
  | cast_case_default =>
      None
  end.

(** The following describes types that can be interpreted as a boolean:
  integers, floats, pointers.  It is used for the semantics of
  the [!] and [?] operators, as well as the [if], [while],
  and [for] statements. *)

Definition classify_bool (ty: type) : classify_bool_cases :=
  match typeconv ty with
  | Tint _ _ => bool_case_i
  | Tpointer _ => bool_case_p
  | Tfloat F64 => bool_case_f
  | Tfloat F32 => bool_case_s
  | _ => bool_default
  end.

(** Interpretation of values as truth values.
  Non-zero integers, non-zero floats and non-null pointers are
  considered as true.  The integer zero (which also represents
  the null pointer) and the float 0.0 are false. *)

Definition bool_val (v: val) (t: type) : option bool :=
  match classify_bool t with
  | bool_case_i =>
      match v with
      | Vint n => Some (negb (Int.eq n Int.zero))
      | _ => None
      end
  | bool_case_f =>
      match v with
      | Vfloat f => Some (negb (Float.cmp Ceq f Float.zero))
      | _ => None
      end
  | bool_case_s =>
      match v with
      | Vsingle f => Some (negb (Float32.cmp Ceq f Float32.zero))
      | _ => None
      end
  | bool_case_p =>
      match v with
      | Vint n => Some (negb (Int.eq n Int.zero))
      | Vptr b ofs => Some true
      | _ => None
      end
  | bool_case_l =>
      match v with
      | Vlong n => Some (negb (Int64.eq n Int64.zero))
      | _ => None
      end
  | bool_default => None
  end.


(** ** Unary operators *)

(** *** Boolean negation *)

Definition sem_notbool (v: val) (ty: type) : option val :=
  match classify_bool ty with
  | bool_case_i =>
      match v with
      | Vint n => Some (Val.of_bool (Int.eq n Int.zero))
      | _ => None
      end
  | bool_case_f =>
      match v with
      | Vfloat f => Some (Val.of_bool (Float.cmp Ceq f Float.zero))
      | _ => None
      end
  | bool_case_s =>
      match v with
      | Vsingle f => Some (Val.of_bool (Float32.cmp Ceq f Float32.zero))
      | _ => None
      end
  | bool_case_p =>
      match v with
      | Vint n => Some (Val.of_bool (Int.eq n Int.zero))
      | Vptr _ _ => Some Vfalse
      | _ => None
      end
  | bool_case_l =>
      match v with
      | Vlong n => Some (Val.of_bool (Int64.eq n Int64.zero))
      | _ => None
      end
  | bool_default => None
  end.

(** *** Opposite and absolute value *)

Definition classify_neg (ty: type) : classify_neg_cases :=
  match ty with
  | Tint I32 Unsigned => neg_case_i Unsigned
  | Tint _ _ => neg_case_i Signed
  | Tfloat F64 => neg_case_f
  | Tfloat F32 => neg_case_s
  | _ => neg_default
  end.

Definition sem_neg (v: val) (ty: type) : option val :=
  match classify_neg ty with
  | neg_case_i sg =>
      match v with
      | Vint n => Some (Vint (Int.neg n))
      | _ => None
      end
  | neg_case_f =>
      match v with
      | Vfloat f => Some (Vfloat (Float.neg f))
      | _ => None
      end
  | neg_case_s =>
      match v with
      | Vsingle f => Some (Vsingle (Float32.neg f))
      | _ => None
      end
  | neg_case_l sg =>
      match v with
      | Vlong n => Some (Vlong (Int64.neg n))
      | _ => None
      end
  | neg_default => None
  end.

Definition sem_absfloat (v: val) (ty: type) : option val :=
  match classify_neg ty with
  | neg_case_i sg =>
      match v with
      | Vint n => Some (Vfloat (Float.abs (cast_int_float sg n)))
      | _ => None
      end
  | neg_case_f =>
      match v with
      | Vfloat f => Some (Vfloat (Float.abs f))
      | _ => None
      end
  | neg_case_s =>
      match v with
      | Vsingle f => Some (Vfloat (Float.abs (Float.of_single f)))
      | _ => None
      end
  | neg_case_l sg =>
      match v with
      | Vlong n => Some (Vfloat (Float.abs (cast_long_float sg n)))
      | _ => None
      end
  | neg_default => None
  end.

(** *** Bitwise complement *)

Definition classify_notint (ty: type) : classify_notint_cases :=
  match ty with
  | Tint I32 Unsigned => notint_case_i Unsigned
  | Tint _ _ => notint_case_i Signed
  | _ => notint_default
  end.

Definition sem_notint (v: val) (ty: type): option val :=
  match classify_notint ty with
  | notint_case_i sg =>
      match v with
      | Vint n => Some (Vint (Int.not n))
      | _ => None
      end
  | notint_case_l sg =>
      match v with
      | Vlong n => Some (Vlong (Int64.not n))
      | _ => None
      end
  | notint_default => None
  end.

(** ** Binary operators *)

(** For binary operations, the "usual binary conversions" consist in
- determining the type at which the operation is to be performed
  (a form of least upper bound of the types of the two arguments);
- casting the two arguments to this common type;
- performing the operation at that type.
*)

Inductive binarith_cases: Type :=
  | bin_case_i (s: signedness)         (**r at int type *)
  | bin_case_f                         (**r at double float type *)
  | bin_case_s                         (**r at single float type *)
  | bin_default.                       (**r error *)

Definition classify_binarith (ty1: type) (ty2: type) : binarith_cases :=
  match ty1, ty2 with
  | Tint I32 Unsigned, Tint _ _ => bin_case_i Unsigned
  | Tint _ _, Tint I32 Unsigned => bin_case_i Unsigned
  | Tint _ _, Tint _ _ => bin_case_i Signed
  | Tfloat F32, Tfloat F32 => bin_case_s
  | Tfloat _, Tfloat _ => bin_case_f
  | Tfloat F64, Tint _ _  => bin_case_f
  | Tint _ _ , Tfloat F64 => bin_case_f
  | Tfloat F32, Tint _ _  => bin_case_s
  | Tint _ _ , Tfloat F32 => bin_case_s
  | _, _ => bin_default
  end.

(** The static type of the result. Both arguments are converted to this type
    before the actual computation. *)

Definition binarith_type (c: binarith_cases) : type :=
  match c with
  | bin_case_i sg => Tint I32 sg
  | bin_case_f    => Tfloat F64
  | bin_case_s    => Tfloat F32
  | bin_default   => Tvoid
  end.

Definition sem_binarith
    (sem_int: signedness -> int -> int -> option val)
    (sem_long: signedness -> int64 -> int64 -> option val)
    (sem_float: float -> float -> option val)
    (sem_single: float32 -> float32 -> option val)
    (v1: val) (t1: type) (v2: val) (t2: type) : option val :=
  let c := classify_binarith t1 t2 in
  let t := binarith_type c in
  match sem_cast v1 t1 t with
  | None => None
  | Some v1' =>
  match sem_cast v2 t2 t with
  | None => None
  | Some v2' =>
  match c with
  | bin_case_i sg =>
      match v1', v2' with
      | Vint n1, Vint n2 => sem_int sg n1 n2
      | _,  _ => None
      end
  | bin_case_f =>
      match v1', v2' with
      | Vfloat n1, Vfloat n2 => sem_float n1 n2
      | _,  _ => None
      end
  | bin_case_s =>
      match v1', v2' with
      | Vsingle n1, Vsingle n2 => sem_single n1 n2
      | _,  _ => None
      end
  | bin_default => None
  end end end.

(** *** Addition *)

Inductive classify_add_cases : Type :=
  | add_case_pi(ty: type)     (**r pointer, int *)
  | add_case_ip(ty: type)     (**r int, pointer *)
  | add_default.                       (**r numerical type, numerical type *)

Definition classify_add (ty1: type) (ty2: type) :=
  match typeconv ty1, typeconv ty2 with
  | Tpointer ty, Tint _ _ => add_case_pi ty
  | Tint _ _, Tpointer ty => add_case_ip ty
  | _, _ => add_default
  end.

Definition sem_add (v1:val) (t1:type) (v2: val) (t2:type) : option val :=
  match classify_add t1 t2 with
  | add_case_pi ty =>                 (**r pointer plus integer *)
      match v1,v2 with
      | Vptr b1 ofs1, Vint n2 =>
        Some (Vptr b1 (Int.add ofs1 (Int.mul (Int.repr (sizeof ty)) n2)))
      | _,  _ => None
      end
  | add_case_ip ty =>                 (**r integer plus pointer *)
      match v1,v2 with
      | Vint n1, Vptr b2 ofs2 =>
        Some (Vptr b2 (Int.add ofs2 (Int.mul (Int.repr (sizeof ty)) n1)))
      | _,  _ => None
      end
  | add_default =>
      sem_binarith
        (fun sg n1 n2 => Some(Vint(Int.add n1 n2)))
        (fun sg n1 n2 => Some(Vlong(Int64.add n1 n2)))
        (fun n1 n2 => Some(Vfloat(Float.add n1 n2)))
        (fun n1 n2 => Some(Vsingle(Float32.add n1 n2)))
        v1 t1 v2 t2
  end.

(** *** Subtraction *)

Inductive classify_sub_cases : Type :=
  | sub_case_pi(ty: type)               (**r pointer, int *)
  | sub_case_pp(ty: type)               (**r pointer, pointer *)
  | sub_default.                        (**r numerical type, numerical type *)

Definition classify_sub (ty1: type) (ty2: type) :=
  match typeconv ty1, typeconv ty2 with
  | Tpointer ty, Tint _ _ => sub_case_pi ty
  | Tpointer ty, Tpointer _ => sub_case_pp ty
  | _, _ => sub_default
  end.

Definition sem_sub (v1:val) (t1:type) (v2: val) (t2:type) : option val :=
  match classify_sub t1 t2 with
  | sub_case_pi ty =>            (**r pointer minus integer *)
      match v1,v2 with
      | Vptr b1 ofs1, Vint n2 =>
          Some (Vptr b1 (Int.sub ofs1 (Int.mul (Int.repr (sizeof ty)) n2)))
      | _,  _ => None
      end
  | sub_case_pp ty =>          (**r pointer minus pointer *)
      match v1,v2 with
      | Vptr b1 ofs1, Vptr b2 ofs2 =>
          if eq_block b1 b2 then
            if Int.eq (Int.repr (sizeof ty)) Int.zero then None
            else Some (Vint (Int.divu (Int.sub ofs1 ofs2) (Int.repr (sizeof ty))))
          else None
      | _, _ => None
      end
  | sub_default =>
      sem_binarith
        (fun sg n1 n2 => Some(Vint(Int.sub n1 n2)))
        (fun sg n1 n2 => Some(Vlong(Int64.sub n1 n2)))
        (fun n1 n2 => Some(Vfloat(Float.sub n1 n2)))
        (fun n1 n2 => Some(Vsingle(Float32.sub n1 n2)))
        v1 t1 v2 t2
  end.

(** *** Multiplication, division, modulus *)

Definition sem_mul (v1:val) (t1:type) (v2: val) (t2:type) : option val :=
  sem_binarith
    (fun sg n1 n2 => Some(Vint(Int.mul n1 n2)))
    (fun sg n1 n2 => Some(Vlong(Int64.mul n1 n2)))
    (fun n1 n2 => Some(Vfloat(Float.mul n1 n2)))
    (fun n1 n2 => Some(Vsingle(Float32.mul n1 n2)))
    v1 t1 v2 t2.

Definition sem_div (v1:val) (t1:type) (v2: val) (t2:type) : option val :=
  sem_binarith
    (fun sg n1 n2 =>
      match sg with
      | Signed =>
          if Int.eq n2 Int.zero
          || Int.eq n1 (Int.repr Int.min_signed) && Int.eq n2 Int.mone
          then None else Some(Vint(Int.divs n1 n2))
      | Unsigned =>
          if Int.eq n2 Int.zero
          then None else Some(Vint(Int.divu n1 n2))
      end)
    (fun sg n1 n2 =>
      match sg with
      | Signed =>
          if Int64.eq n2 Int64.zero
          || Int64.eq n1 (Int64.repr Int64.min_signed) && Int64.eq n2 Int64.mone
          then None else Some(Vlong(Int64.divs n1 n2))
      | Unsigned =>
          if Int64.eq n2 Int64.zero
          then None else Some(Vlong(Int64.divu n1 n2))
      end)
    (fun n1 n2 => Some(Vfloat(Float.div n1 n2)))
    (fun n1 n2 => Some(Vsingle(Float32.div n1 n2)))
    v1 t1 v2 t2.

Definition sem_mod (v1:val) (t1:type) (v2: val) (t2:type) : option val :=
  sem_binarith
    (fun sg n1 n2 =>
      match sg with
      | Signed =>
          if Int.eq n2 Int.zero
          || Int.eq n1 (Int.repr Int.min_signed) && Int.eq n2 Int.mone
          then None else Some(Vint(Int.mods n1 n2))
      | Unsigned =>
          if Int.eq n2 Int.zero
          then None else Some(Vint(Int.modu n1 n2))
      end)
    (fun sg n1 n2 =>
      match sg with
      | Signed =>
          if Int64.eq n2 Int64.zero
          || Int64.eq n1 (Int64.repr Int64.min_signed) && Int64.eq n2 Int64.mone
          then None else Some(Vlong(Int64.mods n1 n2))
      | Unsigned =>
          if Int64.eq n2 Int64.zero
          then None else Some(Vlong(Int64.modu n1 n2))
      end)
    (fun n1 n2 => None)
    (fun n1 n2 => None)
    v1 t1 v2 t2.

Definition sem_and (v1:val) (t1:type) (v2: val) (t2:type) : option val :=
  sem_binarith
    (fun sg n1 n2 => Some(Vint(Int.and n1 n2)))
    (fun sg n1 n2 => Some(Vlong(Int64.and n1 n2)))
    (fun n1 n2 => None)
    (fun n1 n2 => None)
    v1 t1 v2 t2.

Definition sem_or (v1:val) (t1:type) (v2: val) (t2:type) : option val :=
  sem_binarith
    (fun sg n1 n2 => Some(Vint(Int.or n1 n2)))
    (fun sg n1 n2 => Some(Vlong(Int64.or n1 n2)))
    (fun n1 n2 => None)
    (fun n1 n2 => None)
    v1 t1 v2 t2.

Definition sem_xor (v1:val) (t1:type) (v2: val) (t2:type) : option val :=
  sem_binarith
    (fun sg n1 n2 => Some(Vint(Int.xor n1 n2)))
    (fun sg n1 n2 => Some(Vlong(Int64.xor n1 n2)))
    (fun n1 n2 => None)
    (fun n1 n2 => None)
    v1 t1 v2 t2.

(** *** Shifts *)

(** Shifts do not perform the usual binary conversions.  Instead,
  each argument is converted independently, and the signedness
  of the result is always that of the first argument. *)

Definition classify_shift (ty1: type) (ty2: type) :=
  match typeconv ty1, typeconv ty2 with
  | Tint I32 Unsigned, Tint _ _ => shift_case_ii Unsigned
  | Tint _ _, Tint _ _ => shift_case_ii Signed
  | _,_  => shift_default
  end.

Definition sem_shift
    (sem_int: signedness -> int -> int -> int)
    (sem_long: signedness -> int64 -> int64 -> int64)
    (v1: val) (t1: type) (v2: val) (t2: type) : option val :=
  match classify_shift t1 t2 with
  | shift_case_ii sg =>
      match v1, v2 with
      | Vint n1, Vint n2 =>
          if Int.ltu n2 Int.iwordsize
          then Some(Vint(sem_int sg n1 n2)) else None
      | _, _ => None
      end
  | shift_case_il sg =>
      match v1, v2 with
      | Vint n1, Vlong n2 =>
          if Int64.ltu n2 (Int64.repr 32)
          then Some(Vint(sem_int sg n1 (Int64.loword n2))) else None
      | _, _ => None
      end
  | shift_case_li sg =>
      match v1, v2 with
      | Vlong n1, Vint n2 =>
          if Int.ltu n2 Int64.iwordsize'
          then Some(Vlong(sem_long sg n1 (Int64.repr (Int.unsigned n2)))) else None
      | _, _ => None
      end
  | shift_case_ll sg =>
      match v1, v2 with
      | Vlong n1, Vlong n2 =>
          if Int64.ltu n2 Int64.iwordsize
          then Some(Vlong(sem_long sg n1 n2)) else None
      | _, _ => None
      end
  | shift_default => None
  end.

Definition sem_shl (v1:val) (t1:type) (v2: val) (t2:type) : option val :=
  sem_shift
    (fun sg n1 n2 => Int.shl n1 n2)
    (fun sg n1 n2 => Int64.shl n1 n2)
    v1 t1 v2 t2.

Definition sem_shr (v1:val) (t1:type) (v2: val) (t2:type) : option val :=
  sem_shift
    (fun sg n1 n2 => match sg with Signed => Int.shr n1 n2 | Unsigned => Int.shru n1 n2 end)
    (fun sg n1 n2 => match sg with Signed => Int64.shr n1 n2 | Unsigned => Int64.shru n1 n2 end)
    v1 t1 v2 t2.

(** *** Comparisons *)

Definition classify_cmp (ty1: type) (ty2: type) :=
  match typeconv ty1, typeconv ty2 with
  | Tpointer _ , Tpointer _ => cmp_case_pp
  | Tpointer _ , Tint _ _ => cmp_case_pp
  | Tint _ _, Tpointer _ => cmp_case_pp
  | _, _ => cmp_default
  end.

Definition sem_cmp (c:comparison)
                  (v1: val) (t1: type) (v2: val) (t2: type)
                  (m: mem): option val :=
  match classify_cmp t1 t2 with
  | cmp_case_pp =>
      option_map Val.of_bool (Val.cmpu_bool (Mem.valid_pointer m) c v1 v2)
  | cmp_case_pl =>
      match v2 with
      | Vlong n2 =>
          let n2 := Int.repr (Int64.unsigned n2) in
          option_map Val.of_bool (Val.cmpu_bool (Mem.valid_pointer m) c v1 (Vint n2))
      | _ => None
      end
  | cmp_case_lp =>
      match v1 with
      | Vlong n1 =>
          let n1 := Int.repr (Int64.unsigned n1) in
          option_map Val.of_bool (Val.cmpu_bool (Mem.valid_pointer m) c (Vint n1) v2)
      | _ => None
      end
  | cmp_default =>
      sem_binarith
        (fun sg n1 n2 =>
            Some(Val.of_bool(match sg with Signed => Int.cmp c n1 n2 | Unsigned => Int.cmpu c n1 n2 end)))
        (fun sg n1 n2 =>
            Some(Val.of_bool(match sg with Signed => Int64.cmp c n1 n2 | Unsigned => Int64.cmpu c n1 n2 end)))
        (fun n1 n2 =>
            Some(Val.of_bool(Float.cmp c n1 n2)))
        (fun n1 n2 =>
            Some(Val.of_bool(Float32.cmp c n1 n2)))
        v1 t1 v2 t2
  end.

(** ** Function applications *)

Inductive classify_fun_cases : Type :=
  | fun_case_f (targs: typelist) (tres: type) (cc: calling_convention) (**r (pointer to) function *)
  | fun_default.

Definition classify_fun (ty: type) :=
  match ty with
  | Tfunction args res cc => fun_case_f args res cc
  | Tpointer (Tfunction args res cc) => fun_case_f args res cc
  | _ => fun_default
  end.

(** ** Argument of a [switch] statement *)

Definition classify_switch (ty: type) :=
  match ty with
  | Tint _ _ => switch_case_i
  | _ => switch_default
  end.

Definition sem_switch_arg (v: val) (ty: type): option Z :=
  match classify_switch ty with
  | switch_case_i =>
      match v with Vint n => Some(Int.unsigned n) | _ => None end
  | switch_case_l =>
      match v with Vlong n => Some(Int64.unsigned n) | _ => None end
  | switch_default =>
      None
  end.

(** * Combined semantics of unary and binary operators *)

Definition sem_unary_operation
            (op: unary_operation) (v: val) (ty: type): option val :=
  match op with
  | Onotbool => sem_notbool v ty
  | Onotint => sem_notint v ty
  | Oneg => sem_neg v ty
  | Oabsfloat => sem_absfloat v ty
  end.

Definition sem_binary_operation
    (op: binary_operation)
    (v1: val) (t1: type) (v2: val) (t2:type)
    (m: mem): option val :=
  match op with
  | Oadd => sem_add v1 t1 v2 t2
  | Osub => sem_sub v1 t1 v2 t2
  | Omul => sem_mul v1 t1 v2 t2
  | Omod => sem_mod v1 t1 v2 t2
  | Odiv => sem_div v1 t1 v2 t2
  | Oand => sem_and v1 t1 v2 t2
  | Oor  => sem_or v1 t1 v2 t2
  | Oxor  => sem_xor v1 t1 v2 t2
  | Oshl => sem_shl v1 t1 v2 t2
  | Oshr  => sem_shr v1 t1 v2 t2
  | Oeq => sem_cmp Ceq v1 t1 v2 t2 m
  | One => sem_cmp Cne v1 t1 v2 t2 m
  | Olt => sem_cmp Clt v1 t1 v2 t2 m
  | Ogt => sem_cmp Cgt v1 t1 v2 t2 m
  | Ole => sem_cmp Cle v1 t1 v2 t2 m
  | Oge => sem_cmp Cge v1 t1 v2 t2 m
  end.

Definition sem_incrdecr (id: incr_or_decr) (v: val) (ty: type) :=
  match id with
  | Incr => sem_add v ty (Vint Int.one) type_int32s
  | Decr => sem_sub v ty (Vint Int.one) type_int32s
  end.

Definition incrdecr_type (ty: type) :=
  match typeconv ty with
  | Tpointer ty => Tpointer ty
  | Tint sz sg => Tint sz sg
  | Tfloat sz => Tfloat sz
  | _ => Tvoid
  end.

(** * Some properties of operator semantics *)

(** This section collects some common-sense properties about the type
  classification and semantic functions above.  These properties are
  not used in the CompCert semantics preservation proofs, but increase
  confidence in the specification and its relation with the ISO C99 standard. *)

(** Relation between Boolean value and casting to [_Bool] type. *)

Lemma cast_bool_bool_val:
  forall v t,
  sem_cast v t (Tint IBool Signed) =
  match bool_val v t with None => None | Some b => Some(Val.of_bool b) end.
Proof.
  intros.
  assert (A: classify_bool t =
    match t with
    | Tint _ _ => bool_case_i
    | Tpointer _ | Tarray _ _ _ | Tfunction _ _ _ => bool_case_p
    | Tfloat F64 => bool_case_f
    | Tfloat F32 => bool_case_s
    | _ => bool_default
    end).
  {
    unfold classify_bool; destruct t; simpl; auto. destruct i; auto.
  }
  unfold bool_val. rewrite A. unfold sem_cast. destruct t; simpl; auto; destruct v; auto.
  destruct (Int.eq i0 Int.zero); auto.
  destruct f; auto.
  destruct f; auto.
  destruct f; auto.
  destruct f; auto.
  destruct (Float.cmp Ceq f0 Float.zero); auto.
  destruct f; auto.
  destruct (Float32.cmp Ceq f0 Float32.zero); auto.
  destruct f; auto.
  destruct (Int.eq i Int.zero); auto.
  destruct (Int.eq i0 Int.zero); auto.
  destruct (Int.eq i Int.zero); auto.
Qed.

(** Relation between Boolean value and Boolean negation. *)

Lemma notbool_bool_val:
  forall v t,
  sem_notbool v t =
  match bool_val v t with None => None | Some b => Some(Val.of_bool (negb b)) end.
Proof.
  intros. unfold sem_notbool, bool_val.
  destruct (classify_bool t); auto; destruct v; auto; rewrite negb_involutive; auto.
Qed.