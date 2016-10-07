(* *********************************************************************)
(*                                                                     *)
(*              The Compcert verified compiler                         *)
(*                                                                     *)
(*          Xavier Leroy, INRIA Paris-Rocquencourt                     *)
(*                                                                     *)
(*  Copyright Institut National de Recherche en Informatique et en     *)
(*  Automatique.  All rights reserved.  This file is distributed       *)
(*  under the terms of the INRIA Non-Commercial License Agreement.     *)
(*                                                                     *)
(* *********************************************************************)

(** Strength reduction for operators and conditions.
    This is the machine-dependent part of [Constprop]. *)

Require Import Coqlib.
Require Import Compopts.
Require Import AST.
Require Import Integers.
Require Import Floats.
Require Import Op.
Require Import Registers.
Require Import ValueDomain.

(** * Operator strength reduction *)

(** We now define auxiliary functions for strength reduction of
  operators and addressing modes: replacing an operator with a cheaper
  one if some of its arguments are statically known.  These are again
  large pattern-matchings expressed in indirect style. *)

(** Original definition:
<<
Nondetfunction cond_strength_reduction 
              (cond: condition) (args: list reg) (vl: list aval) :=
  match cond, args, vl with
  | Ccomp c, r1 :: r2 :: nil, I n1 :: v2 :: nil =>
      (Ccompimm (swap_comparison c) n1, r2 :: nil)
  | Ccomp c, r1 :: r2 :: nil, v1 :: I n2 :: nil =>
      (Ccompimm c n2, r1 :: nil)
  | Ccompu c, r1 :: r2 :: nil, I n1 :: v2 :: nil =>
      (Ccompuimm (swap_comparison c) n1, r2 :: nil)
  | Ccompu c, r1 :: r2 :: nil, v1 :: I n2 :: nil =>
      (Ccompuimm c n2, r1 :: nil)
  | _, _, _ => 
      (cond, args)
  end.
>>
*)

Inductive cond_strength_reduction_cases: forall (cond: condition) (args: list reg) (vl: list aval), Type :=
  | cond_strength_reduction_case1: forall c r1 r2 n1 v2, cond_strength_reduction_cases (Ccomp c) (r1 :: r2 :: nil) (I n1 :: v2 :: nil)
  | cond_strength_reduction_case2: forall c r1 r2 v1 n2, cond_strength_reduction_cases (Ccomp c) (r1 :: r2 :: nil) (v1 :: I n2 :: nil)
  | cond_strength_reduction_case3: forall c r1 r2 n1 v2, cond_strength_reduction_cases (Ccompu c) (r1 :: r2 :: nil) (I n1 :: v2 :: nil)
  | cond_strength_reduction_case4: forall c r1 r2 v1 n2, cond_strength_reduction_cases (Ccompu c) (r1 :: r2 :: nil) (v1 :: I n2 :: nil)
  | cond_strength_reduction_default: forall (cond: condition) (args: list reg) (vl: list aval), cond_strength_reduction_cases cond args vl.

Definition cond_strength_reduction_match (cond: condition) (args: list reg) (vl: list aval) :=
  match cond as zz1, args as zz2, vl as zz3 return cond_strength_reduction_cases zz1 zz2 zz3 with
  | Ccomp c, r1 :: r2 :: nil, I n1 :: v2 :: nil => cond_strength_reduction_case1 c r1 r2 n1 v2
  | Ccomp c, r1 :: r2 :: nil, v1 :: I n2 :: nil => cond_strength_reduction_case2 c r1 r2 v1 n2
  | Ccompu c, r1 :: r2 :: nil, I n1 :: v2 :: nil => cond_strength_reduction_case3 c r1 r2 n1 v2
  | Ccompu c, r1 :: r2 :: nil, v1 :: I n2 :: nil => cond_strength_reduction_case4 c r1 r2 v1 n2
  | cond, args, vl => cond_strength_reduction_default cond args vl
  end.

Definition cond_strength_reduction (cond: condition) (args: list reg) (vl: list aval) :=
  match cond_strength_reduction_match cond args vl with
  | cond_strength_reduction_case1 c r1 r2 n1 v2 => (* Ccomp c, r1 :: r2 :: nil, I n1 :: v2 :: nil *) 
      (Ccompimm (swap_comparison c) n1, r2 :: nil)
  | cond_strength_reduction_case2 c r1 r2 v1 n2 => (* Ccomp c, r1 :: r2 :: nil, v1 :: I n2 :: nil *) 
      (Ccompimm c n2, r1 :: nil)
  | cond_strength_reduction_case3 c r1 r2 n1 v2 => (* Ccompu c, r1 :: r2 :: nil, I n1 :: v2 :: nil *) 
      (Ccompuimm (swap_comparison c) n1, r2 :: nil)
  | cond_strength_reduction_case4 c r1 r2 v1 n2 => (* Ccompu c, r1 :: r2 :: nil, v1 :: I n2 :: nil *) 
      (Ccompuimm c n2, r1 :: nil)
  | cond_strength_reduction_default cond args vl =>
      (cond, args)
  end.


Definition make_cmp_base (c: condition) (args: list reg) (vl: list aval) :=
  let (c', args') := cond_strength_reduction c args vl in (Ocmp c', args').

(** Original definition:
<<
Nondetfunction make_cmp (c: condition) (args: list reg) (vl: list aval) :=
  match c, args, vl with
  | Ccompimm Ceq n, r1 :: nil, v1 :: nil =>
      if Int.eq_dec n Int.one && vincl v1 (Uns 1) then (Omove, r1 :: nil)
      else if Int.eq_dec n Int.zero && vincl v1 (Uns 1) then (Oxorimm Int.one, r1 :: nil)
      else make_cmp_base c args vl
  | Ccompimm Cne n, r1 :: nil, v1 :: nil =>
      if Int.eq_dec n Int.zero && vincl v1 (Uns 1) then (Omove, r1 :: nil)
      else if Int.eq_dec n Int.one && vincl v1 (Uns 1) then (Oxorimm Int.one, r1 :: nil)
      else make_cmp_base c args vl
  | _, _, _ =>
      make_cmp_base c args vl
  end.
>>
*)

Inductive make_cmp_cases: forall (c: condition) (args: list reg) (vl: list aval), Type :=
  | make_cmp_case1: forall n r1 v1, make_cmp_cases (Ccompimm Ceq n) (r1 :: nil) (v1 :: nil)
  | make_cmp_case2: forall n r1 v1, make_cmp_cases (Ccompimm Cne n) (r1 :: nil) (v1 :: nil)
  | make_cmp_default: forall (c: condition) (args: list reg) (vl: list aval), make_cmp_cases c args vl.

Definition make_cmp_match (c: condition) (args: list reg) (vl: list aval) :=
  match c as zz1, args as zz2, vl as zz3 return make_cmp_cases zz1 zz2 zz3 with
  | Ccompimm Ceq n, r1 :: nil, v1 :: nil => make_cmp_case1 n r1 v1
  | Ccompimm Cne n, r1 :: nil, v1 :: nil => make_cmp_case2 n r1 v1
  | c, args, vl => make_cmp_default c args vl
  end.

Definition make_cmp (c: condition) (args: list reg) (vl: list aval) :=
  match make_cmp_match c args vl with
  | make_cmp_case1 n r1 v1 => (* Ccompimm Ceq n, r1 :: nil, v1 :: nil *) 
      if Int.eq_dec n Int.one && vincl v1 (Uns 1) then (Omove, r1 :: nil) else if Int.eq_dec n Int.zero && vincl v1 (Uns 1) then (Oxorimm Int.one, r1 :: nil) else make_cmp_base c args vl
  | make_cmp_case2 n r1 v1 => (* Ccompimm Cne n, r1 :: nil, v1 :: nil *) 
      if Int.eq_dec n Int.zero && vincl v1 (Uns 1) then (Omove, r1 :: nil) else if Int.eq_dec n Int.one && vincl v1 (Uns 1) then (Oxorimm Int.one, r1 :: nil) else make_cmp_base c args vl
  | make_cmp_default c args vl =>
      make_cmp_base c args vl
  end.


(** Original definition:
<<
Nondetfunction addr_strength_reduction
                (addr: addressing) (args: list reg) (vl: list aval) :=
  match addr, args, vl with

  | Aindexed ofs, r1 :: nil, Ptr(Gl symb n) :: nil =>
      (Aglobal symb (Int.add n ofs), nil)
  | Aindexed ofs, r1 :: nil, Ptr(Stk n) :: nil =>
      (Ainstack (Int.add n ofs), nil)

  | Aindexed2 ofs, r1 :: r2 :: nil, Ptr(Gl symb n1) :: I n2 :: nil =>
      (Aglobal symb (Int.add (Int.add n1 n2) ofs), nil)
  | Aindexed2 ofs, r1 :: r2 :: nil, I n1 :: Ptr(Gl symb n2) :: nil =>
      (Aglobal symb (Int.add (Int.add n1 n2) ofs), nil)
  | Aindexed2 ofs, r1 :: r2 :: nil, Ptr(Stk n1) :: I n2 :: nil =>
      (Ainstack (Int.add (Int.add n1 n2) ofs), nil)
  | Aindexed2 ofs, r1 :: r2 :: nil, I n1 :: Ptr(Stk n2) :: nil =>
      (Ainstack (Int.add (Int.add n1 n2) ofs), nil)
  | Aindexed2 ofs, r1 :: r2 :: nil, Ptr(Gl symb n1) :: v2 :: nil =>
      (Abased symb (Int.add n1 ofs), r2 :: nil)
  | Aindexed2 ofs, r1 :: r2 :: nil, v1 :: Ptr(Gl symb n2) :: nil =>
      (Abased symb (Int.add n2 ofs), r1 :: nil)
  | Aindexed2 ofs, r1 :: r2 :: nil, I n1 :: v2 :: nil =>
      (Aindexed (Int.add n1 ofs), r2 :: nil)
  | Aindexed2 ofs, r1 :: r2 :: nil, v1 :: I n2 :: nil =>
      (Aindexed (Int.add n2 ofs), r1 :: nil)

  | Aindexed2scaled sc ofs, r1 :: r2 :: nil, Ptr(Gl symb n1) :: I n2 :: nil =>
      (Aglobal symb (Int.add (Int.add n1 (Int.mul n2 sc)) ofs), nil)
  | Aindexed2scaled sc ofs, r1 :: r2 :: nil, Ptr(Gl symb n1) :: v2 :: nil =>
      (Abasedscaled sc symb (Int.add n1 ofs), r2 :: nil)
  | Aindexed2scaled sc ofs, r1 :: r2 :: nil, v1 :: I n2 :: nil =>
      (Aindexed (Int.add (Int.mul n2 sc) ofs), r1 :: nil)

  | Abased id ofs, r1 :: nil, I n1 :: nil =>
      (Aglobal id (Int.add ofs n1), nil)

  | Abasedscaled sc id ofs, r1 :: nil, I n1 :: nil =>
      (Aglobal id (Int.add ofs (Int.mul sc n1)), nil)

  | _, _ =>
      (addr, args)
  end.
>>
*)

Inductive addr_strength_reduction_cases: forall (addr: addressing) (args: list reg) (vl: list aval), Type :=
  | addr_strength_reduction_case1: forall ofs r1 symb n, addr_strength_reduction_cases (Aindexed ofs) (r1 :: nil) (Ptr(Gl symb n) :: nil)
  | addr_strength_reduction_case2: forall ofs r1 n, addr_strength_reduction_cases (Aindexed ofs) (r1 :: nil) (Ptr(Stk n) :: nil)
  | addr_strength_reduction_case3: forall ofs r1 r2 symb n1 n2, addr_strength_reduction_cases (Aindexed2 ofs) (r1 :: r2 :: nil) (Ptr(Gl symb n1) :: I n2 :: nil)
  | addr_strength_reduction_case4: forall ofs r1 r2 n1 symb n2, addr_strength_reduction_cases (Aindexed2 ofs) (r1 :: r2 :: nil) (I n1 :: Ptr(Gl symb n2) :: nil)
  | addr_strength_reduction_case5: forall ofs r1 r2 n1 n2, addr_strength_reduction_cases (Aindexed2 ofs) (r1 :: r2 :: nil) (Ptr(Stk n1) :: I n2 :: nil)
  | addr_strength_reduction_case6: forall ofs r1 r2 n1 n2, addr_strength_reduction_cases (Aindexed2 ofs) (r1 :: r2 :: nil) (I n1 :: Ptr(Stk n2) :: nil)
  | addr_strength_reduction_case7: forall ofs r1 r2 symb n1 v2, addr_strength_reduction_cases (Aindexed2 ofs) (r1 :: r2 :: nil) (Ptr(Gl symb n1) :: v2 :: nil)
  | addr_strength_reduction_case8: forall ofs r1 r2 v1 symb n2, addr_strength_reduction_cases (Aindexed2 ofs) (r1 :: r2 :: nil) (v1 :: Ptr(Gl symb n2) :: nil)
  | addr_strength_reduction_case9: forall ofs r1 r2 n1 v2, addr_strength_reduction_cases (Aindexed2 ofs) (r1 :: r2 :: nil) (I n1 :: v2 :: nil)
  | addr_strength_reduction_case10: forall ofs r1 r2 v1 n2, addr_strength_reduction_cases (Aindexed2 ofs) (r1 :: r2 :: nil) (v1 :: I n2 :: nil)
  | addr_strength_reduction_case11: forall sc ofs r1 r2 symb n1 n2, addr_strength_reduction_cases (Aindexed2scaled sc ofs) (r1 :: r2 :: nil) (Ptr(Gl symb n1) :: I n2 :: nil)
  | addr_strength_reduction_case12: forall sc ofs r1 r2 symb n1 v2, addr_strength_reduction_cases (Aindexed2scaled sc ofs) (r1 :: r2 :: nil) (Ptr(Gl symb n1) :: v2 :: nil)
  | addr_strength_reduction_case13: forall sc ofs r1 r2 v1 n2, addr_strength_reduction_cases (Aindexed2scaled sc ofs) (r1 :: r2 :: nil) (v1 :: I n2 :: nil)
  | addr_strength_reduction_case14: forall id ofs r1 n1, addr_strength_reduction_cases (Abased id ofs) (r1 :: nil) (I n1 :: nil)
  | addr_strength_reduction_case15: forall sc id ofs r1 n1, addr_strength_reduction_cases (Abasedscaled sc id ofs) (r1 :: nil) (I n1 :: nil)
  | addr_strength_reduction_default: forall (addr: addressing) (args: list reg) (vl: list aval), addr_strength_reduction_cases addr args vl.

Definition addr_strength_reduction_match (addr: addressing) (args: list reg) (vl: list aval) :=
  match addr as zz1, args as zz2, vl as zz3 return addr_strength_reduction_cases zz1 zz2 zz3 with
  | Aindexed ofs, r1 :: nil, Ptr(Gl symb n) :: nil => addr_strength_reduction_case1 ofs r1 symb n
  | Aindexed ofs, r1 :: nil, Ptr(Stk n) :: nil => addr_strength_reduction_case2 ofs r1 n
  | Aindexed2 ofs, r1 :: r2 :: nil, Ptr(Gl symb n1) :: I n2 :: nil => addr_strength_reduction_case3 ofs r1 r2 symb n1 n2
  | Aindexed2 ofs, r1 :: r2 :: nil, I n1 :: Ptr(Gl symb n2) :: nil => addr_strength_reduction_case4 ofs r1 r2 n1 symb n2
  | Aindexed2 ofs, r1 :: r2 :: nil, Ptr(Stk n1) :: I n2 :: nil => addr_strength_reduction_case5 ofs r1 r2 n1 n2
  | Aindexed2 ofs, r1 :: r2 :: nil, I n1 :: Ptr(Stk n2) :: nil => addr_strength_reduction_case6 ofs r1 r2 n1 n2
  | Aindexed2 ofs, r1 :: r2 :: nil, Ptr(Gl symb n1) :: v2 :: nil => addr_strength_reduction_case7 ofs r1 r2 symb n1 v2
  | Aindexed2 ofs, r1 :: r2 :: nil, v1 :: Ptr(Gl symb n2) :: nil => addr_strength_reduction_case8 ofs r1 r2 v1 symb n2
  | Aindexed2 ofs, r1 :: r2 :: nil, I n1 :: v2 :: nil => addr_strength_reduction_case9 ofs r1 r2 n1 v2
  | Aindexed2 ofs, r1 :: r2 :: nil, v1 :: I n2 :: nil => addr_strength_reduction_case10 ofs r1 r2 v1 n2
  | Aindexed2scaled sc ofs, r1 :: r2 :: nil, Ptr(Gl symb n1) :: I n2 :: nil => addr_strength_reduction_case11 sc ofs r1 r2 symb n1 n2
  | Aindexed2scaled sc ofs, r1 :: r2 :: nil, Ptr(Gl symb n1) :: v2 :: nil => addr_strength_reduction_case12 sc ofs r1 r2 symb n1 v2
  | Aindexed2scaled sc ofs, r1 :: r2 :: nil, v1 :: I n2 :: nil => addr_strength_reduction_case13 sc ofs r1 r2 v1 n2
  | Abased id ofs, r1 :: nil, I n1 :: nil => addr_strength_reduction_case14 id ofs r1 n1
  | Abasedscaled sc id ofs, r1 :: nil, I n1 :: nil => addr_strength_reduction_case15 sc id ofs r1 n1
  | addr, args, vl => addr_strength_reduction_default addr args vl
  end.

Definition addr_strength_reduction (addr: addressing) (args: list reg) (vl: list aval) :=
  match addr_strength_reduction_match addr args vl with
  | addr_strength_reduction_case1 ofs r1 symb n => (* Aindexed ofs, r1 :: nil, Ptr(Gl symb n) :: nil *) 
      (Aglobal symb (Int.add n ofs), nil)
  | addr_strength_reduction_case2 ofs r1 n => (* Aindexed ofs, r1 :: nil, Ptr(Stk n) :: nil *) 
      (Ainstack (Int.add n ofs), nil)
  | addr_strength_reduction_case3 ofs r1 r2 symb n1 n2 => (* Aindexed2 ofs, r1 :: r2 :: nil, Ptr(Gl symb n1) :: I n2 :: nil *) 
      (Aglobal symb (Int.add (Int.add n1 n2) ofs), nil)
  | addr_strength_reduction_case4 ofs r1 r2 n1 symb n2 => (* Aindexed2 ofs, r1 :: r2 :: nil, I n1 :: Ptr(Gl symb n2) :: nil *) 
      (Aglobal symb (Int.add (Int.add n1 n2) ofs), nil)
  | addr_strength_reduction_case5 ofs r1 r2 n1 n2 => (* Aindexed2 ofs, r1 :: r2 :: nil, Ptr(Stk n1) :: I n2 :: nil *) 
      (Ainstack (Int.add (Int.add n1 n2) ofs), nil)
  | addr_strength_reduction_case6 ofs r1 r2 n1 n2 => (* Aindexed2 ofs, r1 :: r2 :: nil, I n1 :: Ptr(Stk n2) :: nil *) 
      (Ainstack (Int.add (Int.add n1 n2) ofs), nil)
  | addr_strength_reduction_case7 ofs r1 r2 symb n1 v2 => (* Aindexed2 ofs, r1 :: r2 :: nil, Ptr(Gl symb n1) :: v2 :: nil *) 
      (Abased symb (Int.add n1 ofs), r2 :: nil)
  | addr_strength_reduction_case8 ofs r1 r2 v1 symb n2 => (* Aindexed2 ofs, r1 :: r2 :: nil, v1 :: Ptr(Gl symb n2) :: nil *) 
      (Abased symb (Int.add n2 ofs), r1 :: nil)
  | addr_strength_reduction_case9 ofs r1 r2 n1 v2 => (* Aindexed2 ofs, r1 :: r2 :: nil, I n1 :: v2 :: nil *) 
      (Aindexed (Int.add n1 ofs), r2 :: nil)
  | addr_strength_reduction_case10 ofs r1 r2 v1 n2 => (* Aindexed2 ofs, r1 :: r2 :: nil, v1 :: I n2 :: nil *) 
      (Aindexed (Int.add n2 ofs), r1 :: nil)
  | addr_strength_reduction_case11 sc ofs r1 r2 symb n1 n2 => (* Aindexed2scaled sc ofs, r1 :: r2 :: nil, Ptr(Gl symb n1) :: I n2 :: nil *) 
      (Aglobal symb (Int.add (Int.add n1 (Int.mul n2 sc)) ofs), nil)
  | addr_strength_reduction_case12 sc ofs r1 r2 symb n1 v2 => (* Aindexed2scaled sc ofs, r1 :: r2 :: nil, Ptr(Gl symb n1) :: v2 :: nil *) 
      (Abasedscaled sc symb (Int.add n1 ofs), r2 :: nil)
  | addr_strength_reduction_case13 sc ofs r1 r2 v1 n2 => (* Aindexed2scaled sc ofs, r1 :: r2 :: nil, v1 :: I n2 :: nil *) 
      (Aindexed (Int.add (Int.mul n2 sc) ofs), r1 :: nil)
  | addr_strength_reduction_case14 id ofs r1 n1 => (* Abased id ofs, r1 :: nil, I n1 :: nil *) 
      (Aglobal id (Int.add ofs n1), nil)
  | addr_strength_reduction_case15 sc id ofs r1 n1 => (* Abasedscaled sc id ofs, r1 :: nil, I n1 :: nil *) 
      (Aglobal id (Int.add ofs (Int.mul sc n1)), nil)
  | addr_strength_reduction_default addr args vl =>
      (addr, args)
  end.


Definition make_addimm (n: int) (r: reg) :=
  if Int.eq n Int.zero
  then (Omove, r :: nil)
  else (Olea (Aindexed n), r :: nil).

Definition make_shlimm (n: int) (r1 r2: reg) :=
  if Int.eq n Int.zero then (Omove, r1 :: nil)
  else if Int.ltu n Int.iwordsize then (Oshlimm n, r1 :: nil)
  else (Oshl, r1 :: r2 :: nil).

Definition make_shrimm (n: int) (r1 r2: reg) :=
  if Int.eq n Int.zero then (Omove, r1 :: nil)
  else if Int.ltu n Int.iwordsize then (Oshrimm n, r1 :: nil)
  else (Oshr, r1 :: r2 :: nil).

Definition make_shruimm (n: int) (r1 r2: reg) :=
  if Int.eq n Int.zero then (Omove, r1 :: nil)
  else if Int.ltu n Int.iwordsize then (Oshruimm n, r1 :: nil)
  else (Oshru, r1 :: r2 :: nil).

Definition make_mulimm (n: int) (r: reg) :=
  if Int.eq n Int.zero then
    (Ointconst Int.zero, nil)
  else if Int.eq n Int.one then
    (Omove, r :: nil)
  else
    match Int.is_power2 n with
    | Some l => (Oshlimm l, r :: nil)
    | None => (Omulimm n, r :: nil)
    end.

Definition make_andimm (n: int) (r: reg) (a: aval) :=
  if Int.eq n Int.zero then (Ointconst Int.zero, nil)
  else if Int.eq n Int.mone then (Omove, r :: nil)
  else if match a with Uns m => Int.eq (Int.zero_ext m (Int.not n)) Int.zero
                     | _ => false end
  then (Omove, r :: nil)
  else (Oandimm n, r :: nil).

Definition make_orimm (n: int) (r: reg) :=
  if Int.eq n Int.zero then (Omove, r :: nil)
  else if Int.eq n Int.mone then (Ointconst Int.mone, nil)
  else (Oorimm n, r :: nil).

Definition make_xorimm (n: int) (r: reg) :=
  if Int.eq n Int.zero then (Omove, r :: nil)
  else if Int.eq n Int.mone then (Onot, r :: nil)
  else (Oxorimm n, r :: nil).

Definition make_divimm n (r1 r2: reg) :=
  match Int.is_power2 n with
  | Some l => if Int.ltu l (Int.repr 31)
              then (Oshrximm l, r1 :: nil)
              else (Odiv, r1 :: r2 :: nil)
  | None   => (Odiv, r1 :: r2 :: nil)
  end.

Definition make_divuimm n (r1 r2: reg) :=
  match Int.is_power2 n with
  | Some l => (Oshruimm l, r1 :: nil)
  | None   => (Odivu, r1 :: r2 :: nil)
  end.

Definition make_moduimm n (r1 r2: reg) :=
  match Int.is_power2 n with
  | Some l => (Oandimm (Int.sub n Int.one), r1 :: nil)
  | None   => (Omodu, r1 :: r2 :: nil)
  end.

Definition make_mulfimm (n: float) (r r1 r2: reg) :=
  if Float.eq_dec n (Float.of_int (Int.repr 2))
  then (Oaddf, r :: r :: nil)
  else (Omulf, r1 :: r2 :: nil).

Definition make_mulfsimm (n: float32) (r r1 r2: reg) :=
  if Float32.eq_dec n (Float32.of_int (Int.repr 2))
  then (Oaddfs, r :: r :: nil)
  else (Omulfs, r1 :: r2 :: nil).

Definition make_cast8signed (r: reg) (a: aval) :=
  if vincl a (Sgn 8) then (Omove, r :: nil) else (Ocast8signed, r :: nil).
Definition make_cast8unsigned (r: reg) (a: aval) :=
  if vincl a (Uns 8) then (Omove, r :: nil) else (Ocast8unsigned, r :: nil).
Definition make_cast16signed (r: reg) (a: aval) :=
  if vincl a (Sgn 16) then (Omove, r :: nil) else (Ocast16signed, r :: nil).
Definition make_cast16unsigned (r: reg) (a: aval) :=
  if vincl a (Uns 16) then (Omove, r :: nil) else (Ocast16unsigned, r :: nil).

(** Original definition:
<<
Nondetfunction op_strength_reduction 
              (op: operation) (args: list reg) (vl: list aval) :=
  match op, args, vl with
  | Ocast8signed, r1 :: nil, v1 :: nil => make_cast8signed r1 v1
  | Ocast8unsigned, r1 :: nil, v1 :: nil => make_cast8unsigned r1 v1
  | Ocast16signed, r1 :: nil, v1 :: nil => make_cast16signed r1 v1
  | Ocast16unsigned, r1 :: nil, v1 :: nil => make_cast16unsigned r1 v1
  | Osub, r1 :: r2 :: nil, v1 :: I n2 :: nil => make_addimm (Int.neg n2) r1
  | Omul, r1 :: r2 :: nil, I n1 :: v2 :: nil => make_mulimm n1 r2
  | Omul, r1 :: r2 :: nil, v1 :: I n2 :: nil => make_mulimm n2 r1
  | Odiv, r1 :: r2 :: nil, v1 :: I n2 :: nil => make_divimm n2 r1 r2
  | Odivu, r1 :: r2 :: nil, v1 :: I n2 :: nil => make_divuimm n2 r1 r2
  | Omodu, r1 :: r2 :: nil, v1 :: I n2 :: nil => make_moduimm n2 r1 r2
  | Oand, r1 :: r2 :: nil, I n1 :: v2 :: nil => make_andimm n1 r2 v2
  | Oand, r1 :: r2 :: nil, v1 :: I n2 :: nil => make_andimm n2 r1 v1
  | Oandimm n, r1 :: nil, v1 :: nil => make_andimm n r1 v1
  | Oor, r1 :: r2 :: nil, I n1 :: v2 :: nil => make_orimm n1 r2
  | Oor, r1 :: r2 :: nil, v1 :: I n2 :: nil => make_orimm n2 r1
  | Oxor, r1 :: r2 :: nil, I n1 :: v2 :: nil => make_xorimm n1 r2
  | Oxor, r1 :: r2 :: nil, v1 :: I n2 :: nil => make_xorimm n2 r1
  | Oshl, r1 :: r2 :: nil, v1 :: I n2 :: nil => make_shlimm n2 r1 r2
  | Oshr, r1 :: r2 :: nil, v1 :: I n2 :: nil => make_shrimm n2 r1 r2
  | Oshru, r1 :: r2 :: nil, v1 :: I n2 :: nil => make_shruimm n2 r1 r2
  | Olea addr, args, vl =>
      let (addr', args') := addr_strength_reduction addr args vl in
      (Olea addr', args')
  | Ocmp c, args, vl => make_cmp c args vl
  | Omulf, r1 :: r2 :: nil, v1 :: F n2 :: nil => make_mulfimm n2 r1 r1 r2
  | Omulf, r1 :: r2 :: nil, F n1 :: v2 :: nil => make_mulfimm n1 r2 r1 r2
  | Omulfs, r1 :: r2 :: nil, v1 :: FS n2 :: nil => make_mulfsimm n2 r1 r1 r2
  | Omulfs, r1 :: r2 :: nil, FS n1 :: v2 :: nil => make_mulfsimm n1 r2 r1 r2
  | _, _, _ => (op, args)
  end.
>>
*)

Inductive op_strength_reduction_cases: forall (op: operation) (args: list reg) (vl: list aval), Type :=
  | op_strength_reduction_case1: forall r1 v1, op_strength_reduction_cases (Ocast8signed) (r1 :: nil) (v1 :: nil)
  | op_strength_reduction_case2: forall r1 v1, op_strength_reduction_cases (Ocast8unsigned) (r1 :: nil) (v1 :: nil)
  | op_strength_reduction_case3: forall r1 v1, op_strength_reduction_cases (Ocast16signed) (r1 :: nil) (v1 :: nil)
  | op_strength_reduction_case4: forall r1 v1, op_strength_reduction_cases (Ocast16unsigned) (r1 :: nil) (v1 :: nil)
  | op_strength_reduction_case5: forall r1 r2 v1 n2, op_strength_reduction_cases (Osub) (r1 :: r2 :: nil) (v1 :: I n2 :: nil)
  | op_strength_reduction_case6: forall r1 r2 n1 v2, op_strength_reduction_cases (Omul) (r1 :: r2 :: nil) (I n1 :: v2 :: nil)
  | op_strength_reduction_case7: forall r1 r2 v1 n2, op_strength_reduction_cases (Omul) (r1 :: r2 :: nil) (v1 :: I n2 :: nil)
  | op_strength_reduction_case8: forall r1 r2 v1 n2, op_strength_reduction_cases (Odiv) (r1 :: r2 :: nil) (v1 :: I n2 :: nil)
  | op_strength_reduction_case9: forall r1 r2 v1 n2, op_strength_reduction_cases (Odivu) (r1 :: r2 :: nil) (v1 :: I n2 :: nil)
  | op_strength_reduction_case10: forall r1 r2 v1 n2, op_strength_reduction_cases (Omodu) (r1 :: r2 :: nil) (v1 :: I n2 :: nil)
  | op_strength_reduction_case11: forall r1 r2 n1 v2, op_strength_reduction_cases (Oand) (r1 :: r2 :: nil) (I n1 :: v2 :: nil)
  | op_strength_reduction_case12: forall r1 r2 v1 n2, op_strength_reduction_cases (Oand) (r1 :: r2 :: nil) (v1 :: I n2 :: nil)
  | op_strength_reduction_case13: forall n r1 v1, op_strength_reduction_cases (Oandimm n) (r1 :: nil) (v1 :: nil)
  | op_strength_reduction_case14: forall r1 r2 n1 v2, op_strength_reduction_cases (Oor) (r1 :: r2 :: nil) (I n1 :: v2 :: nil)
  | op_strength_reduction_case15: forall r1 r2 v1 n2, op_strength_reduction_cases (Oor) (r1 :: r2 :: nil) (v1 :: I n2 :: nil)
  | op_strength_reduction_case16: forall r1 r2 n1 v2, op_strength_reduction_cases (Oxor) (r1 :: r2 :: nil) (I n1 :: v2 :: nil)
  | op_strength_reduction_case17: forall r1 r2 v1 n2, op_strength_reduction_cases (Oxor) (r1 :: r2 :: nil) (v1 :: I n2 :: nil)
  | op_strength_reduction_case18: forall r1 r2 v1 n2, op_strength_reduction_cases (Oshl) (r1 :: r2 :: nil) (v1 :: I n2 :: nil)
  | op_strength_reduction_case19: forall r1 r2 v1 n2, op_strength_reduction_cases (Oshr) (r1 :: r2 :: nil) (v1 :: I n2 :: nil)
  | op_strength_reduction_case20: forall r1 r2 v1 n2, op_strength_reduction_cases (Oshru) (r1 :: r2 :: nil) (v1 :: I n2 :: nil)
  | op_strength_reduction_case21: forall addr args vl, op_strength_reduction_cases (Olea addr) (args) (vl)
  | op_strength_reduction_case22: forall c args vl, op_strength_reduction_cases (Ocmp c) (args) (vl)
  | op_strength_reduction_case23: forall r1 r2 v1 n2, op_strength_reduction_cases (Omulf) (r1 :: r2 :: nil) (v1 :: F n2 :: nil)
  | op_strength_reduction_case24: forall r1 r2 n1 v2, op_strength_reduction_cases (Omulf) (r1 :: r2 :: nil) (F n1 :: v2 :: nil)
  | op_strength_reduction_case25: forall r1 r2 v1 n2, op_strength_reduction_cases (Omulfs) (r1 :: r2 :: nil) (v1 :: FS n2 :: nil)
  | op_strength_reduction_case26: forall r1 r2 n1 v2, op_strength_reduction_cases (Omulfs) (r1 :: r2 :: nil) (FS n1 :: v2 :: nil)
  | op_strength_reduction_default: forall (op: operation) (args: list reg) (vl: list aval), op_strength_reduction_cases op args vl.

Definition op_strength_reduction_match (op: operation) (args: list reg) (vl: list aval) :=
  match op as zz1, args as zz2, vl as zz3 return op_strength_reduction_cases zz1 zz2 zz3 with
  | Ocast8signed, r1 :: nil, v1 :: nil => op_strength_reduction_case1 r1 v1
  | Ocast8unsigned, r1 :: nil, v1 :: nil => op_strength_reduction_case2 r1 v1
  | Ocast16signed, r1 :: nil, v1 :: nil => op_strength_reduction_case3 r1 v1
  | Ocast16unsigned, r1 :: nil, v1 :: nil => op_strength_reduction_case4 r1 v1
  | Osub, r1 :: r2 :: nil, v1 :: I n2 :: nil => op_strength_reduction_case5 r1 r2 v1 n2
  | Omul, r1 :: r2 :: nil, I n1 :: v2 :: nil => op_strength_reduction_case6 r1 r2 n1 v2
  | Omul, r1 :: r2 :: nil, v1 :: I n2 :: nil => op_strength_reduction_case7 r1 r2 v1 n2
  | Odiv, r1 :: r2 :: nil, v1 :: I n2 :: nil => op_strength_reduction_case8 r1 r2 v1 n2
  | Odivu, r1 :: r2 :: nil, v1 :: I n2 :: nil => op_strength_reduction_case9 r1 r2 v1 n2
  | Omodu, r1 :: r2 :: nil, v1 :: I n2 :: nil => op_strength_reduction_case10 r1 r2 v1 n2
  | Oand, r1 :: r2 :: nil, I n1 :: v2 :: nil => op_strength_reduction_case11 r1 r2 n1 v2
  | Oand, r1 :: r2 :: nil, v1 :: I n2 :: nil => op_strength_reduction_case12 r1 r2 v1 n2
  | Oandimm n, r1 :: nil, v1 :: nil => op_strength_reduction_case13 n r1 v1
  | Oor, r1 :: r2 :: nil, I n1 :: v2 :: nil => op_strength_reduction_case14 r1 r2 n1 v2
  | Oor, r1 :: r2 :: nil, v1 :: I n2 :: nil => op_strength_reduction_case15 r1 r2 v1 n2
  | Oxor, r1 :: r2 :: nil, I n1 :: v2 :: nil => op_strength_reduction_case16 r1 r2 n1 v2
  | Oxor, r1 :: r2 :: nil, v1 :: I n2 :: nil => op_strength_reduction_case17 r1 r2 v1 n2
  | Oshl, r1 :: r2 :: nil, v1 :: I n2 :: nil => op_strength_reduction_case18 r1 r2 v1 n2
  | Oshr, r1 :: r2 :: nil, v1 :: I n2 :: nil => op_strength_reduction_case19 r1 r2 v1 n2
  | Oshru, r1 :: r2 :: nil, v1 :: I n2 :: nil => op_strength_reduction_case20 r1 r2 v1 n2
  | Olea addr, args, vl => op_strength_reduction_case21 addr args vl
  | Ocmp c, args, vl => op_strength_reduction_case22 c args vl
  | Omulf, r1 :: r2 :: nil, v1 :: F n2 :: nil => op_strength_reduction_case23 r1 r2 v1 n2
  | Omulf, r1 :: r2 :: nil, F n1 :: v2 :: nil => op_strength_reduction_case24 r1 r2 n1 v2
  | Omulfs, r1 :: r2 :: nil, v1 :: FS n2 :: nil => op_strength_reduction_case25 r1 r2 v1 n2
  | Omulfs, r1 :: r2 :: nil, FS n1 :: v2 :: nil => op_strength_reduction_case26 r1 r2 n1 v2
  | op, args, vl => op_strength_reduction_default op args vl
  end.

Definition op_strength_reduction (op: operation) (args: list reg) (vl: list aval) :=
  match op_strength_reduction_match op args vl with
  | op_strength_reduction_case1 r1 v1 => (* Ocast8signed, r1 :: nil, v1 :: nil *) 
      make_cast8signed r1 v1
  | op_strength_reduction_case2 r1 v1 => (* Ocast8unsigned, r1 :: nil, v1 :: nil *) 
      make_cast8unsigned r1 v1
  | op_strength_reduction_case3 r1 v1 => (* Ocast16signed, r1 :: nil, v1 :: nil *) 
      make_cast16signed r1 v1
  | op_strength_reduction_case4 r1 v1 => (* Ocast16unsigned, r1 :: nil, v1 :: nil *) 
      make_cast16unsigned r1 v1
  | op_strength_reduction_case5 r1 r2 v1 n2 => (* Osub, r1 :: r2 :: nil, v1 :: I n2 :: nil *) 
      make_addimm (Int.neg n2) r1
  | op_strength_reduction_case6 r1 r2 n1 v2 => (* Omul, r1 :: r2 :: nil, I n1 :: v2 :: nil *) 
      make_mulimm n1 r2
  | op_strength_reduction_case7 r1 r2 v1 n2 => (* Omul, r1 :: r2 :: nil, v1 :: I n2 :: nil *) 
      make_mulimm n2 r1
  | op_strength_reduction_case8 r1 r2 v1 n2 => (* Odiv, r1 :: r2 :: nil, v1 :: I n2 :: nil *) 
      make_divimm n2 r1 r2
  | op_strength_reduction_case9 r1 r2 v1 n2 => (* Odivu, r1 :: r2 :: nil, v1 :: I n2 :: nil *) 
      make_divuimm n2 r1 r2
  | op_strength_reduction_case10 r1 r2 v1 n2 => (* Omodu, r1 :: r2 :: nil, v1 :: I n2 :: nil *) 
      make_moduimm n2 r1 r2
  | op_strength_reduction_case11 r1 r2 n1 v2 => (* Oand, r1 :: r2 :: nil, I n1 :: v2 :: nil *) 
      make_andimm n1 r2 v2
  | op_strength_reduction_case12 r1 r2 v1 n2 => (* Oand, r1 :: r2 :: nil, v1 :: I n2 :: nil *) 
      make_andimm n2 r1 v1
  | op_strength_reduction_case13 n r1 v1 => (* Oandimm n, r1 :: nil, v1 :: nil *) 
      make_andimm n r1 v1
  | op_strength_reduction_case14 r1 r2 n1 v2 => (* Oor, r1 :: r2 :: nil, I n1 :: v2 :: nil *) 
      make_orimm n1 r2
  | op_strength_reduction_case15 r1 r2 v1 n2 => (* Oor, r1 :: r2 :: nil, v1 :: I n2 :: nil *) 
      make_orimm n2 r1
  | op_strength_reduction_case16 r1 r2 n1 v2 => (* Oxor, r1 :: r2 :: nil, I n1 :: v2 :: nil *) 
      make_xorimm n1 r2
  | op_strength_reduction_case17 r1 r2 v1 n2 => (* Oxor, r1 :: r2 :: nil, v1 :: I n2 :: nil *) 
      make_xorimm n2 r1
  | op_strength_reduction_case18 r1 r2 v1 n2 => (* Oshl, r1 :: r2 :: nil, v1 :: I n2 :: nil *) 
      make_shlimm n2 r1 r2
  | op_strength_reduction_case19 r1 r2 v1 n2 => (* Oshr, r1 :: r2 :: nil, v1 :: I n2 :: nil *) 
      make_shrimm n2 r1 r2
  | op_strength_reduction_case20 r1 r2 v1 n2 => (* Oshru, r1 :: r2 :: nil, v1 :: I n2 :: nil *) 
      make_shruimm n2 r1 r2
  | op_strength_reduction_case21 addr args vl => (* Olea addr, args, vl *) 
      let (addr', args') := addr_strength_reduction addr args vl in (Olea addr', args')
  | op_strength_reduction_case22 c args vl => (* Ocmp c, args, vl *) 
      make_cmp c args vl
  | op_strength_reduction_case23 r1 r2 v1 n2 => (* Omulf, r1 :: r2 :: nil, v1 :: F n2 :: nil *) 
      make_mulfimm n2 r1 r1 r2
  | op_strength_reduction_case24 r1 r2 n1 v2 => (* Omulf, r1 :: r2 :: nil, F n1 :: v2 :: nil *) 
      make_mulfimm n1 r2 r1 r2
  | op_strength_reduction_case25 r1 r2 v1 n2 => (* Omulfs, r1 :: r2 :: nil, v1 :: FS n2 :: nil *) 
      make_mulfsimm n2 r1 r1 r2
  | op_strength_reduction_case26 r1 r2 n1 v2 => (* Omulfs, r1 :: r2 :: nil, FS n1 :: v2 :: nil *) 
      make_mulfsimm n1 r2 r1 r2
  | op_strength_reduction_default op args vl =>
      (op, args)
  end.

