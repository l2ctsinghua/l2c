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
Require Import Integers.
Require Import Streams.
Require Import Lident.
Require Import Lvalues.
Require Import Values.
Require Import Events.
Require Import Memory.
Require Import Globalenvs.
Require Import Ctemp.
Require Import Ctypes.
Require Import Clight.
Require Import ClightBigstep.

Section TRANSITIONS.

Variable p: program.
Let ge : genv := Genv.globalenv p.

Variable bi: block. (**r the address of input struct in main function. *)
Variable bo: block. (**r the address of output struct in main function. *)

Inductive type_of_fundef_case:type -> type -> type -> type -> bool -> Prop :=
  | type_of_fundef_anil_rnil:
    type_of_fundef_case (Tfunction Tnil Tvoid cc_default) (Tfunction Tnil Tvoid cc_default) Tvoid Tvoid false
  | type_of_fundef_anil_rcons: forall oty,
    type_of_fundef_case (Tfunction (Tcons (Tpointer oty noattr) Tnil) Tvoid cc_default) (Tfunction (Tcons (Tpointer oty noattr) Tnil) Tvoid cc_default) Tvoid oty true
  | type_of_fundef_acons_rnil: forall ity,
    type_of_fundef_case (Tfunction (Tcons (Tpointer ity noattr) Tnil) Tvoid cc_default) (Tfunction Tnil Tvoid cc_default) ity Tvoid false
  | type_of_fundef_acons_rcons: forall ity oty,
    type_of_fundef_case (Tfunction (Tcons (Tpointer ity noattr) (Tcons (Tpointer oty noattr) Tnil)) Tvoid cc_default) (Tfunction (Tcons (Tpointer oty noattr) Tnil) Tvoid cc_default) ity oty true.

Inductive initial_state(f: fundef): mem -> Prop :=
  | initial_state_: forall b1 b2 fi m_init m0 m1 m2 ity oty b,
      Genv.init_mem p = Some m_init ->
      Genv.find_symbol ge (reset_id p.(prog_main)) = Some b1 ->
      Genv.find_symbol ge p.(prog_main) = Some b2 ->
      Genv.find_funct_ptr ge b1 = Some fi ->
      Genv.find_funct_ptr ge b2 = Some f ->
      type_of_fundef_case (type_of_fundef f) (type_of_fundef fi) ity oty b ->
      Mem.alloc m_init 0 (sizeof ity) = (m0, bi) ->
      Mem.alloc m0 0 (sizeof oty) = (m1, bo) ->
      eval_funcall ge m1 fi (if b then Vptr bo Int.zero :: nil else nil) E0 m2 Vundef ->
      initial_state f m2.

Inductive exec_prog (main: fundef)(m: mem)(n maxn: nat)(vass vrss: Stream (list mvl)) : Prop :=
  | exec_prog_term:
    (n > maxn)%nat ->
    exec_prog main m n maxn vass vrss
  | exec_prog_cons: forall (b1 b2: bool) m1 mv1 mv2 m',
    (n <= maxn)%nat ->
    classify_mvls (hd vass) mv1 b1 ->
    classify_mvls (hd vrss) mv2 b2 ->
    Mem.storebytes m bi 0 mv1 = Some m1 ->
    eval_funcall ge m1 main ((if b1 then Vptr bi Int.zero :: nil else nil) ++ if b2 then Vptr bo Int.zero :: nil else nil) E0 m' Vundef ->
    Mem.loadbytes m' bo 0 (Z_of_nat (length mv2)) = Some mv2 ->
    exec_prog main m' (n+1) maxn  (tl vass) (tl vrss) ->
    exec_prog main m n maxn vass vrss.

End TRANSITIONS.
