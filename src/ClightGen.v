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

(** Translation from Ctemp to Clight. *)

Require Import Coqlib.
Require Import AST.
Require Import Integers.
Require Import Cltypes.
Require Import Ctypes.
Require Import Cop.
Require Import Lident.
Require Import Ctemp.
Require Import Clight.
Require Import CtempGen.

Fixpoint trans_type(ty: Cltypes.type) : type :=
  match ty with
  | Cltypes.Tvoid => Tvoid
  | Cltypes.Tint i s => Tint i s noattr
  | Cltypes.Tfloat i => Tfloat i noattr
  | Cltypes.Tpointer t => Tpointer (trans_type t) noattr
  | Cltypes.Tarray id t z => Tarray (trans_type t) z noattr
  | Cltypes.Tfunction tyl t cc => Tfunction (trans_typelist tyl) (trans_type t) cc
  | Cltypes.Tstruct id fld => Tstruct id (trans_fields fld) noattr
  end

with trans_typelist(l: Cltypes.typelist) : typelist :=
  match l with
  | Cltypes.Tnil => Tnil
  | Cltypes.Tcons t l' => Tcons (trans_type t) (trans_typelist l')
  end

with trans_fields (f: Cltypes.fieldlist) : fieldlist :=
  match f with
  | Cltypes.Fnil => Fnil
  | Cltypes.Fcons id t f' => Fcons id (trans_type t) (trans_fields f')
  end.

Fixpoint trans_expr(a: Ctemp.expr) : expr :=
  match a with
  | Ctemp.Econst_int i ty => Econst_int i (trans_type ty)
  | Ctemp.Econst_float f ty => Econst_float f (trans_type ty)
  | Ctemp.Econst_single f ty => Econst_single f (trans_type ty)
  | Ctemp.Evar id ty => Evar id (trans_type ty)
  | Ctemp.Etempvar id ty => Etempvar id (trans_type ty)
  | Ctemp.Etempret id ty => Etempvar id (trans_type ty)
  | Ctemp.Ederef a1 ty => Ederef (trans_expr a1) (trans_type ty)
  | Ctemp.Eaddrof a1 ty => Eaddrof (trans_expr a1) (trans_type ty)
  | Ctemp.Eunop op a1 ty => Eunop op (trans_expr a1) (trans_type ty)
  | Ctemp.Ebinop op a1 a2 ty => Ebinop op (trans_expr a1) (trans_expr a2) (trans_type ty)
  | Ctemp.Ecast a1 ty => Ecast (trans_expr a1) (trans_type ty)
  | Ctemp.Efield a1 id ty => Efield (trans_expr a1) id (trans_type ty)
  | Ctemp.Esizeof ty ty' => Esizeof (trans_type ty) (trans_type ty')
  | Ctemp.Ealignof ty ty' => Ealignof (trans_type ty) (trans_type ty')
  end.

Definition trans_exprs(al: list Ctemp.expr) : list expr :=
  map trans_expr al.

Fixpoint trans_stmt (s: Ctemp.statement): statement :=
  match s with
  | Ctemp.Sskip => Sskip
  | Ctemp.Sassign a1 a2 => Sassign (trans_expr a1) (trans_expr a2)
  | Ctemp.Sset id a => Sset id (trans_expr a)
  | Ctemp.Smemcpy ty tyl al =>
      let size := Int.unsigned (Int.repr (Cltypes.sizeof ty)) in
      let align := Int.unsigned (Int.repr (Cltypes.alignof ty)) in
      Sbuiltin None (EF_memcpy size align) (trans_typelist tyl) (trans_exprs al)  (**r memcpy (lhs, rval, size) *)
  | Ctemp.Scall optid a al rets => Scall optid (trans_expr a) (trans_exprs (al++rets))
  | Ctemp.Ssequence s1 s2 => Ssequence (trans_stmt s1) (trans_stmt s2)
  | Ctemp.Sifthenelse a s1 s2 =>
      Sifthenelse (trans_expr a) (trans_stmt s1) (trans_stmt s2)
  | Ctemp.Sfor s1 a s2 s3 =>
      Sfor (trans_stmt s1) (trans_expr a) (trans_stmt s3) (trans_stmt s2)
  | Ctemp.Sbreak => Sbreak
  | Ctemp.Sreturn opta => Sreturn (option_map trans_expr opta)
  | Ctemp.Sswitch a ls => Sswitch (trans_expr a) (trans_lblstmt ls)
  end

with trans_lblstmt (ls: Ctemp.labeled_statements) : labeled_statements :=
  match ls with
  | Ctemp.LSdefault s => LScons None (trans_stmt s) LSnil
  | Ctemp.LScase n s ls1 => LScons (Some (Int.unsigned n)) (trans_stmt s) (trans_lblstmt ls1)
  end.

Definition trans_var(a: ident*Cltypes.type) : ident*type :=
  (fst a, trans_type (snd a)).

Definition trans_func (f: Ctemp.function) : function :=
  {| fn_return := trans_type f.(Ctemp.fn_return);
     fn_callconv := f.(Ctemp.fn_callconv);
     fn_params := map trans_var (f.(Ctemp.fn_params) ++ f.(Ctemp.fn_temps));
     fn_vars := map trans_var f.(Ctemp.fn_vars);
     fn_temps := nil;
     fn_body := trans_stmt f.(Ctemp.fn_body) |}.

Definition trans_fundef (fd: Ctemp.fundef) : fundef :=
  match fd with
  | Ctemp.Internal f => Internal (trans_func f)
  end.

Definition trans_globvar(v : globvar Cltypes.type) : globvar type :=
  mkglobvar (trans_type (gvar_info v)) (gvar_init v) (gvar_readonly v) (gvar_volatile v).

Definition transform_program_globdef (idg: ident * globdef Ctemp.fundef Cltypes.type)
 : ident * globdef fundef type :=
  match idg with
  | (id, Gfun f) => (id, Gfun (trans_fundef f))
  | (id, Gvar v) => (id, Gvar (trans_globvar v))
  end.

Definition trans_program(p: Ctemp.program) : program :=
  mkprogram (map transform_program_globdef p.(prog_defs)) p.(prog_main).

Lemma trans_expr_typeof:
  forall a, typeof (trans_expr a) = trans_type (Ctemp.typeof a).
Proof.
  induction a; simpl; intros; auto.
Qed.
