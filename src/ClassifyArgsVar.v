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

(** Classify input parameters and global consts from local variables. *)

Require Import Coqlib.
Require Import AST.
Require Import Errors.
Require Import Lident.
Require Import Cltypes.
Require Import Lustre.
Require Import LustreF.
Require Import ClassifyRetsVar.

Local Open Scope error_monad_scope.

Definition trans_v(aids lids: list ident)(id: ident)(ty: type): sexp :=
  if in_list id aids then
    Savar id ty
  else
    if in_list id lids then
      Svar id ty
    else
      Scvar id ty.

(** translate lvalue sexp. *)

Fixpoint trans_lsexp(ids lids: list ident)(e: sexp): res sexp :=
  match e with
  | Svar id ty  =>
    if in_list id lids then
      OK (Svar id ty)
    else
      Error (msg "ClassifyArgsVar.trans_lsexp: only local and return variables are allowed to be assigned!")
  | Ssvar id ty  => OK (Ssvar id ty)
  | Saryacc a1 a2 ty =>
    do a1 <- trans_lsexp ids lids a1;
    OK (Saryacc a1 (trans_sexp (trans_v ids lids) a2) ty)
  | Sfield a id ty =>
    do a <- trans_lsexp ids lids a;
    OK (Sfield a id ty)
  | _ => Error (msg "ClassifyArgsVar.trans_lsexp: l-value expr error!")
  end.

(** translate list of lvalue sexp. *)

Definition trans_lsexps(ids lids: list ident)(l: list sexp) : res (list sexp) :=
  mmap (trans_lsexp ids lids) l.

(** translate equtation. *)

Definition trans_eqf(ids lids: list ident)(s: eqf): res eqf :=
  do a <- trans_lsexp ids lids (fst s);
  OK (a, trans_sexp (trans_v ids lids) (snd s)).

Definition trans_opteqf(ids lids: list ident)(os: option eqf): res (option eqf) :=
  match os with
  | Some s =>
    do s <- trans_eqf ids lids s;
    OK (Some s)
  | None => OK None
  end.

(** translate statement. *)

Fixpoint trans_stmt(ids lids: list ident)(s: stmt): res stmt :=
  match s with
  | Sassign a1 a2 =>
    do a1 <- trans_lsexp ids lids a1;
    OK (Sassign a1 (trans_sexp (trans_v ids lids) a2))
  | Scall oid lh cdef al =>
    do lh <- trans_lsexps ids lids lh;
    OK (Scall oid lh cdef (trans_sexps (trans_v ids lids) al))
  | Sfor s1 a s2 s3 =>
    do s1 <- trans_opteqf ids lids s1;
    do s2 <- trans_eqf ids lids s2;
    do s3 <- trans_stmt ids lids s3;
    OK (Sfor s1 (trans_sexp (trans_v ids lids) a) s2 s3)
  | Sseq s1 s2 =>
    do s1 <- trans_stmt ids lids s1;
    do s2 <- trans_stmt ids lids s2;
    OK (Sseq s1 s2)
  | Sskip => OK Sskip
  | Sif a s1 s2 =>
    do s1 <- trans_stmt ids lids s1;
    do s2 <- trans_stmt ids lids s2;
    OK (Sif (trans_sexp (trans_v ids lids) a) s1 s2)
  | Scase a1 a2 pl =>
    do a1 <- trans_lsexp ids lids a1;
    OK (Scase a1 (trans_sexp (trans_v ids lids) a2) (trans_patns (trans_sexp (trans_v ids lids)) pl))
  end.

(** translate body of node. *)

Definition trans_body(b: func): res func :=
  let aids := map fst (nd_args b) in
  let lids := map fst (nd_vars b) in
  do s <- trans_stmt aids lids (nd_stmt b);
  OK (mknode b.(nd_kind) (nd_args b) (nd_rets b) (nd_svars b) (nd_vars b)
     s b.(nd_sid) b.(nd_fld)).

Definition trans_node(fd: ident*func) : res (ident*func) :=
  do b <- trans_body (snd fd);
  OK (fst fd, b).

Definition trans_typedef(d: ident*type) :=
  (fst d, mkglobvar (snd d) nil true true).

Definition trans_program (p: LustreF.program): res program :=
  do nodes <- mmap (trans_node) (node_block p);
  let tyds := map trans_typedef (type_block p ++ defs_block p) in
  OK (mkprogram nil nil (tyds++const_block p) nodes (node_main p)).

Lemma trans_sexp_typeof:
  forall ids lids a,
  typeof (trans_sexp (trans_v ids lids) a) = typeof a.
Proof.
  induction a; simpl; auto.
  unfold trans_v. destruct (in_list i ids); auto.
  destruct (in_list _ _); auto.
Qed.

Lemma trans_sexps_typeof:
  forall ids lids args, map typeof (trans_sexps (trans_v ids lids) args) = map typeof args.
Proof.
  unfold trans_sexps. intros.
  rewrite map_map. apply map_ext.
  intros. apply trans_sexp_typeof; auto.
Qed.

Lemma trans_lsexp_typeof:
  forall ids lids a a',
  trans_lsexp ids lids a = OK a' ->
  typeof a' = typeof a.
Proof.
  induction a; simpl; intros; inv H; auto.
  +destruct (in_list i _); monadInv H1; auto.
  +monadInv H1; auto.
  +monadInv H1; auto.
Qed.

Lemma trans_lsexps_typeof:
  forall ids lids l l',
  trans_lsexps ids lids l = OK l' ->
  map typeof l' = map typeof l.
Proof.
  intros. symmetry.
  apply mmap_ext with (trans_lsexp ids lids); auto.
  intros. erewrite <-trans_lsexp_typeof; eauto.
Qed.

Lemma trans_stmt_instidof_eq:
  forall ids lids s s',
  trans_stmt ids lids s = OK s' ->
  instidof s' = instidof s.
Proof.
  induction s; intros; monadInv H; simpl; auto; f_equal; auto.
Qed.

Lemma trans_body_ids_norepet:
  forall f f', ids_norepet f ->
  trans_body f = OK f' ->
  ids_norepet f'.
Proof.
  unfold ids_norepet, ids_norepet.
  unfold allidsof,predidof.
  intros. unfold trans_body, allvarsof in *.
  monadInv H0. simpl.
  erewrite trans_stmt_instidof_eq; eauto.
Qed.
