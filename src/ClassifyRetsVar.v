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

(** Correctness proof for output parameters classification. *)

Require Import Coqlib.
Require Import AST.
Require Import Lident.
Require Import Cltypes.
Require Import Lustre.
Require Import LustreF.

(** translate sexp. *)

Fixpoint trans_sexp(mkv: mkvar)(e: sexp): sexp :=
  match e with
  | Sconst c ty => Sconst c ty
  | Svar id ty  => mkv id ty
  | Scvar id ty  => Scvar id ty
  | Ssvar id ty  => Ssvar id ty
  | Savar id ty  => Savar id ty
  | Saryacc a1 a2 ty => Saryacc (trans_sexp mkv a1) (trans_sexp mkv a2) ty
  | Sfield a id ty => Sfield (trans_sexp mkv a) id ty
  | Scast a ty => Scast (trans_sexp mkv a) ty
  | Sunop op a ty => Sunop op (trans_sexp mkv a) ty
  | Sbinop op a1 a2 ty => Sbinop op (trans_sexp mkv a1) (trans_sexp mkv a2) ty
  end.

(** translate list of sexp. *)

Definition trans_sexps(mkv: mkvar)(al: list sexp): list sexp :=
  map (trans_sexp mkv) al.

(** translate equtation. *)

Definition trans_eqf(mkv: mkvar)(s: eqf): eqf :=
  (trans_sexp mkv (fst s), trans_sexp mkv (snd s)).

(** translate statement. *)

Fixpoint trans_stmt(mkv: mkvar)(s: stmt): stmt :=
  match s with
  | Sassign a1 a2 => Sassign (trans_sexp mkv a1) (trans_sexp mkv a2)
  | Scall oid lh cdef al =>
    Scall oid (trans_sexps mkv lh) cdef (trans_sexps mkv al)
  | Sfor s1 a s2 s3 =>
    Sfor (option_map (trans_eqf mkv) s1) (trans_sexp mkv a) (trans_eqf mkv s2) (trans_stmt mkv s3)
  | Sseq s1 s2 => Sseq (trans_stmt mkv s1) (trans_stmt mkv s2)
  | Sskip => Sskip
  | Sif a s1 s2 => Sif (trans_sexp mkv a) (trans_stmt mkv s1) (trans_stmt mkv s2)
  | Scase a1 a2 pl => Scase (trans_sexp mkv a1) (trans_sexp mkv a2) (trans_patns (trans_sexp mkv) pl)
  end.

Definition trans_v(rids: list ident)(id: ident)(ty: type): sexp :=
  if in_list id rids then
    Ssvar id ty
  else
    Svar id ty.

(** translate body of node. *)

Definition trans_body(b: func): func :=
  let rids := map fst (nd_rets b) in
  let mkv := trans_v rids in
  let s := trans_stmt mkv (nd_stmt b) in
  (mknode b.(nd_kind) (nd_args b) (nd_rets b) (nd_svars b) (nd_vars b)
     s b.(nd_sid) b.(nd_fld)).

Definition trans_node(fd: ident*func) :=
  (fst fd, trans_body (snd fd)).

Definition trans_program (p: LustreF.program): program :=
  let nodes1 := map (trans_node) (node_block p)  in
  (mkprogram (type_block p) (defs_block p) (const_block p) nodes1 (node_main p)).

Lemma trans_sexp_typeof:
  forall ids a,
  typeof (trans_sexp (trans_v ids) a) = typeof a.
Proof.
  induction a; simpl; auto.
  unfold trans_v. destruct (in_list i ids); auto.
Qed.

Lemma trans_sexps_typeof:
  forall ids l,
  map typeof (trans_sexps (trans_v ids) l) = map typeof l.
Proof.
  induction l; simpl; auto. f_equal; auto.
  rewrite trans_sexp_typeof; auto.
Qed.

Lemma trans_sexp_lid_disjoint:
  forall lhs ids,
  lid_disjoint lhs ->
  ~ In ACG_I ids ->
  lid_disjoint (trans_sexp (trans_v ids) lhs).
Proof.
  induction lhs; simpl; intros; auto.
  +unfold trans_v. destruct (in_list _ _); simpl; auto.
  +destruct lhs2; auto. destruct H; subst.
   generalize H0. intros.
   apply in_list_false_notin in H0; auto.
   unfold trans_v. simpl. rewrite H0.
   eapply IHlhs1 in H; eauto.
Qed.

Lemma trans_sexps_lid_disjoint:
  forall ids lhs,
  Forall (lid_disjoint) lhs ->
  ~ In ACG_I ids ->
  Forall (lid_disjoint) (trans_sexps (trans_v ids) lhs).
Proof.
  induction 1; simpl; intros.
  constructor.
  constructor 2; auto.
  eapply trans_sexp_lid_disjoint; eauto.
Qed.

Lemma trans_stmt_instidof_eq:
  forall s mkv,
  instidof (trans_stmt mkv s) = instidof s.
Proof.
  induction s; intros; simpl; auto; f_equal; auto.
Qed.

Lemma trans_body_ids_norepet:
  forall f, ids_norepet f ->
  ids_norepet (trans_body f).
Proof.
  unfold ids_norepet, ids_norepet.
  unfold allidsof,predidof.
  intros. unfold trans_body, allvarsof in *. simpl.
  rewrite trans_stmt_instidof_eq.
  intuition.
Qed.

Lemma trans_program_ids_range:
  forall p, ids_range OUTSTRUCT (node_block p) ->
  ids_range OUTSTRUCT (node_block (trans_program p)).
Proof.
  simpl. intros. red. intros.
  apply in_map_iff in H0. destruct H0 as [? [? ?]].
  subst. simpl in *.
  red in H. apply H in H1; auto.
  unfold allidsof, predidof, allvarsof in *; simpl in *.
  rewrite trans_stmt_instidof_eq; auto.
Qed.

Lemma trans_program_gids:
  forall p,
  globidsof (trans_program p) = globidsof p.
Proof.
  unfold trans_program, globidsof.
  intros. simpl; auto. repeat rewrite map_map. auto.
Qed.
