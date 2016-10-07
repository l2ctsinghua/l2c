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
Require Import Integers.
Require Import Cltypes.
Require Import Ltypes.
Require Import Lident.
Require Import Lustre.

(** Statements *)

Inductive stmt: Type :=
  | Sassign: sexp -> sexp -> stmt  (**r assignment *)
  | Scall: option sexp -> list sexp -> calldef -> list sexp -> stmt (**r function call *)
  | Sfor: option eqf -> sexp -> eqf -> stmt -> stmt (**r [for] loop *)
  | Sseq: stmt -> stmt -> stmt  (**r sequence *)
  | Sskip: stmt  (**r do nothing *)
  | Sif: sexp -> stmt -> stmt -> stmt (**r conditional *)
  | Scase: sexp -> sexp -> list (patn * sexp) -> stmt. (**r [switch] statement *)

Fixpoint instidof (s: stmt): list calldef :=
  match s with
  | Scall _ _  c _ => cons_inst c
  | Sfor _ _ _ s1 =>  instidof s1
  | Sseq s1 s2 => instidof s1 ++ instidof s2
  | Sif _ s1 s2 => instidof s1 ++ instidof s2
  | _ => nil
  end.

Definition func: Type := general_node stmt.

Definition predidof(f: func) :=
  map fst (nd_svars f) ++ map instid (instidof (nd_stmt f)).

Definition ids_norepet(f: func) :=
  list_norepet (allidsof f) /\ list_norepet (predidof f)
   /\ list_disjoint (allidsof f) (predidof f) /\ ~ In ACG_I (map fst (nd_args f ++ nd_rets f) ++ predidof f).

Definition program: Type := general_program func.

Definition ids_range(id: ident)(l: list (ident*func)): Prop :=
  forall fd, In fd l -> ids_plt id (allidsof (snd fd) ++ predidof (snd fd)).

Definition call_node(ge: list (ident*func))(nid:ident)(cdef: calldef)(nd fd: ident*func) : Prop :=
  find_funct ge nid = Some nd
     /\ callorder (nd_kind (snd nd)) (nd_kind (snd fd)) = true
     /\ field_type (instid cdef) (nd_fld (snd nd)) = OK
          match callnum cdef with
          | Some j => Tarray xH (mknstruct (snd fd)) (Int.unsigned j)
          | None => mknstruct (snd fd)
          end
     /\ csid cdef = nd_sid (snd fd)
     /\ cfield cdef = nd_fld (snd fd)
     /\ call_func ge cdef fd.

Definition svars_field_match(al:  params)(fld: fieldlist): Prop :=
  exists l, fld = fieldlist_of (al++l).

Definition svars_fld_match(al:  params)(fld: fieldlist): Prop :=
  forall id ty, In (id,ty) al -> field_type id fld = OK ty.

Lemma ids_norepet_instid:
  forall f, ids_norepet f ->
  list_norepet (map instid (instidof (nd_stmt f))).
Proof.
  intros. destruct H as [? [? ?]].
  apply list_norepet_app in H0. intuition.
Qed.

Lemma ids_norepet_insts_svars_disjoint:
  forall f, ids_norepet f ->
  list_disjoint (map fst (svarsof f)) (map instid (instidof (nd_stmt f))) .
Proof.
  intros. destruct H as [? [? [? ?]]].
  apply list_norepet_app in H0.
  unfold predidof, allidsof, allvarsof,svarsof in *.
  rewrite map_app in *.
  apply list_disjoint_app_right in H1. destruct H1.
  apply list_disjoint_app_left in H3.
  apply <-list_disjoint_app_left. intuition.
Qed.

Lemma ids_norepet_rets_svars:
  forall f, ids_norepet f ->
  list_norepet (map fst (nd_rets f ++ nd_svars f)).
Proof.
  intros. destruct H as [? [? [? ?]]].
  unfold allidsof, allvarsof, predidof in *.
  repeat rewrite map_app in *.
  apply list_norepet_app in H. destruct H as [? [? ?]].
  apply list_norepet_app in H0. destruct H0 as [? [? ?]].
  apply list_norepet_app. intuition.
  red; intros. apply H1; apply in_or_app; auto.
Qed.

Lemma ids_norepet_rets_svars_disjoint:
  forall f, ids_norepet f ->
  list_disjoint (map fst (nd_rets f)) (map fst (nd_svars f)).
Proof.
  intros. apply ids_norepet_rets_svars in H.
  rewrite map_app in *.
  apply list_norepet_app in H. intuition.
Qed.

Lemma ids_norepet_rets_norepet:
  forall f, ids_norepet f ->
  list_norepet (map fst (nd_rets f)).
Proof.
  intros. apply ids_norepet_rets_svars in H.
  rewrite map_app in *.
  apply list_norepet_app in H. intuition.
Qed.

Lemma ids_norepet_vars_args_rets_disjoint:
  forall f, ids_norepet f ->
  list_disjoint (map fst (nd_vars f ++ nd_args f)) (map fst (nd_rets f)).
Proof.
  intros. destruct H as [? [? [? ?]]].
  unfold allidsof, allvarsof, predidof in *.
  repeat rewrite map_app in *.
  apply list_norepet_app in H. destruct H as [? [? ?]]. auto.
Qed.

Lemma ids_norepet_args_rets_disjoint:
  forall f, ids_norepet f ->
  list_disjoint (map fst (nd_args f)) (map fst (nd_rets f)).
Proof.
  intros. apply ids_norepet_vars_args_rets_disjoint in H.
  repeat rewrite map_app in *.
  eapply list_disjoint_app_left; eauto.
Qed.

Lemma ids_norepet_loopid_notin_rets:
  forall f, ids_norepet f ->
  ~ In ACG_I (map fst (nd_rets f)).
Proof.
  intros. destruct H as [? [? [? ?]]].
  red; intros. apply H2. rewrite map_app.
  apply in_or_app. left. apply in_or_app; auto.
Qed.

Lemma ids_plt_not_in:
  forall l nid f id,
  find_funct l nid = Some (nid, f) ->
  ids_range id l ->
  ~ In id (map fst (lvarsof f)).
Proof.
  intros.
  apply find_funct_in2 in H.
  apply H0 in H. simpl in *.
  apply ids_plt_le_notin with id _ _ in H; auto.
  red. intros. apply H. apply in_or_app. left.
  unfold allidsof, allvarsof. rewrite map_app.
  apply in_or_app; auto.
  apply Ple_refl; auto.
Qed.

Lemma instidof_cakind_true:
  forall s c, In c (instidof s) -> cakind c = true.
Proof.
  induction s; simpl; auto.
  +unfold cons_inst. intros.
   destruct (cakind c) eqn:?; simpl in *.
   destruct H; subst; auto. inv H.
  +intros. apply in_app_or in H. destruct H; auto.
  +intros. apply in_app_or in H. destruct H; auto.
Qed.
