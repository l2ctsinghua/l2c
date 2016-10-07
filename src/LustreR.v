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
Require Import Cltypes.
Require Import ExtraList.
Require Import Lident.
Require Import Ltypes.
Require Import Lustre.

Inductive stmt: Type :=
  | Sassign: sexp -> sexp -> stmt
  | Scall: option sexp -> list sexp -> calldef -> list sexp -> stmt
  | Sfor: option eqf -> sexp -> eqf -> stmt -> stmt
  | Sifs: sexp -> stmt -> stmt -> stmt
  | Scase: sexp -> sexp -> list (patn * sexp) -> stmt
  | Sfby: sexp -> ident -> sexp -> sexp -> stmt
  | Sfbyn: sexp -> ident*ident*ident -> int -> sexp -> sexp -> stmt
  | Sarrow: sexp -> sexp -> sexp -> stmt
  | Sseq: stmt -> stmt -> stmt
  | Stypecmp:  sexp -> sexp -> sexp -> stmt
  | Sskip: stmt.

Fixpoint fbyvarsof(s: stmt): params:=
  match s with
  | Sseq s1 s2 => fbyvarsof s1 ++ fbyvarsof s2
  | Sfor _ _ _ s => fbyvarsof s
  | Sifs _ s1 s2 => fbyvarsof s1 ++ fbyvarsof s2
  | Sfby lh id a1 a2 => (id,typeof a1)::nil
  | Sfbyn lh (id1,id2,aid) i a1 a2 =>
     let aty := Tarray aid (typeof a1) (Int.unsigned i) in
     (id1,make_fbyn_type id2 aty)::nil
  | _ => nil
  end.

Fixpoint fbyeqof(s: stmt): list eqt :=
  match s with
  | Sseq s1 s2 =>fbyeqof s1 ++ fbyeqof s2
  | Sfor _ _ _ s => fbyeqof s
  | Sifs _ s1 s2 => fbyeqof s1 ++ fbyeqof s2
  | Sfby lh id a1 a2 => (Eqt_assign (Svar id (typeof a1), a1))::nil
  | Sfbyn lh (id1,id2,aid) i a1 a2 =>
     let aty := Tarray aid (typeof a1) (Int.unsigned i) in
     let sty := make_fbyn_type id2 aty in
     let sa := Svar id1 sty in
     let eq1 := (Eqt_assign (Saryacc (Sfield sa FBYITEM aty) (Sfield sa FBYIDX type_int32s) (typeof a1), a1)) in
     let eq2 := (Eqt_counter (index_incr sa i)) in
     eq1 :: eq2 :: nil
  | Sarrow _ _ _ => Eqt_skip :: nil
  | _ => nil
  end.

Fixpoint instidof(s: stmt): list calldef :=
  match s with
  | Scall _ _ c _ => cons_inst c
  | Sfor _ _ _ s1 => instidof s1
  | Sifs _ s1 s2 => instidof s1 ++ instidof s2
  | Sseq s1 s2 => instidof s1 ++ instidof s2
  | _ => nil
  end.

Definition node: Type := general_node stmt.

Fixpoint get_stmt_nids(s: stmt): list ident :=
  match s with
  | Scall _ _ c _ => callid c :: nil
  | Sfor s1 _ s2 s3 => get_stmt_nids s3
  | Sifs _ s1 s2 => get_stmt_nids s1 ++ get_stmt_nids s2
  | Sseq s1 s2 => get_stmt_nids s1 ++ get_stmt_nids s2
  | _ => nil
  end.

Definition callidof(nd: ident*node): list ident :=
  get_stmt_nids (nd_stmt (snd nd)).

Definition dep_of_node(fd: ident*node): depend :=
  mkdepend (fst fd :: nil) (callidof fd) O.

Definition deps_of_nodes (nodes: list (ident*node)) : list depend :=
  map dep_of_node nodes.

Definition predidof(f: node) :=
  map fst (fbyvarsof (nd_stmt f)) ++ map instid (instidof (nd_stmt f)).

Definition ids_norepet(f: node) :=
  list_norepet (allidsof f) /\ list_norepet (predidof f)
   /\ list_disjoint (allidsof f) (predidof f)
   /\ ~ In ACG_I (map fst (nd_args f ++ nd_rets f) ++ predidof f).

Definition program: Type := general_program node.

Definition ids_range(id: ident)(l: list (ident*node)): Prop :=
  forall fd, In fd l -> ids_plt id (allidsof (snd fd) ++ predidof (snd fd)).

Lemma listdependonlist_disjoint:
  forall l1 l2,
  listdependonlist (map dep_of_node l1) (map dep_of_node l2) = false ->
  list_disjoint (flat_map callidof l1)(map (fst (B:=node)) l2).
Proof.
  unfold listdependonlist. intros.
  repeat rewrite flat_map_map in *. simpl in *.
  rewrite flat_map_simpl in H.
  apply list_in_list_disjoint; auto.
Qed.

Lemma topo_sorted_callids_notin:
  forall l fd,
  topo_sorted (map dep_of_node (l++fd::nil)) ->
  ~ In (fst fd) (flat_map callidof (l ++ fd :: nil)).
Proof.
  unfold callidof, dep_of_node.
  intros. rewrite map_app in H.
  apply toposort_app in H. destruct H as [? []].
  apply listdependonlist_disjoint in H1.
  unfold callidof in *.
  apply list_disjoint_sym in H1.
  unfold list_disjoint in H1. simpl in *.
  repeat rewrite flat_map_app.
  apply not_in_app_inv; auto.

  red; intros. eapply H1; eauto.

  unfold dependonlist in H0. simpl in *.
  destruct H0. rewrite list_in_list_swap in H0.
  apply list_in_list_disjoint in H0.
  unfold list_disjoint in H0.
  destruct fd; simpl in *.
  rewrite <-app_nil_end.
  red; intros. eapply H0; eauto.
Qed.

Lemma get_stmt_nids_incl:
  forall nid f l, In (nid, f) l ->
  incl (get_stmt_nids (nd_stmt f)) (flat_map callidof l).
Proof.
  intros.
  change (get_stmt_nids (nd_stmt f)) with (callidof (nid,f)).
  eapply flat_map_in; eauto.
Qed.

Lemma ids_norepet_args_norepet:
  forall f, ids_norepet f ->
  list_norepet (map fst (nd_args f)).
Proof.
  intros. destruct H as [? [? ?]].
  unfold allidsof, allvarsof in H.
  repeat rewrite map_app in H. apply list_norepet_app in H.
  destruct H as [? [? ?]]. apply list_norepet_app in H.
  intuition.
Qed.

Lemma ids_norepet_rets_norepet:
  forall f, ids_norepet f ->
  list_norepet (map fst (nd_rets f)).
Proof.
  intros.  destruct H as [? [? ?]].
  unfold allidsof, allvarsof in H.
  repeat rewrite map_app in H. apply list_norepet_app in H.
  intuition.
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

Lemma ids_range_le:
  forall id1 id2 l,
  ids_range id1 l ->
  Ple id2 id1 ->
  ids_range id2 l.
Proof.
  unfold ids_range. intros.
  apply H in H1; auto.
  eapply ids_plt_trans; eauto.
Qed.

Lemma instid_get_stmt_nids:
  forall s, incl (map callid (instidof s)) (get_stmt_nids s).
Proof.
  induction s; simpl; auto; red; intros; auto.
  +unfold cons_inst in *. destruct (cakind c); simpl in *; auto.
  +rewrite map_app in *. apply in_app_or in H.
   destruct H; apply in_or_app; auto.
  +rewrite map_app in *. apply in_app_or in H.
   destruct H; apply in_or_app; auto.
Qed.