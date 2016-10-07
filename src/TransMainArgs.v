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

(** Translate input parameters of main node into a struct parameter. *)

Require Import Coqlib.
Require Import AST.
Require Import Integers.
Require Import Errors.
Require Import Cltypes.
Require Import Lident.
Require Import Ltypes.
Require Import Lustre.
Require Import LustreR.
Require Import Permutation.

Open Local Scope error_monad_scope.

Fixpoint trans_expr(mkv: mkvar)(e: sexp): sexp :=
  match e with
  | Sconst c ty => Sconst c ty
  | Svar id ty  => mkv id ty
  | Scvar id ty  => Scvar id ty
  | Ssvar id ty  => Ssvar id ty
  | Savar id ty  => Savar id ty
  | Saryacc a1 a2 ty => Saryacc (trans_expr mkv a1) (trans_expr mkv a2) ty
  | Sfield a id ty => Sfield (trans_expr mkv a) id ty
  | Scast a ty => Scast (trans_expr mkv a) ty
  | Sunop op a ty => Sunop op (trans_expr mkv a) ty
  | Sbinop op a1 a2 ty => Sbinop op (trans_expr mkv a1) (trans_expr mkv a2) ty
  end.

Definition trans_exprs(mkv: mkvar)(l: list sexp): list sexp :=
  map (trans_expr mkv) l.

Definition trans_loopexp(mkv: mkvar)(oid: option sexp): option sexp :=
  match oid with
  | None => None
  | Some a => Some (trans_expr mkv a)
  end.

Definition trans_eqf(mkv: mkvar)(s: eqf): eqf :=
  (trans_expr mkv (fst s), trans_expr mkv (snd s)).

Fixpoint trans_stmt(mkv: mkvar)(s: stmt): stmt :=
  match s with
  | Sassign a1 a2 => Sassign (trans_expr mkv a1) (trans_expr mkv a2)
  | Scall oid lh cdef al =>
      Scall oid (trans_exprs mkv lh) cdef (trans_exprs mkv al)
  | Sfor s1 a s2 s3 =>
    Sfor (option_map (trans_eqf mkv) s1) (trans_expr mkv a) (trans_eqf mkv s2) (trans_stmt mkv s3)
  | Sseq s1 s2 => Sseq (trans_stmt mkv s1) (trans_stmt mkv s2)
  | Sskip => Sskip
  | Sifs a s1 s2 => Sifs (trans_expr mkv a) (trans_stmt mkv s1) (trans_stmt mkv s2)
  | Scase a1 a2 pl => Scase (trans_expr mkv a1) (trans_expr mkv a2) (trans_patns (trans_expr mkv) pl)
  | Sfby lh id a1 a2 => Sfby (trans_expr mkv lh) id (trans_expr mkv a1) (trans_expr mkv a2)
  | Sfbyn lh ids i a1 a2 => Sfbyn (trans_expr mkv lh) ids i (trans_expr mkv a1) (trans_expr mkv a2)
  | Sarrow lh a1 a2 => Sarrow (trans_expr mkv lh) (trans_expr mkv a1) (trans_expr mkv a2)
  | Stypecmp lh a1 a2 => Stypecmp (trans_expr mkv lh) (trans_expr mkv a1) (trans_expr mkv a2)
  end.

Definition trans_v(ids: list ident)(e: sexp)(id: ident)(ty: type): sexp :=
  if in_list id ids then
    Sfield e id ty (*inC->Input1*)
  else Svar id ty.

Definition mkstruct(fd: ident*node): type :=
  Tstruct (in_struct_type (fst fd)) (fieldlist_of (nd_args (snd fd))).

Definition makevar(fd: ident*node): mkvar :=
  let ids := map fst (nd_args (snd fd)) in
  let sty := mkstruct fd in
  trans_v ids (Svar INSTRUCT sty).

Definition trans_body(fd: ident*node): node :=
  let b := snd fd in
  let nid := fst fd in
  let ids := map fst (nd_args b) in
  let sty := mkstruct fd in
  let mkv := trans_v ids (Svar INSTRUCT sty) in
  let s := trans_stmt mkv (nd_stmt b) in
  (mknode true ((INSTRUCT, sty)::nil) (nd_rets b) (nd_svars b) (nd_vars b)
     s b.(nd_sid) b.(nd_fld)).

Definition trans_node_kind(fd: ident*node): ident*node :=
  let b := snd fd in
  (fst fd, mknode true (nd_args b) (nd_rets b) (nd_svars b) (nd_vars b) (nd_stmt b) b.(nd_sid) b.(nd_fld)).

Definition trans_node(fd: ident*node): ident*node :=
  if beq_nat (length (nd_args (snd fd))) 0 then
    trans_node_kind fd
  else (fst fd,trans_body fd).

Fixpoint trans_nodes(mid: ident)(l: list (ident*node)): list (ident*node) :=
  match l with
  | nil => nil
  | fd :: tl =>
     if identeq (fst fd) mid then
       trans_node fd :: tl
     else fd :: trans_nodes mid tl
  end.

Definition mksdef(nid: ident)(b: node): res (ident* type)  :=
  let sty := mkstruct (nid,b) in
  if zlt 0 (sizeof sty) && zle (sizeof sty) Int.max_signed then
    OK (in_struct_type nid, sty)
  else Error (msg "sizeof type is overflow!").

Definition trans_sty(mid: ident)(nodes: list (ident*node)): res (list (ident* type)) :=
  match find_funct nodes mid with
  | Some fd =>
    if beq_nat (length (nd_args (snd fd))) 0 then OK nil
    else
      do sty <- mksdef (fst fd) (snd fd);
      OK (sty:: nil)
  | None => Error (msg "Cannot find main node!")
  end.

Definition trans_program (p: program): res program :=
  let nodes := trans_nodes (node_main p) (node_block p)  in
  do sty <- trans_sty (node_main p) (node_block p);
  if list_in_list (map fst sty) (globidsof p) then
    Error (msg "TransMainArgs: in_struct_type are in global names!")
  else
  OK (mkprogram (type_block p) (defs_block p++sty) (const_block p) nodes (node_main p)).

Lemma trans_stmts_instidof_eq:
  forall s mkv,
  instidof (trans_stmt mkv s) = instidof s.
Proof.
  induction s; intros; simpl; auto; f_equal; auto.
Qed.

Lemma trans_expr_get_lids:
  forall fd lh,
  get_lids (trans_expr (makevar fd) lh) = get_lids lh \/ get_lids (trans_expr (makevar fd) lh) = INSTRUCT :: nil.
Proof.
  induction lh; simpl; auto.
  unfold makevar, trans_v. intros.
  destruct (in_list _ _); auto.
Qed.

Lemma trans_expr_typeof:
  forall a fd,
  typeof (trans_expr (makevar fd) a) = typeof a.
Proof.
  induction a; simpl; intros; auto.
  unfold makevar, trans_v.
  destruct (in_list _ _); auto.
Qed.

Lemma trans_exprs_typeof:
  forall fd args, map typeof (trans_exprs (makevar fd) args) = map typeof args.
Proof.
  unfold trans_exprs. intros.
  rewrite map_map. apply map_ext.
  intros. apply trans_expr_typeof; auto.
Qed.

Lemma trans_body_fbyvarsof:
  forall s fd,
  fbyvarsof (trans_stmt (makevar fd) s) = fbyvarsof s .
Proof.
  induction s; simpl; intros; auto;
  f_equal; auto.
  +rewrite trans_expr_typeof; auto.
  +destruct p. destruct p. f_equal. f_equal.
   f_equal. rewrite trans_expr_typeof; auto.
Qed.

Lemma trans_stmt_fbyeqof_length:
  forall mkv s, length (fbyeqof (trans_stmt mkv s)) = length (fbyeqof s).
Proof.
  induction s; simpl; auto.
  repeat rewrite app_length; auto.
  destruct p. destruct p. auto.
  repeat rewrite app_length; auto.
Qed.

Lemma trans_body_ids_norepeat:
  forall f fid,
  ids_norepet f ->
  ids_plt INSTRUCT (allidsof f ++ predidof f) ->
  ids_norepet (trans_body (fid,f)).
Proof.
  unfold ids_norepet, ids_norepet.
  unfold allidsof,predidof.
  intros. unfold trans_body, allvarsof in *.
  generalize (trans_body_fbyvarsof (nd_stmt f) (fid,f)).
  unfold makevar; simpl; intros.
  rewrite H1. rewrite trans_stmts_instidof_eq.
  apply ids_plt_le_notin with INSTRUCT _ _ in H0;
   try (unfold Ple; omega).
  repeat rewrite map_app in *. intuition.
  +rewrite app_ass in *. apply list_norepet_app.
   apply list_norepet_app in H2. destruct H2 as [? [? ?]].
   apply list_norepet_app in H4. destruct H4 as [? [? ?]].
   simpl; intuition.
   -constructor; auto. red; intros.
    apply H0. apply in_or_app. right.
    apply in_or_app; auto.
   -red; simpl; intros. destruct H10; subst.
    *red; intros. subst. apply H0.
     apply in_or_app. left.
     apply in_or_app; auto.
    *apply H6; auto. apply in_or_app; auto.
  +red; simpl; intros.
   apply in_app_or in H4. destruct H4.
   apply in_app_or in H4. destruct H4; simpl in *.
   -apply H3; auto. apply in_or_app. left.
    apply in_or_app; auto.
   -destruct H4; subst. red; intros.
    apply H0. subst. apply in_or_app; auto.
    destruct H4.
   -apply H3; auto. apply in_or_app; auto.
  +unfold INSTRUCT, ACG_I in *. congruence.
  +apply H5. rewrite app_ass. apply in_or_app; auto.
Qed.

Lemma trans_node_ids_plt:
  forall fd,
  ids_plt ACG_INIT (allidsof (snd fd) ++ predidof (snd fd)) ->
  ids_plt ACG_INIT (allidsof (trans_body fd) ++ predidof (trans_body fd)).
Proof.
  unfold allidsof, allvarsof, predidof. intros. simpl.
  rewrite trans_body_fbyvarsof with (fd:=fd).
  unfold makevar in *. simpl in *. repeat rewrite map_app in *.
  rewrite trans_stmts_instidof_eq.
  red; intros. apply in_app_or in H0. destruct H0.
  +apply in_app_or in H0. destruct H0.
   -apply in_app_or in H0. destruct H0.
    *apply H; auto. apply in_or_app; left.
     apply in_or_app; left. apply in_or_app; auto.
    *simpl in *. destruct H0; subst.
     unfold Plt, ACG_INIT, INSTRUCT. omega.
     tauto.
   -apply H; auto. apply in_or_app; left.
    apply in_or_app; auto.
  +apply H; auto. apply in_or_app; auto.
Qed.

Lemma trans_nodes_in:
  forall fd id l,
  In fd (trans_nodes id l) ->
  In fd l \/ (exists fd', In fd' l /\ trans_node fd' = fd).
Proof.
  induction l; simpl; intros.
  +destruct H.
  +destruct (identeq (fst a) id) eqn:?; simpl in *.
   destruct (beq_nat (length (nd_args (snd a))) 0) eqn:?; simpl in *.
   -destruct H; subst; auto.
    right. exists a. split; auto.
   -destruct H; subst; auto. right.
    exists a. split; auto.
   -destruct H; subst; auto.
    apply IHl in H; auto.
    destruct H; auto. right.
    destruct H as [fd' [? ?]].
    exists fd'. split; auto.
Qed.

Lemma trans_program_ids_range:
  forall p1 p2, trans_program p1 = OK p2 ->
  ids_range INSTRUCT (node_block p1) ->
  ids_range ACG_INIT (node_block p2).
Proof.
  unfold ids_range. intros.
  monadInv H.
  destruct (list_in_list _ _) eqn:?; inv EQ0.
  simpl in *.
  eapply trans_nodes_in in H1; eauto.
  destruct H1 as [? | [fd' [? ?]]]; auto.
  +apply H0 in H; auto.
   eapply ids_plt_trans; eauto.
   unfold Ple, ACG_INIT, INSTRUCT. omega.
  +rewrite <-H1. apply H0 in H.
   unfold trans_node. destruct (beq_nat _ _); simpl; auto.
   -apply ids_plt_trans with INSTRUCT; auto.
    unfold Ple, ACG_INIT, INSTRUCT. omega.
   -eapply trans_node_ids_plt; eauto.
    apply ids_plt_trans with INSTRUCT; auto.
    unfold Ple, ACG_INIT, INSTRUCT. omega.
Qed.

Lemma trans_nodes_ids:
  forall id l,
  map fst (trans_nodes id l) = map fst l.
Proof.
  induction l; simpl; intros; auto.
  destruct (identeq _ _); simpl; try congruence.
  unfold trans_node.
  destruct (beq_nat _ _); auto.
Qed.

Lemma node_block_simpl:
  forall l id fd, find_funct l id = Some fd ->
  exists l1 l2, l = l1 ++ fd :: l2
    /\ trans_nodes id l = l1 ++ (trans_node fd) :: l2.
Proof.
  induction l; simpl; intros.
  +congruence.
  +remember (identeq _ _). destruct b.
   -inv H. exists nil, l. unfold node in *.
    simpl. auto.
   -destruct IHl with id fd as [l1 [l2 [? ?]]]; auto.
    exists (a::l1), l2. simpl. subst l. rewrite H1; auto.
Qed.

Lemma trans_sty_norepet:
  forall mid l tys,
  trans_sty mid l = OK tys ->
  list_norepet (map fst tys).
Proof.
  unfold trans_sty. intros.
  destruct (find_funct _ _) eqn:?; try congruence.
  destruct (beq_nat _ _) eqn:?.
  inv H. constructor.
  monadInv H. constructor. auto. constructor.
Qed.

Lemma trans_program_globidspltof:
  forall p p',
  trans_program p = OK p' ->
  globidspltof p' = globidspltof p.
Proof.
  unfold trans_program, globidspltof. intros.
  monadInv H. destruct (list_in_list _ _) eqn:?; inv EQ0.
  simpl. rewrite trans_nodes_ids. auto.
Qed.

Lemma trans_program_gids_norepet:
  forall p p',
  trans_program p = OK p' ->
  list_norepet (globidsof p) ->
  list_norepet (globidsof p').
Proof.
  unfold trans_program, globidsof. intros.
  monadInv H. destruct (list_in_list _ _) eqn:?; inv EQ0.
  apply list_in_list_disjoint in Heqb; auto.
  simpl in *.
  apply list_norepet_permut with (map fst x ++ (map fst (type_block p ++ defs_block p)
        ++ map fst (const_block p)) ++ map fst (node_block p)); auto.
  +apply list_norepet_app; auto. repeat (split; auto).
   eapply trans_sty_norepet; eauto.
  +rewrite trans_nodes_ids. repeat rewrite map_app.
   repeat rewrite <-app_ass. repeat apply Permutation_app_tail.
   rewrite app_ass. apply Permutation_app_swap.
Qed.
