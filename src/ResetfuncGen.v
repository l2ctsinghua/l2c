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

(** Translation of reset functions. *)

Require Import Coqlib.
Require Import AST.
Require Import Integers.
Require Import Errors.
Require Import Cltypes.
Require Import Lident.
Require Import Ltypes.
Require Import Lustre.
Require Import LustreF.
Require Import Permutation.

Open Local Scope error_monad_scope.

Definition trans_calldef(c: calldef): calldef :=
  mkcalldef (cakind c) (instid c) (reset_id (callid c)) (callnum c) (csid c) (cfield c) nil nil.

Definition cons_for(fs: stmt)(i: int) :=
  Sfor (Some loop_init) (loop_cond i) loop_add fs.

Definition trans_init_calldef(c: calldef): stmt :=
  match (callnum c) with
  | Some j =>
      cons_for (Scall (Some (Svar ACG_I type_int32s)) nil (trans_calldef c) nil) j
  | None =>
      Scall None nil (trans_calldef c) nil
  end.

Fixpoint trans_init_stmt(l: list calldef): stmt :=
  match l with
  | nil => Sskip
  | cons c tl =>
    Sseq (trans_init_calldef c) (trans_init_stmt tl)
  end.

Fixpoint mkloopid(l: list calldef): list (ident*type) :=
  match l with
  | nil => nil
  | cons c tl =>
    match callnum c with
    | Some j => (ACG_I,type_int32s) :: nil
    | None => mkloopid tl
    end
  end.

Definition trans_init_body(b: func): func :=
  let init := Sassign (Ssvar ACG_INIT type_bool) (Sconst (Cbool true) type_bool) in
  let cl := instidof (nd_stmt b) in
  let s := trans_init_stmt cl in
  let s' := match nd_svars b with
            | nil => s
            | _ => Sseq init s
            end in
  (mknode b.(nd_kind) nil nil (nd_svars b) (mkloopid cl)
           s' b.(nd_sid) b.(nd_fld)).

Definition trans_init_node(fd: ident*func) :=
  (reset_id (fst fd), trans_init_body (snd fd)).

Definition trans_init_nodes(fd: ident*func) :=
  if nd_kind (snd fd) then trans_init_node fd :: nil else nil.

Definition trans_program (p: program): res program :=
  let inits := flat_map trans_init_nodes (node_block p)  in
  if list_in_list (map fst inits) (ACG_I :: globidsof p) then
    Error (msg "ResetfuncGen: reset funcs are in global names!")
  else
    OK (mkprogram (type_block p) (defs_block p) (const_block p) (inits ++ node_block p) (node_main p)).

Lemma trans_init_stmt_cons_inst:
  forall c, instidof (trans_init_stmt (cons_inst c)) = map trans_calldef (cons_inst c).
Proof.
  destruct c. destruct cakind; simpl; auto.
  destruct callnum; auto.
Qed.

Lemma trans_init_stmt_instidof_app:
  forall l1 l2,
  instidof (trans_init_stmt (l1 ++ l2)) = instidof (trans_init_stmt l1) ++ instidof (trans_init_stmt l2).
Proof.
  induction l1; simpl; intros; auto.
  rewrite IHl1. rewrite app_ass; auto.
Qed.

Lemma trans_init_stmt_instidof:
  forall s, instidof (trans_init_stmt (instidof s)) = map trans_calldef (instidof s).
Proof.
  induction s; simpl; auto.
  +apply trans_init_stmt_cons_inst; auto.
  +rewrite map_app. rewrite <-IHs1,<-IHs2.
   apply trans_init_stmt_instidof_app.
  +rewrite map_app. rewrite <-IHs1,<-IHs2.
   apply trans_init_stmt_instidof_app.
Qed.

Lemma mkloopid_range:
  forall l, mkloopid l = (ACG_I, type_int32s) :: nil \/ mkloopid l = nil.
Proof.
  induction l; simpl; auto.
  destruct (callnum a); auto.
Qed.

Lemma trans_init_body_instidof:
  forall f, instidof (nd_stmt (trans_init_body f)) = map trans_calldef (instidof (nd_stmt f)).
Proof.
  simpl. intros.
  destruct (nd_svars f); simpl;
  rewrite trans_init_stmt_instidof; auto.
Qed.

Lemma trans_init_body_ids_norepet:
  forall f, ids_norepet f ->
  ids_norepet (trans_init_body f).
Proof.
  unfold ids_norepet, allidsof, allvarsof, predidof.
  intros.
  rewrite trans_init_body_instidof.
  simpl. repeat rewrite <-app_nil_end.
  rewrite map_map. simpl. intuition.
  +destruct mkloopid_range with (instidof (nd_stmt f)); rewrite H2;
   constructor; auto. constructor.
  +red. simpl; intros.
   destruct mkloopid_range with (instidof (nd_stmt f));
   rewrite H5 in *; simpl in *; auto.
   destruct H2; auto.
   subst. red; intros. apply H3; auto.
   subst. apply in_or_app. auto.
Qed.

Lemma trans_init_body_ids_plt:
  forall f, ids_plt OUTSTRUCT (allidsof f ++ predidof f) ->
  ids_plt OUTSTRUCT (allidsof (trans_init_body f) ++ predidof (trans_init_body f)).
Proof.
  unfold predidof. intros. rewrite trans_init_body_instidof.
  unfold ids_plt, trans_init_body, allidsof, allvarsof in *.
  simpl in *; intros. repeat rewrite <-app_nil_end in *.
  apply in_app_or in H0. destruct H0.
  +destruct mkloopid_range with (instidof (nd_stmt f));
   rewrite H1 in *; simpl in *; auto.
   destruct H0; subst; auto.
   unfold Plt, OUTSTRUCT, ACG_I. omega.
   tauto. tauto.
  +apply H. apply in_or_app; right.
   rewrite map_map in H0. simpl in *. auto.
Qed.

Lemma trans_program_ids_range:
  forall p p', trans_program p = OK p' ->
  ids_range OUTSTRUCT (node_block p) ->
  ids_range OUTSTRUCT (node_block p').
Proof.
  unfold trans_program. intros.
  destruct (list_in_list _ _); inv H. simpl.
  red. intros.
  apply in_app_or in H. destruct H; auto.
  apply in_flat_map in H. destruct H as [? [? ?]].
  apply H0 in H. unfold trans_init_nodes in *.
  destruct (nd_kind _); simpl in *; try tauto.
  destruct H1; try tauto; subst.
  apply trans_init_body_ids_plt; auto.
Qed.

Lemma trans_init_nodes_map_in:
  forall id l,
  In (reset_id id) (map fst (flat_map trans_init_nodes l)) ->
  In id (map fst l).
Proof.
  induction l; simpl; intros; auto.
  rewrite map_app in *. apply in_app_or in H.
  destruct H; auto.
  unfold trans_init_nodes in *.
  destruct (nd_kind (snd a)); simpl in *; try tauto.
  destruct H; try tauto.
  left. apply Pos.add_reg_r with 3%positive; auto.
Qed.

Lemma reset_ids_map_in:
  forall fd l,
  In fd l -> nd_kind (snd fd) = true ->
  In (reset_id (fst fd)) (map fst (flat_map trans_init_nodes l)).
Proof.
  induction l; simpl; intros; auto.
  rewrite map_app. apply in_or_app.
  destruct H; subst; auto.
  left. unfold trans_init_nodes.
  unfold func in *. rewrite H0.
  simpl. auto.
Qed.

Lemma trans_init_nodes_norepet:
  forall l, list_norepet (map fst l) ->
  list_norepet (map fst (flat_map trans_init_nodes l)).
Proof.
  induction l; simpl; intros; inv H.
  constructor.
  unfold trans_init_nodes at 1.
  destruct (nd_kind (snd a)); simpl; auto.
  constructor 2; auto. red; intros. apply H2.
  apply trans_init_nodes_map_in; auto.
Qed.

Lemma trans_program_gids_norepet:
  forall p p', trans_program p = OK p' ->
  list_norepet (globidsof p) ->
  list_norepet (globidsof p').
Proof.
  unfold trans_program, globidsof. intros.
  destruct (list_in_list _ _) eqn:?; inv H.
  apply list_in_list_disjoint in Heqb; auto.
  apply list_disjoint_cons_right in Heqb.
  simpl in *.
  apply list_norepet_permut with (map fst (flat_map trans_init_nodes (node_block p)) ++ (map fst (type_block p ++ defs_block p)
        ++ map fst (const_block p)) ++ map fst (node_block p)); auto.
  +apply list_norepet_app; auto. repeat (split; auto).
   apply list_norepet_app in H0. destruct H0 as [? [? ?]].
   apply trans_init_nodes_norepet; auto.
  +repeat rewrite map_app.
   repeat rewrite <-app_ass. apply Permutation_app_tail.
   apply Permutation_trans with (map fst (flat_map trans_init_nodes (node_block p)) ++ (((map fst (type_block p) ++ map fst (defs_block p)) ++
       map fst (const_block p)))); auto.
   -repeat rewrite app_ass. apply Permutation_refl.
   -apply Permutation_app_swap.
Qed.
