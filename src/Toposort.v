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
Require Import List.
Require Import ExtraList.
Require Import Permutation.
Require Import Lident.
Require Import Ltypes.
Require Import Lustre.
Require Import LustreS.

Open Local Scope error_monad_scope.

Definition get_nodeps (ll: list ident)(deps: list depend): (list depend)  * (list depend)  :=
  partition (fun dep =>list_in_list (ridl dep) ll) deps.

Fixpoint toposort_deps (max: nat)(deps: list depend): res (list depend) :=
  match max with
  | O => OK nil
  | S max' =>
      let (l1,l2) := get_nodeps (flat_map lidl deps) deps in
      match l2 with
      | nil =>
        match l1 with
        | nil =>  OK nil
        | cons hd tl => Error (msg "has a cycle!!")
        end
      | cons hd tl =>
        match (toposort_deps max' l1) with
        | OK l1' => OK (l2 ++ l1')
        | _ => Error (msg "has a cycle!!")
        end
      end
  end.

Definition toposort_stmts (eqs: list stmt) : res (list stmt):=
  let depl :=  deps_of_stmts eqs in
  do depl' <- toposort_deps (length depl) depl;
  let ids := map seqn depl' in
  OK (map (fun id => nth id eqs Sskip) ids).

Definition toposort_node (b: node) : res node :=
  do eqs' <- toposort_stmts b.(nd_stmt);
  OK (mknode b.(nd_kind) b.(nd_args) b.(nd_rets) nil b.(nd_vars) eqs' b.(nd_sid) b.(nd_fld)).

Definition get_hstmt_nid  (h: hstmt): list ident :=
  match h with
  | Hmapcall _ c _ => callid c :: nil
  | Hmapfoldcall _ _ _ c _ _ => callid c :: nil
  | _ => nil
  end.

Definition get_stmt_nid  (eq: stmt): list ident :=
  match eq with
  | Scall _ c _ => callid c :: nil
  | Sfor _ h _ => get_hstmt_nid h
  | _ => nil
  end.

Definition deps_of_node (nodes: list (ident*node))(n: nat): depend :=
  let nd := nth n nodes nodenil in
  mkdepend (fst nd :: nil) (flat_map get_stmt_nid (nd_stmt (snd nd))) n.

Definition deps_of_nodes (nodes: list (ident*node)): list depend :=
  map (deps_of_node nodes) (seq O (length nodes)).

Definition deps_of_nodes_simpl (nodes: list (ident*node)) : list depend :=
  map (fun fd => mkdepend (fst fd :: nil) (flat_map get_stmt_nid (nd_stmt (snd fd))) O) nodes.

Definition toposort_nodes (nodes: list (ident*node)) : res (list (ident*node)):=
  let depl := deps_of_nodes nodes in
  do depl' <- toposort_deps (length depl) depl;
  let ids := map seqn depl' in
  OK (map (fun id => nth id nodes nodenil) ids).

Definition trans_node_block (f: ident*node) : res (ident*node) :=
  do body <- toposort_node (snd f);
  OK (fst f, body).

Definition toposort_nodes_program (p: program): res program :=
  do nodes <- toposort_nodes p.(node_block);
  OK (mkprogram p.(type_block) p.(defs_block) p.(const_block) nodes p.(node_main)).

Definition toposort_stmts_program (p: program): res program :=
  do nodes <- mmap trans_node_block p.(node_block);
  OK (mkprogram p.(type_block) p.(defs_block) p.(const_block) nodes p.(node_main)).

Theorem toposort_deps_permutation:
  forall (len: nat)(l l1: list depend),
  (length l <= len)%nat ->
  toposort_deps len l = OK l1 ->
  Permutation l l1.
Proof.
  intros len; elim len; simpl; intros.
  inv H0. destruct l. constructor. inv H.

  remember (flat_map lidl l) as idll.
  remember (get_nodeps idll l) as p.
  destruct p. unfold get_nodeps in *.
  apply partition_permutation in Heqp.
  apply Permutation_trans with (l0 ++ l2); trivial.
  destruct l2.
  destruct l0; inv H1. simpl. apply Permutation_refl.
  remember (toposort_deps n l0).
  destruct r; inv H1.
  apply Permutation_sym.
  apply Permutation_cons_app.
  apply Permutation_trans with (l2 ++ l0).
  apply Permutation_app_head.
  apply Permutation_sym.
  apply H; auto.
  apply Permutation_length in Heqp.
  rewrite app_length in Heqp. simpl in Heqp. omega.
  apply Permutation_app_swap.
Qed.

Lemma deps_of_stmts_map: forall (eqs: list stmt),
  seq O (length eqs) = map seqn (deps_of_stmts eqs).
Proof.
  intros.  unfold deps_of_stmts.
  rewrite map_map; simpl. apply seq_map_equal.
Qed.

Theorem toposort_stmts_permutation :
  forall eqs eqs',
  toposort_stmts eqs = OK eqs' ->
  Permutation eqs eqs'.
Proof.
  intros. monadInv H.
  apply seq_nth_perm.
  rewrite deps_of_stmts_map.
  apply Permutation_map.
  apply toposort_deps_permutation in EQ; auto.
Qed.


Lemma deps_of_nodes_map: forall (nodes: list (ident*node)),
  seq O (length nodes) = map seqn (deps_of_nodes nodes).
Proof.
  intros; unfold deps_of_nodes.
  rewrite map_map. simpl. apply seq_map_equal.
Qed.

Theorem toposort_nodes_permutation :
  forall l l',
  toposort_nodes l = OK l' ->
  Permutation l l'.
Proof.
  intros. monadInv H.
  apply seq_nth_perm.
  rewrite deps_of_nodes_map.
  apply Permutation_map.
  apply toposort_deps_permutation in EQ; auto.
Qed.

Lemma toposort_nodes_program_ids_range:
  forall p p',
  toposort_nodes_program p = OK p' ->
  ids_range ACG_B (node_block p) ->
  ids_range ACG_B (node_block p').
Proof.
  red; intros.
  monadInv H. simpl in *.
  apply toposort_nodes_permutation in EQ.
  apply Permutation_sym in EQ.
  apply Permutation_in with (l':=node_block p) in H1; auto.
Qed.

Lemma toposort_nodes_program_gids_range:
  forall id p p',
  toposort_nodes_program p = OK p' ->
  ids_plt id (globidspltof p) ->
  ids_plt id (globidspltof p').
Proof.
  red; intros. apply in_app_or in H1. apply H0. apply in_or_app.
  monadInv H. simpl in *. destruct H1; auto. right.
  apply in_app_or in H. apply in_or_app.
  destruct H; auto. right.
  apply toposort_nodes_permutation in EQ.
  apply Permutation_sym in EQ.
  apply Permutation_map with (f:=fst) in EQ.
  eapply Permutation_in; eauto.
Qed.

Lemma toposort_stmts_program_ids_range:
  forall p p',
  toposort_stmts_program p = OK p' ->
  ids_range ACG_B (node_block p) ->
  ids_range ACG_B (node_block p').
Proof.
  red; intros.
  monadInv H. simpl in *.
  eapply in_mmap_iff in EQ; eauto.
  destruct EQ as [fd' [? ?]].
  apply H0 in H2.
  monadInv H. monadInv EQ.
  unfold allidsof, allvarsof, predidof in *.
  simpl in *. red; intros.
  apply H2. apply in_app_or in H.
  destruct H; apply in_or_app; auto.
  right. apply toposort_stmts_permutation in EQ0.
  apply in_app_or in H. apply Permutation_sym in EQ0; auto.
  destruct H; apply in_or_app; [left | right].
  +apply Permutation_in with (map fst (fbyvarsof x1)); auto.
   apply Permutation_map. apply flat_map_permutation; auto.
  +apply Permutation_in with (map instid (instidof x1)); auto.
   apply Permutation_map. apply flat_map_permutation; auto.
Qed.

Lemma toposort_stmts_program_gids_range:
  forall id p p',
  toposort_stmts_program p = OK p' ->
  ids_plt id (globidspltof p) ->
  ids_plt id (globidspltof p').
Proof.
  unfold globidspltof. intros.
  monadInv H. simpl in *.
  apply trans_nodes_fids_eq in EQ. rewrite <-EQ; auto.
  intros. monadInv H; auto.
Qed.

Definition is_eqs_toposorted (l1 l2:list stmt) : Prop :=
  Permutation l1 l2 /\ topo_sorted (deps_of_stmts l2).

Definition is_nodes_toposorted (l1 l2:list (ident*node)) : Prop :=
  Permutation l1 l2 /\ topo_sorted (deps_of_nodes l2).



Section TOPOSORTED.

Lemma get_nodeps_dependon_false: forall l l1 l2 l',
  (l1,l2) = get_nodeps (flat_map lidl l') l ->
  listdependonlist l2 l' = false.
Proof.
  unfold listdependonlist.
  induction l; simpl; intros.
  inversion H. simpl. auto.
  destruct (get_nodeps _ _) eqn:?.
  destruct (list_in_list (ridl a) _) eqn:?; inv H.
  eapply IHl; eauto.
  simpl. rewrite list_in_list_left_app, Heqb.
  simpl. eapply IHl; eauto.
Qed.

Lemma listdependonlist_topo_sorted:
  forall l, listdependonlist l l = false ->
  topo_sorted l.
Proof.
  induction l; constructor; unfold listdependonlist in *; simpl in *;
  rewrite list_in_list_left_app in H;
  apply orb_false_elim in H; destruct H; auto.
  apply IHl; auto. rewrite list_in_list_right_app in H0.
  apply orb_false_elim in H0; destruct H0. trivial.
Qed.

Lemma toposorted_getnodep2: forall (l l1 l2: list depend),
  (l1,l2) = get_nodeps (flat_map lidl l) l ->
  topo_sorted l2.
Proof.
  unfold get_nodeps. intros. generalize H. intros.
  apply partition_permutation in H0.
  apply get_nodeps_dependon_false in H.
  apply (listdependonlist_permutation l2) in H0.
  rewrite H, listdependonlist_app in H0.
  symmetry in H0. apply orb_false_elim in H0. destruct H0.
  apply listdependonlist_topo_sorted; auto.
Qed.

Theorem toposorted_deps :
  forall len l l1,
  (length l <= len)%nat ->
  toposort_deps len l = OK l1 ->
  topo_sorted l1.
Proof.
  intros len; elim len; simpl; auto.
  intros.
  inv H0. constructor.

  induction l; intros.
  simpl in *. inv H1. constructor.

  remember (get_nodeps _ (a::l)) as p.
  destruct p.
  destruct l2.
  destruct l0; inv H1. constructor.
  destruct (toposort_deps _ _) eqn:?; inv H1.
  rewrite app_comm_cons.
  apply ->toposort_app.
  assert (Hpl: Permutation (a :: l) (l0 ++ d :: l2)).
  unfold get_nodeps in *.
  eapply partition_permutation; eauto.
  assert (length l0 <= n)%nat.
    apply Permutation_length in Hpl.
    rewrite app_length in Hpl. simpl in *. omega.
  split; [| split].
  *apply toposorted_getnodep2 in Heqp; auto.
  *apply H with l0; auto.
  *apply get_nodeps_dependon_false in Heqp.
   rewrite listdependonlist_permutation with _ _ (l0++d::l2) in Heqp; trivial.
   rewrite listdependonlist_app in Heqp. apply orb_false_elim in Heqp.
   destruct Heqp.
   apply toposort_deps_permutation in Heqr; auto.
   rewrite listdependonlist_permutation with _ _ l0; auto.
   apply Permutation_sym; auto.
Qed.


Lemma eqs_map_seq_perm: forall (a: depend)(l: list stmt)(depl: list depend),
  Permutation (deps_of_stmts l) depl ->
  In a depl ->
  lidl a = lidl_of_s (nth (seqn a) l Sskip) /\
  ridl a = ridl_of_s (nth (seqn a) l Sskip).
Proof.
  intros. apply Permutation_sym in H.
  apply Permutation_in with _ _ _ a in H; trivial.
  unfold deps_of_stmts in H.
  apply in_map_iff in H. destruct H as [x [A1 A2]].
  rewrite <- A1; simpl; split; trivial.
Qed.

Lemma eqs_toposorted_sup:
  forall l l1 deps,
  toposort_deps (length (deps_of_stmts l)) (deps_of_stmts l) = OK deps ->
  topo_sorted deps ->
  toposort_stmts l = OK l1 ->
  topo_sorted (deps_of_stmts l1).
Proof.
  intros. apply <- topo_sorted_eqs_simpl.
  apply depend_toposorted with deps; auto.
  unfold deps_of_stmts_simpl. rewrite map_map. simpl.
  unfold toposort_stmts in H1.
  monadInv H1. rewrite EQ in H. inv H.
  repeat rewrite map_map.
  apply map_ext2. intros.
  assert (A: Permutation (deps_of_stmts l) deps).
    eapply toposort_deps_permutation; eauto.
  apply eqs_map_seq_perm with a l deps in A; trivial.
  intuition. f_equal;trivial.
Qed.

Theorem eqs_toposorted :
  forall s s',
  toposort_stmts s = OK s' ->
  is_eqs_toposorted s s'.
Proof.
  intros. unfold is_eqs_toposorted. split.
  apply toposort_stmts_permutation; auto.

  monadInv H.
  apply eqs_toposorted_sup with s x; eauto.
  eapply toposorted_deps; eauto.
  unfold toposort_stmts. rewrite EQ. simpl. auto.
Qed.



Lemma nodes_map_seq_perm: forall (a: depend)(l: list (ident*node))(depl: list depend),
  Permutation (deps_of_nodes l) depl ->
  In a depl ->
  lidl a = fst (nth (seqn a) l nodenil) :: nil /\
  ridl a = flat_map get_stmt_nid (nd_stmt (snd (nth (seqn a) l nodenil))).
Proof.
  intros. apply Permutation_sym in H.
  apply Permutation_in with _ _ _ a in H; trivial.
  unfold deps_of_nodes in H. apply in_map_iff in H.
  destruct H as [x [A1 A2]].
  rewrite <- A1; simpl; split; trivial.
Qed.

Lemma topo_sorted_nodes_simpl:
  forall nodes,
  topo_sorted (deps_of_nodes nodes) <->
  topo_sorted (deps_of_nodes_simpl nodes).
Proof.
  intros. split; intros;
  [ apply depend_toposorted with (deps_of_nodes nodes) |
    apply depend_toposorted with (deps_of_nodes_simpl nodes)]; trivial;
    unfold deps_of_nodes_simpl; unfold deps_of_nodes;
    repeat rewrite map_map; simpl;
    rewrite <- seq_nth_fun_equal with (f:=(fun x => mkdepend (fst x :: nil) (flat_map get_stmt_nid (nd_stmt (snd x))) O));
    trivial.
Qed.

Lemma nodes_toposorted_sup:
  forall l l1 deps,
  toposort_deps (length (deps_of_nodes l)) (deps_of_nodes l) = OK deps ->
  topo_sorted deps ->
  toposort_nodes l = OK l1 ->
  topo_sorted (deps_of_nodes l1).
Proof.
  intros. apply <- topo_sorted_nodes_simpl.
  apply depend_toposorted with deps; auto.
  unfold deps_of_nodes_simpl. rewrite map_map. simpl.
  unfold toposort_nodes in H1.
  monadInv H1. rewrite EQ in H. inv H.
  repeat rewrite map_map.
  apply map_ext2. intros.
  assert (A: Permutation (deps_of_nodes l) deps).
    eapply toposort_deps_permutation; eauto.
  apply nodes_map_seq_perm with a l deps in A; trivial.
  intuition. f_equal;trivial.
Qed.

Theorem nodes_toposorted :
  forall l l',
  toposort_nodes l = OK l' ->
  is_nodes_toposorted l l'.
Proof.
  intros.  split.
  apply toposort_nodes_permutation; auto.

  monadInv H.
  apply nodes_toposorted_sup with l x; eauto.
  eapply toposorted_deps; eauto.
  unfold toposort_nodes. rewrite EQ. simpl. auto.
Qed.

Definition depend_match (d1 d2: depend) :=
  lidl d1 = lidl d2
  /\ Permutation (ridl d1)  (ridl d2).

Definition depends_match (l1 l2: list depend) :=
  Forall2 depend_match l1 l2.

Lemma depends_match_dependonlist:
  forall l1 l2,
  depends_match l1 l2 ->
  forall a,
  dependonlist a l1 = dependonlist a l2.
Proof.
  unfold dependonlist.
  induction 1; simpl; intros; auto.
  destruct H. rewrite H. repeat rewrite list_in_list_right_app.
  rewrite IHForall2; auto.
Qed.

Lemma depend_match_dependon:
  forall x y,
  depend_match x y ->
  dependon x x = dependon y y.
Proof.
  intros. destruct H. unfold dependon.
  rewrite H. apply list_in_list_perm2; auto.
Qed.

Lemma depends_match_toposorted:
  forall l1 l2,
  depends_match l1 l2 ->
  topo_sorted l1 ->
  topo_sorted l2.
Proof.
  induction 1; intros.
  constructor.
  inv H1. constructor; auto.
  rewrite <- H2. repeat rewrite dependonlist_appa.
  symmetry. f_equal.
  apply depend_match_dependon; auto.
  rewrite depends_match_dependonlist with _ l' _; auto.
  destruct H. unfold dependonlist.
  apply list_in_list_perm2; auto.
Qed.

End TOPOSORTED.
