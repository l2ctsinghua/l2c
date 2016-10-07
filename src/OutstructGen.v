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
Require Import Lident.
Require Import Cltypes.
Require Import Ltypes.
Require Import Lustre.
Require Import LustreF.
Require Import Permutation.
Require Import ExtraList.

Open Local Scope error_monad_scope.

Definition trans_calldef(ntl: list (ident*func))(c: calldef): res calldef :=
  do fd <- get_nt_byid (callid c) ntl;
  let sid := out_struct_type (callid c) in
  let fld := nd_fld (snd fd) in
  let atys := map snd (nd_args (snd fd)) in
  OK (mkcalldef (cakind c) (instid c) (callid c) (callnum c) sid fld atys (nd_rets (snd fd))).

Fixpoint trans_stmt(s: stmt)(ntl: list (ident*func)): res stmt :=
  match s with
  | Sassign lh exp => OK (Sassign lh exp)
  | Scall oid lh c vals =>
     if cakind c then
       do c' <- trans_calldef ntl c;
       OK (Scall oid lh c' vals)
     else OK s
  | Sfor a1 a2 a3 a4 =>
     do s4 <- trans_stmt a4 ntl;
     OK (Sfor a1 a2 a3 s4)
  | Sseq s1 s2 =>
     do s3 <- trans_stmt s1 ntl;
     do s4 <- trans_stmt s2 ntl;
     OK (Sseq s3 s4)
  | Sskip => OK Sskip
  | Sif a s1 s2 =>
     do s3 <- trans_stmt s1 ntl;
     do s4 <- trans_stmt s2 ntl;
     OK (Sif a s3 s4)
  | Scase lh a1 a2 => OK (Scase lh a1 a2)
  end.

Definition trans_body (f: ident*func)(ntl: list (ident*func)): res func :=
  let b := snd f in
  do s1 <- trans_stmt (nd_stmt b) ntl;
  OK (mknode b.(nd_kind) b.(nd_args) b.(nd_rets) b.(nd_svars) b.(nd_vars)
           s1 (out_struct_type (fst f)) b.(nd_fld)).

Definition trans_node(ntl: list (ident*func))(f: ident*func): res (ident*func) :=
  do b <- trans_body f ntl;
  OK (fst f, b).

Definition trans_nodes(ntl: list (ident*func)): res (list (ident*func)) :=
  mmap (trans_node ntl) ntl.

Fixpoint calls_of(s: stmt)(ntl: list (ident*func)): res (list (ident*type)) :=
  match s with
  | Scall oid _ (mkcalldef kd isid cnid oj _ _ _ _) _ =>
     if kd then
        do fd <- get_nt_byid cnid ntl;
        let sty := Tstruct (out_struct_type (fst fd)) (nd_fld (snd fd)) in
        match oj with
        | None => OK ((isid, sty) :: nil)
        | Some j => OK ((isid, Tarray xH sty (Int.unsigned j)) :: nil)
        end
     else OK nil
  | Sfor _ _ _ s => calls_of s ntl
  | Sif _ s1 s2 =>
     do tl1 <-calls_of s1 ntl;
     do tl2 <-calls_of s2 ntl;
     OK (tl1 ++ tl2)
  | Sseq s1 s2 =>
     do tl1 <-calls_of s1 ntl;
     do tl2 <-calls_of s2 ntl;
     OK (tl1 ++ tl2)
  | _ => OK nil
  end.

Definition get_nodetype(fd: ident*func)(ntl: list (ident*func)): res (ident*func):=
  let f := snd fd in
  do cdecls <- calls_of f.(nd_stmt) ntl;
  let decls := svarsof f ++ cdecls in
  OK (fst fd, mknode f.(nd_kind) f.(nd_args) f.(nd_rets) f.(nd_svars)
                f.(nd_vars) f.(nd_stmt) f.(nd_sid) (fieldlist_of decls)).

Fixpoint get_nodetypes(fds ntl: list (ident*func)): res (list (ident*func)) :=
  match fds with
  | nil => OK nil
  | fd :: rest =>
      do nt <- get_nodetype fd ntl;
      do ntl2 <- get_nodetypes rest (ntl ++ nt :: nil);
      OK (nt :: ntl2)
  end.

Definition trans_nodetype(fd: ident*func): list (ident*type) :=
  if (nd_kind (snd fd)) then
    match nd_fld (snd fd) with
    | Fnil => nil
    | _ => (out_struct_type (fst fd), Tstruct (out_struct_type (fst fd)) (nd_fld (snd fd))) :: nil
    end
  else nil.

Definition trans_nodetypes(ntl: list (ident*func)) :=
  flat_map (fun nt => trans_nodetype nt) ntl.

Definition trans_program (p: program): res program :=
  do ntl <- get_nodetypes (node_block p) nil;
  do fds <- trans_nodes ntl;
  let sblock := trans_nodetypes ntl in
  if list_in_list (map fst sblock) (globidsof p) then
    Error (msg "OutstructGen: out_struct_type names are in global names!")
  else
    OK (mkprogram (type_block p) (defs_block p++sblock) (const_block p) fds (node_main p)).

Lemma getcallsfromeq_ntl_app_any:
  forall a l1 l2 x,
  calls_of a l1 = OK x ->
  calls_of a (l1 ++ l2) = OK x.
Proof.
  induction a; simpl; intros; auto.
  destruct c. destruct cakind; monadInv H; auto.
  rewrite getntbyid_ntl_app_any with _ _ _ x0 _; auto.
  monadInv H. rewrite IHa1 with _ _ x0; auto. simpl.
    rewrite IHa2 with _ _ x1; auto.
  monadInv H. rewrite IHa1 with _ _ x0; auto. simpl.
    rewrite IHa2 with _ _ x1; auto.
Qed.

Lemma getnodetypes_ntl_app_any:
  forall fd l1 l2 nt,
  get_nodetype fd l1 = OK nt ->
  get_nodetype fd (l1 ++ l2) = OK nt.
Proof.
  destruct fd. destruct f; simpl; intros.
  monadInv H.
  apply getcallsfromeq_ntl_app_any with nd_stmt l1 l2 _ in EQ.
  unfold get_nodetype. simpl. rewrite EQ; auto.
Qed.

Lemma getnodetypes_app:
  forall l1 l2 nl nl0,
  get_nodetypes (l1 ++ l2) nl0 = OK nl ->
  exists nl1, exists nl2, get_nodetypes l1 nl0 = OK nl1
    /\ get_nodetypes l2 (nl0 ++ nl1) = OK nl2
    /\ nl = nl1 ++ nl2.
Proof.
  induction l1; simpl; intros.
  +exists nil; exists nl; simpl; repeat split; auto.
   rewrite <-app_nil_end; auto.
  +destruct a. monadInv H. simpl in *.
   apply IHl1 in EQ1. destruct EQ1 as [nl1 [nl2 [A [A1 A2]]]].
   rewrite EQ. simpl. rewrite A. simpl. subst x0.
   rewrite app_ass in A1. simpl in A1.
   exists (x:: nl1); exists nl2; repeat split; auto.
Qed.

Lemma calls_of_exists:
  forall nlist ntl cnid f,
  get_nodetypes nlist nil = OK ntl ->
  find_funct nlist cnid = Some f ->
  exists cdecls, calls_of (nd_stmt (snd f)) ntl  = OK cdecls.
Proof.
  intros.
  assert (In f nlist).
    apply find_funct_in2 with cnid; auto.
  apply In_split in H1.
  destruct H1 as [l1 [l2 ?]].
  subst. apply getnodetypes_app in H.
  destruct H as [nt1 [ntl2 [? [? ?]]]].
  subst. simpl in *. monadInv H1.
  monadInv EQ. exists x1.
  eapply getcallsfromeq_ntl_app_any; eauto.
Qed.

Lemma get_nodetypes_nid_map:
  forall l ntl nl,
  get_nodetypes l ntl = OK nl ->
  map (fst (B:=func)) nl = map (fst (B:=func)) l.
Proof.
  induction l; simpl; intros.
  +inv H. auto.
  +monadInv H. unfold get_nodetype in *.
   destruct (nd_kind (snd a)); monadInv EQ; simpl; f_equal; eauto.
Qed.

Lemma find_funct_getnodetypes_exists:
  forall l ntl nid f1 f2,
  find_funct l nid = Some f1 ->
  get_nodetypes l nil = OK ntl ->
  get_nodetype f1 ntl = OK f2 ->
  find_funct ntl nid = Some f2.
Proof.
  intros. generalize H; intros.
  apply find_funct_fid in H2. subst.
  apply find_funct_notin_app in H.
  destruct H as [l1 [l2 [? ?]]]; auto.
  subst. apply getnodetypes_app in H0.
  destruct H0 as [nl1 [nl2 [? [? ?]]]].
  subst. simpl in *. monadInv H0.
  assert (fst f1 = fst f2).
    unfold get_nodetype in *.
    destruct (nd_kind (snd f1)); monadInv H1; auto.
  rewrite H0.
  erewrite getnodetypes_ntl_app_any in H1; eauto.
  inv H1. erewrite find_funct_app_notin_right; eauto.
  simpl. rewrite Peqb_refl; auto.
  rewrite <-H0. erewrite get_nodetypes_nid_map; eauto.
Qed.

Lemma getnodetype_exists:
  forall l fd ntl,
  get_nodetypes l nil = OK ntl ->
  find_funct l (fst fd) = Some fd ->
  exists fde, get_nodetype fd ntl = OK fde.
Proof.
  intros.
  assert (exists x, calls_of (nd_stmt (snd fd)) ntl = OK x).
    apply calls_of_exists with l (fst fd); auto.
  destruct H1. unfold get_nodetype.
  rewrite H1. simpl. eauto.
Qed.

Lemma get_nodetype_eq:
  forall l ntl nid f1,
  get_nodetypes l nil = OK ntl ->
  find_funct l nid = Some f1 ->
  exists f2, find_funct ntl nid = Some f2
    /\ get_nodetype f1 ntl = OK f2.
Proof.
  intros. generalize H0. intros.
  apply find_funct_fid in H1. subst.
  destruct getnodetype_exists with l f1 ntl as [f2 ?]; auto.
  exists f2. split; auto.
  apply find_funct_getnodetypes_exists with l f1; auto.
Qed.

Lemma calls_of_instid_eq:
  forall s ntl l,
  calls_of s ntl = OK l ->
  map fst l = map instid (instidof s).
Proof.
  induction s; simpl; intros; inv H; eauto.
  +destruct c. destruct cakind; monadInv H1; auto.
   destruct callnum; inv EQ0; auto.
  +monadInv H1. repeat rewrite map_app.
   f_equal; eauto.
  +monadInv H1. repeat rewrite map_app.
   f_equal; eauto.
Qed.

Lemma trans_body_calldef_mmap:
  forall ntl s s',
  trans_stmt s ntl = OK s' ->
  mmap (trans_calldef ntl) (instidof s) = OK (instidof s').
Proof.
  induction s; simpl; intros; inv H; auto.
  +destruct c. destruct cakind; simpl in *.
   monadInv H1. unfold cons_inst.
   -rewrite EQ. simpl. monadInv EQ. auto.
   -inv H1. auto.
  +monadInv H1. simpl. eapply IHs; eauto.
  +monadInv H1. simpl. eapply mmap_app; eauto.
  +monadInv H1. simpl. eapply mmap_app; eauto.
Qed.

Lemma trans_stmt_instid_map:
  forall ntl s s',
  trans_stmt s ntl = OK s' ->
  map instid (instidof s') = map instid (instidof s).
Proof.
  induction s; simpl; intros; inv H; auto.
  +destruct c. destruct cakind; simpl in *.
   monadInv H1. unfold cons_inst in *. monadInv EQ. auto.
   inv H1. auto.
  +monadInv H1. simpl. eapply IHs; eauto.
  +monadInv H1. simpl. repeat rewrite map_app.
   f_equal; eauto.
  +monadInv H1. simpl. repeat rewrite map_app.
   f_equal; eauto.
Qed.

Lemma trans_nodes_ids_range:
  forall l l',
  trans_nodes l = OK l' ->
  ids_range OUTSTRUCT l ->
  ids_range OUTSTRUCT l'.
Proof.
  intros. red; intros.
  unfold trans_nodes in H.
  apply in_mmap_iff with (y:=fd) in H; auto.
  destruct H as [? [? ?]]. monadInv H.
  monadInv EQ. red in H0. apply H0 in H2; auto.
  unfold allidsof, predidof, allvarsof in *.
  simpl in *. erewrite trans_stmt_instid_map; eauto.
Qed.

Lemma getnodetypes_app_inv:
  forall l nl nl1 nl2,
  get_nodetypes l nl = OK (nl1++nl2) ->
  exists l1 l2, get_nodetypes l1 nl = OK nl1
    /\ get_nodetypes l2 (nl ++ nl1) = OK nl2
    /\ l = l1 ++ l2.
Proof.
  induction l; simpl; intros.
  +inv H. destruct nl1; inv H1. simpl in *. subst.
   exists nil, nil; simpl; repeat split; auto.
  +monadInv H. destruct nl1; simpl in *; subst.
   -exists nil, (a::l). repeat (split; auto).
    rewrite <-app_nil_end. simpl. rewrite EQ.
    simpl. rewrite EQ1. auto.
   -inv H0. apply IHl in EQ1.
    destruct EQ1 as [l1 [l2 [? [? ?]]]]; auto.
    subst. rewrite app_ass in H0. simpl in *.
    exists (a::l1), l2. repeat (split; auto).
    simpl. rewrite EQ. simpl. rewrite H; auto.
Qed.

Lemma get_nodetypes_in_inv:
  forall l nl ntl f2,
  get_nodetypes l nl = OK ntl ->
  In f2 ntl ->
  exists f1 nl0, In f1 l /\ get_nodetype f1 nl0 = OK f2.
Proof.
  intros. apply in_split in H0.
  destruct H0 as [? [? ?]]. subst.
  apply getnodetypes_app_inv in H.
  destruct H as [? [? [? [? ?]]]]. subst.
  destruct x2; simpl in *. inv H0.
  monadInv H0. exists p, (nl++x). split; auto.
  apply in_or_app. simpl; auto.
Qed.

Lemma get_nodetypes_ids_range:
  forall l l',
  get_nodetypes l nil = OK l' ->
  ids_range OUTSTRUCT l ->
  ids_range OUTSTRUCT l'.
Proof.
  intros. red; intros.
  destruct get_nodetypes_in_inv with l (@nil (ident*func)) l' fd as [f1 [nl [? ?]]]; auto.
  monadInv H3; auto.
  red in H0. apply H0 in H2; auto.
Qed.

Lemma trans_program_ids_range:
  forall p p', trans_program p = OK p' ->
  ids_range OUTSTRUCT (node_block p) ->
  ids_range OUTSTRUCT (node_block p').
Proof.
  intros. monadInv H. simpl.
  destruct (list_in_list _ _); inv EQ2.
  eapply trans_nodes_ids_range; eauto.
  eapply get_nodetypes_ids_range; eauto.
Qed.

Lemma trans_program_ids_plt:
  forall id p p' l,
  trans_program p = OK p' ->
  ids_plt id (map fst (const_block p) ++ l) ->
  ids_plt id (map fst (const_block p')).
Proof.
  intros. red; intros. apply H0.
  apply in_or_app. left.
  monadInv H. destruct (list_in_list _ _); inv EQ2; auto.
Qed.

Lemma trans_nodetypes_map_in:
  forall id l,
  In (out_struct_type id) (map fst (trans_nodetypes l)) ->
  In id (map fst l).
Proof.
  induction l; simpl; intros; auto.
  rewrite map_app in *. apply in_app_or in H.
  destruct H; auto.
  unfold trans_nodetype in *.
  destruct (nd_kind (snd a)); simpl in *; try tauto.
  destruct (nd_fld (snd a)) eqn:?; simpl in *; try tauto.
  destruct H; try tauto.
  left. apply Pos.add_reg_r with 2%positive; auto.
Qed.

Lemma trans_nodetypes_norepet:
  forall l, list_norepet (map fst l) ->
  list_norepet (map fst (trans_nodetypes l)).
Proof.
  induction l; simpl; intros; inv H.
  constructor.
  unfold trans_nodetype.
  destruct (nd_kind (snd a)); simpl; auto.
  destruct (nd_fld (snd a)); simpl; auto.
  constructor 2; auto. red; intros. apply H2.
  apply trans_nodetypes_map_in; auto.
Qed.

Lemma trans_program_gids_norepet:
  forall p p',
  trans_program p = OK p' ->
  list_norepet (globidsof p) ->
  list_norepet (globidsof p').
Proof.
  unfold trans_program, globidsof; intros.
  monadInv H. destruct (list_in_list _ _) eqn:?; inv EQ2.
  simpl in *. apply list_in_list_disjoint in Heqb.
  apply trans_nodes_fids_eq in EQ1.
  apply get_nodetypes_nid_map in EQ.
  rewrite <-EQ1, EQ. rewrite map_app.
  rewrite map_app.

  apply list_norepet_permut with (map fst (trans_nodetypes x) ++ (map fst (type_block p ++ defs_block p)
        ++ map fst (const_block p)) ++ map fst (node_block p)); auto.
  +apply list_norepet_app; auto. repeat (split; auto).
   apply list_norepet_app in H0. destruct H0 as [? [? ?]].
   rewrite <-EQ in *.
   apply trans_nodetypes_norepet; auto.
  +repeat rewrite map_app. repeat rewrite <-app_ass.
   repeat apply Permutation_app_tail.
   rewrite app_ass. apply Permutation_app_swap.
  +unfold trans_node. intros.
   destruct (nd_kind (snd x1)); monadInv H; auto.
Qed.

Lemma trans_node_ids_norepet:
  forall nid f ntl fd f',
  get_nodetype (nid, f) ntl = OK fd ->
  trans_node ntl fd = OK (nid, f') ->
  ids_norepet f ->
  ids_norepet f'.
Proof.
  unfold ids_norepet, allidsof,allvarsof,predidof. simpl; intros.
  monadInv H. monadInv H0. monadInv EQ0. simpl in *.
  erewrite trans_stmt_instid_map; eauto.
Qed.
