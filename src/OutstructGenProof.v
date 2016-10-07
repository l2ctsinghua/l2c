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
Require Import Maps.
Require Import Integers.
Require Import List.
Require Import ExtraList.
Require Import Cltypes.
Require Import Lident.
Require Import Ltypes.
Require Import Lustre.
Require Import LustreF.
Require Import Lvalues.
Require Import Lenv.
Require Import Lenvmatch.
Require Import Lsem.
Require Import LsemF.
Require Import OutstructGen.

Section CORRECTNESS.

Variable prog1: program.
Variable prog2: program.

Hypothesis TRANS:
  trans_program prog1 = OK prog2.

Section NODE_CORRECT.

Variable ntl: list (ident*func).

Hypothesis GET_TYPES:
  get_nodetypes (node_block prog1) nil = OK ntl.

Lemma calls_of_field_type_inst:
  forall s calls c fd,
  calls_of s ntl = OK calls ->
  list_norepet (map instid (instidof s)) ->
  In c (instidof s) ->
  find_funct ntl (callid c) = Some fd ->
  field_type (instid c) (fieldlist_of calls) = OK
    match callnum c with
    | Some j => Tarray xH (Tstruct (out_struct_type (fst fd)) (nd_fld (snd fd))) (Int.unsigned j)
    | None => (Tstruct (out_struct_type (fst fd)) (nd_fld (snd fd)))
    end.
Proof.
  induction s; simpl; intros; try (inv H1; fail); eauto.
  +unfold cons_inst in *. destruct c. simpl in *.
   destruct cakind; simpl in *; destruct H1; try inv H1.
   simpl in *. unfold get_nt_byid in H. rewrite H2 in H.
   simpl in *. destruct callnum; inv H.
   -simpl. rewrite peq_true; auto.
   -simpl. rewrite peq_true; auto.
  +monadInv H. rewrite map_app in H0.
   apply list_norepet_app in H0. destruct H0 as [? [? ?]]; auto.
   apply in_app_or in H1. destruct H1.
   -eapply field_type_ok_app; eauto.
   -rewrite field_type_notin_app; auto.
    erewrite calls_of_instid_eq; eauto.
    red; intros. red in H3. red in H3.
    eapply H3 in H4; eauto. eapply in_map; eauto.
  +monadInv H. rewrite map_app in H0.
   apply list_norepet_app in H0. destruct H0 as [? [? ?]]; auto.
   apply in_app_or in H1. destruct H1.
   -eapply field_type_ok_app; eauto.
   -rewrite field_type_notin_app; auto.
    erewrite calls_of_instid_eq; eauto.
    red; intros. red in H3. red in H3.
    eapply H3 in H4; eauto. eapply in_map; eauto.
Qed.

Lemma trans_node_map:
  mmap (trans_node ntl) ntl = OK (node_block prog2).
Proof.
  monadInv TRANS. destruct (list_in_list _ _); inv EQ2.
  simpl in *. rewrite GET_TYPES in EQ. inv EQ; auto.
Qed.

Lemma trans_call_node_exists:
  forall nid isid callid callnum csid cfld ats rts nd fd,
  Lustre.call_node (node_block prog1) nid (mkcalldef true isid callid callnum csid cfld ats rts) nd fd ->
  ids_norepet (snd nd) ->
  In (mkcalldef true isid callid callnum csid cfld ats rts) (instidof (nd_stmt (snd nd))) ->
  exists ndx fdx nd' fd', get_nodetype nd ntl = OK ndx
    /\ get_nodetype fd ntl = OK fdx
    /\ trans_node ntl ndx = OK nd'
    /\ trans_node ntl fdx = OK fd'
    /\ find_funct ntl nid = Some ndx
    /\ find_funct ntl callid = Some fdx
    /\ call_node (node_block prog2) nid
         (mkcalldef true isid callid callnum (out_struct_type callid) (nd_fld (snd fdx))
            (map (snd (B:=type)) (nd_args (snd fdx)))
            (nd_rets (snd fdx))) nd' fd'.
Proof.
  intros.
  destruct H as [A [A1 [A2 [A3 [A4 [A5 A6]]]]]].
  assert(A7: mmap (trans_node ntl) ntl = OK (node_block prog2)).
    apply trans_node_map.
  destruct get_nodetype_eq with (node_block prog1) ntl callid fd as [fdx [A9 A10]]; auto.
  destruct find_funcs_monad_exits with func func ntl (node_block prog2) (trans_node ntl) callid fdx
    as [fd' [A11 A12]]; auto.
    intros. monadInv H; auto.
  destruct get_nodetype_eq with (node_block prog1) ntl nid nd as [ndx [A13 A14]]; auto.
  destruct find_funcs_monad_exits with func func ntl (node_block prog2) (trans_node ntl) nid ndx
    as [nd' [A15 A16]]; auto.
    intros. monadInv H; auto.
  exists ndx, fdx, nd', fd'. repeat (split; simpl in *; auto).
  +monadInv A10. monadInv A14. simpl in *.
   monadInv A15. monadInv A11. monadInv EQ1. monadInv EQ2. auto.
  +monadInv A14. monadInv A15. monadInv EQ0.
   unfold ids_norepet in H0. unfold allidsof, predidof in *.
   unfold allvarsof, svarsof in *. destruct H0 as [D [D1 [D2 D3]]].
   monadInv A10. monadInv A11. monadInv EQ2. simpl in *.
   rewrite field_type_notin_app; auto.
   eapply calls_of_field_type_inst in H1; eauto. simpl in *. auto.
   *apply list_norepet_app in D1. destruct D1 as [? [? ?]]; auto.
   *clear -D1 D2 H1. rewrite map_app in *. red; intros.
    apply in_map with _ ident instid _ _ in H1; simpl in *;auto.
    apply in_app_or in H. destruct H.
    red in D2. red in D2. apply D2 with isid isid; auto.
    apply in_or_app; auto. apply in_or_app; auto.
    apply list_norepet_app in D1. destruct D1 as [? [? D1]].
    red in D1. red in D1. apply D1 with isid isid; auto.
  +monadInv A10. monadInv A11; simpl. monadInv EQ0. simpl.
   f_equal. eapply find_funct_fid in A12; eauto.
  +monadInv A10. monadInv A11. monadInv EQ0. auto.
  +monadInv A10. monadInv A11. monadInv EQ0. auto.
  +monadInv A10. monadInv A11. monadInv EQ0. auto.
  +monadInv A10. monadInv A11. monadInv EQ0. auto.
Qed.

Lemma trans_call_func_exists:
  forall nid c nd fd,
  Lustre.call_node (node_block prog1) nid c nd fd ->
  exists ndx fdx nd' fd', get_nodetype nd ntl = OK ndx
    /\ get_nodetype fd ntl = OK fdx
    /\ trans_node ntl ndx = OK nd'
    /\ trans_node ntl fdx = OK fd'
    /\ Lustre.call_node (node_block prog2) nid c nd' fd'.
Proof.
  intros.
  destruct H as [A [A1 [A2 [A3 [A4 [A5 A6]]]]]].
  assert(A7: mmap (trans_node ntl) ntl = OK (node_block prog2)).
    apply trans_node_map.
  destruct get_nodetype_eq with (node_block prog1) ntl (callid c) fd as [fdx [A9 A10]]; auto.
  destruct find_funcs_monad_exits with func func ntl (node_block prog2) (trans_node ntl) (callid c) fdx
    as [fd' [A11 A12]]; auto.
    intros. monadInv H; auto.
  destruct get_nodetype_eq with (node_block prog1) ntl nid nd as [ndx [A13 A14]]; auto.
  destruct find_funcs_monad_exits with func func ntl (node_block prog2) (trans_node ntl) nid ndx
    as [nd' [A15 A16]]; auto.
    intros. monadInv H; auto.
  exists ndx, fdx, nd', fd'. repeat (split; simpl in *; auto).
  +monadInv A10. monadInv A14. simpl in *.
   monadInv A15. monadInv A11. monadInv EQ1. monadInv EQ2. auto.
  +monadInv A10. monadInv A11. monadInv EQ0. auto.
  +monadInv A10. monadInv A11. monadInv EQ0. auto.
  +monadInv A10. monadInv A11. monadInv EQ0. auto.
Qed.

Lemma trans_node_all_correct:
  forall gc e e' main1 vargs vrets,
  LsemF.eval_node false prog1 gc e e' main1 vargs vrets ->
  find_funct (node_block prog1) (fst main1) = Some main1 ->
  forall fd main2, get_nodetype main1 ntl = OK fd ->
  trans_node ntl fd = OK main2 ->
  eval_node true prog2 gc e e' main2 vargs vrets.
Proof.
  intros gc.
  induction 1 using LsemF.eval_node_ind2 with
  ( P0 := fun nid te e te' e' s =>
          forall nd s', find_funct (node_block prog1) nid = Some nd ->
          ids_norepet (snd nd) ->
          incl (instidof s) (instidof (nd_stmt (snd nd))) ->
          trans_stmt s ntl = OK s' ->
          LsemF.eval_stmt true prog2 gc nid te e te' e' s'
  ); intros; simpl in *.
 +(*node*)
  destruct main2 as [nid' f'].
  assert (nid' = nid).
    monadInv H8; monadInv H9; auto.
  subst.
  apply exec_node with te te1 te2; auto;
  try (monadInv H8; monadInv H9; monadInv EQ0; auto; fail).
  -eapply trans_node_ids_norepet; eauto.
  -eapply IHeval_node; eauto.
   red; intros; auto.
   monadInv H8. monadInv H9. monadInv EQ0. auto.
  -monadInv H9. monadInv EQ. unfold svarsof. simpl in *.
   monadInv H8. unfold svarsof. simpl in *.
   red. intros. apply field_type_ok_app.
   eapply list_in_fieldlist; eauto.
   apply ids_norepet_rets_svars; auto.
 +(** Sassign *)
  inv H3. apply LsemF.eval_Sassign; auto.
 +(** Scall *)
  destruct cdef. unfold trans_calldef in *.
  simpl in *. generalize H0. intros A.
  destruct H0 as [C [C1 [C2 C3]]]. unfold func in *. rewrite H13 in *. inv C.
  destruct cakind; monadInv H16.
  -eapply trans_call_node_exists in A; eauto.
   destruct A as [ndx [fdx [nd' [fd' [A [A1 [A2 [A3 [A4 [A5 A6]]]]]]]]]].
   generalize A6. intros B.
   destruct B as [B [B1 [B2 [B3 [B4 B5]]]]]. simpl in *.
   unfold get_nt_byid in EQ. unfold func in *. rewrite A5 in EQ.
   simpl in *. inv EQ.
   apply LsemF.eval_Scall with ef ef' nd' fd' vl vargs vargs' vrets i; simpl; auto.
   *inv H1; simpl in *; try congruence.
    constructor; auto. inv H16. constructor 1 with efs; auto.
   *eapply IHeval_node; eauto.
    eapply find_funct_eq; eauto.
   *rewrite H7. monadInv A3. monadInv EQ. monadInv A1; auto.
   *rewrite H8. monadInv A3. monadInv EQ. monadInv A1; auto.
   *apply H15; simpl; auto.
  -eapply trans_call_func_exists in A; eauto.
   destruct A as [ndx [fdx [nd' [fd' [A [A1 [A2 [A3 A4]]]]]]]].
   generalize A4. intros B.
   destruct B as [B [B1 [B2 [B3 [B4 B5]]]]]. simpl in *.
   apply LsemF.eval_Scall with ef ef' nd' fd' vl vargs vargs' vrets i; simpl; auto.
   *eapply IHeval_node; eauto.
    eapply find_funct_eq; eauto.
   *rewrite H7. monadInv A3. monadInv EQ. monadInv A1; auto.
   *rewrite H8. monadInv A3. monadInv EQ. monadInv A1; auto.
 +(** Sfor_start *)
  monadInv H4. eapply LsemF.eval_Sfor_start; eauto.
  eapply IHeval_node; eauto.
  rewrite EQ. auto.
 +(** Sfor_false *)
  monadInv H3. eapply LsemF.eval_Sfor_false; eauto.
 +(** Sfor_loop *)
  monadInv H6. eapply LsemF.eval_Sfor_loop; eauto.
  eapply IHeval_node0; eauto.
  rewrite EQ. auto.
 +(** Sskip *)
  inv H2. constructor.
 +(** Sseq *)
  monadInv H4. apply LsemF.eval_Sseq with te1 e1; eauto.
  eapply IHeval_node; eauto. red; intros. apply H3; apply in_or_app; auto.
  eapply IHeval_node0; eauto. red; intros. apply H3; apply in_or_app; auto.
 +(** Sif *)
  monadInv H5. apply LsemF.eval_Sif with v b; auto.
  destruct b.
  eapply IHeval_node; eauto. red; intros. apply H4; apply in_or_app; auto.
  eapply IHeval_node; eauto. red; intros. apply H4; apply in_or_app; auto.
 +(** Scase *)
  inv H5. eapply LsemF.eval_Scase; eauto.
Qed.

Lemma init_node_correct:
  forall e main1,
  LsemF.init_node false prog1 e main1 ->
  find_funct (node_block prog1) (fst main1) = Some main1 ->
  forall fd main2, get_nodetype main1 ntl = OK fd ->
  trans_node ntl fd = OK main2 ->
  init_node true prog2 e main2.
Proof.
  intros gc.
  induction 1 using LsemF.init_node_ind2 with
  ( P0 := fun nid e1 e2 l =>
      forall nd l', find_funct (node_block prog1) nid = Some nd ->
      ids_norepet (snd nd) ->
      incl l (instidof (nd_stmt (snd nd))) ->
      mmap (trans_calldef ntl) l = OK l' ->
      init_stmt true prog2 nid e1 e2 l'
   ); intros.
 +(*init_node*)
  destruct main2 as [nid' f'].
  assert (nid' = nid).
    monadInv H6. monadInv H5. auto.
  subst.
  apply init_node_; auto;
  try (monadInv H6; monadInv EQ; monadInv H5; auto; fail).
  -eapply trans_node_ids_norepet; eauto.
  -monadInv H6. monadInv EQ. unfold svarsof. simpl in *.
   monadInv H5. unfold svarsof. simpl in *.
   red. intros. apply field_type_ok_app.
   eapply list_in_fieldlist; eauto.
   apply ids_norepet_rets_svars; auto.
  -apply IHinit_node with (nid,f); auto.
   red; intros; auto.
   monadInv H5. monadInv H6. monadInv EQ0. simpl in *.
   eapply trans_body_calldef_mmap; eauto.
 +(*nil*)
  simpl in *. inv H2. constructor.
 +(*cons*)
  simpl in *. monadInv H6.
  assert (In c (instidof (nd_stmt (snd nd0)))).
    apply H5; simpl; auto.
  apply instidof_cakind_true in H1.
  destruct c. unfold trans_calldef in *. simpl in *.
  generalize H. intros A.
  destruct H as [C [C1 [C2 ?]]]. unfold func in *. rewrite H3 in *. inv C.
  eapply trans_call_node_exists in A; eauto.
  destruct A as [ndx [fdx [nd' [fd' [A [A1 [A2 [A3 [A4 [A5 A6]]]]]]]]]].
  generalize A6. intros B.
  destruct B as [B [B1 [B2 [B3 [B4 B5]]]]]. simpl in *.
  unfold get_nt_byid in EQ. unfold func in *. rewrite A5 in EQ.
  simpl in *. inv EQ.
  econstructor 2 with _ nd' fd' ef; simpl; auto.
  -eapply IHinit_node; eauto.
   eapply find_funct_eq; eauto.
  -eapply IHinit_node0; eauto. red; intros. apply H5; simpl; auto.
  -apply H5; simpl; auto.
Qed.

End NODE_CORRECT.

Theorem exec_prog_correct_node:
  forall gc1 e main1 mass vrss n maxn,
  exec_prog1 prog1 gc1 (LsemF.eval_node false) main1 e n maxn mass vrss ->
  find_funct (node_block prog1) (fst main1) = Some main1 ->
  forall ntl fd main2, get_nodetypes (node_block prog1) nil = OK ntl ->
  get_nodetype main1 ntl = OK fd ->
  trans_node ntl fd = OK main2 ->
  exec_prog1 prog2 gc1 (LsemF.eval_node true) main2 e n maxn mass vrss.
Proof.
  induction 1; intros.
  +constructor 1 with mrss; trivial.
   monadInv H4. monadInv H3. monadInv EQ. simpl. auto.
  +assert (A: LsemF.eval_node true prog2 gc1 e e' main2 (map Vmvl (Streams.hd mass)) (Streams.hd vrss)).
    apply trans_node_all_correct with ntl main1 fd; auto.
   constructor 2 with e'; auto.
   -monadInv H6. monadInv EQ. monadInv H5; auto.
   -apply IHexec_prog1 with ntl fd; auto.
Qed.

Lemma initial_states_match:
  forall gc main1 e,
  Lenv.initial_state1 prog1 gc (fun p e fd => LsemF.init_node false p e fd) main1 e ->
  exists ntl main2 fd, Lenv.initial_state1 prog2 gc (fun p e fd => init_node true p e fd) main2 e
    /\ get_nodetypes (node_block prog1) nil = OK ntl
    /\ get_nodetype main1 ntl = OK fd
    /\ trans_node ntl fd = OK main2.
Proof.
  assert(A: exists ntl, get_nodetypes (node_block prog1) nil = OK ntl).
    monadInv TRANS. exists x; auto.
  destruct A as [ntl A].
  induction 1; simpl; intros.
  +generalize H0. intros.
   apply get_nodetype_eq with (ntl:=ntl) in H0; auto.
   destruct H0 as [f2 [? ?]].
   destruct find_funcs_monad_exits with func func ntl (node_block prog2) (trans_node ntl) (node_main prog1) f2
    as [main2 [? ?]]; auto.
    monadInv TRANS. destruct (list_in_list _ _); inv EQ2.
    simpl. rewrite EQ in A. inv A. auto.
    intros. monadInv H5; auto.
   exists ntl, main2, f2.  split; [| split]; auto.
   constructor 1; auto.
   *monadInv TRANS. destruct (list_in_list _ _); inv EQ2. auto.
   *monadInv TRANS. destruct (list_in_list _ _); inv EQ2. auto.
   *monadInv H5. monadInv EQ. monadInv H4. simpl in *. auto.
   *eapply init_node_correct; eauto.
    eapply find_funct_eq in H3; eauto.
Qed.

Theorem trans_program_node_correct:
  forall gc e main1 mass vrss maxn,
  Lenv.initial_state1 prog1 gc (fun p e fd => LsemF.init_node false p e fd) main1 e ->
  exec_prog1 prog1 gc (LsemF.eval_node false) main1 e 1 maxn mass vrss ->
  exists main2, Lenv.initial_state1 prog2 gc (fun p e fd => init_node true p e fd) main2 e
    /\ exec_prog1 prog2 gc (LsemF.eval_node true) main2 e 1 maxn mass vrss
    /\ nd_rets (snd main2) = nd_rets (snd main1)
    /\ svars_field_match (nd_rets (snd main2)) (nd_fld (snd main2))
    /\ nd_kind (snd main2) = nd_kind (snd main1).
Proof.
  intros.
  destruct initial_states_match with gc main1 e as [ntl [main2 [fd [A [A1 [A2 A3]]]]]]; auto.
  exists main2. split; [| split; [| split]]; auto.
  apply exec_prog_correct_node with main1 ntl fd; auto.
  inv H; try congruence. eapply find_funct_eq; eauto.
  monadInv A2. monadInv A3. monadInv EQ0. auto.
  monadInv A2. monadInv A3. monadInv EQ0. simpl.
   unfold svarsof. rewrite app_ass.
   split; auto. red. eauto.
Qed.

End CORRECTNESS.
