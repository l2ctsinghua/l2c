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

(** Translate output parameters, tempo variables and call instances into
   a output struct parameter. *)

Require Import Coqlib.
Require Import AST.
Require Import Errors.
Require Import Integers.
Require Import Permutation.
Require Import Cop.
Require Import Cltypes.
Require Import Ltypes.
Require Import Lident.
Require Import Lustre.
Require Import LustreF.

Open Local Scope error_monad_scope.

Fixpoint trans_expr(mkv: mkvar)(e: sexp): sexp :=
  match e with
  | Sconst c ty => Sconst c ty
  | Svar id ty  => Svar id ty
  | Savar id ty  => Savar id ty
  | Scvar id ty  => Scvar id ty
  | Ssvar id ty  => mkv id ty
  | Saryacc a1 a2 ty => Saryacc (trans_expr mkv a1) (trans_expr mkv a2) ty
  | Sfield a id ty => Sfield (trans_expr mkv a) id ty
  | Scast a ty => Scast (trans_expr mkv a) ty
  | Sunop op a ty => Sunop op (trans_expr mkv a) ty
  | Sbinop op a1 a2 ty => Sbinop op (trans_expr mkv a1) (trans_expr mkv a2) ty
  end.

Definition trans_exprs(mkv: mkvar)(al: list sexp): list sexp :=
  map (trans_expr mkv) al.

Definition trans_lhs_ret(inst: sexp)(p: sexp*(ident*type)): stmt :=
  Sassign (fst p) (Sfield inst (fst (snd p)) (snd (snd p))).

Definition trans_lhs_rets(l: list (sexp*(ident*type)))(inst: sexp): stmt :=
  let s := map (trans_lhs_ret inst) l in
  fold_right Sseq Sskip s.

Definition make_inst (oid: option sexp)(mkv: mkvar)(isid: ident)(sty: type)(j: int): sexp :=
  match oid with
  | None => mkv isid sty
  | Some a =>
     let aty := Tarray xH sty (Int.intval j) in
     let insta := mkv isid aty in
     Saryacc insta a sty
  end.

Fixpoint trans_lhs_rets_simpl(s: stmt)(l: list stmt) : stmt :=
  match l with
  | nil => s
  | cons s1 tl => trans_lhs_rets_simpl (Sseq s s1) tl
  end.

Definition trans_eqf(mkv: mkvar)(s: eqf): eqf :=
  (trans_expr mkv (fst s), trans_expr mkv (snd s)).

Definition trans_calldef(c: calldef): calldef :=
  mkcalldef (cakind c) (instid c) (callid c) (callnum c) (csid c) (cfield c) (argtys c) ((OUTSTRUCT, mkcstruct c)::nil).

Fixpoint trans_stmt(mkv: mkvar)(s: stmt): stmt :=
  match s with
  | Scall oid lh cdef vals =>
     let cnid := callid cdef in
     let args := trans_exprs mkv vals in
     let lv := trans_exprs mkv lh in
     match cakind cdef with
     | true =>
        match cfield cdef with
        | Fnil => Scall oid lv cdef args
        | _ =>
          let sty := mkcstruct cdef in
          let inst := make_inst oid mkv (instid cdef) sty (intof_opti (callnum cdef)) in
          let c := trans_calldef cdef in
          let l := map (trans_lhs_ret inst) (combine lv (rettys cdef)) in
          let cs := Scall oid (inst::nil) c args in
          trans_lhs_rets_simpl cs l
        end
     | false =>
        Scall oid lv cdef args
     end
  | Sfor a1 a2 a3 s1 =>
     Sfor (option_map (trans_eqf mkv) a1) (trans_expr mkv a2) (trans_eqf mkv a3) (trans_stmt mkv s1)
  | Sseq s1 s2 => Sseq (trans_stmt mkv s1) (trans_stmt mkv s2)
  | Sskip => Sskip
  | Sassign lh a => Sassign (trans_expr mkv lh) (trans_expr mkv a)
  | Sif a s1 s2 =>
     let st := trans_stmt mkv s1 in
     let sf := trans_stmt mkv s2 in
     Sif (trans_expr mkv a) st sf
  | Scase lh swt cases =>
    Scase (trans_expr mkv lh) (trans_expr mkv swt) (trans_patns (trans_expr mkv) cases)
  end.

Definition makevar(b: func): mkvar :=
  let sty := mknstruct b in
  let nsd := Ssvar OUTSTRUCT sty in
  Sfield nsd.

Definition trans_body(b: func): func :=
  let sty := mknstruct b in
  let nsd := Ssvar OUTSTRUCT sty in
  let s := trans_stmt (Sfield nsd) b.(nd_stmt) in
  (mknode b.(nd_kind) (nd_args b) ((OUTSTRUCT, sty)::nil) nil (nd_vars b)
     s b.(nd_sid) b.(nd_fld)).

Definition trans_node(fd: ident*func): res (ident*func) :=
  if nd_kind (snd fd) then
    match nd_fld (snd fd) with
    | Fnil => OK fd
    | _ =>
      if zlt 0 (sizeof_fld (nd_fld (snd fd))) && zle (sizeof_fld (nd_fld (snd fd))) Int.max_signed then
        OK (fst fd, trans_body (snd fd))
      else Error (msg "sizeof struct is overflow!")
    end
  else OK fd.

Definition trans_program(p: LustreF.program): res program :=
  do nodes <- mmap trans_node (node_block p);
  OK (mkprogram (type_block p) (defs_block p) (const_block p) nodes (node_main p)).

Lemma trans_expr_typeof:
  forall fd a,
  typeof (trans_expr (makevar fd) a) = typeof a.
Proof.
  induction a; simpl; auto.
Qed.

Lemma trans_exprs_typeof:
  forall fd args, map typeof (trans_exprs (makevar fd) args) = map typeof args.
Proof.
  unfold trans_exprs. intros.
  rewrite map_map. apply map_ext.
  intros. apply trans_expr_typeof; auto.
Qed.

Lemma trans_expr_lid_disjoint:
  forall lhs f,
  lid_disjoint lhs ->
  lid_disjoint (trans_expr (makevar f) lhs).
Proof.
  induction lhs; simpl; intros; auto.
  +unfold OUTSTRUCT, ACG_I. congruence.
  +destruct lhs2; auto. destruct H; subst.
   simpl; split; auto.
Qed.

Lemma trans_exprs_lid_disjoint:
  forall l (f: func),
  Forall (lid_disjoint) l ->
  Forall (lid_disjoint) (trans_exprs (makevar f) l).
Proof.
  induction 1; simpl; intros; auto.
  constructor 2; auto.
  apply trans_expr_lid_disjoint; auto.
Qed.

Lemma trans_lhs_rets_instidof:
  forall l inst s,
  instidof (trans_lhs_rets_simpl s (map (trans_lhs_ret inst) l)) = instidof s.
Proof.
  induction l; simpl; intros; auto.
  rewrite IHl. simpl. rewrite <-app_nil_end. auto.
Qed.

Lemma trans_stmt_instidof_map:
  forall s mkv,
  map instid (instidof (trans_stmt mkv s)) = map instid (instidof s).
Proof.
  induction s; intros; simpl; auto; try (repeat rewrite map_app; f_equal; auto; fail).
  destruct (cakind c) eqn:?; simpl; unfold cons_inst; rewrite Heqb; auto.
  destruct (cfield c) eqn:?; simpl; unfold cons_inst; try rewrite Heqb; auto.
  unfold trans_calldef. simpl. rewrite Heqb.
  rewrite trans_lhs_rets_instidof; auto.
Qed.

Lemma trans_body_ids_norepeat:
  forall f,
  ids_norepet f ->
  ids_plt OUTSTRUCT (allidsof f ++ predidof f) ->
  ids_norepet (trans_body f).
Proof.
  unfold ids_norepet, ids_norepet.
  unfold allidsof,predidof.
  intros. unfold trans_body, allvarsof in *.
  unfold makevar; simpl; intros.
  rewrite trans_stmt_instidof_map.
  apply ids_plt_le_notin with OUTSTRUCT _ _ in H0.
  repeat rewrite map_app in *. intuition.
  +apply list_norepet_app.
   apply list_norepet_app in H1. destruct H1 as [? [? ?]].
   simpl; intuition.
   -constructor; auto. constructor.
   -red; simpl; intros. destruct H7; subst.
    *red; intros. subst. apply H0.
     apply in_or_app. left.
     apply in_or_app; auto.
    *eauto.
  +apply list_norepet_app in H. intuition.
  +red; simpl; intros.
   apply in_app_or in H3. destruct H3.
   -apply H2; auto. apply in_or_app;auto.
    apply in_or_app; auto.
   -simpl in H3. destruct H3; auto. subst.
    red; intros; subst. apply H0.
    apply in_or_app. right. apply in_or_app; auto.
  +apply H4. apply in_app_or in H3.
   destruct H3; apply in_or_app;[left | right].
   -apply in_app_or in H3. destruct H3; apply in_or_app; auto.
    simpl in *. unfold OUTSTRUCT, ACG_I in *.
    destruct H3. congruence. destruct H3.
   -apply in_or_app; auto.
  +apply Ple_refl.
Qed.

Lemma trans_program_gids_norepet:
  forall p p', trans_program p = OK p' ->
  globidsof p' = globidsof p.
Proof.
  unfold globidsof. intros. monadInv H.
  simpl. apply trans_nodes_fids_eq in EQ.
  rewrite <-EQ; auto.
  unfold trans_node. intros.
  destruct (nd_kind _); try congruence.
  destruct (nd_fld _); try congruence.
  destruct (_ && _); inv H. auto.
Qed.

Lemma trans_program_ids_range:
  forall p p', trans_program p = OK p' ->
  ids_range OUTSTRUCT (node_block p) ->
  ids_range ACG_MEMCPY (node_block p').
Proof.
  unfold trans_program. intros. monadInv H.
  simpl. red. intros.
  eapply in_mmap_iff in H; eauto. destruct H as [? [? ?]].
  apply H0 in H1. unfold trans_node in H.
  cut (Ple ACG_MEMCPY OUTSTRUCT). intros.
  destruct (nd_kind _); simpl in *.
  +destruct (nd_fld _).
   -inv H. eapply ids_plt_trans; eauto.
   -destruct (_ && _); inv H. simpl.
    unfold trans_body, allidsof,allvarsof,predidof in *.
    simpl in *. rewrite trans_stmt_instidof_map, map_app in *.
    red; intros. apply in_app_or in H. destruct H.
    apply in_app_or in H. destruct H.
    *eapply ids_plt_trans; eauto.
     apply in_or_app. left. apply in_or_app. auto.
    *simpl in *. destruct H; subst; try tauto.
     unfold Plt, OUTSTRUCT, ACG_MEMCPY. omega.
    *eapply ids_plt_trans; eauto. apply in_or_app; right.
     apply in_or_app; auto.
  +inv H. eapply ids_plt_trans; eauto.
  +unfold Ple, ACG_MEMCPY, OUTSTRUCT. omega.
Qed.