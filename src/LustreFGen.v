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

(** Translation of tempo statement. *)

Require Import Coqlib.
Require Import AST.
Require Import Errors.
Require Import Integers.
Require Import Lident.
Require Import Cltypes.
Require Import Ltypes.
Require Import Lop.
Require Import LustreR.
Require Import Lustre.
Require Import LustreF.
Require Import Permutation.
Require Import Inclusion.

(** example of fbyn translation. *)
(** x = fby(y ; 2; 10);

typedef struct { int idx; array_int_2 items; } struct_fby;

if (outC->init) {
    for (i = 0; i < 2; i++) {
      fs.items[i] = 10;
    }
    fs.idx = 0;
  }
x = fs.items[fs.idx];
fs.items[fs.idx] = y;
fs.idx = (fs.idx + 1) % 2; *)

Definition loop_cond (j: int) :=
  Sbinop Olt (Svar ACG_J type_int32s) (Sconst (Cint j) type_int32s) type_bool.

Definition loop_init :=
  (Svar ACG_J type_int32s, Sconst (Cint Int.zero) type_int32s).

Definition loop_add :=
  (Svar ACG_J type_int32s, self_add ACG_J).

Definition cons_for(s: stmt)(i: int) :=
  Sfor (Some loop_init) (loop_cond i) loop_add s.

Definition flag_incr:=
  Sassign (Ssvar ACG_INIT type_bool) (Sconst (Cbool false) type_bool).

(** translate fbyn. *)

Definition cons_fbyn(lh a1 a2 sa: sexp)(i: int)(aty: type): stmt :=
  let ei := Sfield sa FBYIDX type_int32s in (**r acg_fby1.idx  *)
  let ea := Sfield sa FBYITEM aty in (**r acg_fby1.items  *)
  let fs := Sassign (Saryacc ea (Svar ACG_J type_int32s) (typeof a2)) a2 in (**r acg_fby1.items[acg_j] = a2  *)
  let init := Sassign ei (Sconst (Cint Int.zero) type_int32s) in (**r acg_fby1.idx = 0  *)
  let fs := cons_for fs i in
  let s1 := Sif (Ssvar ACG_INIT type_bool) (Sseq fs init) Sskip in
  let s2 := Sassign lh (Saryacc ea ei (typeof a2)) in (**r lh = acg_fby1.items[acg_fby1.idx]  *)
  (Sseq s1 s2).

(** translate statement. *)

Fixpoint trans_stmt(s: LustreR.stmt): stmt:=
  match s with
  | LustreR.Sassign lh a => Sassign lh a
  | LustreR.Scall oid lhs cdef a => Scall oid lhs cdef a
  | LustreR.Sfor a1 a2 a3 fs => Sfor a1 a2 a3 (trans_stmt fs)
  | LustreR.Sifs a s1 s2 => Sif a (trans_stmt s1) (trans_stmt s2)
  | LustreR.Scase lh a pel => Scase lh a pel
  | LustreR.Sseq s1 s2 => Sseq (trans_stmt s1) (trans_stmt s2)
  | LustreR.Sfby lh id a1 a2 =>
    Sif (Ssvar ACG_INIT type_bool) (Sassign lh a2) (Sassign lh (Ssvar id (typeof a1)))
  | LustreR.Sfbyn lh (id1,id2,aid) i a1 a2 =>
     let aty := Tarray aid (typeof a1) (Int.unsigned i) in
     let sty := make_fbyn_type id2 aty in
     let sa := Ssvar id1 sty in
     cons_fbyn lh a1 a2 sa i aty
  | LustreR.Sarrow lh a1 a2 => Sif (Ssvar ACG_INIT type_bool) (Sassign lh a1) (Sassign lh a2)
  | LustreR.Sskip => Sskip
  | LustreR.Stypecmp _ _ _ => Sskip
  end.

Fixpoint trans_peqs (eqs: list eqt): stmt :=
  match eqs with
  | nil => Sskip
  | cons (Eqt_assign eq) eql =>  Sseq (Sassign (fst eq) (snd eq)) (trans_peqs eql)
  | cons (Eqt_counter eq) eql =>  Sseq (Sassign (fst eq) (snd eq)) (trans_peqs eql)
  | cons Eqt_skip eql => trans_peqs eql
  end.

(**r translate postpositive statement of tempo statement. *)

Definition mkpoststmt(eqs: list eqt): stmt :=
   if le_lt_dec (length eqs) 0 then Sskip
   else Sseq (trans_peqs eqs) flag_incr.

Fixpoint mkloopid(eqs: list eqt): list (ident*type) :=
  match eqs with
  | nil => nil
  | cons (Eqt_counter eq) eql => (ACG_J,type_int32s)::nil
  | cons _ eql => mkloopid eql
  end.

Fixpoint fbyeqof(s: LustreR.stmt): list eqt :=
  match s with
  | LustreR.Sseq s1 s2 =>fbyeqof s1 ++ fbyeqof s2
  | LustreR.Sfor _ _ _ s => fbyeqof s
  | LustreR.Sifs _ s1 s2 => fbyeqof s1 ++ fbyeqof s2
  | LustreR.Sfby lh id a1 a2 => Eqt_assign (Ssvar id (typeof a1), a1)::nil
  | LustreR.Sfbyn lh (id1,id2,aid) i a1 a2 =>
     let aty := Tarray aid (typeof a1) (Int.unsigned i) in
     let sty := make_fbyn_type id2 aty in
     let sa := Ssvar id1 sty in
     let eq1 := Eqt_assign (Saryacc (Sfield sa FBYITEM aty) (Sfield sa FBYIDX type_int32s) (typeof a1), a1) in
     let eq2 := Eqt_counter (index_incr sa i) in
     eq1 :: eq2 ::nil
  | Sarrow _ _ _ => Eqt_skip :: nil
  | _ => nil
  end.

(** translate body of node. *)

Definition trans_body(f: LustreR.node): func :=
  let s := trans_stmt f.(nd_stmt) in
  let lv := fbyvarsof f.(nd_stmt) in
  let eqs := fbyeqof f.(nd_stmt) in
  let s1 := mkpoststmt eqs in
  let vars := mkloopid eqs in
  let svars := if lt_dec 0 (length eqs) then (ACG_INIT, type_bool) :: lv else nil in
  mknode f.(nd_kind) f.(nd_args) f.(nd_rets) svars (nd_vars f++vars) (Sseq s s1) f.(nd_sid) f.(nd_fld).

Definition trans_node(f: ident*LustreR.node): ident*func :=
  (fst f,trans_body (snd f)).

Definition trans_program (p: LustreR.program): program :=
  let nodes := map trans_node (node_block p) in
  mkprogram (type_block p) (defs_block p) (const_block p) nodes (node_main p).


Lemma trans_peqs_instidof:
  forall l, instidof (trans_peqs l) = nil.
Proof.
  induction l; simpl; auto.
  destruct a; auto.
Qed.

Lemma trans_stmt_instidof:
  forall s, instidof (trans_stmt s) = LustreR.instidof s.
Proof.
  induction s; simpl; intros; auto.
  f_equal; auto.
  destruct p. destruct p. auto.
  f_equal; auto.
Qed.

Lemma mkpoststmt_instidof:
  forall l,
  instidof (mkpoststmt l) = nil.
Proof.
  unfold mkpoststmt. intros.
  destruct (le_lt_dec _ _); auto. simpl.
  rewrite trans_peqs_instidof; auto.
Qed.

Lemma mkloopid_idrange:
  forall l, mkloopid l = nil \/ mkloopid l = (ACG_J, type_int32s) :: nil.
Proof.
  induction l; simpl; auto.
  destruct a; auto.
Qed.

Lemma mkloopid_in:
  forall l a, In (Eqt_counter a) l ->
  mkloopid l = (ACG_J, type_int32s) :: nil.
Proof.
  induction l; simpl; intros; try tauto.
  destruct a, H;try congruence; eauto.
Qed.

Lemma fbyeqof_length:
  forall s, length (LustreR.fbyeqof s) = length (fbyeqof s).
Proof.
  induction s; simpl; auto.
  repeat rewrite app_length; auto.
  destruct p. destruct p. auto.
  repeat rewrite app_length; auto.
Qed.

Lemma allvarsof_permut:
  forall (f:LustreR.node) z,
  Permutation (mkloopid z ++ allvarsof f)
   (((nd_vars f ++ mkloopid z) ++ nd_args f) ++ nd_rets f).
Proof.
  intros. unfold allvarsof.
  repeat rewrite <-app_ass. apply Permutation_app_tail.
  apply Permutation_app_tail. apply Permutation_app_swap.
Qed.

Lemma mkloopid_norepet:
  forall z, list_norepet (map fst (mkloopid z)).
Proof.
  intros.
  destruct mkloopid_idrange with z as [ | ];
  rewrite H; simpl; auto;
  constructor; auto. constructor.
Qed.

Lemma mkloopid_disjoint:
  forall (f: LustreR.node) z,
  ~ In ACG_J (allidsof f ++ LustreR.predidof f) ->
  list_disjoint (map fst (mkloopid z)) (map fst (allvarsof f)).
Proof.
  intros. destruct mkloopid_idrange with z as [ | ];
  rewrite H0; red; simpl; intros; try tauto.
  destruct H1; subst; try tauto.
  red; intros; subst. apply H; auto.
  apply in_or_app; auto.
Qed.

Lemma trans_body_allidsof_norepet:
  forall f z,
  LustreR.ids_norepet f ->
  ids_plt ACG_INIT (allidsof f ++ LustreR.predidof f) ->
  list_norepet (map fst (mkloopid z ++ allvarsof f)).
Proof.
  intros. rewrite map_app.
  apply ids_plt_le_notin with ACG_J _ _ in H0;
   try (unfold Ple, ACG_J, ACG_INIT; omega).
  apply list_norepet_app. repeat (split; auto).
  -apply mkloopid_norepet.
  -destruct H. auto.
  -apply mkloopid_disjoint;auto.
Qed.

Lemma trans_body_ids_norepet:
  forall f, LustreR.ids_norepet f ->
  ids_plt ACG_INIT (allidsof f ++ LustreR.predidof f) ->
  ids_norepet (trans_body f).
Proof.
  intros.
  assert(A: ~ In ACG_J (allidsof f ++ LustreR.predidof f)).
    apply ids_plt_le_notin with ACG_INIT; auto.
    unfold Ple ,ACG_J, ACG_INIT. omega.
  apply ids_plt_le_notin with ACG_INIT _ _ in H0; try apply Ple_refl.
  destruct H as [? [? ?]]. unfold trans_body.
  unfold ids_norepet, allidsof, allvarsof,LustreR.predidof,predidof in *.
  simpl in *. rewrite mkpoststmt_instidof,  <-app_nil_end.
  erewrite trans_stmt_instidof; eauto.
  destruct H2.
  repeat (split; auto).
  +apply list_norepet_permut with (map fst (mkloopid (fbyeqof (nd_stmt f)) ++ allvarsof f)).
   destruct mkloopid_idrange with (fbyeqof (nd_stmt f)) as [ | ];
   rewrite H4; simpl; auto.
   constructor; auto.
   red. intros. apply A. apply in_or_app; auto.
   apply Permutation_map. apply allvarsof_permut.
  +destruct (lt_dec _ _); simpl.
   -constructor; auto.
    red. intros. apply H0. apply in_or_app; auto.
   -apply list_norepet_app in H1. destruct H1 as [? [? ?]]; auto.
  +apply list_disjoint_incl_left with (map fst (mkloopid (fbyeqof (nd_stmt f))++allvarsof f)).
   destruct mkloopid_idrange with (fbyeqof (nd_stmt f));
   destruct (lt_dec 0 _) eqn:?; rewrite H4 in *; simpl.
   -red; simpl; intros. destruct H6; subst; eauto.
    red; intros. subst. apply H0. apply in_or_app; auto.
   -red; intros. apply H2; auto. apply in_or_app; auto.
   -red; simpl; intros. destruct H5, H6; subst.
    *unfold ACG_J, ACG_INIT. congruence.
    *red; intros. subst. apply A. apply in_or_app; auto.
    *red; intros. subst. apply H0. apply in_or_app; auto.
    *apply H2; auto.
   -red; simpl; intros. destruct H5; subst.
    *red; intros. subst. apply A. in_tac.
    *apply H2; auto. in_tac.
   -unfold allvarsof. repeat rewrite map_app. incl_tac.
  +red; intros. apply H3. apply in_app_or in H4.
   destruct H4; apply in_or_app; auto.
   right. apply in_app_or in H4. destruct H4.
   -apply in_or_app; left.
    destruct (lt_dec _ _); simpl in *; try tauto.
    destruct H4; auto. unfold ACG_INIT,ACG_I in *. congruence.
   -apply in_or_app; auto.
Qed.

Lemma trans_program_ids_range:
  forall p, LustreR.ids_range OUTSTRUCT (node_block p) ->
  ids_range OUTSTRUCT (node_block (trans_program p)).
Proof.
  intros. simpl. red; intros.
  apply in_map_iff with (y:=fd) in H0; auto. destruct H0 as [? [? ?]].
  subst. red in H.
  unfold allidsof, predidof,LustreR.predidof, allvarsof in *.
  simpl in *. rewrite mkpoststmt_instidof, <-app_nil_end.
  erewrite trans_stmt_instidof; eauto.
  apply H in H1; auto.
  red. intros.
  apply Permutation_in with (l':=(map fst
          (mkloopid (fbyeqof (nd_stmt (snd x)))++allvarsof (snd x)) ++
        map fst
          (if lt_dec 0 (length (fbyeqof (nd_stmt (snd x))))
           then (ACG_INIT, type_bool) :: fbyvarsof (nd_stmt (snd x))
           else nil) ++ map instid (LustreR.instidof (nd_stmt (snd x)))))  in H0.
  apply in_app_or in H0. simpl in *.
  destruct H0.
  +destruct mkloopid_idrange with (fbyeqof (nd_stmt (snd x))) as [ | ];
   rewrite H2 in *; simpl in *.
   -apply H1. apply in_or_app; auto.
   -destruct H0; subst.
    unfold Plt, OUTSTRUCT, ACG_J. omega.
    apply H1. apply in_or_app; auto.
  +destruct (lt_dec _ _); simpl in *.
   destruct H0; subst.
   -unfold Plt, OUTSTRUCT, ACG_INIT. omega.
   -apply H1. apply in_or_app; right; auto.
   -apply H1. apply in_or_app; right. apply in_or_app; auto.
  +apply Permutation_app_tail. apply Permutation_map.
   apply Permutation_sym. apply allvarsof_permut.
Qed.

Lemma trans_program_const_block:
  forall p,
  const_block p = const_block (trans_program p).
Proof.
  intros. auto.
Qed.

Lemma trans_program_gids_norepet:
  forall p, globidsof (trans_program p) = globidsof p.
Proof.
  intros.
  unfold globidsof. intros.
  simpl. repeat rewrite map_map. auto.
Qed.
