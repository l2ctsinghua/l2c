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
Require Import Inclusion.
Require Import Cop.
Require Import Ctypes.
Require Import Cltypes.
Require Import Lident.
Require Import Ltypes.
Require Import Lop.
Require Import Lustre.
Require Import Permutation.
Require Import ExtraList.

Inductive unary_operationL : Type :=
  | Oshort : unary_operationL            (* convert to short(signed 16 bits) ([short]) *)
  | Oint : unary_operationL              (* convert to int(signed 32 bits) ([int]) *)
  | Ofloat : unary_operationL            (* convert to float(32 bits) ([float]) *)
  | Oreal : unary_operationL             (* convert to real(64 bits) ([real]) *)
  | Onot : unary_operationL              (* boolean negation ([not]) *)
  | Opos : unary_operationL              (* positive (unary [+]) *)
  | Oneg : unary_operationL.             (* opposite (unary [-]) *)

Inductive hstmt: Type:=
  | Hmapary: ident*type -> binary_operationL -> sexp -> sexp -> hstmt
  | Hmaptycmp: ident*type -> bool -> sexp -> sexp -> hstmt
  | Hmapunary: ident*type -> unary_operationL -> sexp -> hstmt
  | Hfoldary: ident*type -> binary_operationL -> sexp -> sexp -> hstmt
  | Hfoldunary: ident*type -> unary_operation -> sexp -> hstmt
  | Hfoldcast: ident*type -> sexp -> type -> hstmt
  | Harydef: ident*type -> sexp -> hstmt
  | Haryslc: ident*type -> sexp -> int -> hstmt
  | Hboolred: ident*type -> sexp -> hstmt
  | Hmapcall: lhs -> calldef -> list sexp -> hstmt
  | Hmapfoldcall: ident*type -> ident*type -> lhs -> calldef -> sexp -> list sexp -> hstmt.

Inductive expr: Type:=
  | Expr: sexp -> expr
  | Earyprj: sexp -> list sexp -> sexp -> expr
  | Ecase: sexp -> list (patn*sexp) -> expr
  | Eif: sexp -> sexp -> sexp -> expr
  | Eprefix: binary_operationL -> list sexp -> expr
  | Etypecmp: bool -> sexp -> sexp -> expr.

Inductive stmt: Type :=
  | Sassign: ident*type -> expr -> stmt
  | Scall: lhs -> calldef -> list sexp -> stmt
  | Sfor: bool -> hstmt -> int -> stmt
  | Sarydif: ident*type -> int -> list sexp -> stmt
  | Smix: ident*type ->sexp -> list lindex -> sexp ->  stmt
  | Sstruct: ident*type -> fieldlist -> list sexp -> stmt
  | Sfby: ident*type -> ident -> sexp -> sexp -> stmt
  | Sfbyn: ident*type -> (ident*ident*ident) -> int -> sexp -> sexp -> stmt
  | Sarrow: ident*type -> sexp -> sexp -> stmt
  | Sskip: stmt.

Definition ridl_of_e (e: expr) : list ident :=
  match e with
  | Expr a => get_expids a
  | Earyprj a1 al a2 => get_expids a1 ++ get_expsids al ++ get_expids a2
  | Ecase a pl => get_expids a ++ flat_map (fun p => get_expids (snd p)) pl
  | Eif a1 a2 a3 => get_expids a1 ++ get_expids a2 ++ get_expids a3
  | Eprefix _ al => get_expsids al
  | Etypecmp _ a1 a2 => get_expids a1 ++ get_expids a2
  end.

Definition lidl_of_fs (fs: hstmt): list ident :=
  match fs with
  | Hmaptycmp a _ _  _ => fst a :: nil
  | Hmapary a _ _ _ => fst a :: nil
  | Hmapunary a _ _ => fst a :: nil
  | Hfoldary a _ _ _  => fst a :: nil
  | Hfoldunary a _ _  => fst a :: nil
  | Hfoldcast a _ _  => fst a :: nil
  | Harydef a _ => fst a :: nil
  | Haryslc a _ _ => fst a :: nil
  | Hboolred a _ => fst a :: nil
  | Hmapcall lh _ _ => map fst lh
  | Hmapfoldcall a f lh _ _ _  => fst a :: fst f :: map fst lh
  end.

Definition lidl_of_s (s: stmt) : list ident :=
  match s with
  | Sassign a  _ => fst a :: nil
  | Scall lh _ _ => map fst lh
  | Sfor _ fs _ => lidl_of_fs fs
  | Sarydif a _ _  => fst a :: nil
  | Smix a _ _ _ => fst a :: nil
  | Sstruct a _ _ => fst a :: nil
  | Sfbyn a _ _ _ _ => fst a :: nil
  | Sfby a _ _ _ => fst a :: nil
  | Sarrow a _ _ => fst a :: nil
  | Sskip => nil
  end.

Definition ridl_of_fs (fs: hstmt): list ident :=
  match fs with
  | Hmaptycmp _ _ e1 e2 => get_expids e1 ++ get_expids e2
  | Hmapary _ _ e1 e2 => get_expids e1 ++ get_expids e2
  | Hmapunary _ _ e1 => get_expids e1
  | Hfoldary _ _ e1 e2  => get_expids e1 ++ get_expids e2
  | Hfoldunary _ _ e1 => get_expids e1
  | Hfoldcast _ e1 _ => get_expids e1
  | Harydef _ e => get_expids e
  | Haryslc _ e _ => get_expids e
  | Hboolred _ e => get_expids e
  | Hmapcall _ _ el => get_expsids el
  | Hmapfoldcall _ _ _ _ e el => get_expids e ++ get_expsids el
 end.

Definition ridl_of_s (s: stmt) : list ident :=
  match s with
  | Sassign _ e => ridl_of_e e
  | Scall _ _ el => get_expsids el
  | Sfor _ fs _ => ridl_of_fs fs
  | Sarydif _ _ el => get_expsids el
  | Smix _ e1 lil e2 => get_expids e1 ++ get_lindexids lil ++ get_expids e2
  | Sstruct _ _ cs => get_expsids cs
  | Sfbyn _ _ _ _ a2 =>  get_expids a2
  | Sfby _ _ _ a2 =>  get_expids a2
  | Sarrow _ a1 a2 => get_expids a1 ++ get_expids a2
  | Sskip => nil
  end.

Definition deps_of_stmt (ss: list stmt)(n: nat): depend :=
  let s := nth n ss Sskip in
  mkdepend (lidl_of_s s) (ridl_of_s s) n.

Definition deps_of_stmts (ss: list stmt): list depend :=
  map (deps_of_stmt ss) (seq O (length ss)).

Definition deps_of_stmts_simpl (eqs: list stmt) : list depend :=
  map (fun eq =>  mkdepend (lidl_of_s eq) (ridl_of_s eq) O) eqs.

Definition has_for(s: stmt): Z :=
  match s with
  | Sfor _ hs _ => 1
  | _ => 0
  end.

Fixpoint has_fors(l: list stmt): Z :=
  match l with
  | nil => 0
  | cons s sl =>
     let z := has_for s in
     if zlt z 1 then Zmax z (has_fors sl) else 1
  end.

Definition mkloopmapw(l: list stmt): params :=
  match has_fors l with
  | 0 => nil
  | _ => (ACG_I,type_int32s) :: nil
  end.

Definition trans_prefix_unary_expr (op: unary_operationL)(val: sexp)(ty: type) : sexp :=
  match op with
  | Oshort => Scast val (Cltypes.Tint I16 Signed)
  | Oint => Scast val (Cltypes.Tint I32 Signed)
  | Ofloat => Scast val (Cltypes.Tfloat F32)
  | Oreal => Scast val (Cltypes.Tfloat F64)
  | Onot => Sunop Cop.Onotbool val ty
  | Opos => val
  | Oneg => Sunop Cop.Oneg val ty
  end.

Definition prefix_unary_type (op: unary_operationL)(aty ty: type): Prop :=
  match op with
  | Oshort => ty = Tint I16 Signed
  | Oint => ty = Tint I32 Signed
  | Ofloat => ty = Tfloat F32
  | Oreal => ty = Tfloat F64
  | Onot => True
  | Opos => ty = aty
  | Oneg => True
  end.

Definition lids_of_e (e: expr) : list ident :=
  match e with
  | Expr a => get_lids a
  | Earyprj a1 al a2 => get_lids a1 ++ get_lids a2
  | Ecase a pl => flat_map (fun p => get_lids (snd p)) pl
  | Eif a1 a2 a3 => get_lids a2 ++ get_lids a3
  | Eprefix _ al => nil
  | Etypecmp _ a1 a2 => get_lids a1 ++ get_lids a2
  end.

Definition fbyvarsof_s(s: stmt): params:=
  match s with
  | Sfby lh id a1 a2 => (id,typeof a1)::nil
  | Sfbyn lh (id1,id2,aid) i a1 a2 =>
     let aty := Tarray aid (typeof a1) (Int.unsigned i) in
     (id1,make_fbyn_type id2 aty)::nil
  | _ => nil
  end.

Definition fbyeqof(s: stmt): list eqt :=
  match s with
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

Definition fbyvarsof(ss: list stmt): params :=
  flat_map fbyvarsof_s ss.

Definition fbyeqsof(ss: list stmt): list eqt :=
  flat_map fbyeqof ss.

Definition instidofh(h: hstmt): list calldef :=
  match h with
  | Hmapcall _ c _ => cons_inst c
  | Hmapfoldcall _ _ _ c _ _  => cons_inst c
  | _ => nil
  end.

Definition instidof_s(s: stmt): list calldef :=
  match s with
  | Scall _ c _ => cons_inst c
  | Sfor _ h _ => instidofh h
  | _ => nil
  end.

Definition instidof(ss: list stmt): list calldef :=
  flat_map instidof_s ss.

Definition initstmtsof1(f: hstmt): list stmt :=
  match f with
  | Hfoldary lh _ init _ => Sassign lh (Expr init) :: nil
  | Hfoldunary lh _ init => Sassign lh (Expr init) :: nil
  | Hfoldcast lh init _ => Sassign lh (Expr init) :: nil
  | Hboolred lh _ => Sassign lh (Expr (Sconst (Cint Int.zero) type_int32s)) :: nil
  | Hmapfoldcall lh _ _ _ init _ => Sassign lh (Expr init) :: nil
  | _ => nil
  end.

Definition initstmtsof2(f: hstmt): list stmt :=
  match f with
  | Hfoldary lh _ init _ => Sassign lh (Expr init) :: nil
  | Hfoldunary lh _ init => Sassign lh (Expr init) :: nil
  | Hfoldcast lh init _ => Sassign lh (Expr init) :: nil
  | Hboolred lh _ => Sassign lh (Expr (Sconst (Cint Int.zero) type_int32s)) :: nil
  | Hmapfoldcall lh _ _ _ init _ => Sassign lh (Expr init) :: nil
  | _ => nil
  end.

Definition nodenil:= (xH,mknode true nil nil nil nil (@nil stmt) xH Fnil).

Definition node: Type := general_node (list stmt).

Definition predidof(f: node) :=
  map fst (fbyvarsof (nd_stmt f)) ++ map instid (instidof (nd_stmt f)).

Definition ids_norepet(f: node) :=
  list_norepet (allidsof f) /\ list_norepet (predidof f)
   /\ list_disjoint (allidsof f) (predidof f)
   /\ ~ In ACG_INIT (map fst (fbyvarsof (nd_stmt f))).

Definition program: Type := general_program node.

Definition nodup_lids (l: list depend) :=
  list_norepet (flat_map (fun a => lidl a) l).

Definition ids_range(id: ident)(l: list (ident*node)): Prop :=
  forall fd, In fd l ->
  ids_plt id (allidsof (snd fd) ++ predidof (snd fd)).

Lemma ids_norepet_instid:
  forall f, ids_norepet f ->
  list_norepet (map instid (instidof (nd_stmt f))).
Proof.
  intros. destruct H as [? [? ?]].
  apply list_norepet_app in H0. intuition.
Qed.

Lemma ids_norepet_instid_permut:
  forall f ss, ids_norepet f ->
  Permutation (nd_stmt f) ss ->
  list_norepet (map instid (instidof ss)).
Proof.
  intros.
  apply list_norepet_permut with (map instid (instidof (nd_stmt f))); auto.
  apply ids_norepet_instid; auto.
  apply Permutation_map. apply flat_map_permutation; auto.
Qed.

Lemma has_for_range:
  forall s, 0 <= has_for s <=1.
Proof.
  destruct s; simpl; try omega.
Qed.

Lemma has_fors_range:
  forall s, 0 <= has_fors s <=1.
Proof.
  induction s; simpl; try omega.
  destruct (zlt _ _); try omega.
  generalize (has_for_range a). intros.
  destruct (zle (has_for a) (has_fors s)).
  rewrite Z.max_r; omega.
  rewrite Z.max_l; omega.
Qed.

Lemma mkloopmapw_norepet:
  forall l, list_norepet (map fst (mkloopmapw l)).
Proof.
  unfold mkloopmapw. intros.
  destruct (has_fors l); simpl.
  +constructor.
  +repeat constructor; auto.
  +repeat constructor; auto.
Qed.

Lemma mkloopmapw_range:
  forall l a, In a (mkloopmapw l) ->
  a = (ACG_I, type_int32s).
Proof.
  unfold mkloopmapw. intros l.
  destruct (has_fors l); simpl; intros; try tauto.
  +destruct H; auto. tauto.
  +destruct H; auto. tauto.
Qed.

Lemma mkloopmapw_idrange:
  forall l id, In id (map fst (mkloopmapw l)) ->
  id = ACG_I.
Proof.
  intros. apply in_map_iff in H.
  destruct H as [? [? ?]]. subst.
  apply mkloopmapw_range in H0.
  subst; auto.
Qed.

Lemma mkloopmapw_disjoint:
  forall s l,
  list_disjoint (ACG_I::nil) l ->
  list_disjoint (map fst (mkloopmapw s)) l.
Proof.
  intros. red; intros.
  apply H; auto.
  apply mkloopmapw_idrange in H0.
  destruct H0; subst; simpl; auto.
Qed.

Lemma has_fors_loop_in:
  forall l, 0 < has_fors l ->
  In (ACG_I, type_int32s) (mkloopmapw l).
Proof.
  induction l; simpl; intros.
  omega.
  unfold mkloopmapw. simpl.
  destruct (zlt (has_for a) 1); simpl; auto.
  destruct (Z.max (has_for a) (has_fors l)); try omega; simpl; auto.
Qed.

Lemma ids_norepet_fbyids_norepet:
  forall f, ids_norepet f ->
  list_norepet (map fst (fbyvarsof (nd_stmt f))).
Proof.
  intros.
  destruct H as [? [? ?]]. apply list_norepet_app in H0.
  intuition.
Qed.

Lemma ids_norepet_fbyids_norepet_permut:
  forall f ss, ids_norepet f ->
  Permutation (nd_stmt f) ss ->
  list_norepet (map fst (fbyvarsof ss)).
Proof.
  intros.
  apply list_norepet_permut with (map fst (fbyvarsof (nd_stmt f))); auto.
  apply ids_norepet_fbyids_norepet; auto.
  apply Permutation_map. apply flat_map_permutation; auto.
Qed.

Lemma ids_norepet_fbyids_flagid_notin:
  forall f ss, ids_norepet f ->
  Permutation (nd_stmt f) ss ->
  ~ In ACG_INIT (map fst (fbyvarsof ss)).
Proof.
  intros. destruct H as [? [? [? ?]]].
  red; intros. apply H3.
  eapply Permutation_in in H4; eauto.
  apply Permutation_map. apply flat_map_permutation; auto.
  apply Permutation_sym; auto.
Qed.

Lemma deps_of_stmts_simpl_app:
  forall l1 l2,
  deps_of_stmts_simpl (l1 ++ l2) = deps_of_stmts_simpl l1 ++ deps_of_stmts_simpl l2.
Proof.
  induction l1; simpl; intros; try rewrite IHl1; auto.
Qed.

Lemma nodup_lids_appa: forall (a: depend)(l: list depend),
  nodup_lids (a :: l)  ->
  nodup_lids l.
Proof.
  unfold nodup_lids. simpl. intuition.
  apply list_norepet_app in H. intuition.
Qed.

Lemma nodup_lids_sube: forall (l1 l2: list depend),
  nodup_lids (l1 ++ l2)  ->
  nodup_lids l1.
Proof.
  unfold nodup_lids. intuition.
  rewrite flat_map_app in H. apply list_norepet_app in H. intuition.
Qed.

Lemma nodup_lids_perm: forall (l1 l2: list depend),
  Permutation l1 l2 ->
  nodup_lids l1 ->
  nodup_lids l2.
Proof.
  unfold nodup_lids. intros.
  eapply list_norepet_permut; eauto.
  apply flat_map_permutation;trivial.
Qed.

Lemma topo_sorted_eqs_simpl:
  forall eql,
  topo_sorted (deps_of_stmts eql) <->
  topo_sorted (deps_of_stmts_simpl eql).
Proof.
  intros. split; intros;
  [ apply depend_toposorted with (deps_of_stmts eql) |
    apply depend_toposorted with (deps_of_stmts_simpl eql)]; trivial;
  unfold deps_of_stmts_simpl; unfold deps_of_stmts;
  repeat rewrite map_map; simpl;
  set (idll:= map (fun eq => lidl_of_s  eq) eql);
  rewrite <- seq_nth_fun_equal with _ _ (fun eq => mkdepend (lidl_of_s eq) (ridl_of_s eq) O) eql Sskip;
  trivial.
Qed.

Definition is_assign(s: stmt) : Prop :=
  match s with
  | Sassign _ (Expr _) => True
  | _ => False
  end.

Lemma lidl_of_fs_incl:
  forall s, incl (flat_map lidl_of_s (initstmtsof1 s)) (lidl_of_fs s).
Proof.
  induction s; simpl; try incl_tac.
Qed.

Lemma ridl_of_fs_incl:
  forall s, incl (flat_map ridl_of_s (initstmtsof1 s)) (ridl_of_fs s).
Proof.
  induction s; simpl; try rewrite <-app_nil_end; try incl_tac.
Qed.

Lemma initstmtsof_is_assign:
  forall s, Forall is_assign (initstmtsof1 s).
Proof.
  induction s; simpl; repeat constructor; simpl; auto.
Qed.
