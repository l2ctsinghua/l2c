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

(** Translation from LustreS to LustreR. *)

Require Import Coqlib.
Require Import AST.
Require Import Integers.
Require Import Errors.
Require Import Cop.
Require Import Lident.
Require Import Cltypes.
Require Import Ltypes.
Require Import Lop.
Require Import Toposort.
Require Import Lustre.
Require Import LustreS.
Require Import LustreR.
Require Import Permutation.
Require Import ExtraList.

Local Open Scope error_monad_scope.

Definition cons_aryprj(a i:sexp): res (sexp * sexp) :=
  do (t,z) <- typeof_array (typeof a);
  let cd1 := Sbinop Ole (Sconst (Cint Int.zero) type_int32s) i type_bool in
  let cd2 := Sbinop Olt i (Sconst (Cint (Int.repr z)) type_int32s) type_bool in
  OK (Sbinop Oand cd1 cd2 type_bool, Saryacc a i t).

Fixpoint cons_aryprjs(indexs: list sexp)(a i: sexp): res (sexp*sexp) :=
  match indexs with
  | nil  => cons_aryprj a i
  | hd :: tl =>
     do (cd, ethen) <- cons_aryprj a i;
     do (cds, ethens) <- cons_aryprjs tl ethen hd;
     OK (Sbinop Oand cd cds type_bool, ethens)
  end.

Definition trans_var_pary(v: ident*type): res sexp :=
  do (t,_) <- typeof_array (snd v);
  OK (Saryacc (lvarof v) (Svar ACG_I type_int32s) t).

Definition trans_expr_proj(exp: sexp): res sexp :=
  do (t,_) <- typeof_array (typeof exp);
  OK (Saryacc exp (Svar ACG_I type_int32s) t).

Fixpoint cons_arydif(lh: ident*type)(t: type)(el: list sexp)(i: int): stmt :=
  match el with
  | nil => Sskip
  | cons hd tl =>
      let s := Sassign (Saryacc (lvarof lh) (Sconst (Cint i) type_int32s) t) hd in
      Sseq s (cons_arydif lh t tl (Int.add i Int.one))
  end.

Fixpoint cons_struct(lh: ident*type)(fld: fieldlist)(es:list sexp): res stmt :=
  match fld,es with
  | Fcons fid fty ftl, hd :: tl =>
     let s1 := Sassign (Sfield (lvarof lh) fid fty) hd in
     do s2 <- cons_struct lh ftl tl;
     OK (Sseq s1 s2)
  | Fnil, nil => OK Sskip
  | _,_ => Error (msg "LustreRGen.trans_stmt: cons_struct")
  end.

Fixpoint cons_lhs_exp(lv: list sexp) (la: list sexp): res stmt :=
  match lv, la with
  | nil, nil => OK Sskip
  | hd1 :: tl1, hd2 :: tl2  =>
      let s := Sassign hd1 hd2 in
      do s1 <- cons_lhs_exp tl1 tl2;
      OK (Sseq s s1)
  | _, _ => Error (msg "Ls2lr.trans_stmt: cons_lhs_exp")
  end.

Definition trans_finit(s: hstmt): stmt :=
  match s with
  | Hfoldary lh _ init _ =>Sassign (lvarof lh) init
  | Hfoldunary lh _ init =>Sassign (lvarof lh) init
  | Hfoldcast lh init _ =>Sassign (lvarof lh) init
  | Hboolred lh _ => Sassign (lvarof lh) (Sconst (Cint Int.zero) type_int32s)
  | Hmapfoldcall lh _ _ _ init _ => Sassign (lvarof lh) init
  | _ => Sskip
end.

Definition trans_hcalldef(c: calldef) : res calldef :=
  match callnum c with
  | Some j => OK c
  | None => Error (msg "LustreRGen.trans_hcalldef")
  end.

Definition trans_calldef(c: calldef) : res calldef :=
  match callnum c with
  | Some j => Error (msg "LustreRGen.trans_calldef")
  | None => OK c
  end.

Definition trans_hstmt(s: hstmt): res stmt :=
  match s with
  | Hmaptycmp lh k a1 a2 =>
     do (t,_) <- typeof_array (typeof a1);
     let lh1 := Saryacc (lvarof lh) (Svar ACG_I type_int32s) type_bool in
     let a3 := Saryacc a1 (Svar ACG_I type_int32s) t in
     let a4 := Saryacc a2 (Svar ACG_I type_int32s) t in
     let s1 := Stypecmp lh1 a3 a4 in
     let s2 := Sassign lh1 (Sunop Onotbool lh1 type_bool) in
     if in_list (fst lh) (ACG_I::get_lids a1++get_lids a2) then
       Error (msg "LustreRGen.trans_hstmt: Hmaptyeq")
     else
       OK (if k then s1 else Sseq s1 s2)
  | Hmapary lh op a1 a2 =>
     do (t,_) <- typeof_array (snd lh);
     let es := Sbinop op (Saryacc a1 (Svar ACG_I type_int32s) t) (Saryacc a2 (Svar ACG_I type_int32s) t) t in
     OK (Sassign (Saryacc (lvarof lh) (Svar ACG_I type_int32s) t) es)
  | Hfoldary lh op init a =>
     let es := Sbinop op (Svar (fst lh) (snd lh)) (Saryacc a (Svar ACG_I type_int32s) (snd lh)) (snd lh) in
     OK (Sassign (lvarof lh) es)
  | Hmapunary lh op a1 =>
     do (t1,_) <- typeof_array (typeof a1);
     do (t2,_) <- typeof_array (snd lh);
     let es := trans_prefix_unary_expr op (Saryacc a1 (Svar ACG_I type_int32s) t1) t2 in
     OK (Sassign (Saryacc (lvarof lh) (Svar ACG_I type_int32s) t2) es)
  | Hfoldunary lh op init =>
     let es := Sunop op (Svar (fst lh) (snd lh)) (snd lh) in
     OK (Sassign (lvarof lh) es)
  | Hfoldcast lh init ty =>
     let es := Scast (Svar (fst lh) (snd lh)) ty in
     OK (Sassign (lvarof lh) es)
  | Harydef lh a =>
     do (t,_) <- typeof_array (snd lh);
     OK (Sassign (Saryacc (lvarof lh) (Svar ACG_I type_int32s) t) a)
  | Haryslc (lid,ty) a k =>
     do (aty,_) <- typeof_array ty;
     let ai := Sbinop Oadd (Sconst (Cint k) type_int32s) (Svar ACG_I type_int32s) type_int32s in
     OK (Sassign (Saryacc (Svar lid ty) (Svar ACG_I type_int32s) aty) (Saryacc a ai aty))
  | Hboolred (lid,ty) a =>
     let cond := Saryacc a (Svar ACG_I type_int32s) type_bool in
     let add := Sassign (Svar lid ty) (self_add lid) in
     OK (Sifs cond add Sskip)
  | Hmapcall lhs c a =>
     do lv <- mmap trans_var_pary lhs;
     do a' <- mmap trans_expr_proj a;
     do c <- trans_hcalldef c;
     OK (Scall (Some (Svar ACG_I type_int32s)) lv c a')
  | Hmapfoldcall lh th lhs c init a =>
     do lv <- mmap trans_var_pary lhs;
     do a' <- mmap trans_expr_proj a;
     do c <- trans_hcalldef c;
     let s1 := Sassign (lvarof th) (lvarof lh) in
     let fs := Scall (Some (Svar ACG_I type_int32s)) ((lvarof lh)::lv) c ((Svar (fst th) (snd th)) :: a') in
     OK (Sseq s1 fs )
end.

Definition cons_mix_cond(ty: type) (li: lindex) : res (sexp*type):=
  match li with
  | Label fid =>
    do fld <- fieldof_struct ty;
    do sty <- field_type fid fld;
    OK (Sconst (Cbool true) type_bool, sty)
  | Index index =>
    do (aty, num) <- typeof_array ty;
    let enum := Sconst (Cint (Int.repr num)) type_int32s in
    let cond1 := Sbinop Ole (Sconst (Cint Int.zero) type_int32s) index type_bool  in (*0<=i*)
    let cond2 := Sbinop Olt index enum type_bool in (*i<num*)
    OK (Sbinop Oand cond1 cond2 type_bool, aty) (*0<=i & i<num*)
  end.

Fixpoint cons_mixs_cond (ty: type) (l: list lindex) : res sexp :=
  match l with
  | nil => OK (Sconst (Cbool true) type_bool)
  | hd::nil =>
    do (cond, t) <- cons_mix_cond ty hd;
    OK cond
  | hd::tl =>
    do (cond, t) <- cons_mix_cond ty hd;
    do conds <- cons_mixs_cond t tl;
    match hd with
    | Label _  => OK conds
    | Index _ => OK (Sbinop Oand cond conds type_bool)
    end
  end.

Definition cons_mix_expr (lh: sexp) (li: lindex) : res sexp :=
  match li with
  | Label fid =>
    do fld <- fieldof_struct (typeof lh);
    do ty <- field_type fid fld;
    OK (Sfield lh fid ty)
  | Index index =>
    do (aty, num) <- typeof_array (typeof lh);
    OK (Saryacc lh index aty)
  end.

Fixpoint cons_mixs_expr (lh: sexp) (l: list lindex) : res sexp :=
  match l with
  | nil => OK lh
  | hd::tl =>
    do lh' <- cons_mix_expr lh hd;
    cons_mixs_expr lh' tl
  end.

Fixpoint cons_prefix(es: list sexp)(e: sexp)(op: binary_operationL)(ty: type): sexp :=
  match es with
  | nil => e
  | hd :: tl => cons_prefix tl (Sbinop op e hd ty) op ty
  end.

Definition trans_expr (lh: ident*type)(e: expr): res stmt:=
  match e with
  | Expr a => OK (Sassign (lvarof lh) a)
  | Earyprj a is d =>
     match is with
     | nil => Error (msg "LustreRGen.trans_stmt: Saryprj indexs is null")
     | i::il =>
        do (conds,thens) <- cons_aryprjs il a i;
        OK (Sifs conds (Sassign (lvarof lh) thens) (Sassign (lvarof lh) d))
     end
  | Ecase a pel => OK (Scase (lvarof lh) a pel)
  | Eif a a1 a2 =>
     OK (Sifs a (Sassign (lvarof lh) a1) (Sassign (lvarof lh) a2))
  | Eprefix op al  =>
     match al with
     | nil => Error (msg "LustreRGen.trans_expr: Eprefix")
     | hd :: nil => Error (msg "LustreRGen.trans_expr: Eprefix")
     | hd :: hd1 :: tl => OK (Sassign (lvarof lh) (cons_prefix tl (Sbinop op hd hd1 (snd lh)) op (snd lh)))
     end
  | Etypecmp k a1 a2 =>
     let s1 := Stypecmp (lvarof lh) a1 a2 in
     let s2 := Sassign (lvarof lh) (Sunop Onotbool (lvarof lh) type_bool) in
     if in_list (fst lh) (ACG_I::nil) then
       Error (msg "LustreRGen.trans_expr: Etypecmp")
     else
       OK (if k then s1 else Sseq s1 s2)
  end.

Definition trans_stmt(s: LustreS.stmt): res stmt:=
  match s with
  | LustreS.Sassign lh a => trans_expr lh a
  | LustreS.Scall lh c a =>
     do c <- trans_calldef c;
     OK (Scall None (map lvarof lh) c a)
  | LustreS.Sfor true fs j =>
     do fs1 <- trans_hstmt fs;
     OK (Sseq (trans_finit fs) (Sfor (Some Lustre.loop_init) (loop_cond j) Lustre.loop_add fs1))
  | LustreS.Sfor false fs j =>
     do fs1 <- trans_hstmt fs;
     OK (Sfor None (loop_cond j) Lustre.loop_add fs1)
  | LustreS.Sarydif lh i a =>
     do (t,_) <- typeof_array (snd lh);
     OK (cons_arydif lh t a i)
  | LustreS.Smix lh a ids exp =>
     let s1 := Sassign (lvarof lh) a in
     do cond <- cons_mixs_cond (snd lh) ids;
     do ethen <- cons_mixs_expr (lvarof lh) ids;
     let sif := Sifs cond (Sassign ethen exp) Sskip in
     OK (Sseq s1 sif)
  | LustreS.Sstruct lh fld a => cons_struct lh fld a
  | LustreS.Sfbyn lh ti i a1 a2 => OK (Sfbyn (lvarof lh) ti i a1 a2)
  | LustreS.Sfby lh id a1 a2 => OK (Sfby (lvarof lh) id a1 a2)
  | LustreS.Sarrow lh a1 a2 => OK (Sarrow (lvarof lh) a1 a2)
  | LustreS.Sskip => OK Sskip
  end.

Fixpoint trans_stmts(ss: list LustreS.stmt): res stmt:=
  match ss with
  | nil => OK Sskip
  | s :: tl =>
     do s1 <- trans_stmt s;
     do s2 <- trans_stmts tl;
     OK (Sseq s1 s2)
  end.

Definition trans_body(b: LustreS.node): res node :=
  do s <- trans_stmts b.(nd_stmt);
  let vl := b.(nd_vars) ++ mkloopmapw b.(nd_stmt) in
  OK (mknode b.(nd_kind) b.(nd_args) b.(nd_rets) nil vl s b.(nd_sid) b.(nd_fld)).

Definition trans_node(f: ident*LustreS.node): res (ident*node) :=
  do body <- trans_body (snd f);
  OK (fst f,body).

Definition trans_program(p: LustreS.program): res program :=
  do nodes <- mmap trans_node (node_block p);
  OK (mkprogram (type_block p) (defs_block p) (const_block p) nodes (node_main p)).

Lemma cons_aryprjs_typeof_bool:
  forall ids a i c e,
  cons_aryprjs ids a i = OK (c, e) ->
  typeof c = type_bool.
Proof.
  induction ids; simpl; intros; monadInv H; auto.
Qed.

Lemma trans_hcalldef_eq:
  forall c x,
  trans_hcalldef c = OK x ->
  x = c.
Proof.
  unfold trans_hcalldef.
  intros. destruct (callnum c); inv H; auto.
Qed.

Lemma trans_calldef_eq:
  forall c x,
  trans_calldef c = OK x ->
  x = c.
Proof.
  unfold trans_calldef.
  intros. destruct (callnum c); inv H; auto.
Qed.

Lemma cons_mix_cond_typeof:
  forall a t cond t',
  cons_mix_cond t a = OK (cond, t') ->
  typeof cond = type_bool.
Proof.
  unfold cons_mix_cond. intros.
  destruct a; monadInv H; auto.
Qed.

Lemma cons_mixs_cond_typeof:
  forall lis t cond,
  cons_mixs_cond t lis = OK cond ->
  typeof cond = type_bool.
Proof.
  induction lis; simpl; intros.
  inv H; auto.
  destruct lis; monadInv H.
  eapply cons_mix_cond_typeof; eauto.
  destruct a; inv EQ2; eauto.
Qed.

Lemma trans_hstmt_instidof_eq:
  forall h1 h2,
  trans_hstmt h1 = OK h2 ->
  instidof h2 = instidofh h1.
Proof.
  destruct h1; intros; inv H; simpl; auto;
  try (monadInv H1; simpl; auto);
  try (f_equal; eapply trans_hcalldef_eq; eauto;fail).
  +destruct (_ || _); inv EQ0; auto.
   destruct b; auto.
  +destruct p. monadInv H1; auto.
  +destruct p. inv H1. auto.
Qed.

Lemma cons_arydif_instidof_eq:
  forall l p a i,
  instidof (cons_arydif p a l i) = nil.
Proof.
  induction l; simpl; auto.
Qed.

Lemma cons_struct_instidof_eq:
  forall l f p s,
  cons_struct p f l = OK s ->
  instidof s = nil.
Proof.
  induction l, f; intros; inv H; simpl; auto.
  monadInv H1. simpl. eauto.
Qed.

Lemma trans_stmt_instidof_eq:
  forall s1 s2,
  trans_stmt s1 = OK s2 ->
  instidof s2 = instidof_s s1.
Proof.
  induction s1; intros; inv H; simpl; auto.
  +destruct e; try (inv H1; auto; fail).
   -inv H1. destruct l; inv H0; auto.
    monadInv H1; auto.
   -inv H1. destruct l; try congruence.
    destruct l; try congruence. inv H0; auto.
   -unfold trans_expr in *.
    destruct (in_list _ _); inv H1. auto.
    destruct b; auto.
  +monadInv H1. simpl.
   f_equal; eapply trans_calldef_eq; eauto.
  +destruct b; monadInv H1; simpl;
   erewrite <-trans_hstmt_instidof_eq; eauto.
   destruct h; simpl; auto.
  +monadInv H1. apply cons_arydif_instidof_eq; auto.
  +monadInv H1. simpl; auto.
  +eapply cons_struct_instidof_eq; eauto.
Qed.

Lemma trans_stmts_instidof_eq:
  forall s1 s2,
  trans_stmts s1 = OK s2 ->
  instidof s2 = LustreS.instidof s1.
Proof.
  induction s1; intros; inv H; simpl; auto.
  monadInv H1. simpl. f_equal; eauto.
  eapply trans_stmt_instidof_eq; eauto.
Qed.

Lemma trans_finit_fbyvarsof_nil:
  forall h, fbyvarsof (trans_finit h) = nil.
Proof.
  destruct h; simpl; intros; auto.
Qed.

Lemma cons_arydif_fbyvarsof_nil:
  forall p x l i, fbyvarsof (cons_arydif p x l i) = nil.
Proof.
  induction l; simpl; auto.
Qed.

Lemma cons_struct_fbyvarsof_nil:
  forall l fld lh s, cons_struct lh fld l = OK s ->
  fbyvarsof s = nil.
Proof.
  induction l, fld; simpl; intros; inv H; auto.
  monadInv H1. simpl. eapply IHl; eauto.
Qed.

Lemma trans_hstmt_fbyvarsof_nil:
  forall h s,
  trans_hstmt h = OK s ->
  fbyvarsof s = nil.
Proof.
  destruct h; intros; try monadInv H; simpl in *; auto.
  -destruct (_ || _); inv EQ0; simpl; auto.
   destruct b; auto.
  -destruct p. monadInv H. auto.
  -destruct p. inv H; auto.
Qed.

Lemma trans_body_fbyvarsof:
  forall l s,
  trans_stmts l = OK s ->
  fbyvarsof s = LustreS.fbyvarsof l.
Proof.
  induction l; simpl; intros.
  inv H. simpl. auto.
  monadInv H. simpl. rewrite IHl with x0; eauto.
  f_equal. destruct a; inv EQ; simpl; auto.
  +destruct e; try (inv H0; auto; fail).
   -inv H0. destruct l0; inv H1.
    monadInv H0. simpl. auto.
   -inv H0. destruct l0; inv H1. destruct l0; inv H0. auto.
   -unfold trans_expr in H0. destruct (in_list _ _); inv H0. destruct b; auto.
  +monadInv H0. simpl. auto.
  +destruct b; monadInv H0; simpl; auto.
   rewrite trans_finit_fbyvarsof_nil; auto.
   erewrite trans_hstmt_fbyvarsof_nil; eauto.
   eapply trans_hstmt_fbyvarsof_nil; eauto.
  +monadInv H0. rewrite cons_arydif_fbyvarsof_nil; auto.
  +monadInv H0. simpl; auto.
  +erewrite cons_struct_fbyvarsof_nil; eauto.
Qed.

Lemma allvarsof_permut:
  forall f,
  Permutation (mkloopmapw (nd_stmt f) ++ allvarsof f)
   (((nd_vars f ++ mkloopmapw (nd_stmt f)) ++ nd_args f) ++ nd_rets f).
Proof.
  intros. unfold allvarsof.
  repeat rewrite <-app_ass. apply Permutation_app_tail.
  apply Permutation_app_tail. apply Permutation_app_swap.
Qed.

Lemma trans_body_allidsof_norepet:
  forall f,
  LustreS.ids_norepet f ->
  ids_plt ACG_B (allidsof f ++ LustreS.predidof f) ->
  list_norepet (map fst (mkloopmapw (nd_stmt f) ++ allvarsof f)).
Proof.
  intros. rewrite map_app.
  generalize H0. intros.
  apply ids_plt_le_notin with ACG_I _ _ in H0;
   try (unfold Ple, ACG_I, ACG_B; omega).
  apply ids_plt_le_notin with ACG_B _ _ in H1;
   try (unfold Ple, ACG_B; omega).
  apply list_norepet_app. repeat (split; auto).
  -apply mkloopmapw_norepet.
  -destruct H. auto.
  -red; intros. apply mkloopmapw_idrange in H2.
   destruct H2; subst; red; intros; subst.
   apply H0. apply in_or_app; auto.
Qed.

Lemma trans_body_ids_norepet:
  forall f f',
  trans_body f = OK f' ->
  LustreS.ids_norepet f ->
  ids_plt ACG_B (allidsof f ++ LustreS.predidof f) ->
  ids_norepet f'.
Proof.
  unfold LustreS.ids_norepet, ids_norepet.
  unfold allidsof, allvarsof,LustreS.predidof,predidof.
  intros. monadInv H. simpl in *.
  generalize H0 H1; intros A A1.
  erewrite trans_stmts_instidof_eq; eauto.
  erewrite trans_body_fbyvarsof; eauto.
  generalize H1; intros.
  apply ids_plt_le_notin with ACG_I _ _ in H1;
   try (unfold Ple, ACG_I, ACG_B; omega).
  apply ids_plt_le_notin with ACG_B _ _ in H2;
   try (unfold Ple, ACG_B; omega).
  intuition.
  +apply list_norepet_permut with (map fst (mkloopmapw (nd_stmt f)++allvarsof f)).
   eapply trans_body_allidsof_norepet; eauto. repeat (split; auto).
   apply Permutation_map. apply allvarsof_permut.
  +apply list_disjoint_incl_left with (map fst (mkloopmapw (nd_stmt f)++allvarsof f)).
   rewrite map_app.
   red; simpl; intros. apply in_app_or in H7.
   destruct H7 as [ | ].
   -red; intros; subst. apply mkloopmapw_idrange in H7.
    destruct H7; subst.
    apply H1. apply in_or_app; auto.
   -apply H4; auto.
   -red; intros. eapply Permutation_in in H7; eauto.
    apply Permutation_map. apply Permutation_sym.
    apply allvarsof_permut.
  +apply H1. rewrite app_ass.
   rewrite map_app. rewrite app_ass.
   apply in_or_app; auto.
Qed.

Lemma trans_hstmt_fby_nil:
  forall h s,
  trans_hstmt h = OK s ->
  fbyeqof s = nil.
Proof.
  destruct h; intros; try monadInv H; simpl in *; auto.
  -destruct (_ || _); inv EQ0; simpl; auto.
   destruct b; auto.
  -destruct p. monadInv H. auto.
  -destruct p. inv H; auto.
Qed.

Lemma trans_finit_fby_nil:
  forall h,
  fbyeqof (trans_finit h) = nil.
Proof.
  destruct h; intros; simpl in *; auto.
Qed.

Lemma cons_struct_fby_nil:
  forall l fld p s',
  cons_struct p fld l = OK s' ->
  fbyeqof s' = nil.
Proof.
  induction l, fld; simpl; intros; monadInv H; auto.
  simpl. eauto.
Qed.

Lemma trans_stmt_fby_eq:
  forall s s',
  trans_stmt s = OK s' ->
  fbyeqof s' = LustreS.fbyeqof s.
Proof.
  destruct s; intros; inv H; simpl; auto.
  +destruct e; inv H1; auto.
   destruct l; inv H0. monadInv H1; auto.
   destruct l; try congruence. destruct l; try congruence.
     inv H0; auto.
   destruct (_ || _); inv H0; destruct b; auto.
  +monadInv H1; auto.
  +destruct b; monadInv H1; auto; simpl.
   rewrite trans_finit_fby_nil. erewrite trans_hstmt_fby_nil; eauto.
   erewrite trans_hstmt_fby_nil; eauto.
  +monadInv H1; auto. clear. revert i.
   induction l; simpl; intros; auto.
  +monadInv H1. simpl;auto.
  +eapply cons_struct_fby_nil; eauto.
Qed.

Lemma trans_stmts_fby_eq:
  forall s s',
  trans_stmts s = OK s' ->
  fbyeqof s' = LustreS.fbyeqsof s.
Proof.
  induction s; intros; monadInv H; simpl; auto.
  f_equal; auto.
  eapply trans_stmt_fby_eq; eauto.
Qed.

Lemma cons_prefix_typeof:
  forall l a op t, typeof a = t ->
  typeof (cons_prefix l a op t) = t.
Proof.
  induction l; simpl; intros; auto.
Qed.

Lemma map_lvarof_typeof:
  forall l, map typeof (map lvarof l) =  map (snd (B:=type)) l.
Proof.
  induction l; simpl; auto.
  f_equal; auto.
Qed.

Lemma trans_body_ids_plt:
  forall f f', ids_plt ACG_B (allidsof f ++ LustreS.predidof f) ->
  trans_body f = OK f' ->
  ids_plt INSTRUCT (allidsof f' ++ predidof f').
Proof.
  unfold allidsof,predidof,allvarsof, LustreS.predidof.
  intros. monadInv H0. simpl in *.
  erewrite trans_body_fbyvarsof; eauto.
  erewrite trans_stmts_instidof_eq; eauto.
  red; simpl; intros.
  apply Permutation_in with (l':=(map fst
          (mkloopmapw (nd_stmt f)++allvarsof f) ++
        map fst (LustreS.fbyvarsof (nd_stmt f)) ++
        map instid (LustreS.instidof (nd_stmt f))))  in H0.
  rewrite app_ass in *.
  rewrite map_app in H0. rewrite app_ass in H0.
  apply in_app_or in H0. destruct H0.
  +apply mkloopmapw_idrange in H0. subst.
   unfold Plt, INSTRUCT, ACG_I. omega.
  +eapply ids_plt_trans; eauto.
   unfold Ple, INSTRUCT, ACG_B. omega.
   unfold allvarsof in *. rewrite app_ass in H0; auto.
  +apply Permutation_app_tail. apply Permutation_map.
   apply Permutation_sym. apply allvarsof_permut.
Qed.

Lemma trans_program_ids_range:
  forall p p', LustreS.ids_range ACG_B (node_block p) ->
  trans_program p = OK p' ->
  ids_range INSTRUCT (node_block p').
Proof.
  unfold LustreS.ids_range, ids_range. intros.
  monadInv H0. simpl in *.
  generalize H1; intros.
  eapply in_mmap_iff in H1; eauto.
  destruct H1 as [fd1 [? ?]].
  apply H in H2. subst.
  monadInv H1. simpl in *.
  eapply trans_body_ids_plt; eauto.
Qed.

Lemma trans_hcalldef_callid:
  forall c c',
  trans_hcalldef c = OK c' ->
  callid c = callid c'.
Proof.
  unfold trans_hcalldef. intros.
  destruct (callnum c); inv H; auto.
Qed.

Lemma trans_hstmt_get_hstmt:
  forall h h',
  trans_hstmt h = OK h' ->
  get_hstmt_nid h = get_stmt_nids h'.
Proof.
  induction h; simpl; intros; try monadInv H; simpl; auto;
  try (erewrite trans_hcalldef_callid; eauto; fail).
  +destruct (_ || _); inv EQ0; destruct b; auto.
  +destruct p; monadInv H. auto.
  +destruct p. inv H; auto.
Qed.

Lemma get_stmt_nids_trans_finit:
  forall h, get_stmt_nids (trans_finit h) = nil.
Proof.
  destruct h; simpl; auto;
  destruct l; simpl; auto.
Qed.

Lemma trans_stmt_get_stmt_nid:
  forall s s', trans_stmt s = OK s' ->
  get_stmt_nid s = get_stmt_nids s'.
Proof.
  induction s; simpl; intros.
  +revert s' H. destruct e; intros; try (inv H; auto;fail).
   -inv H. destruct l; monadInv H1; auto.
   -inv H. destruct l; inv H1; auto.
    destruct l; inv H0; auto.
   -unfold trans_expr in *. destruct (in_list _ _); inv H; destruct b; auto.
  +monadInv H; auto. unfold trans_calldef in *.
   destruct c. simpl in *. destruct callnum; inv EQ; auto.
  +destruct b; monadInv H; simpl.
   erewrite trans_hstmt_get_hstmt; eauto.
   rewrite get_stmt_nids_trans_finit; auto.
   erewrite trans_hstmt_get_hstmt; eauto.
  +monadInv H; auto.
   clear. revert x i.
   induction l; simpl; auto.
  +monadInv H. simpl; auto.
  +revert H. clear. revert l s'.
   induction f; simpl; intros.
   destruct l; inv H; auto.
   destruct l; monadInv H; simpl; eauto.
  +inv H. simpl. auto.
  +inv H; auto.
  +inv H; auto.
  +inv H; auto.
Qed.

Lemma trans_program_deps_of_nodes:
  forall p p', trans_program p = OK p' ->
  Toposort.deps_of_nodes_simpl (node_block p) = deps_of_nodes (node_block p').
Proof.
  unfold Toposort.deps_of_nodes_simpl, deps_of_nodes.
  intros. monadInv H. simpl.
  apply mmap_inversion in EQ.
  apply list_forall2_infer in EQ. revert x EQ.
  induction (node_block p); simpl; intros; auto.
  inv EQ. auto.
  inv EQ. simpl. f_equal; auto.
  unfold dep_of_node, callidof.
  monadInv H1. monadInv EQ. simpl. f_equal.
  revert x0 EQ0; clear. unfold LustreS.node in *.
  induction (nd_stmt (snd a)); simpl; intros; auto.
  inv EQ0. auto.
  monadInv EQ0. simpl. f_equal; auto.
  apply trans_stmt_get_stmt_nid; auto.
Qed.

Lemma trans_program_globidspltof:
  forall p p',
  trans_program p = OK p' ->
  globidspltof p' = globidspltof p.
Proof.
  unfold globidspltof. intros.
  monadInv H; simpl in *.
  apply trans_nodes_fids_eq in EQ. rewrite <-EQ. auto.
  intros. monadInv H; auto.
Qed.

Lemma trans_program_gids_eq:
  forall p p',
  trans_program p = OK p' ->
  globidsof p' = globidsof p.
Proof.
  unfold globidsof.
  intros. monadInv H; simpl in *.
  apply trans_nodes_fids_eq in EQ. rewrite <-EQ. auto.
  intros. monadInv H; auto.
Qed.
