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

(** Translation of type comparision. *)

Require Import Coqlib.
Require Import AST.
Require Import Integers.
Require Import Errors.
Require Import Cop.
Require Import Lident.
Require Import Cltypes.
Require Import Ltypes.
Require Import Lop.
Require Import Lustre.
Require Import LustreR.
Require Import Permutation.
Require Import ExtraList.

Local Open Scope error_monad_scope.

(** get the name of struct or array type. *)

Definition id_of_type(t: type): res ident :=
  match t with
  | Tarray id ty num => OK id
  | Tstruct id _ => OK id
  | _ => Error (msg "TransTypecmp: not Tarray or Struct")
  end.

(** the return expr in acg_comp function. *)

Definition result := Svar ACG_EQU type_bool.

(** then temp result expr in acg_comp function. *)

Definition local_result := Svar ACG_LOCAL type_bool.

(** the initiation statement of return expr in acg_comp function. *)

Definition result_init := Sassign result (Sconst (Cbool true) type_bool).

(** the assign statement of return expr in acg_comp function. *)

Definition result_assign := Sassign result (Sbinop Oand result local_result type_bool). (* result=result & local_result *)

(** input parameters in acg_comp function. *)

Definition cmp_paras(ty: type) := (ACG_C1, ty) :: (ACG_C2, ty) :: nil.

(** local variables in acg_cmp fuction of struct. *)

Definition str_vars := (ACG_LOCAL , type_bool) :: nil.

(** local variables in acg_cmp fuction of array. *)

Definition ary_vars := (ACG_LOCAL , type_bool) :: (ACG_I , type_int32s):: nil.

(** output parameters in acg_comp function. *)

Definition cmp_rets := (ACG_EQU,type_bool)::nil.

(** call for type comparision function.  *)

Definition comp_cdef(id: ident)(ty: type) :=
  mkcalldef false xH (comp_funcs_id id) None xH Fnil (ty::ty::nil) cmp_rets.

(** translate statement. *)

Fixpoint trans_stmt(tdl: list (ident*type))(s: LustreR.stmt): res stmt:=
  match s with
  | LustreR.Sassign lh a => OK (Sassign lh a)
  | LustreR.Scall oid lhs cdef a => OK (Scall oid lhs cdef a)
  | LustreR.Sfor a1 a2 a3 fs =>
    do fs1 <- trans_stmt tdl fs;
    OK (Sfor a1 a2 a3 fs1)
  | LustreR.Sifs a s1 s2 =>
    do s3 <- trans_stmt tdl s1;
    do s4 <- trans_stmt tdl s2;
    OK (Sifs a s3 s4)
  | LustreR.Scase lh a pel => OK (Scase lh a pel)
  | LustreR.Sfby lh id a1 a2 => OK (Sfby lh id a1 a2)
  | LustreR.Sfbyn lh ti i a1 a2 => OK (Sfbyn lh ti i a1 a2)
  | LustreR.Sarrow lh a1 a2 => OK (Sarrow lh a1 a2)
  | LustreR.Sseq s1 s2 =>
    do s3 <- trans_stmt tdl s1;
    do s4 <- trans_stmt tdl s2;
    OK (Sseq s3 s4)
  | LustreR.Stypecmp lh a1 a2 =>
    let t := typeof a1 in
    do id <- id_of_type t;
    OK (Scall None (lh::nil) (comp_cdef id t) (a1::a2::nil))
  | LustreR.Sskip => OK Sskip
  end.

(** translate body of node. *)

Definition trans_body(tdl: list (ident*type))(b: LustreR.node): res node :=
  do s <- trans_stmt tdl b.(nd_stmt);
  OK (mknode b.(nd_kind) b.(nd_args) b.(nd_rets) nil b.(nd_vars) s b.(nd_sid) b.(nd_fld)).

Definition trans_node(tdl: list (ident*type))(f: ident*LustreR.node): res (ident*node) :=
  do body <- trans_body tdl (snd f);
  OK (fst f,body).

Definition arystr_comp_stmt(a1 a2: sexp): stmt :=
  let ele_t := typeof a1 in
  match ele_t with
  | Tarray id1 _ _ => (* local_result = comp_array (a1, a2) *)
    Scall None (local_result::nil) (comp_cdef id1 ele_t) (a1 :: a2 :: nil)
  | Tstruct id1 _ => (* local_result = comp_struct (a1, a2) *)
    Scall None (local_result::nil) (comp_cdef id1 ele_t) (a1 :: a2 :: nil)
  | _ => (* local_result = a1 == a2) *)
    Sassign local_result (Sbinop Oeq a1 a2 type_bool)
  end.

Definition array_comp_stmt(id:ident) (ele_t: type) (num:Z) : stmt :=
  let ty := Tarray id ele_t num in
  let para1 := Svar ACG_C1 ty in
  let para2 := Svar ACG_C2 ty in
  let i := Svar ACG_I type_int32s in
  let num := Int.repr num in
  let fs := arystr_comp_stmt (Saryacc para1 i ele_t) (Saryacc para2 i ele_t) in
  Sfor None (loop_cond num) loop_add (Sseq fs result_assign).

(** make the body of array comparision function. *)

Definition array_comp_body(id:ident)(ele_t: type) (num:Z) : node  :=
  let ty := Tarray id ele_t num in
  let para1 := Svar ACG_C1 ty in
  let para2 := Svar ACG_C2 ty in
  let i := Svar ACG_I type_int32s in
  let num := Int.repr num in
  let fs := arystr_comp_stmt (Saryacc para1 i ele_t) (Saryacc para2 i ele_t) in
  let comp_s :=  Sfor (Some loop_init) (loop_cond num) loop_add (Sseq fs result_assign) in
  let ss := (Sseq result_init comp_s) in
  (mknode false (cmp_paras ty) cmp_rets nil ary_vars ss xH Fnil) .

Fixpoint struct_comp_stmt_rec(para1 para2: sexp)(fl : fieldlist): stmt :=
  let ty := typeof para1 in
  match fl with
  | Fnil => Sskip
  | Fcons label ele_t flt =>
    let s1 :=  arystr_comp_stmt (Sfield para1 label ele_t) (Sfield para2 label ele_t) in
    let comp_s1 := Sseq s1 result_assign in
    Sseq comp_s1 (struct_comp_stmt_rec para1 para2 flt)
  end.

Definition struct_comp_stmt (id:ident) (fl: fieldlist) : stmt :=
  let ty := Tstruct id fl in
  let para1 := Svar ACG_C1 ty in
  let para2 := Svar ACG_C2 ty in
  struct_comp_stmt_rec para1 para2 fl.

(** make the body of struct comparision function. *)

Definition struct_comp_body (id:ident) (fl: fieldlist) : node :=
  let ty := Tstruct id fl in
  let comp_s := struct_comp_stmt id fl in
  let ss := (Sseq result_init comp_s) in
  (mknode false (cmp_paras ty) cmp_rets nil str_vars ss xH Fnil).

(** make array comparision function. *)

Definition array_comp(id:ident)(ele_t: type) (num:Z) : ident*node  :=
  (comp_funcs_id id, array_comp_body id ele_t num).

(** make struct comparision function.  *)

Definition struct_comp (id:ident) (fl: fieldlist) : ident*node :=
  (comp_funcs_id id, struct_comp_body id fl).

(** make list of comparision function. *)

Fixpoint comp_functions (types: list (ident*type)): list (ident * node) :=
  match types with
  | nil => nil
  | (lty_id, lty) :: rest =>
    let comp_functions_tl := comp_functions rest in
    match lty with
    | Tarray _ ele_t num =>
      let array_comp := array_comp lty_id ele_t num in
      (array_comp::comp_functions_tl)
    | Tstruct _ fl =>
      let struct_comp := struct_comp lty_id fl in
      (struct_comp::comp_functions_tl)
    | _  => comp_functions_tl
    end
  end.

(** 翻译程序。 *)

Definition trans_program(p: LustreR.program): res program :=
  do nodes <- mmap (trans_node (type_block p)) (node_block p);
  let comp_funcs := comp_functions (type_block p) in
  if list_in_list (map fst comp_funcs) (globidsof p) then
    Error (msg "TransTypecmp: comp_funcs names are in global names!")
  else
    OK (mkprogram (type_block p) (defs_block p) (const_block p) (comp_funcs ++ nodes) (node_main p)).

Lemma trans_stmt_instidof_eq:
  forall tdl s s',
  trans_stmt tdl s = OK s' ->
  instidof s' = LustreR.instidof s.
Proof.
  induction s; intros; inv H; auto.
  +monadInv H1. simpl; auto.
  +monadInv H1. simpl; f_equal; auto.
  +monadInv H1. simpl. f_equal; auto.
  +monadInv H1. simpl. auto.
Qed.

Lemma trans_stmt_fbysvarsof:
  forall s s' tdl,
  trans_stmt tdl s = OK s' ->
  fbyvarsof s' = LustreR.fbyvarsof s.
Proof.
  induction s; simpl; intros; inv H; auto.
  +monadInv H1. simpl. eauto.
  +monadInv H1. simpl. f_equal; eauto.
  +monadInv H1. simpl. f_equal; eauto.
  +monadInv H1. simpl. auto.
Qed.

Lemma trans_body_ids_norepet:
  forall f f' tdl,
  LustreR.ids_norepet f ->
  trans_body tdl f = OK f' ->
  ids_norepet f'.
Proof.
  unfold ids_norepet, LustreR.ids_norepet, allidsof, allvarsof, predidof,
  LustreR.predidof. intros.
  monadInv H0. simpl in *.
  erewrite trans_stmt_instidof_eq; eauto.
  erewrite trans_stmt_fbysvarsof; eauto.
Qed.

Lemma arystr_comp_stmt_fbyvarsof:
  forall a1 a2,
  fbyvarsof (arystr_comp_stmt a1 a2) = nil.
Proof.
  unfold arystr_comp_stmt. intros.
  destruct (typeof a1); auto.
Qed.

Lemma struct_comp_stmt_rec_fbyeqof:
  forall fld a1 a2,
  fbyeqof (struct_comp_stmt_rec a1 a2 fld) = nil.
Proof.
  induction fld; simpl; intros; auto.
  rewrite IHfld. destruct t; simpl; auto.
Qed.

Lemma arystr_comp_stmt_instidof:
  forall a1 a2,
  instidof (arystr_comp_stmt a1 a2) = nil.
Proof.
  unfold arystr_comp_stmt. intros.
  destruct (typeof a1); auto.
Qed.

Lemma array_cmp_vars_norepet:
  list_norepet (ACG_LOCAL :: ACG_I :: ACG_C1 :: ACG_C2 :: ACG_EQU :: nil).
Proof.
  unfold ACG_LOCAL, ACG_I, ACG_C1, ACG_C2, ACG_EQU.
  repeat (split; auto). constructor; auto.
  red; simpl; intros.
  destruct H as [ | [ | [ | [ | ]]]]; congruence.
  constructor; auto.
  red; simpl; intros.
  destruct H as [ | [ | [ | ]]]; congruence.
  constructor; auto.
  red; simpl; intros. destruct H as [ | [ | ]]; congruence.
  constructor; auto. red; simpl; intros. destruct H; congruence.
  constructor; auto. constructor.
Qed.

Lemma array_comp_body_ids_norepet:
  forall aid aty num,
  ids_norepet (array_comp_body aid aty num).
Proof.
  unfold ids_norepet, LustreR.ids_norepet, allidsof, allvarsof, predidof,
  LustreR.predidof. intros. simpl.
  rewrite arystr_comp_stmt_instidof, arystr_comp_stmt_fbyvarsof; auto.
  repeat (split; auto).
  +apply array_cmp_vars_norepet.
  +simpl; constructor.
  +red; simpl; intros; tauto.
  +simpl. unfold ACG_LOCAL, ACG_I, ACG_C1, ACG_C2, ACG_EQU.
   red; intros. destruct H as [ | [ | [ | ]]]; congruence.
Qed.

Lemma struct_comp_stmt_fbyvarsof:
  forall fld a1 a2,
  fbyvarsof (struct_comp_stmt_rec a1 a2 fld) = nil.
Proof.
  induction fld; simpl; intros; auto.
  rewrite arystr_comp_stmt_fbyvarsof; auto.
  rewrite IHfld; auto.
Qed.

Lemma struct_comp_stmt_instidof:
  forall fld a1 a2,
  instidof (struct_comp_stmt_rec a1 a2 fld) = nil.
Proof.
  induction fld; simpl; intros; auto.
  rewrite arystr_comp_stmt_instidof; auto.
  rewrite IHfld; auto.
Qed.

Lemma struct_cmp_vars_norepet:
  list_norepet (ACG_LOCAL :: ACG_C1 :: ACG_C2 :: ACG_EQU :: nil).
Proof.
  unfold ACG_LOCAL, ACG_C1, ACG_C2, ACG_EQU.
  repeat (split; auto).
  +constructor; auto.
   red; simpl; intros.
   destruct H as [ | [ | [ | ]]]; congruence.
   constructor; auto.
   red; simpl; intros.
   destruct H as [ | [ | ]]; congruence.
   constructor; auto.
   red; simpl; intros. destruct H as [ | ]; congruence.
   constructor; auto. constructor.
Qed.

Lemma struct_comp_body_ids_norepet:
  forall sid fld,
  ids_norepet (struct_comp_body sid fld).
Proof.
  unfold ids_norepet, LustreR.ids_norepet, allidsof, allvarsof, predidof,
  LustreR.predidof. intros. simpl.
  unfold struct_comp_stmt. rewrite struct_comp_stmt_fbyvarsof.
  rewrite struct_comp_stmt_instidof; auto. simpl.
  repeat (split; auto).
  +apply struct_cmp_vars_norepet.
  +constructor.
  +red; simpl; intros; tauto.
  +unfold ACG_LOCAL, ACG_C1, ACG_C2, ACG_EQU, ACG_I.
   red; intros. destruct H as [ | [ | [ | ]]]; congruence.
Qed.

Lemma trans_body_ids_plt:
  forall f f' tdl id, ids_plt id (allidsof f ++ LustreR.predidof f) ->
  trans_body tdl f = OK f' ->
  ids_plt id (allidsof f' ++ predidof f').
Proof.
  unfold allidsof,predidof,allvarsof, LustreR.predidof.
  intros. monadInv H0. simpl in *.
  erewrite trans_stmt_fbysvarsof; eauto.
  erewrite trans_stmt_instidof_eq; eauto.
Qed.

Lemma comp_functions_ids_plt:
  forall fd l,
  In fd (comp_functions l) ->
  ids_plt ACG_INIT (allidsof (snd fd) ++ predidof (snd fd)).
Proof.
  induction l; simpl; intros; try tauto.
  destruct a.
  destruct t; simpl in *; auto;
  destruct H; subst; auto; simpl.
  +unfold array_comp_body. unfold predidof. simpl.
   rewrite arystr_comp_stmt_instidof, arystr_comp_stmt_fbyvarsof.
   simpl. unfold ACG_INIT, ACG_LOCAL, ACG_I, ACG_C1, ACG_C2, ACG_EQU.
   red; simpl; intros. unfold Plt.
   destruct H as [ | [ | [ | [ | [|]]]]]; subst; try omega.
  +unfold struct_comp_body. unfold predidof. simpl.
   unfold struct_comp_stmt.
   rewrite struct_comp_stmt_instidof, struct_comp_stmt_fbyvarsof.
   simpl. unfold ACG_INIT, ACG_LOCAL, ACG_C1, ACG_C2, ACG_EQU.
   red; simpl; intros. unfold Plt.
   destruct H as [ | [ | [ | [ | ]]]]; subst; try omega.
Qed.

Lemma trans_program_ids_range:
  forall p p', LustreR.ids_range ACG_INIT (node_block p) ->
  trans_program p = OK p' ->
  ids_range ACG_INIT (node_block p').
Proof.
  unfold LustreR.ids_range, ids_range. intros.
  monadInv H0. destruct (list_in_list _ _); inv EQ0.
  simpl in *.
  apply in_app_or in H1. destruct H1.
  +apply comp_functions_ids_plt with (type_block p); auto.
  +generalize H0; intros.
   eapply in_mmap_iff in H1; eauto.
   destruct H1 as [fd1 [? ?]].
   apply H in H2. subst.
   monadInv H1. simpl in *.
   eapply trans_body_ids_plt; eauto.
Qed.

Lemma comp_functions_in:
  forall l i,
  In (comp_funcs_id i) (map fst (comp_functions l)) ->
  In i (map fst l).
Proof.
  induction l; simpl; intros; auto.
  destruct a.
  destruct t; simpl in *; auto;
  destruct H; eauto; left;
  apply Pos.add_reg_r with 1%positive; auto.
Qed.

Lemma comp_functions_norepet:
  forall l, list_norepet (map fst l) ->
  list_norepet (map fst (comp_functions l)).
Proof.
  induction l; simpl; intros.
  +constructor.
  +destruct a. inv H.
   destruct t; auto; simpl; constructor; auto;
   red; intros; apply H2;
   eapply comp_functions_in; eauto.
Qed.

Lemma trans_stmt_fby_eq:
  forall l s s',
  trans_stmt l s = OK s' ->
  fbyeqof s' = LustreR.fbyeqof s.
Proof.
  induction s; intros; monadInv H; simpl; auto.
  +f_equal; auto.
  +f_equal; auto.
Qed.

Lemma filter_type_comp_functions_ids:
  forall l, flat_map filter_type l = map fst (comp_functions l).
Proof.
  induction l; simpl; intros; auto.
  destruct a. rewrite IHl. unfold filter_type.
  simpl. destruct t; auto.
Qed.

Lemma trans_program_ids_plt:
  forall p p', trans_program p = OK p' ->
  globidspltof p = map fst (const_block p') ++ map fst (node_block p').
Proof.
  unfold globidspltof. intros. monadInv H.
  destruct (list_in_list _ _); inv EQ0. simpl.
  rewrite filter_type_comp_functions_ids; auto.
  rewrite map_app; auto.
  apply trans_nodes_fids_eq in EQ.
  rewrite EQ; auto.
  intros. monadInv H; auto.
Qed.

Lemma trans_program_gids_norepet:
  forall p p',
  trans_program p = OK p' ->
  list_norepet (globidsof p) ->
  list_norepet (globidsof p').
Proof.
  unfold trans_program, globidsof. intros.
  monadInv H. destruct (list_in_list _ _) eqn:?; try congruence.
  apply list_in_list_disjoint in Heqb; auto. inv EQ0.
  simpl in *. apply trans_nodes_fids_eq in EQ.
  apply list_norepet_permut with (map fst (comp_functions (type_block p)) ++ (map fst (type_block p ++ defs_block p)
        ++ map fst (const_block p)) ++ map fst (node_block p)); auto.
  +apply list_norepet_app; auto. repeat (split; auto).
   apply comp_functions_norepet; auto.
   apply list_norepet_app in H0. destruct H0.
   apply list_norepet_app in H. destruct H.
   rewrite map_app in H. apply list_norepet_app in H.
   destruct H; auto.
  +repeat rewrite map_app. rewrite <-EQ.
   repeat rewrite <-app_ass. apply Permutation_app_tail.
   apply Permutation_trans with (map fst (comp_functions (type_block p)) ++ (((map fst (type_block p) ++ map fst (defs_block p)) ++
       map fst (const_block p)))); auto.
   -repeat rewrite app_ass. apply Permutation_refl.
   -apply Permutation_app_swap.
  +intros. monadInv H; auto.
Qed.
