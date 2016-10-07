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
Require Import List.
Require Import Maps.
Require Import Lvalues.
Require Import Cltypes.
Require Import Lint.
Require Import Lident.
Require Import ExtraList.
Require Import Lop.
Require Import Ltypes.
Require Import Lustre.
Require Import LustreF.
Require Import Lenv.
Require Import Lenvmatch.
Require Import Lsem.
Require Import LsemF.
Require Import LsemD.

Section SEMANTICS.

Variable p: program.
Variable gc: locenv.

Inductive eval_node: env -> env -> ident*func -> list val -> list val  -> Prop :=
  | exec_node: forall te te1 te2 eh eh1 se se' vrs vas nid f,
      alloc_variables empty_locenv (lvarsof f) te ->
      locenv_setvars te f.(nd_args) vas te1 ->
      ids_norepet f ->
      eval_stmt nid te1 (mkenv eh se) te2 (mkenv eh1 se') f.(nd_stmt) ->
      Lsem.locenv_getvars eh1 f.(nd_rets) vrs ->
      svars_fld_match (svarsof f) (nd_fld f) ->
      has_types vrs (List.map snd (nd_rets f)) ->
      eval_casts vrs (map snd f.(nd_rets)) vrs ->
      eval_node (mkenv eh se) (mkenv eh1 se') (nid,f) vas vrs

with eval_stmt: ident -> locenv -> env -> locenv -> env -> stmt  -> Prop :=
  | eval_Sassign: forall nid te te' eh eh' se lh a,
      eval_eqf gc te eh te' eh' (lh,a) ->
      eval_stmt nid te (mkenv eh se) te' (mkenv eh' se) (Sassign lh a)
  | eval_Scall: forall nid te te' eh eh' se ef ef' se' oid cdef fd nd args lhs vargs vargs' vrets i,
      cakind cdef = true ->
      load_loopid gc te oid (callnum cdef) i ->
      LustreF.call_node (node_block p) nid cdef nd fd ->
      callnd_env cdef i se se' ef ef' ->
      eval_sexps gc te eh args vargs ->
      eval_casts vargs (List.map typeof args) vargs' ->
      eval_node ef ef' fd vargs' vrets ->
      locenv_setvarfs gc te eh lhs vrets  te' eh' ->
      Forall (lid_disjoint) lhs ->
      List.map typeof lhs = List.map snd (nd_rets (snd fd)) ->
      List.map typeof args = List.map snd (nd_args (snd fd)) ->
      lvalue_list_norepet (eval_lvalue gc te eh) lhs ->
      assign_list_disjoint (eval_lvalue gc te eh) lhs args ->
      te ! (callid cdef) = None ->
      eval_stmt nid te (mkenv eh se) te' (mkenv eh' se') (Scall oid lhs cdef args)
  | eval_Fcall: forall nid te te' eh eh' se ef ef' vl oid cdef fd args lhs vargs vargs' vrets,
      cakind cdef = false ->
      Lustre.call_func (node_block p) cdef fd ->
      eval_sexps gc te eh args vargs ->
      eval_casts vargs (List.map typeof args) vargs' ->
      locenv_getmvls gc te eh lhs vl ->
      locenv_setmvls empty_locenv (nd_rets (snd fd)) vl ef ->
      eval_node (mkenv ef empty_subenv) ef' fd vargs' vrets ->
      locenv_setvarfs gc te eh lhs vrets  te' eh' ->
      Forall (lid_disjoint) lhs ->
      List.map typeof lhs = List.map snd (nd_rets (snd fd)) ->
      List.map typeof args = List.map snd (nd_args (snd fd)) ->
      lvalue_list_norepet (eval_lvalue gc te eh) lhs ->
      assign_list_disjoint (eval_lvalue gc te eh) lhs args ->
      te ! (callid cdef) = None ->
      eval_stmt nid te (mkenv eh se) te' (mkenv eh' se) (Scall oid lhs cdef args)
  | eval_Sfor_start: forall nid te te1 te2 eh eh1 se e2 a1 a2 a3 s,
      eval_eqf gc te eh te1 eh1 a1 ->
      eval_stmt nid te1 (mkenv eh1 se) te2 e2 (Sfor None a2 a3 s) ->
      eval_stmt nid te (mkenv eh se) te2 e2 (Sfor (Some a1) a2 a3 s)
  | eval_Sfor_false: forall nid te eh se a2 a3 s,
      eval_sexp gc te eh a2 Vfalse ->
      eval_stmt nid te (mkenv eh se) te (mkenv eh se) (Sfor None a2 a3 s)
  | eval_Sfor_loop: forall nid te te1 te2 te3 eh eh1 eh2 se se1 e3 a2 a3 s,
      eval_sexp gc te eh a2 Vtrue ->
      eval_stmt nid te (mkenv eh se) te1 (mkenv eh1 se1) s ->
      eval_eqf gc te1 eh1 te2 eh2 a3 ->
      eval_stmt nid te2 (mkenv eh2 se1) te3 e3 (Sfor None a2 a3 s) ->
      eval_stmt nid te (mkenv eh se) te3 e3 (Sfor None a2 a3 s)
  | eval_Sskip: forall nid te e ,
      eval_stmt nid te e te e Sskip
  | eval_Sseq: forall nid te te1 te2 e e1 e2 s1 s2,
      eval_stmt nid te e te1 e1 s1 ->
      eval_stmt nid te1 e1 te2 e2 s2 ->
      eval_stmt nid te e te2 e2 (Sseq s1 s2)
  | eval_Sif: forall nid te te1 eh se e1 a s1 s2 v b,
      eval_sexp gc te eh a v ->
      bool_val v (typeof a) = Some b ->
      eval_stmt nid te (mkenv eh se) te1 e1 (if b then s1 else s2)  ->
      eval_stmt nid te (mkenv eh se) te1 e1 (Sif a s1 s2)
  | eval_Scase: forall nid te te1 eh eh1 se lh ca pl i a,
      eval_sexp gc te eh ca (Vint i) ->
      select_case i pl = Some a ->
      eval_stmt nid te (mkenv eh se) te1 (mkenv eh1 se) (Sassign lh a) ->
      eval_stmt nid te (mkenv eh se) te1 (mkenv eh1 se) (Scase lh ca pl).

Scheme eval_node_ind2 := Minimality for eval_node Sort Prop
  with eval_stmt_ind2 := Minimality for eval_stmt Sort Prop.
Combined Scheme eval_node_stmt_ind2 from eval_node_ind2, eval_stmt_ind2.


Inductive init_node: env -> ident*func -> Prop :=
  | init_node_: forall eh eh1 se nid f,
      alloc_variables empty_locenv (nd_rets f) eh ->
      ids_norepet f ->
      eval_init (length (nd_svars f)) eh (nd_svars f) eh1 ->
      svars_fld_match (svarsof f) (nd_fld f) ->
      (forall ty, In ty (map snd (svarsof f)) -> 0 < sizeof ty) ->
      init_stmt nid (mkenv eh1 empty_subenv) (mkenv eh1 se) (instidof f.(nd_stmt)) ->
      init_node (mkenv eh1 se) (nid,f)

with init_stmt: ident -> env -> env -> list calldef ->  Prop :=
  | init_call_nil: forall nid e,
      init_stmt nid e e nil
  | init_call_node_cons: forall nid le se se1 se2 nd fd ef c l,
      call_node (node_block p) nid c nd fd ->
      init_node ef fd ->
      se1 = PTree.set (instid c) (list_repeat (nat_of_int (intof_opti (callnum c))) ef) se ->
      init_stmt nid (mkenv le se1) (mkenv le se2) l ->
      init_stmt nid (mkenv le se) (mkenv le se2) (c::l).

Scheme init_node_ind2 := Minimality for init_node Sort Prop
  with init_stmt_ind2 := Minimality for init_stmt Sort Prop.
Combined Scheme init_node_stmt_ind2 from init_node_ind2, init_stmt_ind2.

Inductive alloc_node: env -> (ident*func) ->Prop :=
  | alloc_node_: forall eh se nid f,
      alloc_variables empty_locenv (svarsof f) eh ->
      ids_norepet f ->
      svars_fld_match (svarsof f) (nd_fld f) ->
      (forall ty, In ty (map snd (svarsof f)) -> 0 < sizeof ty) ->
      alloc_stmt nid (mkenv eh empty_subenv) (mkenv eh se) (instidof f.(nd_stmt)) ->
      alloc_node (mkenv eh se) (nid,f)

with alloc_stmt: ident -> env -> env -> list calldef ->  Prop :=
  | alloc_call_nil: forall nid e,
      alloc_stmt nid e e nil
  | alloc_call_node_cons: forall nid le se se1 se2 nd fd ef c l,
      call_node (node_block p) nid c nd fd ->
      alloc_node ef fd ->
      se1 = PTree.set (instid c) (list_repeat (nat_of_int (intof_opti (callnum c))) ef) se ->
      alloc_stmt nid (mkenv le se1) (mkenv le se2) l ->
      alloc_stmt nid (mkenv le se) (mkenv le se2) (c::l).

Scheme alloc_node_ind2 := Minimality for alloc_node Sort Prop
  with alloc_stmt_ind2 := Minimality for alloc_stmt Sort Prop.
Combined Scheme alloc_node_stmt_ind2 from alloc_node_ind2, alloc_stmt_ind2.

Lemma alloc_stmt_le_any:
  forall l nid eh1 eh2 se1 se2,
  alloc_stmt nid (mkenv eh1 se1) (mkenv eh1 se2) l ->
  alloc_stmt nid (mkenv eh2 se1) (mkenv eh2 se2) l.
Proof.
  induction l; simpl; intros; inv H;
  try (econstructor; eauto; fail).
Qed.

Lemma alloc_stmt_notin_eq:
  forall nid e e' l,
  alloc_stmt  nid e e' l ->
  forall id, ~ In id (List.map instid l) ->
  (sube e') ! id = (sube e) ! id.
Proof.
  induction 1; simpl in *; intros; auto.
  rewrite IHalloc_stmt; auto.
  subst. rewrite PTree.gso; auto.
Qed.

Lemma alloc_stmt_set_other:
  forall nid id el le l se se',
  alloc_stmt nid (mkenv le se) (mkenv le se') l ->
  ~ In id (List.map instid l) ->
  alloc_stmt nid (mkenv le (PTree.set id el se)) (mkenv le (PTree.set id el se')) l.
Proof.
  induction l; simpl in *; intros; inv H; auto.
  constructor.
  econstructor 2; eauto.
  rewrite ptree_set_swap; auto.
Qed.

Inductive eval_flag: locenv -> list (ident*type)-> locenv ->  Prop :=
  | eval_flag_none: forall eh,
     eval_flag eh nil eh
  | eval_flag_some: forall svars eh eh1,
     locenv_range_perm_var eh ACG_INIT type_bool ->
     store_env type_bool eh ACG_INIT Int.zero (Vint Int.one) eh1 ->
     eval_flag eh ((ACG_INIT,type_bool)::svars) eh1.

Inductive init_env: env -> env -> ident*func -> Prop :=
  | init_env_: forall eh eh1 se se1 nid f,
      ids_norepet f ->
      eval_flag eh (nd_svars f) eh1 ->
      svars_fld_match (svarsof f) (nd_fld f) ->
      init_subenv nid se se1 (instidof f.(nd_stmt)) ->
      init_env (mkenv eh se) (mkenv eh1 se1) (nid,f)

with init_subenv: ident -> subenv -> subenv -> list calldef ->  Prop :=
  | init_subenv_nil: forall nid se,
      init_subenv nid se se nil
  | init_subenv_cons: forall nid se se1 se2 nd fd ef ef' c l,
      call_node (node_block p) nid c nd fd ->
      init_env ef ef' fd ->
      se ! (instid c)  = Some (list_repeat (nat_of_int (intof_opti (callnum c))) ef) ->
      se1 =  PTree.set (instid c) (list_repeat (nat_of_int (intof_opti (callnum c))) ef') se ->
      init_subenv nid se1 se2 l ->
      init_subenv nid se se2 (c::l).

Scheme init_env_ind2 := Minimality for init_env Sort Prop
  with init_subenv_ind2 := Minimality for init_subenv Sort Prop.
Combined Scheme init_env_subenv_ind2 from init_env_ind2, init_subenv_ind2.


Lemma alloc_init_node_exists:
  forall e' main,
  init_node e' main ->
  exists e0, alloc_node e0 main
    /\ init_env e0 e' main.
Proof.
  intros until main.
  induction 1 using init_node_ind2 with
  ( P0 := fun nid e1 e1' l =>
       forall eh se1 se1' se2 ids el,
       e1 = (mkenv eh se1) ->
       e1' = (mkenv eh se1') ->
       list_norepet (List.map instid l) ->
       list_disjoint (List.map instid l) ids ->
       ptree_sets se2 ids el se1 ->
       exists se21 se2', alloc_stmt nid (mkenv eh se2) (mkenv eh se21) l
         /\ init_subenv nid se21 se2' l
         /\ ptree_sets se2' ids el se1'
   ); simpl; intros; eauto.
  +(*node*)
  destruct IHinit_node with eh1 empty_subenv se empty_subenv (@nil ident) (@nil (list env))
    as [se21 [se2' [A1 [A2 A3]]]]; auto.
    apply ids_norepet_instid; auto.
    red; intros ? ? ? A. inv A.
    constructor.
  inv A3. inv H1.
  -cut (nd_svars f = nil). intros A4.
   exists (mkenv eh1 se21). split; auto.
   *constructor 1; simpl; auto.
    unfold svarsof. rewrite A4. rewrite <-app_nil_end; auto.
   *constructor 1; simpl; auto. rewrite A4. constructor 1.
   *destruct (nd_svars f); auto. simpl in *. omega.
  -exists (mkenv eh2 se21). split; auto.
   *constructor 1; simpl; auto.
    unfold svarsof. rewrite <-H6.
    apply alloc_variables_trans with eh; auto.
    eapply alloc_stmt_le_any; eauto.
   *constructor 1; simpl; auto.
    rewrite <-H6. constructor 2; auto.
    apply alloc_variables_norepeat_in_eq with (id:=ACG_INIT) (ty:=type_bool) in H7; simpl; auto.
    red. exists (alloc (sizeof type_bool)).
     split; [| split];auto.
     apply alloc_range_perm. simpl.
     unfold Int.max_signed. simpl. omega.
    apply ids_norepet_rets_svars in H0; auto.
    rewrite map_app in H0. rewrite <-H6 in *.
    apply list_norepet_app in H0. destruct H0 as [? [? ?]]; auto.
 +(*nil*)
  subst. inv H0.
  exists se2, se2. repeat (split; auto); constructor.
 +(*cons*)
  inv H3. inv H4. inv H5.
  destruct IHinit_node as [ef0 [A A1]]; auto.
  remember (PTree.set _ _ _) as se1.
  destruct IHinit_node0 with eh se1 se1' (PTree.set (instid c) (list_repeat (nat_of_int (intof_opti (callnum c))) ef) se3) ids el
    as [se21 [se2' [A2 [A3 A4]]]]; auto.
    red; intros; apply H6; simpl; auto.
    subst. apply ptree_sets_shift; auto.
    eapply list_disjoint_notin; eauto. simpl; auto.
  exists (PTree.set (instid c) (list_repeat (nat_of_int (intof_opti (callnum c))) ef0) se21).
  exists se2'. repeat (split; auto).
  -constructor 2 with (PTree.set (instid c) (list_repeat (nat_of_int (intof_opti (callnum c))) ef0) se3) nd fd ef0; auto.
   rewrite <- ptree_set_repeat with (v1:=list_repeat (nat_of_int (intof_opti (callnum c))) ef); eauto.
   eapply alloc_stmt_set_other; eauto.
  -constructor 2 with (PTree.set (instid c) (list_repeat (nat_of_int (intof_opti (callnum c))) ef) se21) nd fd ef0 ef; auto.
   *rewrite PTree.gss; auto.
   *rewrite ptree_set_repeat; auto.
   *rewrite ptree_set_same; auto.
    eapply alloc_stmt_notin_eq in A2; eauto.
    simpl in A2. rewrite PTree.gss in A2; auto.
Qed.

Lemma eval_eqf_empty_locenv:
  forall gc te te' eh' a,
  eval_eqf gc te empty_locenv te' eh' a ->
  eh' = empty_locenv.
Proof.
  intros. inv H. inv H4; auto.
  inv H5. rewrite PTree.gempty in H4. congruence.
Qed.

Lemma locenv_setvarfs_empty_locenv:
  forall gc te eh lhs vrets te' eh',
  locenv_setvarfs gc te eh lhs vrets te' eh' ->
  eh = empty_locenv ->
  eh' = empty_locenv.
Proof.
  induction 1; intros; auto.
  subst. inv H; auto.
  inv H2. rewrite PTree.gempty in *. congruence.
Qed.

Lemma eval_node_empty_env:
  forall e e' fd vargs' vrets,
  eval_node e e' fd vargs' vrets ->
  e = empty_env ->
  e' = empty_env.
Proof.
  induction 1 using eval_node_ind2 with
  ( P0 := fun nid te e te' e' s =>
      e = empty_env ->
      e' = empty_env
  ); intros; eauto.
  +inv H0. apply eval_eqf_empty_locenv in H; auto. subst; auto.
  +inv H13. inv H2. rewrite PTree.gempty in *. congruence.
  +inv H13. apply locenv_setvarfs_empty_locenv in H6; auto. subst; auto.
  +inv H1. apply eval_eqf_empty_locenv in H; auto. subst; auto.
  +inv H3.
  assert ({| le := eh1; sube := se1 |} = empty_env).
    apply IHeval_node; auto.
  inv H3. apply eval_eqf_empty_locenv in H1; auto. subst; auto.
Qed.

End SEMANTICS.

Section GLOBAL_ENV.

Variable p: program.
Variable gc: locenv.

Inductive node_match: ident*func -> ident*func -> Prop :=
  | node_match_: forall f1 f2,
      nd_kind (snd f1) = nd_kind (snd f2) ->
      nd_fld (snd f1) = nd_fld (snd f2) ->
      nd_sid (snd f1) = nd_sid (snd f2) ->
      calldefs_match (instidof (nd_stmt (snd f1))) (instidof (nd_stmt (snd f2))) ->
      node_match f1 f2

with calldefs_match: list calldef -> list calldef -> Prop :=
  | calldefs_match_nil:
      calldefs_match nil nil
  | calldefs_match_cons: forall c1 c2 l1 l2 f1 f2,
      instid c1 = instid c2 ->
      find_funct (node_block p) (callid c1) = Some f1 ->
      find_funct (node_block p) (callid c2) = Some f2 ->
      node_match f1 f2 ->
      calldefs_match l1 l2 ->
      calldefs_match (c1::l1) (c2::l2).

Scheme node_match_ind2 := Minimality for node_match Sort Prop
  with calldefs_match_ind2 := Minimality for calldefs_match Sort Prop.
Combined Scheme node_calldefs_match_ind2 from node_match_ind2, calldefs_match_ind2.

Inductive env_fld_match: ident*func -> env -> Prop :=
  | env_fld_match_fcons: forall nd eh se,
      nd_fld (snd nd) <> Fnil ->
      subenv_fld_match (nd_fld (snd nd)) (instidof (nd_stmt (snd nd))) se ->
      env_fld_match nd (mkenv eh se)
  | env_fld_match_fnil: forall nd,
      nd_fld (snd nd) = Fnil ->
      env_fld_match nd empty_env

with subenv_fld_match: fieldlist -> list calldef -> subenv -> Prop :=
  | subenv_fld_match_nil: forall fld se,
     subenv_fld_match fld nil se
  | subenv_fld_match_cons: forall fld c l se el fd,
     se ! (instid c) = Some el ->
     find_funct (node_block p) (callid c) = Some fd ->
     list_fld_match fd el ->
     subenv_fld_match fld l se ->
     subenv_fld_match fld (c::l) se
with list_fld_match: ident*func -> list env -> Prop :=
  | list_fld_match_nil: forall fd,
     list_fld_match fd nil
  | list_fld_match_cons: forall fd e el,
     env_fld_match fd e ->
     list_fld_match fd el ->
     list_fld_match fd (e::el).

Scheme env_fld_match_ind3 := Minimality for env_fld_match Sort Prop
  with subenv_fld_match_ind3 := Minimality for subenv_fld_match Sort Prop
  with list_fld_match_ind3 := Minimality for list_fld_match Sort Prop.

Combined Scheme env_fld_match_combined_ind3 from env_fld_match_ind3, subenv_fld_match_ind3, list_fld_match_ind3.

Lemma node_match_sym:
 (
  forall f1 f2,
  node_match f1 f2 ->
  node_match f2 f1
 )
/\
 (
  forall l1 l2,
  calldefs_match l1 l2 ->
  calldefs_match l2 l1
 ).
Proof.
  apply node_calldefs_match_ind2; intros.
  +constructor 1; auto.
  +constructor.
  +constructor 2 with f2 f1; auto.
Qed.

Lemma env_fld_match_node_match:
  (
    forall f1 e,
    env_fld_match f1 e ->
    forall f2, node_match f1 f2 ->
    env_fld_match f2 e
  )
/\
  (
    forall fld l1 se,
    subenv_fld_match fld l1 se ->
    forall l2, calldefs_match l1 l2 ->
    subenv_fld_match fld l2 se
  )
/\
  (
    forall f1 el,
    list_fld_match f1 el ->
    forall f2, node_match f1 f2 ->
    list_fld_match f2 el
  ).
Proof.
  apply env_fld_match_combined_ind3; intros.
  +inv H2. constructor 1. congruence.
   rewrite <-H4. apply H1; auto.
  +constructor 2; auto. inv H0. congruence.
  +inv H. constructor.
  +inv H5. constructor 2 with el f2; auto.
   congruence. apply H2; auto. congruence.
  +constructor.
  +constructor 2; auto.
Qed.

Lemma subenv_fld_match_list:
  forall fld l se,
  subenv_fld_match fld l se ->
  forall cdef efs fd,
  se ! (instid cdef) = Some efs ->
  find_funct (node_block p) (callid cdef) = Some fd ->
  In cdef l ->
  list_fld_match fd efs.
Proof.
  induction 1; simpl; intros. tauto.
  destruct H5; eauto. subst. congruence.
Qed.

Lemma list_fld_match_nth:
  forall fd efs,
  list_fld_match fd efs ->
  forall i ef,
  nth_error efs i = value ef ->
  env_fld_match fd ef.
Proof.
  induction 1, i; simpl; intros; try (inv H; fail); eauto.
  inv H1; auto.
Qed.

Lemma env_fld_match_sube:
  forall nd eh se nid cdef fd i se' ef ef',
  env_fld_match nd (mkenv eh se) ->
  call_node (node_block p) nid cdef nd fd ->
  callnd_env cdef i se se' ef ef' ->
  In cdef (instidof (nd_stmt (snd nd))) ->
  env_fld_match fd ef.
Proof.
  intros. inv H; inv H1.
  +destruct H0 as [? [? [? [? [? [? [? ?]]]]]]].
   destruct H4. eapply list_fld_match_nth; eauto.
   eapply subenv_fld_match_list; eauto.
  +rewrite PTree.gempty in H. congruence.
Qed.

Lemma list_fld_match_replace:
  forall fd el,
  list_fld_match fd el ->
  forall ef' i, env_fld_match fd ef' ->
  list_fld_match fd (replace_nth el i ef').
Proof.
  induction 1; simpl; intros; auto.
  rewrite replace_nth_nil. constructor; auto. constructor.
  destruct i; simpl.
  unfold replace_nth. simpl. constructor 2;auto.
  rewrite replace_nth_shift. constructor 2;auto.
Qed.

Lemma subenv_fld_match_setother:
  forall fld l se,
  subenv_fld_match fld l se ->
  forall id el, ~ In id (map instid l) ->
  subenv_fld_match fld l (PTree.set id el se).
Proof.
  induction 1; simpl; intros.
  constructor.
  constructor 2 with el fd; auto.
  rewrite PTree.gso; auto.
Qed.

Lemma env_fld_match_replace:
  forall fld l se,
  subenv_fld_match fld l se ->
  forall cdef i se' ef ef' nid nd fd,
  call_node (node_block p) nid cdef nd fd ->
  callnd_env cdef i se se' ef ef' ->
  In cdef l ->
  list_norepet (map instid l) ->
  env_fld_match fd ef' ->
  subenv_fld_match fld l se'.
Proof.
  induction 1; simpl; intros. constructor.
  inv H6. destruct H5; subst.
  +inv H4. destruct H3 as [? [? [? [? [? [? [? ?]]]]]]].
   unfold func in *. rewrite H14,H5 in *. inv H. inv H0.
   constructor 2 with (replace_nth el (nat_of_int i) ef') fd; auto.
   -rewrite PTree.gss; auto.
   -eapply list_fld_match_replace; eauto.
   -apply subenv_fld_match_setother; auto.
  +econstructor 2; eauto.
   inv H4. rewrite PTree.gso; auto.
   red; intros. rewrite H4 in *.
   apply H10. apply in_map; auto.
Qed.

Inductive initial_node_state(fd: ident*func): env -> Prop :=
  | initial_state_node: forall e e1 fi,
      init_genvc (const_block p) = Some gc ->
      find_funct (node_block p) (reset_id p.(node_main)) = Some fi ->
      find_funct (node_block p) p.(node_main) = Some fd ->
      node_match fi fd ->
      args_prop (nd_args (snd fd)) ->
      alloc_node p e fd ->
      eval_node p gc e e1 fi nil nil ->
      initial_node_state fd e1.

End GLOBAL_ENV.
