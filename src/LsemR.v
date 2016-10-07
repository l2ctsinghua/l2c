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
Require Import Ctypes.
Require Import Cltypes.
Require Import Cop.
Require Import Maps.
Require Import Memdata.
Require Import List.
Require Import ExtraList.
Require Import Lvalues.
Require Import Inclusion.
Require Import Ltypes.
Require Import Lop.
Require Import Lident.
Require Import Lustre.
Require Import LustreR.
Require Import Lenv.
Require Import Lenvmatch.
Require Import Lsem.

Section SEMANTICS.

Variable typecmp: bool.
Variable p: program.
Variable gc: locenv.

Inductive eval_node: env -> env -> ident*node -> list val -> list val -> Prop :=
  | exec_node: forall te te1 te2 eh eh1 eh3 se se' vrs vas nid f,
      alloc_variables empty_locenv (allvarsof f) te ->
      locenv_setvars te f.(nd_args) vas te1 ->
      ids_norepet f ->
      eval_stmt (nd_kind f) te1 (mkenv eh se) te2 (mkenv eh1 se') f.(nd_stmt) ->
      eval_poststmt gc te2 eh1 (fbyeqof f.(nd_stmt)) eh3 ->
      locenv_getvars te2 f.(nd_rets) vrs ->
      has_types vrs (map snd (nd_rets f)) ->
      eval_node (mkenv eh se) (mkenv eh3 se') (nid,f) vas vrs

with eval_stmt: bool -> locenv -> env -> locenv -> env -> stmt  -> Prop :=
  | eval_Sassign: forall nk te te' e lh a,
      eval_eqf gc te te' (lh,a) ->
      eval_stmt nk te e te' e (Sassign lh a)
  | eval_Scall: forall nk te te' eh se ef ef' se' oid cdef fd args lhs vl vargs vargs' vrets i,
      load_loopid gc te oid (callnum cdef) i ->
      callorder nk (nd_kind (snd fd)) = true ->
      call_func (node_block p) cdef fd ->
      call_env cdef i se se' ef ef' ->
      eval_sexps gc te args vargs ->
      eval_casts vargs (map typeof args) vargs' ->
      eval_node ef ef' fd vargs' vrets ->
      locenv_setlvars gc te lhs vrets te' ->
      Forall (lid_disjoint) lhs ->
      map typeof lhs = map snd (nd_rets (snd fd)) ->
      map typeof args = map snd (nd_args (snd fd)) ->
      locenv_getmvls gc te lhs vl ->
      lvalue_list_norepet (eval_lvalue gc te) lhs ->
      assign_list_disjoint (eval_lvalue gc te) lhs args ->
      te ! (callid cdef) = None ->
      eval_stmt nk te (mkenv eh se) te' (mkenv eh se') (Scall oid lhs cdef args)
  | eval_Sfor_start: forall nk te te1 te2 e e1 a1 a2 a3 s,
      eval_eqf gc te te1 a1 ->
      eval_stmt nk te1 e te2 e1 (Sfor None a2 a3 s) ->
      eval_stmt nk te e te2 e1 (Sfor (Some a1) a2 a3 s)
  | eval_Sfor_false: forall nk te e a2 a3 s,
      eval_sexp gc te a2 Vfalse ->
      eval_stmt nk te e te e (Sfor None a2 a3 s)
  | eval_Sfor_loop: forall nk te te1 te2 te3 e e1 e2 a2 a3 s,
      eval_sexp gc te a2 Vtrue ->
      eval_stmt nk te e te1 e1 s ->
      eval_eqf gc te1 te2 a3 ->
      eval_stmt nk te2 e1 te3 e2 (Sfor None a2 a3 s) ->
      eval_stmt nk te e te3 e2 (Sfor None a2 a3 s)
  | eval_Sskip: forall nk te e ,
      eval_stmt nk te e te e Sskip
  | eval_Sseq: forall nk te te1 te2 e e1 e2 s1 s2,
      eval_stmt nk te e te1 e1 s1 ->
      eval_stmt nk te1 e1 te2 e2 s2 ->
      eval_stmt nk te e te2 e2 (Sseq s1 s2)
  | eval_Sif: forall nk te te1 e e1 a s1 s2 v b,
      eval_sexp gc te a v ->
      bool_val v (typeof a) = Some b ->
      eval_stmt nk te e te1 e1 (if b then s1 else s2)  ->
      eval_stmt nk te e te1 e1 (Sifs a s1 s2)
  | eval_Scase: forall nk te te1 e lh ca pl i a,
      eval_sexp gc te ca (Vint i) ->
      select_case i pl = Some a ->
      eval_stmt nk te e te1 e (Sassign lh a) ->
      eval_stmt nk te e te1 e (Scase lh ca pl)
  | eval_Sfby_cycle_1: forall te te1 eh se lh id a1 a2,
      eval_sexp empty_locenv eh (Svar ACG_INIT type_bool) Vtrue ->
      eval_eqf gc te te1 (lh,a2) ->
      eval_stmt true te (mkenv eh se) te1 (mkenv eh se) (Sfby lh id a1 a2)
  | eval_Sfby_cycle_n: forall te te1 eh se lh id a1 a2 v1 v,
      eval_sexp empty_locenv eh (Svar ACG_INIT type_bool) Vfalse ->
      eval_sexp empty_locenv eh (Svar id (typeof a1)) v1 ->
      typeof lh = typeof a1 ->
      eval_cast v1 (typeof lh) v ->
      locenv_setlvar gc te lh v te1 ->
      ~ In id (get_lids lh) ->
      eval_stmt true te (mkenv eh se) te1 (mkenv eh se) (Sfby lh id a1 a2)
  | eval_Sfbyn_cycle_1: forall te te1 eh eh1 eh2 se lh id1 id2 aid sa aty i a1 a2 v1 v2 v,
      Tarray aid (typeof a1) (Int.unsigned i) = aty ->
      Svar id1 (make_fbyn_type id2 aty) = sa ->
      eval_sexp empty_locenv eh (Svar ACG_INIT type_bool) Vtrue->
      eval_sexp gc te a2 v2 ->
      eval_fbyn_init gc id1 id2 aid (typeof a2) Int.zero i v2 eh eh1 ->
      eval_eqf gc eh1 eh2 (Sfield sa FBYIDX type_int32s, Sconst (Cint Int.zero) type_int32s) ->
      eval_sexp empty_locenv eh2 (fbyn_aryacc sa (typeof a1) aty) v1 ->
      typeof lh = typeof a2 ->
      typeof lh = typeof a1 ->
      eval_cast v1 (typeof lh) v ->
      locenv_setlvar gc te lh v te1 ->
      ~ In id1 (get_lids a2++get_lids lh) ->
      eval_stmt true te (mkenv eh se) te1 (mkenv eh2 se) (Sfbyn lh (id1,id2,aid) i a1 a2)
  | eval_Sfbyn_cycle_n: forall te te1 eh se lh id1 id2 aid sa aty i a1 a2 v1 v,
      Tarray aid (typeof a1) (Int.unsigned i) = aty ->
      Svar id1 (make_fbyn_type id2 aty) = sa ->
      eval_sexp empty_locenv eh (Svar ACG_INIT type_bool) Vfalse->
      eval_sexp empty_locenv eh (fbyn_aryacc sa (typeof a1) aty) v1 ->
      typeof lh = typeof a2 ->
      typeof lh = typeof a1 ->
      eval_cast v1 (typeof lh) v ->
      locenv_setlvar gc te lh v te1 ->
      ~ In id1 (get_lids lh) ->
      eval_stmt true te (mkenv eh se) te1 (mkenv eh se) (Sfbyn lh (id1,id2,aid) i a1 a2)
  | eval_Sarrow: forall te te1 eh se lh a1 a2 v b,
      eval_sexp empty_locenv eh (Svar ACG_INIT type_bool) v ->
      bool_val v type_bool = Some b ->
      eval_eqf gc te te1 (if b then (lh,a1) else (lh,a2)) ->
      eval_stmt true te (mkenv eh se) te1 (mkenv eh se) (Sarrow lh a1 a2)
  | eval_Stypecmp: forall nk te te' e lh a1 a2 b,
      typecmp = true ->
      eval_typecmp gc (type_block p) te a1 a2 b ->
      lid_disjoint lh ->
      typeof lh = type_bool ->
      assign_list_disjoint (eval_lvalue gc te) (lh :: nil) (a1 :: a2 :: nil) ->
      locenv_setlvar gc te lh (if b then Vtrue else Vfalse) te' ->
      eval_stmt nk te e te' e (Stypecmp lh a1 a2).

Scheme eval_node_ind2 := Minimality for eval_node Sort Prop
  with eval_stmt_ind2 := Minimality for eval_stmt Sort Prop.
Combined Scheme eval_node_stmt_ind2 from eval_node_ind2, eval_stmt_ind2.

Inductive init_node: env -> ident*node -> Prop :=
  | init_node_: forall eh1 se nid f,
      ids_norepet f ->
      eval_init (length (fbyeqof (nd_stmt f))) empty_locenv ((ACG_INIT,type_bool) :: fbyvarsof f.(nd_stmt)) eh1 ->
      (forall ty, In ty (map snd (nd_rets f ++ fbyvarsof f.(nd_stmt))) -> 0 < sizeof ty) ->
      init_stmt (nd_kind f) (mkenv eh1 empty_subenv) (mkenv eh1 se) (instidof f.(nd_stmt)) ->
      init_node (mkenv eh1 se) (nid,f)

with init_stmt: bool -> env -> env -> list calldef ->  Prop :=
  | init_call_nil: forall nk e,
      init_stmt nk e e nil
  | init_call_node_cons: forall nk le se se1 se2 fd ef c l,
      callorder nk (nd_kind (snd fd)) = true ->
      call_func (node_block p) c fd ->
      init_node ef fd ->
      se1 = PTree.set (instid c) (list_repeat (nat_of_int (intof_opti (callnum c))) ef) se ->
      init_stmt nk (mkenv le se1) (mkenv le se2) l ->
      init_stmt nk (mkenv le se) (mkenv le se2) (c::l).

Scheme init_node_ind2 := Minimality for init_node Sort Prop
  with init_stmt_ind2 := Minimality for init_stmt Sort Prop.
Combined Scheme init_node_stmt_ind2 from init_node_ind2, init_stmt_ind2.

Lemma locenv_setlvar_cast_mvl_ret:
  forall e lh v e1 id mv t chunk,
  locenv_setlvar gc e lh v e1 ->
  In id (get_lids lh) ->
  e ! id = Some (mv, t) ->
  eval_cast v (typeof lh) v ->
  access_mode t = By_value chunk ->
  exists mv1 v1, e1 ! id = Some (mv1,t)
    /\ mv1 = encode_val chunk v1
    /\ eval_cast v1 t v1.
Proof.
  intros. inv H.
  erewrite eval_lvalue_get_lids in H0; eauto.
  simpl in *. destruct H0; try tauto; subst.
  inv H5. rewrite H in H1. inv H1.
  rewrite PTree.gss. exists m', v. split; auto.
  generalize H4; intros.
  eapply eval_lvalue_by_value_lid in H4; eauto.
  subst. inv H1. inv H6. simpl in *.
  rewrite H1 in H3. inv H3. split; auto.
  unfold store in *. destruct (valid_access_dec _ _ _); inv H4.
  rewrite setN_full; auto.
  rewrite encode_val_length. unfold Memdata.size_chunk_nat.
  erewrite sizeof_chunk_eq; eauto. rewrite H0.
  rewrite nat_of_Z_of_nat; auto.
  simpl in *. destruct H1; congruence.
Qed.

Lemma locenv_setlvars_cast_ret_alloc:
  forall e1 e2 l vl,
  locenv_setlvars gc e1 l vl e2 ->
  eval_casts vl (map typeof l) vl ->
  forall id t mv1 mv2 chunk,
  e1 ! id = Some (mv1,t)->
  e2 ! id = Some (mv2, t) ->
  mv1 <> mv2 ->
  access_mode t = By_value chunk ->
  exists v1, mv2 = encode_val chunk v1 /\ eval_cast v1 t v1.
Proof.
  induction 1; simpl; intros; auto.
  +congruence.
  +assert(A: ~In id (get_lids lhs) \/ In id (get_lids lhs)).
     tauto.
   inv H1. destruct A as [A | A].
   -inv H. eapply IHlocenv_setlvars; eauto.
    erewrite eval_lvalue_get_lids in A; eauto.
    inv H6. simpl in *. rewrite PTree.gso; auto.
   -eapply locenv_setlvar_cast_mvl_ret in H; eauto.
    destruct H as [mv [v1 [? [? ?]]]].
    assert (A1: mv2 = mv \/ mv2 <>  mv).
      tauto.
    destruct A1; subst; eauto.
Qed.

Lemma eval_eqf_locenv_setlvars_cast_exists:
  forall e e' a,
  eval_eqf gc e e' a ->
  exists l vl, locenv_setlvars gc e l vl e' /\ eval_casts vl (map typeof l) vl.
Proof.
  intros. inv H.
  exists (a1::nil), (v'::nil). split.
  +constructor 2 with e'; auto. constructor.
  +constructor 2; auto.
   eapply eval_cast_idem; eauto.
   constructor.
Qed.

Lemma eval_casts_idem_nth:
  forall vrs tys ,
  length vrs = length tys ->
  (forall i, (i < length vrs)%nat ->
    eval_cast (nth i vrs Vtrue) (nth i tys Tvoid) (nth i vrs Vtrue)) ->
  eval_casts vrs tys vrs.
Proof.
  induction vrs; destruct tys; intros; simpl in H; try omega.
  constructor.
  constructor 2; auto.
  generalize (H0 O). simpl. intros. apply H1; omega.
  apply IHvrs; auto. intros.
  generalize (H0 (S i)). simpl. intros. apply H2; omega.
Qed.

Lemma locenv_setlvars_eval_casts_idem:
  forall te1 l vl te2,
  locenv_setlvars gc te1 l vl te2 ->
  eval_casts vl (map typeof l) vl ->
  forall rets vrs,
  (forall id ty, In (id,ty) rets -> te1 ! id = Some (alloc (sizeof ty),ty))->
  locenv_getvars te2 rets vrs ->
  has_types vrs (map snd rets) ->
  eval_casts vrs (map snd rets) vrs.
Proof.
  intros. generalize H3; intros A.
  apply Forall2_length in A.
  eapply eval_casts_idem_nth; eauto.
  rewrite map_length in A.
  intros. apply Forall2_nth_in with (A:=(prod positive type)) (B:=val) (i:=i) (d1:=(1%positive,Tvoid)) (d2:=Vtrue) in H2.
  change Tvoid with (snd (xH, Tvoid)). rewrite map_nth.
  cut (In (nth i rets (1%positive,Tvoid)) rets). intros A1.
  destruct (nth i rets (1%positive, Tvoid)) eqn:?.
  destruct H2 as [? [? [? ?]]].
  generalize A1; intros A2. apply H1 in A1.
  simpl in *. inv H6.
  +rewrite Int.unsigned_zero in *.
   unfold load in *. destruct (valid_access_dec _ _ _); try congruence.
   simpl in *. unfold Memdata.size_chunk_nat in *.
   erewrite sizeof_chunk_eq in H8; eauto.
   rewrite H5, nat_of_Z_of_nat in *. rewrite getN_full in H8.
   eapply locenv_setlvars_cast_ret_alloc in H; eauto.
   destruct H as [v1 [? ?]]. subst.
   generalize H6; intros A3.
   inv H6. rewrite H in H7. inv H7.
   eapply sem_cast_decode_encode_val in H9; eauto.
   rewrite H9 in H8. inv H8. auto.
   constructor 2; auto.
   red; intros. rewrite <-H6, <-H5 in H8.
   rewrite decode_val_alloc_none in H8; auto.
   congruence.
  +constructor 2; auto.
  +apply nth_In; auto. omega.
  +omega.
Qed.

Lemma eval_node_rets_cast:
  forall e e' fd vargs vrets,
  eval_node e e' fd vargs vrets ->
  eval_casts vrets (map snd (nd_rets (snd fd))) vrets.
Proof.
  induction 1 using eval_node_ind2 with
  ( P0 := fun nid te e te' e' s =>
      exists l vl, locenv_setlvars gc te l vl te'
        /\ eval_casts vl (map typeof l) vl); eauto;
 try (eapply eval_eqf_locenv_setlvars_cast_exists; eauto; fail).
 +simpl in *. destruct IHeval_node as [l [vl [? ?]]].
  eapply locenv_setlvars_eval_casts_idem; eauto.
  intros. unfold allvarsof in H. apply alloc_variables_app in H.
   destruct H as [e0 [? ?]].
   erewrite set_new_vars_getid_eq; eauto.
   *eapply alloc_variables_norepeat_in_eq with (e:=e0); eauto.
    apply ids_norepet_rets_norepet in H1; auto.
   *apply ids_norepet_vars_args_rets_disjoint in H1; auto.
    simpl in *. rewrite map_app in H1.
    apply list_disjoint_notin with (map fst (nd_rets f)); eauto.
    apply list_disjoint_sym. eapply list_disjoint_app_left; eauto.
    apply in_map with (f:=fst) in H8; auto.
 +exists lhs, vrets. split; auto.
  rewrite H8; auto.
 +eapply eval_eqf_locenv_setlvars_cast_exists in H; eauto.
   destruct H  as [l1 [vl1 [? ?]]].
   destruct IHeval_node as [l2 [vl2 [? ?]]].
   exists (l1++l2), (vl1++vl2). split.
   -eapply locenv_setlvars_app; eauto.
   -rewrite map_app. apply eval_casts_app; auto.
  +exists nil, nil. split; constructor.
  +destruct IHeval_node as [l1 [vl1 [? ?]]].
   eapply eval_eqf_locenv_setlvars_cast_exists in H1; eauto.
   destruct H1 as [l2 [vl2 [? ?]]].
   destruct IHeval_node0 as [l3 [vl3 [? ?]]].
   exists (l1++l2++l3), (vl1++vl2++vl3). split.
   -repeat eapply locenv_setlvars_app; eauto.
   -repeat rewrite map_app. repeat apply eval_casts_app; auto.
  +exists nil, nil. split; constructor.
  +destruct IHeval_node as [l1 [vl1 [? ?]]].
   destruct IHeval_node0 as [l2 [vl2 [? ?]]].
   exists (l1++l2), (vl1++vl2). split.
   -eapply locenv_setlvars_app; eauto.
   -rewrite map_app. apply eval_casts_app; auto.
  +exists (lh::nil), (v::nil). split; econstructor 2; eauto.
   constructor. eapply eval_cast_idem; eauto. constructor.
  +exists (lh::nil), (v::nil). split; econstructor 2; eauto.
   constructor. eapply eval_cast_idem; eauto. constructor.
  +exists (lh::nil), (v::nil). split; econstructor 2; eauto.
   constructor. eapply eval_cast_idem; eauto. constructor.
  +exists (lh::nil), ((if b then Vtrue else Vfalse)::nil).
   split; econstructor 2; eauto.
   constructor. rewrite H2. constructor 1 with Mint8unsigned; auto.
   destruct b; auto. constructor.
Qed.

End SEMANTICS.

Lemma eval_node_nocycle_app1:
  forall tk p1 gc e e' fd vargs vrets,
  eval_node tk p1 gc e e' fd vargs vrets->
  forall p2 l, node_block p2 = node_block p1 ++ l ->
  type_block p2 = type_block p1 ->
  eval_node tk p2 gc e e' fd vargs vrets.
Proof.
  intros until vrets.
  induction 1 using eval_node_ind2 with
  (P0:= fun nk te e te' e' s=>
     forall p2 l, node_block p2 = node_block p1 ++ l ->
     type_block p2 = type_block p1 ->
     eval_stmt tk p2 gc nk te e te' e' s); intros;
  try (econstructor; eauto; fail).
  +eapply eval_Scall; eauto. rewrite H14. eapply call_func_app in H1; eauto.
  +eapply eval_Sfby_cycle_n; eauto.
  +eapply eval_Sfbyn_cycle_n; eauto.
  +eapply eval_Stypecmp; eauto. congruence.
Qed.


Lemma eval_node_nocycle_app2:
  forall tk p gc e e' fd vargs vrets,
  eval_node tk p gc e e' fd vargs vrets ->
  forall nd p1 l,
  In fd (node_block p1 ++ nd :: nil) ->
  node_block p = node_block p1 ++ nd :: l ->
  type_block p1 = type_block p ->
  list_disjoint (flat_map callidof (node_block p1 ++ nd :: nil)) (map fst (nd::l)) ->
  eval_node tk p1 gc e e' fd vargs vrets.
Proof.
  intros until vrets.
  induction 1 using eval_node_ind2 with
  (P0:= fun nk te e te' e' s =>
     forall nd p1 l,
     node_block p = node_block p1 ++ nd :: l ->
     type_block p1 = type_block p ->
     list_disjoint (flat_map callidof (node_block p1 ++ nd :: nil)) (map fst (nd::l)) ->
     list_disjoint (get_stmt_nids s) (map fst (nd::l)) ->
     eval_stmt tk p1 gc nk te e te' e' s); simpl in *; intros;
  try (econstructor; eauto; fail).
  +eapply exec_node; eauto. apply IHeval_node with nd l; auto.
   eapply list_disjoint_incl_left; eauto.
   eapply get_stmt_nids_incl; eauto.
  +rewrite H14 in *. eapply call_func_disjoint in H1; eauto.
   eapply eval_Scall; eauto.
   eapply IHeval_node; eauto.
   apply call_func_in in H1; intuition.
  +apply list_disjoint_app_left in H4. destruct H4.
   eapply eval_Sseq; eauto.
  +apply list_disjoint_app_left in H5. destruct H5.
   eapply eval_Sif; eauto.
   eapply IHeval_node; eauto. destruct b; auto.
  +eapply eval_Sfby_cycle_n; eauto.
  +eapply eval_Sfbyn_cycle_n; eauto.
  +eapply eval_Stypecmp; eauto. congruence.
Qed.

Lemma eval_node_program_dep:
  forall tk p1 gc e e' node vargs vrets,
  eval_node tk p1 gc e e' node vargs vrets ->
  forall p2, node_block p1 = node_block p2 ->
  type_block p1 = type_block p2 ->
  eval_node tk p2 gc e e' node vargs vrets.
Proof.
  intros until vrets.
  induction 1 using eval_node_ind2 with
  (P0:= fun nk te e te' e' s =>
     forall p2, node_block p1 = node_block p2 ->
     type_block p1 = type_block p2 ->
     eval_stmt tk p2 gc nk te e te' e' s); simpl in *; intros;
  try (econstructor; eauto; fail).
  +eapply eval_Scall; eauto. congruence.
  +eapply eval_Sfby_cycle_n; eauto.
  +eapply eval_Sfbyn_cycle_n; eauto.
  +eapply eval_Stypecmp; eauto. congruence.
Qed.

Lemma init_node_program_dep:
  forall p1 e fd,
  init_node p1 e fd ->
  forall p2, node_block p1 = node_block p2 ->
  init_node p2 e fd.
Proof.
  intros until fd.
  induction 1 using init_node_ind2 with
  (P0:= fun nk e e' cs =>
     forall p2, node_block p1 = node_block p2 ->
     init_stmt p2 nk e e' cs);
  simpl in *; intros.
  +constructor 1; eauto.
  +constructor.
  +constructor 2 with se1 fd ef; eauto. congruence.
Qed.

Lemma init_node_nocycle_app1:
  forall p1 e fd,
  init_node p1 e fd ->
  forall p2 l, node_block p2 = node_block p1 ++ l ->
  init_node p2 e fd.
Proof.
  intros until fd.
  induction 1 using init_node_ind2 with
  (P0:= fun nk e e' cs=>
     forall p2 l, node_block p2 = node_block p1 ++ l ->
     init_stmt p2 nk e e' cs); intros.
  +econstructor; eauto.
  +constructor.
  +constructor 2 with se1 fd ef; eauto.
   rewrite H4. eapply call_func_app in H0; eauto.
Qed.

Lemma init_node_nocycle_app2:
  forall p e fd,
  init_node p e fd ->
  forall nd p1 l,
  In fd (node_block p1 ++ nd :: nil) ->
  node_block p = node_block p1 ++ nd :: l ->
  list_disjoint (flat_map callidof (node_block p1 ++ nd :: nil)) (map fst (nd::l)) ->
  init_node p1 e fd.
Proof.
  intros until fd.
  induction 1 using init_node_ind2 with
  (P0:= fun nk e e' cs =>
     forall nd p1 l,
     node_block p = node_block p1 ++ nd :: l ->
     list_disjoint (flat_map callidof (node_block p1 ++ nd :: nil)) (map fst (nd::l)) ->
     list_disjoint (map callid cs) (map fst (nd::l)) ->
     init_stmt p1 nk e e' cs); simpl in *; intros.
  +constructor 1; auto.
   apply IHinit_node with nd l; auto.
   eapply list_disjoint_incl_left; eauto.
   generalize (instid_get_stmt_nids (nd_stmt f)); intros.
   eapply get_stmt_nids_incl in H3; eauto.
   unfold incl in *. auto.
  +constructor.
  +rewrite H4 in *. eapply call_func_disjoint in H0; eauto.
   constructor 2 with se1 fd ef; auto.
   eapply IHinit_node; eauto.
   apply call_func_in in H0; intuition.
   eapply IHinit_node0; eauto.
   red; intros. apply H6; simpl; auto.
   red; intros. apply H6; simpl in *; auto.
   destruct H7; auto. tauto.
Qed.

Definition mkprog(p: program)(l1: list (ident*node))(tys: list (ident * type)):=
  mkprogram p.(type_block) (p.(defs_block) ++ tys) p.(const_block)
      l1 p.(node_main).

Definition mkprog1(p: program)(l1 l2: list (ident*node))(main: ident*node)(tys: list (ident * type)):=
  mkprogram p.(type_block) (p.(defs_block) ++ tys) p.(const_block)
      (l1 ++ main :: l2) p.(node_main).

Lemma eval_node_nocycle2:
  forall tk p gc l1 l2 node e e' vargs vrets,
  eval_node tk (mkprog1 p l1 l2 node nil) gc e e' node vargs vrets ->
  topo_sorted (deps_of_nodes (l1++node::l2)) ->
  eval_node tk (mkprog p l1 nil) gc e e' node vargs vrets.
Proof.
  unfold mkprog1, mkprog. intros.
  assert(A: l1++node::l2= (l1++node::nil) ++ l2).
    rewrite <-app_assoc; auto.
  rewrite A in H0. unfold deps_of_nodes in H0.
  rewrite map_app in H0.
  apply toposort_app in H0. destruct H0 as [A1 [A2 A3]].
  assert (A4: In node (l1 ++ node :: nil)).
    apply in_or_app; simpl; auto.
  apply eval_node_nocycle_app2 with (mkprog1 p l1 l2 node nil) node l2; simpl; auto.
  apply list_disjoint_appa_right. split.
  eapply topo_sorted_callids_notin; eauto.
  eapply listdependonlist_disjoint; eauto.
Qed.

Lemma init_node_nocycle2:
  forall p l1 l2 node e,
  init_node (mkprog1 p l1 l2 node nil) e node ->
  topo_sorted (deps_of_nodes (l1++node::l2)) ->
  init_node (mkprog p l1 nil) e node.
Proof.
  unfold mkprog1, mkprog. intros.
  assert(A: l1++node::l2= (l1++node::nil) ++ l2).
    rewrite <-app_assoc; auto.
  rewrite A in H0. unfold deps_of_nodes in H0.
  rewrite map_app in H0.
  apply toposort_app in H0. destruct H0 as [A1 [A2 A3]].
  assert (A4: In node (l1 ++ node :: nil)).
    apply in_or_app; simpl; auto.
  apply init_node_nocycle_app2 with (mkprog1 p l1 l2 node nil) node l2; simpl; auto.
  apply list_disjoint_appa_right. split.
  eapply topo_sorted_callids_notin; eauto.
  eapply listdependonlist_disjoint; eauto.
Qed.
