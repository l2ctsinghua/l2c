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
Require Import ExtraList.
Require Import List.
Require Import Maps.
Require Import Cltypes.
Require Import Cop.
Require Import Lint.
Require Import Lident.
Require Import Ltypes.
Require Import Lop.
Require Import Lustre.
Require Import LustreF.
Require Import Lvalues.
Require Import Lenv.
Require Import Lenvmatch.
Require Import Lsem.
Require Import LsemD.

Section SEMANTICS.

Variable p: program.
Variable gc: locenv.

Section EXPR.

Variable ta te se: locenv.

Definition case_env(k: vkind): locenv :=
  match k with
  | Gid => gc
  | Lid => te
  | Aid => ta
  | Sid => se
  end.

Inductive eval_sexp: sexp -> val -> Prop :=
  | eval_Sconst: forall c ty,
      has_type (eval_const c) ty ->
      eval_sexp (Sconst c ty) (eval_const c)
  | eval_Sunop:  forall op a ty v1 v,
      eval_sexp a v1 ->
      sem_unary_operation op v1 (typeof a) = Some v ->
      has_type v ty ->
      eval_sexp (Sunop op a ty) v
  | eval_Sbinop: forall op a1 a2 ty v1 v2 v,
      eval_sexp a1 v1 ->
      eval_sexp a2 v2 ->
      typeof a1 = typeof a2 ->
      sem_binary_operation op v1 v2 (typeof a1) ty = Some v ->
      has_type v ty ->
      eval_sexp (Sbinop op a1 a2 ty) v
  | eval_Scast: forall a ty v v1,
      eval_sexp a v1 ->
      sem_cast v1 (typeof a) ty = Some v ->
      eval_sexp (Scast a ty) v
  | eval_Rlvalue: forall a id ofs v k,
      eval_lvalue a id ofs k ->
      load_env (typeof a) (case_env k) id ofs v->
      has_type v (typeof a) ->
      eval_sexp a v

with eval_lvalue: sexp -> ident -> int -> vkind -> Prop :=
  | eval_Svar: forall id ty m,
     te ! id = Some (m, ty) ->
     eval_lvalue (Svar id ty) id Int.zero Lid
  | eval_Scvar: forall id ty m,
     te ! id = None ->
     gc ! id = Some (m,ty) ->
     eval_lvalue (Scvar id ty) id Int.zero Gid
  | eval_Ssvar: forall id ty m,
     se ! id = Some (m, ty) ->
     eval_lvalue (Ssvar id ty) id Int.zero Sid
  | eval_Savar: forall id ty m,
     ta ! id = Some (m, ty) ->
     eval_lvalue (Savar id ty) id Int.zero Aid
  | eval_Saryacc: forall a a1 ty l ofs i k aid z,
     eval_lvalue a l ofs k->
     eval_sexp a1 (Vint i) ->
     typeof a = Tarray aid ty z ->
     eval_lvalue (Saryacc a a1 ty) l (Int.add ofs (array_ofs i ty)) k
  | eval_Sfield: forall a i ty l sid fld ofs k delta,
     eval_lvalue a l ofs k ->
     typeof a = Tstruct sid fld->
     field_offset i fld = OK delta ->
     field_type i fld = OK ty ->
     eval_lvalue (Sfield a i ty) l (Int.add ofs (Int.repr delta)) k.

Scheme eval_sexp_ind2 := Minimality for eval_sexp Sort Prop
  with eval_lvalue_ind2 := Minimality for eval_lvalue Sort Prop.
Combined Scheme eval_sexp_lvalue_ind from eval_sexp_ind2, eval_lvalue_ind2.

Definition eval_sexps(al: list sexp)(vl: list val):=
  Forall2 eval_sexp al vl.

Lemma eval_sexp_has_type:
  forall a v,
  eval_sexp a v ->
  has_type v (typeof a).
Proof.
  induction 1; simpl; auto.
  eapply sem_cast_has_type; eauto.
Qed.

Lemma eval_sexps_has_types:
  forall al vl,
  eval_sexps al vl ->
  has_types vl (map typeof al).
Proof.
  induction 1; simpl; auto.
  constructor.
  constructor 2; auto.
  apply eval_sexp_has_type; auto.
Qed.

Lemma eval_sexp_determ:
(
  forall s v1,
  eval_sexp s v1 ->
  forall v2, eval_sexp s v2 ->
  v1 = v2
)
/\
(
  forall a id1 ofs1 k1,
  eval_lvalue a id1 ofs1 k1->
  forall id2 ofs2 k2, eval_lvalue a id2 ofs2 k2 ->
  id1 = id2 /\ ofs1 = ofs2 /\ k1 = k2
).
  apply eval_sexp_lvalue_ind; intros.
  +inv H0; auto. destruct c; inv H1.
  +inv H3. apply H0 in H7. congruence. inv H4.
  +inv H6. apply H0 in H11. apply H2 in H12.
    congruence. inv H7.
  +inv H2. apply H0 in H5. congruence. inv H3.
  +inv H3; try (inv H; fail).
   apply H0 with id0 ofs0 k0 in H4; auto. destruct H4 as [? [? ?]]; subst.
   apply load_env_determ with (typeof a) (case_env k0) id0 ofs0; auto.
  +inv H0; auto.
  +inv H1; auto.
  +inv H0. auto.
  +inv H0; auto.
  +inv H4. apply H0 in H8; auto. destruct H8 as [? [? ?]].
   apply H2 with (Vint i0) in H12; auto. inv H12. auto.
  +inv H4. apply H0 in H8; auto. intuition. congruence.
Qed.

Lemma eval_sexp_exists_lvalue:
  forall a m,
  eval_sexp a (Vmvl m) ->
  exists id ofs k, eval_lvalue a id ofs k
    /\ load_env (typeof a) (case_env k) id ofs (Vmvl m)
    /\ has_type (Vmvl m) (typeof a).
Proof.
  induction a; intros;
  try (inv H; exists id, ofs, k; eauto; fail).
  +destruct c; inv H; try inv H0.
   destruct b; inv H3.
  +inv H. apply sem_cast_not_mvl in H4. inv H4. inv H0.
  +inv H. apply sem_unary_operation_not_mvl in H5.
   inv H5. inv H0.
  +inv H. apply sem_binary_operation_not_mvl in H8.
   inv H8. inv H0.
Qed.

Lemma eval_lvalue_env_some:
  forall a id ofs k,
  eval_lvalue a id ofs k ->
  exists m t, (case_env k) ! id = Some (m, t).
Proof.
  induction 1; intros; eauto.
Qed.

Lemma eval_lvalue_get_lids:
  forall a id ofs k,
  eval_lvalue a id ofs k ->
  get_lids a = id :: nil.
Proof.
  induction 1; simpl; auto.
Qed.

Lemma eval_lvalue_lid_disjoint_not_loopid:
  forall a id o k,
  eval_lvalue a id o k ->
  lid_disjoint a ->
  id <> ACG_I.
Proof.
  induction 1; simpl; intros; auto.
  destruct a1; auto. destruct H2; auto.
Qed.

Lemma eval_lvalue_some_alignof:
  forall a id ofs k m ty,
  eval_lvalue a id ofs k ->
  (case_env k) ! id = Some (m, ty) ->
  (alignof (typeof a) | alignof ty).
Proof.
  induction 1; simpl; intros.
  +rewrite H in H0. inv H0. exists 1. omega.
  +rewrite H1 in H0. inv H0. exists 1. omega.
  +rewrite H in H0. inv H0. exists 1. omega.
  +rewrite H in H0. inv H0. exists 1. omega.
  +apply Zdivide_trans with (alignof (typeof a)); eauto.
   rewrite H1. simpl. exists 1. omega.
  +apply Zdivide_trans with (alignof (typeof a)); eauto.
   rewrite H0. simpl.
   eapply field_type_alignof; eauto.
Qed.

Lemma eval_lvalue_alignof_ofs:
  forall a id ofs k,
  eval_lvalue a id ofs k ->
  (alignof (typeof a) | Int.unsigned ofs).
Proof.
  induction 1; intros.
  +rewrite Int.unsigned_zero. exists 0. omega.
  +rewrite Int.unsigned_zero. exists 0. omega.
  +rewrite Int.unsigned_zero. exists 0. omega.
  +rewrite Int.unsigned_zero. exists 0. omega.
  +rewrite H1 in *. apply Zdivides_plus_int; eauto.
   apply alignof_1248. apply alignof_array_ofs.
  +rewrite H0 in *. simpl in *. apply Zdivides_plus_int.
   apply alignof_1248.
   apply Zdivide_trans with (alignof_fields fld); auto.
   eapply field_type_alignof; eauto.
   apply Zdivide_unsigned_repr; auto.
   eapply field_offset_aligned; eauto.
   apply alignof_1248.
Qed.

Lemma eval_sexp_type_size:
  forall a v,
  eval_sexp a v ->
  0 < sizeof (typeof a) <= Int.max_signed.
Proof.
  intros. generalize H; intros.
  apply eval_sexp_has_type in H0.
  destruct has_type_access_mode with v (typeof a) as [[? ?] | ]; auto.
  +unfold Int.max_signed. simpl.
   destruct (typeof a); simpl in *; try congruence; try omega.
   destruct i; omega. destruct f; omega.
  +destruct has_type_access_mode_mvl with v (typeof a) as [? [? ?]]; auto.
   subst. generalize H; intros.
   apply eval_sexp_exists_lvalue in H2; auto. destruct H2 as [? [? [? [? [? ?]]]]].
   apply load_env_range_perm in H4; auto.
   generalize (Int.unsigned_range x1). omega.
Qed.

Record vaddr: Type := mkvaddr {
  ad_id: ident;
  ad_ofs: int;
  ad_type: type;
  ad_kind: vkind
  }.

Inductive eval_vaddr(lh: sexp): vaddr-> Prop :=
  | eval_vaddr_: forall id ofs k,
      eval_lvalue lh id ofs k ->
      eval_vaddr lh (mkvaddr id ofs (typeof lh) k).

Definition eval_vaddrs(l: list sexp)(vl: list vaddr): Prop :=
  Forall2 eval_vaddr l vl.

Lemma eval_vaddrs_type_map:
  forall l dl,
  eval_vaddrs l dl ->
  map typeof l = map ad_type dl.
Proof.
  induction 1; simpl; auto.
  inv H. f_equal; auto.
Qed.

End EXPR.

Inductive locenv_setvaddr(te e: locenv): vaddr -> val-> locenv -> locenv -> Prop :=
  | locenv_setvaddr_lid: forall te' b ofs ty v,
      store_env ty te b ofs v te' ->
      locenv_setvaddr te e (mkvaddr b ofs ty Lid) v te' e
  | locenv_setvaddr_sid: forall e' b ofs ty v,
      store_env ty e b ofs v e' ->
      locenv_setvaddr te e (mkvaddr b ofs ty Sid) v te e'.

Inductive locenv_setvaddrs(te e: locenv): list vaddr -> list val-> locenv -> locenv -> Prop :=
  | locenv_setvaddrs_nil:
      locenv_setvaddrs te e nil nil te e
  | locenv_setvaddrs_cons: forall te1 te' e1 e' a dl v vl,
      locenv_setvaddr te e a v te1 e1 ->
      locenv_setvaddrs te1 e1 dl vl te' e' ->
      locenv_setvaddrs te e (a :: dl) (v :: vl) te' e'.

Inductive vaddr_disjoint: vaddr -> vaddr -> Prop :=
  | vaddr_disjoint_arystr: forall id1 id2 o1 o2 t1 t2 k1 k2,
     id1 <> id2 \/ Int.unsigned o1 + sizeof t1 <= Int.unsigned o2 \/
       Int.unsigned o2 + sizeof t2 <= Int.unsigned o1 ->
     vaddr_disjoint (mkvaddr id1 o1 t1 k1) (mkvaddr id2 o2 t2 k2).

Definition vaddr_disjoints(dl: list vaddr)(d: vaddr) : Prop :=
  forall d1, In d1 dl -> vaddr_disjoint d d1.

Inductive vaddr_list_norepet: list vaddr -> Prop :=
  | vaddr_list_norepet_nil:
     vaddr_list_norepet nil
  | vaddr_list_norepet_cons: forall d dl,
     vaddr_disjoints dl d ->
     vaddr_list_norepet dl ->
     vaddr_list_norepet (d::dl).

Lemma eval_vaddr_disjoint:
  forall ta te e a1 a2 d1 d2,
  eval_vaddr ta te e a1 d1 ->
  eval_vaddr ta te e a2 d2 ->
  lvalue_disjoint (eval_lvalue ta te e) a1 a2 ->
  vaddr_disjoint d1 d2.
Proof.
  intros. inv H. inv H0. inv H1.
  eapply eval_sexp_determ in H; eauto.
  destruct H as [? [? ?]]; subst.
  eapply eval_sexp_determ in H2; eauto.
  destruct H2 as [? [? ?]]; subst.
  constructor; auto.
Qed.

Lemma eval_vaddrs_disjoints:
  forall ta te e a d l l',
  eval_vaddr ta te e a d ->
  eval_vaddrs ta te e l l' ->
  lvalue_disjoints (eval_lvalue ta te e) a l ->
  vaddr_disjoints l' d.
Proof.
  intros. red; intros.
  apply in_split in H2. destruct H2 as [? [? ?]]. subst.
  apply Forall2_app_inv_r in H0. destruct H0 as [? [? [? [? ?]]]].
  inv H2. eapply eval_vaddr_disjoint; eauto.
  apply H1; apply in_or_app; simpl; auto.
Qed.

Lemma eval_vaddrs_list_norepet:
  forall ta te e l dl,
  eval_vaddrs ta te e l dl ->
  lvalue_list_norepet (eval_lvalue ta te e) l ->
  vaddr_list_norepet dl.
Proof.
  induction 1; simpl; intros.
  +constructor.
  +inv H1. constructor 2; auto.
   eapply eval_vaddrs_disjoints; eauto.
Qed.

Inductive eval_eqf(ta te e: locenv): locenv -> locenv -> eqf -> Prop :=
  | eval_Eqf: forall te' e' a1 a2 v v' d,
      eval_sexp ta te e a2 v ->
      typeof a1 = typeof a2 ->
      assign_disjoint (eval_lvalue ta te e) a1 a2 ->
      eval_cast v (typeof a1) v' ->
      eval_vaddr ta te e a1 d ->
      locenv_setvaddr te e d v' te' e' ->
      te ! ACG_MEMCPY = None ->
      eval_eqf ta te e te' e' (a1,a2).

Inductive locenv_getmvl(ta te e: locenv)(lh: sexp)(mv: mvl): Prop :=
  | locenv_getmvl_: forall id ofs k m t,
      eval_lvalue ta te e lh id ofs k ->
      k = Lid \/ k = Sid ->
      (case_env ta te e k) ! id = Some (m,t) ->
      loadbytes m (Int.unsigned ofs) (sizeof (typeof lh)) = Some mv ->
      locenv_getmvl ta te e lh mv.

Definition locenv_getmvls(ta te e: locenv)(l: list sexp)(vl: list mvl): Prop :=
  Forall2 (locenv_getmvl ta te e) l vl.

Lemma locenv_getmvl_mvl_length:
  forall ta te e a mv,
  locenv_getmvl ta te e a mv ->
  0 < Z.of_nat (length mv).
Proof.
  intros. inv H.
  erewrite <-loadbytes_length2; eauto.
  apply loadbytes_range_perm in H3. red in H3. omega.
Qed.

Definition locenv_rets_match(e: locenv)(rets: list (ident*type)) : Prop :=
  forall id mv t, e ! id = Some (mv,t) -> In (id,t) rets.

Lemma locenv_setmvls_locenv_rets_match:
  forall rets vl ef,
  LsemD.locenv_setmvls empty_locenv rets vl ef ->
  list_norepet (map fst rets) ->
  locenv_rets_match ef rets.
Proof.
  intros. red; intros.
  eapply locenv_setmvls_locenv_rets_match_rec; eauto.
  rewrite PTree.gempty; auto.
Qed.

Lemma alloc_variables_locenv_sets_match:
  forall al ta,
  alloc_variables empty_locenv al ta ->
  list_norepet (map fst al) ->
  locenv_rets_match ta al.
Proof.
  intros. red; intros.
  eapply  alloc_variables_norepeat_ptree_in_exists in H; eauto.
  +destruct H as [ty [? ?]]. inv H2. auto.
  +rewrite PTree.gempty; auto.
Qed.

Lemma locenv_setvars_locenv_sets_match:
  forall ta al vas ta1,
  locenv_setvars ta al vas ta1 ->
  locenv_rets_match ta al ->
  list_norepet (map fst al) ->
  locenv_rets_match ta1 al.
Proof.
  unfold locenv_rets_match. intros.
  assert(In id (map fst al) \/ ~ In id (map fst al)).
    tauto.
  destruct H3.
  +eapply locenv_setvars_in_exists in H3; eauto.
   destruct H3 as [m ?]. destruct m.
   eapply locenv_setvars_type_determ in H; eauto.
   subst. apply H0 with m; auto.
  +apply H0 with mv.
   erewrite <- set_new_vars_getid_eq; eauto.
Qed.

Inductive eval_node: locenv -> locenv -> ident*func -> list val -> list val  -> Prop :=
  | exec_node: forall ta ta1 te te1 e e1 vrs vas nid f,
      alloc_variables empty_locenv (nd_args f) ta ->
      alloc_variables empty_locenv (nd_vars f) te ->
      locenv_setvars ta f.(nd_args) vas ta1 ->
      list_norepet (map fst (nd_vars f)) ->
      list_norepet (map fst (nd_args f++nd_rets f)) ->
      eval_stmt ta1 te e te1 e1 f.(nd_stmt) ->
      locenv_getvars e1 f.(nd_rets) vrs ->
      eval_node e e1 (nid,f) vas vrs

with eval_stmt: locenv -> locenv -> locenv -> locenv -> locenv -> stmt  -> Prop :=
  | eval_Sassign: forall ta te te' e e' lh a,
      eval_eqf ta te e te' e' (lh,a) ->
      eval_stmt ta te e te' e' (Sassign lh a)
  | eval_Scall: forall ta te te' e e' ef ef' vl dl oid cdef fd args lhs vargs vargs' vrets,
      call_func (node_block p) cdef fd ->
      eval_sexps ta te e args vargs ->
      eval_casts vargs (map typeof args) vargs' ->
      locenv_getmvls ta te e lhs vl ->
      locenv_setmvls empty_locenv (nd_rets (snd fd)) vl ef ->
      eval_node ef ef' fd vargs' vrets ->
      eval_vaddrs ta te e lhs dl ->
      locenv_setvaddrs te e dl vrets te' e' ->
      map typeof lhs = map snd (nd_rets (snd fd)) ->
      map typeof args = map snd (nd_args (snd fd)) ->
      lvalue_list_norepet (eval_lvalue ta te e) lhs ->
      assign_list_disjoint (eval_lvalue ta te e) lhs args ->
      te ! (callid cdef) = None ->
      eval_stmt ta te e te' e' (Scall oid lhs cdef args)
  | eval_Sfor_start: forall ta te te1 te2 e e1 e2 a1 a2 a3 s,
      eval_eqf ta te e te1 e1 a1 ->
      eval_stmt ta te1 e1 te2 e2 (Sfor None a2 a3 s) ->
      eval_stmt ta te e te2 e2 (Sfor (Some a1) a2 a3 s)
  | eval_Sfor_false: forall ta te e a2 a3 s,
      eval_sexp ta te e a2 Vfalse ->
      eval_stmt ta te e te e (Sfor None a2 a3 s)
  | eval_Sfor_loop: forall ta te te1 te2 te3 e e1 e2 e3 a2 a3 s,
      eval_sexp ta te e a2 Vtrue ->
      eval_stmt ta te e te1 e1 s ->
      eval_eqf ta te1 e1 te2 e2 a3 ->
      eval_stmt ta te2 e2 te3 e3 (Sfor None a2 a3 s) ->
      eval_stmt ta te e te3 e3 (Sfor None a2 a3 s)
  | eval_Sskip: forall ta te e ,
      eval_stmt ta te e te e Sskip
  | eval_Sseq: forall ta te te1 te2 e e1 e2 s1 s2,
      eval_stmt ta te e te1 e1 s1 ->
      eval_stmt ta te1 e1 te2 e2 s2 ->
      eval_stmt ta te e te2 e2 (Sseq s1 s2)
  | eval_Sif: forall ta te te1 e e1 a s1 s2 v b,
      eval_sexp ta te e a v ->
      bool_val v (typeof a) = Some b ->
      eval_stmt ta te e te1 e1 (if b then s1 else s2)  ->
      eval_stmt ta te e te1 e1 (Sif a s1 s2)
  | eval_Scase: forall ta te te1 e e1 lh ca pl i a,
      eval_sexp ta te e ca (Vint i) ->
      select_case i pl = Some a ->
      eval_stmt ta te e te1 e1 (Sassign lh a) ->
      eval_stmt ta te e te1 e1 (Scase lh ca pl).

Scheme eval_node_ind2 := Minimality for eval_node Sort Prop
  with eval_stmt_ind2 := Minimality for eval_stmt Sort Prop.
Combined Scheme eval_node_stmt_ind2 from eval_node_ind2, eval_stmt_ind2.

Lemma store_env_rets_match:
  forall ty e id o v e1 l,
  store_env ty e id o v e1 ->
  locenv_rets_match e l ->
  locenv_rets_match e1 l.
Proof.
  intros. inv H.
  red; intros.
  compare id id0; intros; subst.
  +rewrite PTree.gss in H. inv H.
   red in H0. eapply H0; eauto.
  +rewrite PTree.gso in H; auto. eauto.
Qed.

Lemma locenv_setvaddrs_locenv_rets_match:
  forall te e l vl te' e' rets,
  locenv_setvaddrs te e l vl te' e' ->
  locenv_rets_match e rets ->
  locenv_rets_match e' rets.
Proof.
  induction 1; simpl; intros; auto.
  apply IHlocenv_setvaddrs; auto.
  inv H; auto. eapply store_env_rets_match; eauto.
Qed.

Lemma eval_stmt_locenv_rets_match:
  forall ta te e te' e' s rets,
  eval_stmt ta te e te' e' s ->
  locenv_rets_match e rets ->
  locenv_rets_match e' rets.
Proof.
  induction 1; simpl; intros; auto.
  +inv H. inv H10; auto. eapply store_env_rets_match; eauto.
  +eapply locenv_setvaddrs_locenv_rets_match; eauto.
  +apply IHeval_stmt. inv H.
   inv H7; auto. eapply store_env_rets_match; eauto.
  +apply IHeval_stmt2. inv H1.
   inv H9; auto. eapply store_env_rets_match; eauto.
Qed.

End SEMANTICS.
