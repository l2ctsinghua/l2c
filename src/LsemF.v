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
Require Import Errors.
Require Import List.
Require Import Maps.
Require Import Lvalues.
Require Import Lint.
Require Import Lident.
Require Import Cop.
Require Import Lop.
Require Import Cltypes.
Require Import Ltypes.
Require Import Lustre.
Require Import LustreF.
Require Import Lenv.
Require Import Lenvmatch.
Require Import Lsem.

Section SEMANTICS.

Variable semkind: bool.
Variable p: program.
Variable gc: locenv.


Section EXPR.

Variable te se: locenv.


Definition case_env(k: vkind): locenv :=
  match k with
  | Gid => gc
  | Sid => se
  | _ => te
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
     gc ! id = Some (m, ty) ->
     eval_lvalue (Svar id ty) id Int.zero Gid
  | eval_Ssvar: forall id ty m,
     se ! id = Some (m, ty) ->
     eval_lvalue (Ssvar id ty) id Int.zero Sid
  | eval_Saryacc: forall a a1 ty l ofs i k aid z,
     eval_lvalue a l ofs k->
     eval_sexp a1 (Vint i) ->
     typeof a = Tarray aid ty z ->
     0 <= Int.signed i < Z.max 0 z ->
     Int.unsigned ofs + sizeof (typeof a) <= Int.max_signed ->
     eval_lvalue (Saryacc a a1 ty) l (Int.add ofs (array_ofs i ty)) k
  | eval_Sfield: forall a i ty l sid fld ofs k delta,
     eval_lvalue a l ofs k ->
     typeof a = Tstruct sid fld ->
     field_offset i fld = OK delta ->
     field_type i fld = OK ty ->
     Int.unsigned ofs + sizeof (typeof a) <= Int.max_signed ->
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
  induction 1; simpl; constructor.
  apply eval_sexp_has_type; auto.
  auto.
Qed.

Lemma eval_lvalue_vkind:
  forall a id ofs k,
  eval_lvalue a id ofs k ->
  (k = Gid \/ k = Sid) \/ k = Lid.
Proof.
  induction 1; intros; auto.
Qed.

Lemma eval_sexpm_determ:
  forall s v1,
  eval_sexp s v1 ->
  forall v2, eval_sexp s v2 ->
  v1 = v2
with eval_lvaluem_determ:
  forall a id1 ofs1 k1,
  eval_lvalue a id1 ofs1 k1->
  forall id2 ofs2 k2, eval_lvalue a id2 ofs2 k2 ->
  id1 = id2 /\ ofs1 = ofs2 /\ k1 = k2.
Proof.
  +induction 1; intros; auto.
   -inv H0; auto. destruct c; inv H1.
   -inv H2. apply IHeval_sexp in H6. congruence. inv H3.
   -inv H4. apply IHeval_sexp1 in H9. apply IHeval_sexp2 in H10.
    congruence. inv H5.
   -inv H1. apply IHeval_sexp in H4. congruence. inv H2.
   -inv H2; try (inv H; fail).
    apply eval_lvaluem_determ with  _ _ _ _ id0 ofs0 k0 in H; auto. destruct H as [? [? ?]]; subst.
    eapply load_env_determ; eauto.
  +induction 1; intros; auto.
   -inv H0; auto. congruence.
   -inv H1; auto. congruence.
   -inv H0; auto.
   -inv H4. apply IHeval_lvalue in H8; auto. destruct H8 as [? [? ?]].
    apply eval_sexpm_determ with  _ _ (Vint i0) in H0; auto. inv H0. auto.
   -inv H4. apply IHeval_lvalue in H8; auto. intuition.
    congruence.
Qed.

Lemma eval_lvalue_env_some:
  forall a id ofs k,
  eval_lvalue a id ofs k ->
  exists m t, (case_env k) ! id = Some (m, t).
Proof.
  induction 1; intros; eauto.
Qed.

Lemma eval_lvalue_some_alignof:
  forall a id ofs m ty,
  eval_lvalue a id ofs Sid ->
  se ! id = Some (m, ty) ->
  (alignof (typeof a) | alignof ty).
Proof.
  induction a; simpl; intros; inv H.
  +rewrite H5 in H0. inv H0. exists 1. omega.
  +apply Zdivide_trans with (alignof (typeof a1)); eauto.
   rewrite H6. simpl. exists 1. omega.
  +apply Zdivide_trans with (alignof (typeof a)); eauto.
   rewrite H5. simpl.
   eapply field_type_alignof; eauto.
Qed.

Lemma eval_lvalue_eval_offset:
  forall a id ofs k,
  eval_lvalue a id ofs k ->
  forall m ty,
  (case_env k) ! id = Some (m, ty) ->
  eval_offset ty a (Int.unsigned ofs).
Proof.
  induction 1; simpl; intros.
  +rewrite H0 in H. inv H. rewrite Int.unsigned_zero. constructor.
  +rewrite H1 in H0. inv H0. rewrite Int.unsigned_zero. constructor.
  +rewrite H in H0. inv H0. rewrite Int.unsigned_zero. constructor.
  +generalize Int.max_signed_unsigned (Int.unsigned_range i)
    (Int.unsigned_range ofs) (sizeof_pos ty). intros.
   unfold array_ofs. rewrite int_mul_repr.
   cut (0 <= Int.unsigned i < Z.max 0 z); intros.
   rewrite <-repr_add_int_r. rewrite Int.unsigned_repr.
   econstructor; eauto.
   -split.
    *apply Zle_trans with (Int.unsigned ofs + 0); try omega.
     apply Zplus_le_compat_l.
     apply Zmult_le_0_compat; try omega.
    *apply Zle_trans with (Int.unsigned ofs + sizeof (typeof a)); try omega.
     apply Zplus_le_compat_l.
     rewrite H1. simpl.
     apply Zmult_le_compat_l; omega.
   -split; try omega. apply signed_unsigned_range; auto.
  +generalize Int.max_signed_unsigned (Int.unsigned_range ofs) (sizeof_pos ty). intros.
   cut (0 <= Int.unsigned ofs + delta <= Int.max_unsigned). intros.
   rewrite <-repr_add_int_r. rewrite Int.unsigned_repr; auto.
   econstructor; eauto.
   eapply field_offset_in_range with (sid:=sid) in H1; eauto.
   split; try omega. rewrite H0 in *. omega.
Qed.

Lemma eval_lvalue_lid_disjoint_not_loopid:
  forall a id ofs,
  eval_lvalue a id ofs Lid ->
  lid_disjoint a ->
  id <> ACG_I.
Proof.
  induction 1; simpl; intros; auto.
  destruct a1; auto. destruct H4; auto.
Qed.

End EXPR.

Lemma eval_sexp_sexp:
  forall te s v,
  Lsem.eval_sexp gc te s v ->
  forall eh, eval_sexp te eh s v
with eval_lvalue_lvalue:
  forall te a id ofs k,
  Lsem.eval_lvalue gc te a id ofs k ->
  forall eh, eval_lvalue te eh a id ofs k.
Proof.
  +induction 1; simpl; intros; try (econstructor; eauto; fail).
   inv H0; econstructor; eauto.
  +induction 1; simpl; intros; econstructor; eauto.
Qed.

Lemma eval_sexps_sexps:
  forall te al vl,
  Lsem.eval_sexps gc te al vl ->
  forall eh, eval_sexps te eh al vl.
Proof.
  induction 1; simpl; intros; auto.
  constructor.
  constructor 2; eauto.
  eapply eval_sexp_sexp; eauto.
  eapply IHForall2; eauto.
Qed.

Lemma eval_sexp_mvl_inv:
  forall te e a m,
  eval_sexp te e a (Vmvl m) ->
  exists id ofs k, eval_lvalue te e a id ofs k
    /\ load_env (typeof a) (case_env te e k) id ofs (Vmvl m).
Proof.
  induction a; intros;
  try (inv H; eauto; fail).
  +destruct c; inv H; try inv H0.
   destruct b; inv H3.
  +inv H. apply sem_cast_not_mvl in H4. inv H4. inv H0.
  +inv H. apply sem_unary_operation_not_mvl in H5.
   inv H5. inv H0.
  +inv H. apply sem_binary_operation_not_mvl in H8.
   inv H8. inv H0.
Qed.

Lemma eval_lvalue_get_lids:
  forall te e a id ofs k,
  eval_lvalue te e a id ofs k ->
  get_lids a = id :: nil.
Proof.
  induction 1; simpl; auto.
Qed.

Lemma eval_var_svar:
  forall te eh id t v,
  Lsem.eval_sexp empty_locenv eh (Svar id t) v ->
  eval_sexp te eh (Ssvar id t) v.
Proof.
  intros. inv H. inv H0.
  apply eval_Rlvalue with id0 Int.zero Sid;auto.
  constructor 3 with m; auto. inv H1. simpl; auto.
  rewrite PTree.gempty in *. congruence.
Qed.

Lemma eval_field_field:
  forall eh id ty v te,
  Lsem.eval_sexp empty_locenv eh (Sfield (Svar id ty) FBYIDX type_int32s) v ->
  eval_sexp te eh (Sfield (Ssvar id ty) FBYIDX type_int32s) v.
Proof.
  intros. inv H. inv H0. inv H5.
  +apply eval_Rlvalue with id0 (Int.add Int.zero (Int.repr delta)) Sid; auto.
   eapply eval_Sfield; eauto. constructor 3 with m; auto.
   inv H1. simpl in *. auto.
  +rewrite PTree.gempty in *. congruence.
Qed.

Lemma eval_aryacc_aryacc:
  forall eh id ty t aty v te,
  Lsem.eval_sexp empty_locenv eh (Saryacc (Sfield (Svar id ty) FBYITEM aty) (Sfield (Svar id ty) FBYIDX type_int32s) t) v ->
  eval_sexp te eh (Saryacc (Sfield (Ssvar id ty) FBYITEM aty) (Sfield (Ssvar id ty) FBYIDX type_int32s) t) v.
Proof.
  intros. inv H. inv H0. inv H5. inv H4.
  +apply eval_Rlvalue with id0 (Int.add (Int.add Int.zero (Int.repr delta)) (array_ofs i t)) Sid; auto.
   -eapply eval_Saryacc; eauto. eapply eval_Sfield; eauto.
    constructor 3 with m; auto. eapply eval_field_field; eauto.
   -inv H1. simpl in *. auto.
  +rewrite PTree.gempty in *. congruence.
Qed.

Lemma assign_disjoint_trans_left:
  forall te e a1 a2,
  assign_disjoint (Lsem.eval_lvalue gc te) a1 a2 ->
  assign_disjoint (eval_lvalue te e) a1 a2.
Proof.
  intros. inv H.
  constructor 1 with chunk; auto.
  constructor 2; auto.
  inv H1.
  constructor 1 with id1 id2 o1 o2 k1 k2; auto;
  eapply eval_lvalue_lvalue; eauto.
Qed.

Lemma lids_disjoint_assign_disjoint:
  forall te e a v lh b o k,
  eval_sexp te e a v ->
  eval_lvalue te e lh b o k ->
  k = Lid \/ k = Sid ->
  list_disjoint (get_lids lh) (get_lids a) ->
  assign_disjoint (eval_lvalue te e) lh a.
Proof.
  intros. generalize H; intros.
  apply eval_sexp_has_type in H3.
  destruct has_type_access_mode with v (typeof a) as [[chunk ?] | ?]; auto.
  +constructor 1 with chunk; auto.
  +destruct has_type_access_mode_mvl with v (typeof a) as [mv [? ?]]; auto.
   subst.
   destruct eval_sexp_mvl_inv with te e a mv as [id1 [o1 [k1 [? ?]]]]; auto.
   constructor 2; auto.
   constructor 1 with b id1 o o1 k k1; auto.
   left. apply H2; erewrite eval_lvalue_get_lids; simpl; eauto.
Qed.

Lemma lvalue_list_norepet_trans_left:
  forall te lhs,
  lvalue_list_norepet (Lsem.eval_lvalue gc te) lhs ->
  forall eh, lvalue_list_norepet (eval_lvalue te eh) lhs.
Proof.
  induction 1; intros.
  constructor.
  constructor 2; auto.
  red; intros. apply H in H1. inv H1.
  constructor 1 with id1 id2 o1 o2 k1 k2; auto.
  eapply eval_lvalue_lvalue; eauto.
  eapply eval_lvalue_lvalue; eauto.
Qed.

Inductive locenv_setvarf(te e: locenv): sexp -> val -> locenv -> locenv -> Prop :=
  | locenv_setvarf_lid: forall te' var id ofs v,
      eval_lvalue te e var id ofs Lid ->
      store_env (typeof var) te id ofs v te' ->
      locenv_setvarf te e var v te' e
  | locenv_setvarf_sid: forall e' var id ofs v,
      eval_lvalue te e var id ofs Sid ->
      store_env (typeof var) e id ofs v e' ->
      locenv_setvarf te e var v te e'.

Inductive locenv_setvarfs: locenv -> locenv -> list sexp -> list val-> locenv -> locenv -> Prop :=
  | locenv_setvarfs_nil: forall te e,
      locenv_setvarfs te e nil nil te e
  | locenv_setvarfs_cons: forall te te1 te' e e1 e' lhs dl v vl,
      locenv_setvarf te e lhs v te1 e1 ->
      locenv_setvarfs te1 e1 dl vl te' e' ->
      locenv_setvarfs te e (lhs :: dl) (v :: vl) te' e'.

Inductive eval_eqf(te e: locenv): locenv ->  locenv -> eqf -> Prop :=
  | eval_Eqf: forall te' e' a1 a2 v v',
      eval_sexp te e a2 v ->
      typeof a1 = typeof a2 ->
      assign_disjoint (eval_lvalue te e) a1 a2 ->
      eval_cast v (typeof a1) v' ->
      locenv_setvarf te e a1 v' te' e' ->
      eval_eqf te e te' e' (a1,a2).

Inductive eval_node: env -> env -> ident*func -> list val -> list val  -> Prop :=
  | exec_node: forall te te1 te2 eh eh1 se se' vrs vas nid f,
      alloc_variables empty_locenv (allvarsof f) te ->
      locenv_setvars te f.(nd_args) vas te1 ->
      ids_norepet f ->
      eval_stmt nid te1 (mkenv eh se) te2 (mkenv eh1 se') f.(nd_stmt) ->
      locenv_getvars te2 f.(nd_rets) vrs ->
      (if semkind then svars_fld_match (svarsof f) (nd_fld f) else True) ->
      has_types vrs (map snd (nd_rets f)) ->
      eval_casts vrs (map snd f.(nd_rets)) vrs ->
      eval_node (mkenv eh se) (mkenv eh1 se') (nid,f) vas vrs

with eval_stmt: ident -> locenv -> env -> locenv -> env -> stmt  -> Prop :=
  | eval_Sassign: forall nid te te' eh eh' se lh a,
      eval_eqf te eh te' eh' (lh,a) ->
      eval_stmt nid te (mkenv eh se) te' (mkenv eh' se) (Sassign lh a)
  | eval_Scall: forall nid te te' eh eh' se ef ef' se' oid cdef nd fd args lhs vl vargs vargs' vrets i,
      load_loopid gc te oid (callnum cdef) i ->
      (if semkind && cakind cdef then LustreF.call_node (node_block p) nid cdef nd fd
       else Lustre.call_node (node_block p) nid cdef nd fd) ->
      call_env cdef i se se' ef ef' ->
      eval_sexps te eh args vargs ->
      eval_casts vargs (map typeof args) vargs' ->
      eval_node ef ef' fd vargs' vrets ->
      locenv_setvarfs te eh lhs vrets  te' eh' ->
      Forall (lid_disjoint) lhs ->
      map typeof lhs = map snd (nd_rets (snd fd)) ->
      map typeof args = map snd (nd_args (snd fd)) ->
      locenv_getmvls gc te lhs vl ->
      lvalue_list_norepet (eval_lvalue te eh) lhs ->
      assign_list_disjoint (eval_lvalue te eh) lhs args ->
      te ! (callid cdef) = None ->
      eval_stmt nid te (mkenv eh se) te' (mkenv eh' se') (Scall oid lhs cdef args)
  | eval_Sfor_start: forall nid te te1 te2 eh eh1 se e2 a1 a2 a3 s,
      eval_eqf te eh te1 eh1 a1 ->
      eval_stmt nid te1 (mkenv eh1 se) te2 e2 (Sfor None a2 a3 s) ->
      eval_stmt nid te (mkenv eh se) te2 e2 (Sfor (Some a1) a2 a3 s)
  | eval_Sfor_false: forall nid te eh se a2 a3 s,
      eval_sexp te eh a2 Vfalse ->
      eval_stmt nid te (mkenv eh se) te (mkenv eh se) (Sfor None a2 a3 s)
  | eval_Sfor_loop: forall nid te te1 te2 te3 eh eh1 eh2 se se1 e3 a2 a3 s,
      eval_sexp te eh a2 Vtrue ->
      eval_stmt nid te (mkenv eh se) te1 (mkenv eh1 se1) s ->
      eval_eqf te1 eh1 te2 eh2 a3 ->
      eval_stmt nid te2 (mkenv eh2 se1) te3 e3 (Sfor None a2 a3 s) ->
      eval_stmt nid te (mkenv eh se) te3 e3 (Sfor None a2 a3 s)
  | eval_Sskip: forall nid te e ,
      eval_stmt nid te e te e Sskip
  | eval_Sseq: forall nid te te1 te2 e e1 e2 s1 s2,
      eval_stmt nid te e te1 e1 s1 ->
      eval_stmt nid te1 e1 te2 e2 s2 ->
      eval_stmt nid te e te2 e2 (Sseq s1 s2)
  | eval_Sif: forall nid te te1 eh se e1 a s1 s2 v b,
      eval_sexp te eh a v ->
      bool_val v (typeof a) = Some b ->
      eval_stmt nid te (mkenv eh se) te1 e1 (if b then s1 else s2)  ->
      eval_stmt nid te (mkenv eh se) te1 e1 (Sif a s1 s2)
  | eval_Scase: forall nid te te1 eh se lh ca pl i a,
      eval_sexp te eh ca (Vint i) ->
      select_case i pl = Some a ->
      eval_stmt nid te (mkenv eh se) te1 (mkenv eh se) (Sassign lh a) ->
      eval_stmt nid te (mkenv eh se) te1 (mkenv eh se) (Scase lh ca pl).

Scheme eval_node_ind2 := Minimality for eval_node Sort Prop
  with eval_stmt_ind2 := Minimality for eval_stmt Sort Prop.
Combined Scheme eval_node_stmt_ind2 from eval_node_ind2, eval_stmt_ind2.

Inductive init_node: env -> ident*func -> Prop :=
  | init_node_: forall eh1 se nid f,
      ids_norepet f ->
      eval_init (length (nd_svars f)) empty_locenv (nd_svars f) eh1 ->
      (if semkind then svars_fld_match (svarsof f) (nd_fld f) else True) ->
      (forall ty, In ty (map snd (svarsof f)) -> 0 < sizeof ty) ->
      init_stmt nid (mkenv eh1 empty_subenv) (mkenv eh1 se) (instidof f.(nd_stmt)) ->
      init_node (mkenv eh1 se) (nid,f)

with init_stmt: ident -> env -> env -> list calldef ->  Prop :=
  | init_call_nil: forall nid e,
      init_stmt nid e e nil
  | init_call_node_cons: forall nid le se se1 se2 nd fd ef c l,
      (if semkind then LustreF.call_node (node_block p) nid c nd fd
       else Lustre.call_node (node_block p) nid c nd fd) ->
      init_node ef fd ->
      se1 = PTree.set (instid c) (list_repeat (nat_of_int (intof_opti (callnum c))) ef) se ->
      init_stmt nid (mkenv le se1) (mkenv le se2) l ->
      init_stmt nid (mkenv le se) (mkenv le se2) (c::l).

Scheme init_node_ind2 := Minimality for init_node Sort Prop
  with init_stmt_ind2 := Minimality for init_stmt Sort Prop.
Combined Scheme init_node_stmt_ind2 from init_node_ind2, init_stmt_ind2.

End SEMANTICS.
