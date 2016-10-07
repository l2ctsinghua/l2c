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
Require Import Errors.
Require Import AST.
Require Import Integers.
Require Import Maps.
Require Import Streams.
Require Import List.
Require Import ExtraList.
Require Import Lident.
Require Import Lustre.
Require Import LustreF.
Require Import Lint.
Require Import Cltypes.
Require Import Lvalues.
Require Import Ltypes.
Require Import Lsem.
Require Import Lenv.
Require Import Lenvmatch.
Require Import LsemF.
Require Import LsemE.
Require Import LsemD.
Require Import SimplEnv.

Section CORRECTNESS.

Variable prog1 prog2: program.

Hypothesis TRANSL:
  trans_program prog1 = OK prog2.

Hypothesis GID_NOREPET:
  list_norepet (globidsof prog1).

Hypothesis GID_RANGE:
  ids_plt ACG_EQU (map fst (const_block prog1)).

Hypothesis ID_RANGE:
  ids_range OUTSTRUCT (node_block prog1).

Section NODE_CORRECT.

Variable gc: locenv.

Hypothesis GENV_NONE:
  gc ! OUTSTRUCT = None.

Definition locals_struct_match(e: locenv)(fld: fieldlist)(o: int)(m: mvl) : Prop :=
  forall id mv ty, e!id = Some (mv,ty) ->
  exists delta, field_offset id fld = OK delta
    /\ field_type id fld = OK ty
    /\ loadbytes m  (Int.unsigned (Int.add o (Int.repr delta))) (sizeof ty) = Some mv.

Inductive env_struct_match(m: mvl)(o: int): ident*func -> env -> Prop :=
  | env_struct_match_: forall nd eh se,
      locals_struct_match eh (nd_fld (snd nd)) o m ->
      ptree_disjoint eh se ->
      subenv_struct_match m o (nd_fld (snd nd)) (instidof (nd_stmt (snd nd))) se ->
      env_struct_match m o nd (mkenv eh se)

with subenv_struct_match(m: mvl)(o: int): fieldlist -> list calldef -> subenv -> Prop :=
  | subenv_struct_match_nil: forall fld se,
     subenv_struct_match m o fld nil se
  | subenv_struct_match_cons: forall fld c l se el delta fd ty,
     se ! (instid c) = Some el ->
     field_offset (instid c) fld = OK delta ->
     field_type (instid c) fld = OK ty ->
     find_funct (node_block prog1) (callid c) = Some fd ->
     env_type_match m (Int.add o (Int.repr delta)) fd ty el ->
     subenv_struct_match m o fld l se ->
     subenv_struct_match m o fld (c::l) se

with env_type_match(m: mvl)(o: int): ident*func -> type -> list env -> Prop :=
  | env_str_match: forall fd eh,
      env_struct_match m o fd eh ->
      env_type_match m o fd (mknstruct (snd fd)) (eh::nil)
  | env_ary_match: forall fd el aid j,
      env_list_match m o fd (nat_of_int j) el ->
      env_type_match m o fd (Tarray aid (mknstruct (snd fd)) (Int.unsigned j)) el

with env_list_match(m: mvl)(o: int): ident*func -> nat -> list env -> Prop :=
  | env_list_match_nil: forall fd,
     env_list_match m o fd 0 nil
  | env_list_match_cons: forall fd j e el,
     env_struct_match m o fd e ->
     env_list_match m (Int.add o (Int.repr (sizeof_fld (nd_fld (snd fd))))) fd j el ->
     env_list_match m o fd (S j) (e::el).

Scheme env_struct_match_ind3 := Minimality for env_struct_match Sort Prop
  with subenv_struct_match_ind3 := Minimality for subenv_struct_match Sort Prop
  with env_type_match_ind3 := Minimality for env_type_match Sort Prop
  with env_list_match_ind3 := Minimality for env_list_match Sort Prop.
Combined Scheme env_struct_match_combined_ind3 from env_struct_match_ind3, subenv_struct_match_ind3,
  env_type_match_ind3, env_list_match_ind3.

Inductive env_match(nd: ident*func): env -> locenv ->  Prop :=
  | env_match_intro: forall eh1 eh2 se m,
      eh2 ! OUTSTRUCT = Some (m,mknstruct (snd nd)) ->
      Z_of_nat (length m) = sizeof_fld (nd_fld (snd nd)) ->
      env_struct_match m Int.zero nd (mkenv eh1 se) ->
      env_match nd (mkenv eh1 se) eh2.

Lemma env_struct_match_node_match:
forall m o,
  ( forall f1 e,
    env_struct_match m o f1 e ->
    forall f2, node_match prog1 f1 f2 ->
    env_struct_match m o f2 e
  ) /\
  ( forall fld l1 se,
    subenv_struct_match m o fld l1 se ->
    forall l2, calldefs_match prog1 l1 l2 ->
    subenv_struct_match m o fld l2 se
  ) /\
  ( forall f1 ty el,
    env_type_match m o f1 ty el ->
    forall f2, node_match prog1 f1 f2 ->
    env_type_match m o f2 ty el
  ) /\
  ( forall f1 j el,
    env_list_match m o f1 j el ->
    forall f2, node_match prog1 f1 f2 ->
    env_list_match m o f2 j el
  ).
Proof.
  intros until m.
  apply env_struct_match_combined_ind3; intros.
  +inv H3. constructor 1; auto.
   rewrite <-H5. auto.
   rewrite <-H5. auto.
  +inv H. constructor.
  +inv H7. constructor 2 with el delta f2 ty; auto; try congruence.
   apply H4; auto. congruence.
  +replace (mknstruct (snd fd)) with (mknstruct (snd f2)).
   constructor 1; auto.
   inv H1. unfold mknstruct. unfold func in *. congruence.
  +replace (mknstruct (snd fd)) with (mknstruct (snd f2)).
   constructor 2; auto.
   inv H1. unfold mknstruct. unfold func in *. congruence.
  +constructor 1.
  +constructor 2; auto.
   replace (nd_fld (snd f2)) with (nd_fld (snd fd)); auto.
   inv H3. auto.
Qed.

Lemma subenv_struct_match_in:
  forall m o fld l se,
  subenv_struct_match m o fld l se ->
  forall c el delta ty fd,
  In c l ->
  se ! (instid c) = Some el ->
  field_offset (instid c) fld = OK delta ->
  field_type (instid c) fld = OK ty ->
  find_funct (node_block prog1) (callid c) = Some fd ->
  env_type_match m (Int.add o (Int.repr delta)) fd ty el.
Proof.
  induction 1; simpl; intros; try tauto.
  destruct H5; subst; eauto.
  congruence.
Qed.

Lemma env_list_match_nth:
  forall m o fd j efs,
  env_list_match m o fd j efs ->
  forall i ef,
  nth_error efs i = value ef ->
  env_struct_match m (Int.add o (Int.repr (sizeof_fld (nd_fld (snd fd)) * (Z_of_nat i)))) fd ef.
Proof.
  induction 1; intros.
  +destruct i; simpl in *; inv H.
  +destruct i.
   -simpl in *. inv H1. rewrite Zmult_0_r, Int.add_zero. auto.
   -rewrite Nat2Z.inj_succ. rewrite Zmult_succ_r.
    rewrite Zplus_comm. rewrite repr_add_int.
    rewrite <-Int.add_assoc.
    apply IHenv_list_match; auto.
Qed.

Lemma locals_struct_match_eval_sexp:
  forall te e1,
  (
    forall a v,
    LsemF.eval_sexp gc te e1 a v ->
    forall f e2 m,
    e2 ! OUTSTRUCT = Some (m, mknstruct f) ->
    sizeof_fld (nd_fld f) = Z.of_nat (length m) ->
    locals_struct_match e1 (nd_fld f) Int.zero m ->
    sizeof_fld (nd_fld f) <= Int.max_signed ->
    LsemF.eval_sexp gc te e2 (trans_expr (makevar f) a) v
  )
/\
  (
    forall a id ofs k,
    LsemF.eval_lvalue gc te e1 a id ofs k ->
    forall f e2 m,
    e2 ! OUTSTRUCT = Some (m, mknstruct f) ->
    sizeof_fld (nd_fld f) = Z.of_nat (length m) ->
    locals_struct_match e1 (nd_fld f) Int.zero m ->
    sizeof_fld (nd_fld f) <= Int.max_signed ->
    match k with
    | Sid =>
      forall ofs',
      field_offset id (nd_fld f) = OK ofs' ->
      LsemF.eval_lvalue gc te e2 (trans_expr (makevar f) a) OUTSTRUCT (Int.add (Int.repr ofs') ofs) Sid
    | Gid | Lid =>
      LsemF.eval_lvalue gc te e2 (trans_expr (makevar f) a) id ofs k
    | Aid => False
    end
  ).
Proof.
  intros until e1.
  apply LsemF.eval_sexp_lvalue_ind; intros; simpl.
  +constructor 1; auto.
  +constructor 2 with v1; auto.
   apply H0 with m; auto.
   rewrite trans_expr_typeof; auto.
  +constructor 3 with v1 v2; eauto;
   repeat rewrite trans_expr_typeof; auto.
  +constructor 4 with v1; eauto.
   rewrite trans_expr_typeof; auto.
  +generalize H5; intros A. eapply H0 in A; eauto.
   destruct k; try tauto.
   -apply LsemF.eval_Rlvalue with id ofs Gid; auto;
    rewrite trans_expr_typeof; auto.
   -apply LsemF.eval_Rlvalue with id ofs Lid; auto;
    rewrite trans_expr_typeof; auto.
   -generalize H1. unfold load_env. simpl.
    intros. destruct H7 as [m1 [t1 [? [? ?]]]].
    destruct H5 with id m1 t1 as [delta [? [? ?]]]; auto.
    apply LsemF.eval_Rlvalue with OUTSTRUCT (Int.add (Int.repr delta) ofs) Sid; auto;
    rewrite trans_expr_typeof; auto. simpl.
    exists m, (mknstruct f); repeat split; auto.
    rewrite Int.add_zero_l in *.
    apply loadbytes_load_mvl_inv with t1 m1; eauto.
    erewrite field_offset_unsigned_repr; eauto.
    apply Zdivide_trans with (alignof t1).
    eapply eval_lvalue_some_alignof; eauto.
    eapply field_offset_aligned; eauto.
    generalize Int.max_signed_unsigned. omega.
  +constructor 1 with m; auto.
  +constructor 2 with m;auto.
  +rewrite Int.add_commut.
   destruct H2 with id m ty as [delta [? [? ?]]]; auto.
   apply LsemF.eval_Sfield with (nd_sid f) (nd_fld f); auto.
   constructor 3 with m0; auto.
  +generalize H6; intros A. eapply H0 in A; eauto.
   destruct k; try auto.
   -apply LsemF.eval_Saryacc with aid z; eauto;
    rewrite trans_expr_typeof; auto.
   -apply LsemF.eval_Saryacc with aid z; eauto;
    rewrite trans_expr_typeof; auto.
   -intros. rewrite <-Int.add_assoc.
    apply LsemF.eval_Saryacc with aid z; eauto.
    rewrite trans_expr_typeof; auto.
    apply A in H10. apply eval_lvalue_eval_offset with (m:=m) (ty:=mknstruct f) in H10; auto.
    apply eval_offset_pos in H10. apply Zle_trans with (sizeof (mknstruct f)); auto.
    omega.
  +generalize H5; intros A.
   eapply H0 in H5; eauto. destruct k; auto.
   -apply LsemF.eval_Sfield with sid fld; eauto;
    rewrite trans_expr_typeof; auto.
   -apply LsemF.eval_Sfield with sid fld; eauto;
    rewrite trans_expr_typeof; auto.
   -intros. rewrite <-Int.add_assoc.
    apply LsemF.eval_Sfield with sid fld; eauto.
    rewrite trans_expr_typeof; auto.
    apply H5 in H9. apply eval_lvalue_eval_offset with (m:=m) (ty:=mknstruct f) in H9; auto.
    apply eval_offset_pos in H9. apply Zle_trans with (sizeof (mknstruct f)); auto.
    omega.
Qed.

Lemma env_match_eval_sexp:
  forall te eh se a v nd e2,
  LsemF.eval_sexp gc te eh a v ->
  env_match nd (mkenv eh se) e2 ->
  sizeof_fld (nd_fld (snd nd)) <= Int.max_signed ->
  LsemF.eval_sexp gc te e2 (trans_expr (makevar (snd nd)) a) v.
Proof.
  intros. inv H0. inv H7.
  eapply locals_struct_match_eval_sexp; eauto.
Qed.

Lemma env_match_eval_sexps:
  forall te eh se al vl e2 nd,
  eval_sexps gc te eh al vl ->
  env_match nd (mkenv eh se) e2 ->
  sizeof_fld (nd_fld (snd nd)) <= Int.max_signed ->
  eval_sexps gc te e2 (trans_exprs (makevar (snd nd)) al) vl.
Proof.
  induction 1; intros.
  +constructor.
  +constructor 2; simpl; auto.
   eapply env_match_eval_sexp; eauto.
   eapply IHForall2; eauto.
Qed.

Lemma locenv_getmvl_match:
  forall te e1 lh v,
  locenv_getmvl gc te e1 lh v ->
  forall e2 m f,
  e2 ! OUTSTRUCT = Some (m, mknstruct f) ->
  sizeof_fld (nd_fld f) = Z.of_nat (length m) ->
  locals_struct_match e1 (nd_fld f) Int.zero m ->
  sizeof_fld (nd_fld f) <= Int.max_signed ->
  locenv_getmvl gc te e2 (trans_expr (makevar f) lh) v.
Proof.
  intros. inv H.
  eapply locals_struct_match_eval_sexp in H4; eauto.
  destruct H5; subst; simpl case_env in *.
  +constructor 1 with id ofs Lid m0 t; auto.
   rewrite trans_expr_typeof; auto.
  +apply H2 in H6. destruct H6 as [delta [? [? ?]]].
   constructor 1 with OUTSTRUCT (Int.add (Int.repr delta) ofs) Sid m (mknstruct f); auto.
   rewrite trans_expr_typeof; auto.
   rewrite Int.add_zero_l in *.
   eapply loadbytes_loadbytes_app; eauto.
Qed.

Lemma locenv_getmvls_match:
  forall te e1 lhs vl,
  locenv_getmvls gc te e1 lhs vl ->
  forall e2 m f,
  e2 ! OUTSTRUCT = Some (m, mknstruct f) ->
  sizeof_fld (nd_fld f) = Z.of_nat (length m) ->
  locals_struct_match e1 (nd_fld f) Int.zero m ->
  sizeof_fld (nd_fld f) <= Int.max_signed ->
  locenv_getmvls gc te e2 (trans_exprs (makevar f) lhs) vl.
Proof.
  induction 1; intros.
  +constructor.
  +simpl. constructor 2; auto.
   eapply locenv_getmvl_match; eauto.
   eapply IHForall2; eauto.
Qed.

Lemma locals_struct_match_set_loc:
  forall fld e1 b z ty m mv m' mv' t ofs v,
  locals_struct_match e1 fld Int.zero m ->
  field_offset b fld= OK z ->
  field_type b fld = OK ty ->
  loadbytes m' (Int.unsigned (Int.repr z)) (sizeof ty) = Some mv'->
  e1 ! b = Some (mv, ty) ->
  store_mvl t mv ofs v mv' ->
  store_mvl t m (Int.add (Int.repr z) ofs) v m' ->
  sizeof_fld fld <= Int.max_signed ->
  locals_struct_match (PTree.set b (mv',ty) e1) fld Int.zero m'.
Proof.
  intros. red; intros.
  generalize (sizeof_pos ty) (sizeof_pos t); intros A A1.
  compare b id; intros; subst.
  +rewrite PTree.gss in H7. inv H7.
   exists z. rewrite Int.add_zero_l.
   split;[| split]; auto.
  +rewrite PTree.gso in H7; auto.
   destruct H with id mv0 ty0 as [delta [? [? ?]]]; auto.
   exists delta. split;[| split]; auto.
   rewrite Int.add_zero_l in *.
   rewrite <-H10. generalize (sizeof_pos ty0); intros A2.
   apply loadbytes_store_mvl_other with t (Int.add (Int.repr z) ofs) v; auto.
   generalize H0; intros A3.
   eapply field_offset_in_range with (sid:=xH) in A3; eauto.
   eapply field_offset_no_overlap in H0; eauto.
   eapply field_offset_in_range with (sid:=xH) in H8; eauto.
   simpl in A3, H8. unfold sizeof_fld in *.
   destruct A3 as [A3 A4]. destruct H8 as [? ?].
   rewrite Int.add_unsigned in *.
   generalize Int.max_signed_unsigned. intros.
   assert (A5: (Int.unsigned (Int.repr z) = z)).
     rewrite Int.unsigned_repr;try omega.
   rewrite A5 in *.
   assert(A6: Int.unsigned ofs + sizeof t <= sizeof ty).
     apply store_mvl_range_perm in H4. red in H4.
     apply loadbytes_length in H2.
     rewrite <-H2 in H4.
     rewrite nat_of_Z_eq in H4; try omega.
   rewrite Int.unsigned_repr;try omega.
   generalize (Int.unsigned_range ofs); intros.
   repeat rewrite Int.unsigned_repr; try omega.
Qed.

Lemma mvl_mapping_incl:
  forall m m' o1 o2 ty1 ty2,
  mvl_mapping m m' o2 ty2 ->
  Int.unsigned o1 <= Int.unsigned o2 ->
  Int.unsigned o2 + sizeof ty2 <= Int.unsigned o1 + sizeof ty1 ->
  mvl_mapping m m' o1 ty1.
Proof.
  unfold mvl_mapping. intros.
  apply H; try omega.
Qed.

Lemma mvl_mapping_getN_right:
  forall m m' o ty n,
  mvl_mapping m m' o ty ->
  length m = length m' ->
  Int.unsigned o + sizeof ty + n <= Z.of_nat (length m) <= Int.max_signed ->
  getN (nat_of_Z n) (nat_of_Z (Int.unsigned o + sizeof ty)) m' =
  getN (nat_of_Z n) (nat_of_Z (Int.unsigned o + sizeof ty)) m.
Proof.
  unfold mvl_mapping. intros.
  generalize (Int.unsigned_range o) (sizeof_pos ty) Int.max_signed_unsigned; intros.
  destruct (zle n 0).
  +destruct n; simpl; auto.
   generalize (Pos2Z.is_pos p). omega.
  +apply loadbytes_getN_eq; auto; try omega.
   apply H; try omega.
Qed.

Lemma store_struct_item_mvl_mapping:
  forall m m' b fld z ty t ofs v,
  field_offset b fld= OK z ->
  field_type b fld = OK ty ->
  store_mvl t m (Int.add (Int.repr z) ofs) v m' ->
  sizeof_fld fld <= Int.max_signed ->
  Int.unsigned ofs + sizeof t <= sizeof ty ->
  mvl_mapping m m' (Int.repr z) ty.
Proof.
  unfold mvl_mapping. intros.
  generalize (sizeof_pos ty) (sizeof_pos t) (Int.unsigned_range ofs) Int.max_signed_unsigned; intros.
  eapply field_offset_in_range_simpl in H; eauto.
  unfold sizeof_fld in *.
  eapply loadbytes_store_mvl_other; eauto.
  destruct H4; [left | right]; unfold Int.add;
  rewrite Int.unsigned_repr; try omega;
  rewrite Int.unsigned_repr in *; try omega.
Qed.

Lemma getn_eq_locals_struct_match:
  forall eh fld o m,
  locals_struct_match eh fld o m ->
  forall m' o',
  Int.unsigned o + sizeof_fld fld <= Z_of_nat (length m) <= Int.max_signed ->
  Int.unsigned o' + sizeof_fld fld <= Z_of_nat (length m') <= Int.max_signed ->
  getN (nat_of_Z (sizeof_fld fld)) (nat_of_Z (Int.unsigned o')) m' = getN (nat_of_Z (sizeof_fld fld)) (nat_of_Z (Int.unsigned o)) m ->
  locals_struct_match eh fld o' m'.
Proof.
  unfold locals_struct_match. intros.
  destruct H with id mv ty as [delta [? [? ?]]]; auto.
  exists delta. repeat (split; auto).
  eapply field_offset_in_range_simpl in H4; eauto.
  unfold sizeof_fld in *.
  generalize (Int.unsigned_range o) (Int.unsigned_range o') Int.max_signed_unsigned; intros.
  unfold loadbytes in *. destruct (range_perm_dec _ _ _) in H6; try congruence.
  unfold range_perm in *. rewrite pred_dec_true.
  +rewrite <-H6.
   f_equal. repeat rewrite <-repr_add_int_r.
   repeat rewrite Int.unsigned_repr; try omega.
   eapply getN_offset_incl_eq; eauto; try omega.
  +rewrite <-repr_add_int_r.
   rewrite Int.unsigned_repr; try omega.
Qed.

Lemma getn_offset_eq_env_struct_match:
  forall m o,
  ( forall nd e,
    env_struct_match m o nd e ->
    forall m' o',
    Int.unsigned o + sizeof_fld (nd_fld (snd nd)) <= Z_of_nat (length m) <= Int.max_signed ->
    Int.unsigned o' + sizeof_fld (nd_fld (snd nd)) <= Z_of_nat (length m') <= Int.max_signed ->
    getN (nat_of_Z (sizeof_fld (nd_fld (snd nd)))) (nat_of_Z (Int.unsigned o')) m' = getN (nat_of_Z (sizeof_fld (nd_fld (snd nd)))) (nat_of_Z (Int.unsigned o)) m ->
    env_struct_match m' o' nd e
  ) /\
  ( forall fld l se,
    subenv_struct_match m o fld l se ->
    forall m' o',
    Int.unsigned o + sizeof_fld fld <= Z_of_nat (length m) <= Int.max_signed ->
    Int.unsigned o' + sizeof_fld fld <= Z_of_nat (length m') <= Int.max_signed ->
    getN (nat_of_Z (sizeof_fld fld)) (nat_of_Z (Int.unsigned o')) m' = getN (nat_of_Z (sizeof_fld fld)) (nat_of_Z (Int.unsigned o)) m ->
    subenv_struct_match m' o' fld l se
  ) /\
  ( forall nd ty el,
    env_type_match m o nd ty el ->
    forall m' o',
    Int.unsigned o + sizeof ty <= Z_of_nat (length m) <= Int.max_signed ->
    Int.unsigned o' + sizeof ty <= Z_of_nat (length m') <= Int.max_signed ->
    getN (nat_of_Z (sizeof ty)) (nat_of_Z (Int.unsigned o')) m' = getN (nat_of_Z (sizeof ty)) (nat_of_Z (Int.unsigned o)) m ->
    env_type_match m' o' nd ty el
  ) /\
  ( forall nd j el,
    env_list_match m o nd j el ->
    forall m' o',
    Int.unsigned o + sizeof_fld (nd_fld (snd nd))* Z_of_nat j <= Z_of_nat (length m) <= Int.max_signed ->
    Int.unsigned o' + sizeof_fld (nd_fld (snd nd))* Z_of_nat j <= Z_of_nat (length m') <= Int.max_signed ->
    getN (nat_of_Z (sizeof_fld (nd_fld (snd nd))*Z_of_nat j)) (nat_of_Z (Int.unsigned o')) m' = getN (nat_of_Z (sizeof_fld (nd_fld (snd nd))*Z_of_nat j)) (nat_of_Z (Int.unsigned o)) m ->
    env_list_match m' o' nd j el
  ).
Proof.
  intros until m.
  apply env_struct_match_combined_ind3; intros.
  +constructor; auto.
   eapply getn_eq_locals_struct_match; eauto.
  +constructor.
  +econstructor 2; eauto.
   generalize (sizeof_pos ty) (Int.unsigned_range o) (Int.unsigned_range o') Int.max_signed_unsigned; intros.
   eapply field_offset_in_range_simpl in H0; eauto.
   unfold sizeof_fld in *. apply H4; auto.
   -unfold Int.add. repeat rewrite Int.unsigned_repr; try omega.
   -unfold Int.add. repeat rewrite Int.unsigned_repr; try omega.
   -repeat rewrite <-repr_add_int_r.
    repeat rewrite Int.unsigned_repr; try omega.
    eapply getN_offset_incl_eq; eauto; unfold sizeof_fld; try omega.
  +constructor 1; auto.
  +constructor 2; auto.
   generalize (Int.unsigned_range o) (Int.unsigned_range o') (Int.unsigned_range j) (sizeof_fld_pos (nd_fld (snd fd))); intros.
   assert(A: 0 = Int.unsigned j \/ 0 < Int.unsigned j).
     omega.
   destruct A as [A | A].
   unfold nat_of_int in *. rewrite <-A in *. simpl in *. inv H. constructor.
   apply H0; unfold sizeof_fld in *; unfold nat_of_int; simpl in *;
   rewrite nat_of_Z_eq; try omega.
   -rewrite Z.max_r with 0 (Int.unsigned j) in H1; omega.
   -rewrite Z.max_r with 0 (Int.unsigned j) in H2; omega.
   -rewrite (Z.max_r 0 (Int.unsigned j)) in H3; try omega.
    auto.
  +constructor.
  +generalize (Int.unsigned_range o) (Int.unsigned_range o') (sizeof_fld_pos (nd_fld (snd fd))) Int.max_signed_unsigned; intros.
   cut (sizeof_fld (nd_fld (snd fd)) <= sizeof_fld (nd_fld (snd fd)) * Z.of_nat (S j)). intros.
   cut (0 <= sizeof_fld (nd_fld (snd fd)) * Z.of_nat j). intros.
   constructor 2; auto.
   -apply H0; try omega.
    rewrite <-(Z.add_0_r (Int.unsigned o')).
    rewrite <-(Z.add_0_r (Int.unsigned o)).
    eapply getN_offset_incl_eq; eauto; try omega.
   -assert(A: (0 = j \/ 0 < j)%nat).
     omega.
    destruct A as [A | A].
    subst. inv H1. constructor.
    rewrite Nat2Z.inj_succ in *. rewrite Z.mul_succ_r in *.
    apply H2; auto.
    *split; try omega. rewrite <-repr_add_int_r.
     rewrite Int.unsigned_repr; try omega.
    *split; try omega. rewrite <-repr_add_int_r.
     rewrite Int.unsigned_repr; try omega.
    *repeat rewrite <-repr_add_int_r.
     repeat rewrite Int.unsigned_repr; try omega.
     eapply getN_offset_incl_eq; eauto; try omega.
   -rewrite Nat2Z.inj_succ, Z.mul_succ_r in H10. omega.
   -rewrite Nat2Z.inj_succ. apply Zle_trans with (sizeof_fld (nd_fld (snd fd))*1); try omega.
    apply Zmult_le_compat_l; try omega.
Qed.

Lemma mvl_mapping_local_struct_match:
  forall e fld m isid ty delta m' ofs t,
  locals_struct_match e fld Int.zero m ->
  field_type isid fld = OK ty ->
  field_offset isid fld = OK delta ->
  mvl_mapping m m' ofs t ->
  delta <= Int.unsigned ofs ->
  Int.unsigned ofs + sizeof (t) <= delta + sizeof ty ->
  e ! isid = None ->
  sizeof_fld fld <= Int.max_signed ->
  locals_struct_match e fld Int.zero m'.
Proof.
  unfold locals_struct_match; intros.
  destruct H with id mv ty0 as [delta' [? [? ?]]]; auto.
  exists delta'. repeat (split; auto).
  generalize (sizeof_pos ty0); intros.
  rewrite <- H10. apply H2; try omega.
  assert(isid <> id). congruence.
  eapply field_offset_no_overlap in H1; eauto.
  rewrite Int.add_zero_l.
  eapply field_offset_in_range_simpl in H8; eauto.
  generalize Int.max_signed_unsigned. intros.
  rewrite Int.unsigned_repr; try omega.
Qed.

Lemma mvl_mapping_subenv_struct_match:
  forall l m fld se,
  subenv_struct_match m Int.zero fld l se ->
  forall m' b ty z,
  mvl_mapping m m' (Int.repr z) ty ->
  field_offset b fld= OK z ->
  field_type b fld = OK ty ->
  se ! b = None ->
  sizeof_fld fld <= Z_of_nat (length m) <= Int.max_signed ->
  length m = length m' ->
  subenv_struct_match m' Int.zero fld l se.
Proof.
  induction l; intros.
  +constructor.
  +inv H. econstructor 2; eauto.
   assert(instid a <>  b).
     congruence.
  generalize H1.
  eapply field_offset_no_overlap in H1; eauto.
  intros A. eapply field_offset_in_range_simpl in A;eauto.
  eapply field_offset_in_range_simpl in H9;eauto.
  unfold sizeof_fld in *.
  generalize (sizeof_pos ty) (sizeof_pos ty0) Int.max_signed_unsigned; intros.
  assert(A1: z = Int.unsigned (Int.repr z)).
    rewrite Int.unsigned_repr; try omega.
  assert(A2: delta = Int.unsigned (Int.repr delta)).
    rewrite Int.unsigned_repr; try omega.
  rewrite A1, A2 in H1.
  apply H0 in H1; try omega. rewrite Int.add_zero_l in *.
  eapply getn_offset_eq_env_struct_match; eauto; try omega.
  rewrite <-A2 in *. destruct (zlt 0 (sizeof ty0)).
  -unfold loadbytes in H1.
   rewrite pred_dec_true, pred_dec_true in H1.
   congruence.
   destruct (range_perm_dec _ _ _); try congruence.
   unfold range_perm in *. omega.
  -rewrite nat_of_Z_neg; try omega.
   unfold getN, getn. simpl. auto.
Qed.

Lemma mvl_mapping_env_type_match_other:
  forall m m' id1 id2 delta1 delta2 ty1 ty2 fd el fld,
  env_type_match m (Int.repr delta1) fd ty1 el ->
  field_offset id2 fld = OK delta2 ->
  field_type id2 fld = OK ty2 ->
  field_offset id1 fld = OK delta1 ->
  field_type id1 fld = OK ty1 ->
  mvl_mapping m m' (Int.repr delta2) ty2 ->
  sizeof_fld fld <= Int.max_signed ->
  length m = length m' ->
  Z_of_nat (length m) = sizeof_fld fld ->
  id1 <> id2 ->
  env_type_match m' (Int.repr delta1) fd ty1 el.
Proof.
  intros.
  generalize H0 (sizeof_pos ty1) (sizeof_pos ty2) Int.max_signed_unsigned.
  eapply field_offset_no_overlap in H0; eauto.
  intros A ? ? ?. eapply field_offset_in_range_simpl in A; eauto.
  eapply field_offset_in_range_simpl in H2; eauto.
  unfold mvl_mapping in H4. rewrite Int.unsigned_repr in H4; try omega.
  assert(A1: delta1 = Int.unsigned (Int.repr delta1)).
    rewrite Int.unsigned_repr; try omega.
  rewrite A1 in H0. apply H4 in H0; try omega.
  eapply getn_offset_eq_env_struct_match; eauto.
  +rewrite <-A1. omega.
  +rewrite <-A1. omega.
  +destruct (zlt 0 (sizeof ty1)).
   -unfold loadbytes in *.
    rewrite pred_dec_true, pred_dec_true in H0; auto.
    congruence.
    unfold range_perm. rewrite <-A1. omega.
    unfold range_perm. rewrite <-A1, <-H6. omega.
   -rewrite nat_of_Z_neg; try omega.
   unfold getN, getn. simpl. auto.
Qed.

Lemma mvl_mapping_subenv_struct_match_other:
  forall m o fld l se,
  subenv_struct_match m o fld l se ->
  forall c el' delta ty fd m',
  o = Int.zero ->
   ~ In (instid c) (map instid l) ->
  field_offset (instid c) fld = OK delta ->
  field_type (instid c) fld = OK ty ->
  find_funct (node_block prog1) (callid c) = Some fd ->
  env_type_match m' (Int.repr delta) fd ty el' ->
  mvl_mapping m m' (Int.repr delta) ty ->
  sizeof_fld fld <= Int.max_signed ->
  length m = length m' ->
  Z_of_nat (length m) = sizeof_fld fld ->
  subenv_struct_match m' o fld l (PTree.set (instid c) el' se).
Proof.
  induction 1; simpl; intros.
  +constructor.
  +constructor 2 with el delta fd ty; auto.
   -rewrite PTree.gso; auto.
   -subst. rewrite Int.add_zero_l in *.
    eapply mvl_mapping_env_type_match_other; eauto.
   -eapply IHsubenv_struct_match; eauto.
Qed.

Lemma mvl_mapping_subenv_struct_match_set:
  forall m o fld l se,
  subenv_struct_match m o fld l se ->
  forall c el' se' delta ty fd m',
  In c l ->
  o = Int.zero ->
  list_norepet (map instid l) ->
  se' = PTree.set (instid c) el' se ->
  field_offset (instid c) fld = OK delta ->
  field_type (instid c) fld = OK ty ->
  find_funct (node_block prog1) (callid c) = Some fd ->
  env_type_match m' (Int.add o (Int.repr delta)) fd ty el' ->
  mvl_mapping m m' (Int.add o (Int.repr delta)) ty ->
  sizeof_fld fld  <= Int.max_signed ->
  length m = length m' ->
  Z_of_nat (length m) = sizeof_fld fld ->
  subenv_struct_match m' o fld l se'.
Proof.
  induction 1; simpl; intros.
  +inv H.
  +inv H7. destruct H5; subst.
   -constructor 2 with el' delta fd ty; auto.
    *rewrite PTree.gss; auto.
    *congruence.
    *rewrite Int.add_zero_l in *.
     eapply mvl_mapping_subenv_struct_match_other with (delta:=delta0) (ty:=ty0) (fd:=fd0); eauto.
   -assert(A: instid c <> instid c0).
      apply in_map with (B:=ident) (f:=instid) in H5. congruence.
    constructor 2 with el delta fd ty; auto.
    *rewrite PTree.gso; auto.
    *rewrite Int.add_zero_l in *.
     eapply mvl_mapping_env_type_match_other; eauto.
    *eapply IHsubenv_struct_match; eauto.
Qed.

Lemma env_match_setvarf_exists:
  forall te eh lh v te' eh',
  locenv_setvarf gc te eh lh v te' eh' ->
  forall se nd e2, env_match nd (mkenv eh se) e2 ->
  sizeof_fld (nd_fld (snd nd)) <= Int.max_signed ->
  te ! OUTSTRUCT = None ->
  env_fld_match prog1 nd (mkenv eh se) ->
  exists e2',locenv_setvarf gc te e2 (trans_expr (makevar (snd nd)) lh) v te' e2'
    /\ env_match nd (mkenv eh' se) e2'
    /\ te' ! OUTSTRUCT = None
    /\ env_fld_match prog1 nd (mkenv eh' se).
Proof.
  induction 1; intros.
  +exists e2. split; [| split; [| split]]; auto.
   constructor 1 with id ofs; auto.
   -inv H1. inv H10.
    eapply locals_struct_match_eval_sexp in H; eauto.
   -rewrite trans_expr_typeof; auto.
   -inv H0. rewrite PTree.gso; congruence.
  +inv H1. inv H10. generalize H0. intros A.
   inv A. destruct H6 with id m0 t as [delta [? [? ?]]]; auto.
   generalize H Int.max_signed_unsigned; intros B B1.
   eapply locals_struct_match_eval_sexp in H; eauto.
   rewrite Int.add_zero_l in *.
   destruct loadbytes_store_mvl_exists
     with (typeof var) m0 ofs v m' m (Int.repr delta) (sizeof t)
     as [m1' [? ?]]; auto.
     erewrite field_offset_unsigned_repr; eauto.
     apply Zdivide_trans with (alignof t).
     eapply eval_lvalue_some_alignof; eauto.
     eapply field_offset_aligned; eauto.
     unfold func in *. omega.
   exists (PTree.set OUTSTRUCT (m1',mknstruct (snd nd)) e2). split; [| split; [| split]]; auto.
   -constructor 2 with OUTSTRUCT (Int.add (Int.repr delta) ofs); auto.
    constructor 1 with m; auto.
    rewrite trans_expr_typeof; auto.
   -constructor 1 with m1'; auto.
    *rewrite PTree.gss; auto.
    *erewrite <- store_mvl_length; eauto.
    *constructor 1; auto.
     eapply locals_struct_match_set_loc; eauto.
     eapply ptree_disjoint_set_left; eauto.
     apply mvl_mapping_subenv_struct_match with m id t delta; eauto.
     eapply store_struct_item_mvl_mapping; eauto.
     generalize (sizeof_pos t) H9; intros ? A1.
     apply loadbytes_length in H14.
     apply store_mvl_length in A1. rewrite A1 in *.
     apply Zle_trans with (Z_of_nat (length m')).
     apply store_mvl_range_perm in H9.
     red in H9. omega.
     rewrite <-H14. rewrite nat_of_Z_eq; try omega.
     rewrite H8. unfold sizeof_fld, func in *. omega.
     eapply store_mvl_length; eauto.
   -inv H4. constructor 1; auto. rewrite PTree.gempty in *. congruence.
Qed.

Lemma locenv_setvarfs_id_none:
  forall te eh l vl te' eh',
  LsemF.locenv_setvarfs gc te eh l vl te' eh' ->
  te ! OUTSTRUCT = None ->
  te' ! OUTSTRUCT = None.
Proof.
  induction 1;intros; auto.
  apply IHlocenv_setvarfs; auto.
  inv H; auto. inv H3. rewrite PTree.gso; congruence.
Qed.

Lemma env_match_setvarfs_env_fld_match:
  forall te eh l vl te' eh',
  locenv_setvarfs gc te eh l vl te' eh' ->
  forall se nd,
  env_fld_match prog1 nd (mkenv eh se) ->
  env_fld_match prog1 nd (mkenv eh' se).
Proof.
  induction 1; intros; auto.
  +apply IHlocenv_setvarfs.
   inv H; auto.
   inv H3. inv H1. constructor 1; auto.
   rewrite PTree.gempty in *. congruence.
Qed.

Lemma env_match_setvarfs_func_exists:
  forall te eh l vl te' eh',
  locenv_setvarfs gc te eh l vl te' eh' ->
  forall se nd e2, env_match nd (mkenv eh se) e2 ->
  sizeof_fld (nd_fld (snd nd)) <= Int.max_signed ->
  te ! OUTSTRUCT = None ->
  env_fld_match prog1 nd (mkenv eh se) ->
  exists e2',locenv_setvarfs gc te e2 (trans_exprs (makevar (snd nd)) l) vl te' e2'
    /\ env_match nd (mkenv eh' se) e2'
    /\ te' ! OUTSTRUCT = None
    /\ env_fld_match prog1 nd (mkenv eh' se).
Proof.
  induction 1; intros.
  +exists e2. split; auto. constructor.
  +eapply env_match_setvarf_exists in H; eauto.
   destruct H as [e21 [? [? [? ?]]]].
   destruct IHlocenv_setvarfs with se nd e21 as [e2' [? [? [? ?]]]]; auto.
   exists e2'; split; auto.
   constructor 2 with te1 e21; auto.
Qed.

Lemma eval_lvalue_loadbytes_range_perm:
  forall te e a id o m fld mv z ty,
  eval_lvalue gc te e a id o Sid ->
  e ! id = Some (mv, ty) ->
  loadbytes m (Int.unsigned (Int.repr z)) (sizeof ty) = Some mv ->
  field_type id fld = OK ty ->
  field_offset id fld = OK z ->
  sizeof_fld fld <= Int.max_signed ->
  Int.unsigned (Int.add (Int.repr z) o) = z + Int.unsigned o
    /\ Int.unsigned o + sizeof (typeof a) <= sizeof ty.
Proof.
  intros. generalize Int.max_signed_unsigned. intros.
  eapply eval_lvalue_eval_offset in H; eauto.
  eapply eval_offset_pos in H; eauto.
  rewrite Int.add_commut. rewrite <-repr_add_int_r.
  erewrite field_offset_unsigned_repr in H1; eauto; try omega.
  apply loadbytes_range_perm in H1. red in H1.
  generalize (sizeof_pos (typeof a)); intros.
  rewrite Int.unsigned_repr; try omega.
Qed.

Lemma lvalue_disjoint_locenv_match:
  forall te eh a1 a2 nd se e2,
  lvalue_disjoint (eval_lvalue gc te eh) a1 a2 ->
  env_match nd (mkenv eh se) e2 ->
  sizeof_fld (nd_fld (snd nd)) <= Int.max_signed ->
  te ! OUTSTRUCT = None ->
  lvalue_disjoint (eval_lvalue gc te e2) (trans_expr (makevar (snd nd)) a1) (trans_expr (makevar (snd nd)) a2).
Proof.
  intros. inv H.
  generalize H3 H4 H3 H4 H0. intros A A1 A2 A3 A4. inv H0. inv H11.
  apply eval_lvalue_env_some in H3. destruct H3 as [mv1 [t1 A5]].
  apply eval_lvalue_env_some in H4. destruct H4 as [mv2 [t2 A6]].
  destruct H5; subst; simpl in A5.
  +eapply locals_struct_match_eval_sexp in A; eauto; try congruence.
   -compare k2 Sid; intros; subst; simpl in A6.
    *destruct H7 with id2 mv2 t2 as [z [B [B1 B2]]]; auto.
     eapply locals_struct_match_eval_sexp in A1; eauto.
     econstructor 1; try repeat rewrite trans_expr_typeof; eauto.
     left. congruence.
    *eapply locals_struct_match_eval_sexp in A1; eauto; try congruence.
     destruct k2; try congruence; try tauto;
     econstructor 1; try repeat rewrite trans_expr_typeof; eauto.
  +destruct H7 with id1 mv1 t1 as [z1 [B [B1 B2]]]; auto.
   eapply locals_struct_match_eval_sexp in A; eauto.
   -compare k2 Sid; intros; subst; simpl in A6.
    *destruct H7 with id2 mv2 t2 as [z [B3 [B4 B5]]]; auto.
     eapply locals_struct_match_eval_sexp in A1; eauto.
     econstructor 1; try repeat rewrite trans_expr_typeof; eauto.
     right. rewrite Int.add_zero_l in *.
     eapply eval_lvalue_loadbytes_range_perm in A2; eauto.
     eapply eval_lvalue_loadbytes_range_perm in A3; eauto.
     destruct A2 as [A2 ?].  destruct A3 as [A3 ?]. rewrite A2, A3.
     compare id1 id2; intros; subst.
     destruct H6; try congruence.
     rewrite B in B3. inv B3. destruct H3; omega.

     eapply field_offset_no_overlap in B; eauto.
     generalize (Int.unsigned_range o1) (Int.unsigned_range o2); intros.
     destruct B; [right | left]; try omega.
    *eapply locals_struct_match_eval_sexp in A1; eauto; try congruence.
     destruct k2; try congruence; try tauto;
     econstructor 1; try repeat rewrite trans_expr_typeof; eauto.
     left. simpl in A6. congruence.
     left. simpl in A6. congruence.
Qed.

Lemma assign_disjoint_env_match:
  forall te eh se e2 a1 a2 nd,
  assign_disjoint (eval_lvalue gc te eh) a1 a2 ->
  env_match nd (mkenv eh se) e2 ->
  sizeof_fld (nd_fld (snd nd)) <= Int.max_signed ->
  te ! OUTSTRUCT = None ->
  assign_disjoint (eval_lvalue gc te e2) (trans_expr (makevar (snd nd)) a1) (trans_expr (makevar (snd nd)) a2).
Proof.
  intros. inv H.
  +constructor 1 with chunk; auto.
   rewrite trans_expr_typeof; auto.
  +constructor 2; auto.
   rewrite trans_expr_typeof; auto.
   eapply lvalue_disjoint_locenv_match; eauto.
Qed.

Lemma assign_list_disjoint_env_match_out:
  forall te eh args vargs,
  eval_sexps gc te eh args vargs ->
  forall se e2 nd lh ofs m isid delta ty,
  env_match nd (mkenv eh se) e2 ->
  sizeof_fld (nd_fld (snd nd)) <= Int.max_signed ->
  te ! OUTSTRUCT = None ->
  eh ! isid = None ->
  eval_lvalue gc te e2 lh OUTSTRUCT ofs Sid ->
  e2 ! OUTSTRUCT = Some (m, mknstruct (snd nd)) ->
  Z.of_nat (length m) = sizeof_fld (nd_fld (snd nd)) ->
  field_offset isid (nd_fld (snd nd)) = OK delta ->
  field_type isid (nd_fld (snd nd)) = OK ty ->
  delta <= Int.unsigned ofs /\ Int.unsigned ofs + sizeof (typeof lh) <= delta + sizeof ty ->
  assign_list_disjoint (eval_lvalue gc te e2) (lh::nil) (trans_exprs (makevar (snd nd)) args).
Proof.
  unfold trans_exprs. intros. red; simpl; intros.
  destruct H10; try tauto. subst a1.
  apply in_map_iff in H11. destruct H11 as [? [? ?]].
  subst. apply in_split in H11. destruct H11 as [? [? ?]]. subst.
  apply Forall2_app_inv_l in H. destruct H as [? [? [? [? ?]]]]. subst.
  inv H10.
  destruct has_type_access_mode with y (typeof x) as [[chunk ?] | ?]; auto.
  eapply eval_sexp_has_type; eauto.
  +constructor 1 with chunk; auto.
   rewrite trans_expr_typeof; auto.
  +generalize H13; intros A. apply eval_sexp_has_type in A.
   destruct has_type_access_mode_mvl with y (typeof x) as [mv [A1 A2]]; auto.
   subst. destruct eval_sexp_mvl_inv with gc te eh x mv as [id [o [k [A4 A5]]]]; auto.
   generalize A4 H0; intros A6 A7. inv H0. inv H18.
   destruct A5 as [m1 [t1 [A10 [A11 A12]]]].
   apply eval_lvalue_vkind in A6. destruct A6 as [[ | ] | ]; subst; simpl in A10.
   -eapply locals_struct_match_eval_sexp in A4; eauto; try congruence.
    econstructor 2. rewrite trans_expr_typeof; eauto.
    econstructor; eauto. left. congruence.
   -destruct H12 with id m1 t1 as [z [B [B1 B2]]]; auto.
    eapply locals_struct_match_eval_sexp in A4; eauto.
    econstructor 2. rewrite trans_expr_typeof; eauto.
    econstructor; eauto. right. rewrite trans_expr_typeof.
    rewrite Int.add_zero_l in *.
    generalize Int.max_signed_unsigned. intros.
    erewrite field_offset_unsigned_repr in B2; eauto.
    assert (B3: isid <> id). congruence.
    generalize H7; intros B4. eapply field_offset_no_overlap with (id1:=id) in B4; eauto.
    apply load_mvl_range_perm in A12. red in A12. rewrite <-A11 in *.
    rewrite Int.add_commut. rewrite  <-repr_add_int_r.
    apply loadbytes_range_perm in B2. red in B2.
    unfold sizeof_fld in *. rewrite Int.unsigned_repr; try omega.
    unfold func in *. omega.
   -eapply locals_struct_match_eval_sexp in A4; eauto; try congruence.
    econstructor 2. rewrite trans_expr_typeof; eauto.
    econstructor; eauto. left. congruence.
Qed.

Lemma lvalue_list_norepet_env_match:
  forall te eh l,
  lvalue_list_norepet (eval_lvalue gc te eh) l ->
  forall  se e2 nd,
  env_match nd (mkenv eh se) e2 ->
  sizeof_fld (nd_fld (snd nd)) <= Int.max_signed ->
  te ! OUTSTRUCT = None ->
  lvalue_list_norepet (eval_lvalue gc te e2) (trans_exprs (makevar (snd nd)) l).
Proof.
  induction 1; intros; simpl.
  +constructor.
  +constructor 2; eauto.
   unfold trans_exprs. red; intros.
   apply in_map_iff in H4. destruct H4 as [? [? ?]]. subst.
   apply in_split in H5. destruct H5 as [? [? ?]]. subst.
   eapply lvalue_disjoint_locenv_match; eauto.
   apply H. apply in_or_app; simpl; auto.
Qed.

Lemma assign_list_disjoint_env_match:
  forall te eh l args,
  assign_list_disjoint (eval_lvalue gc te eh) l args ->
  forall  se e2 nd,
  env_match nd (mkenv eh se) e2 ->
  sizeof_fld (nd_fld (snd nd)) <= Int.max_signed ->
  te ! OUTSTRUCT = None ->
  assign_list_disjoint (eval_lvalue gc te e2) (trans_exprs (makevar (snd nd)) l) (trans_exprs (makevar (snd nd)) args).
Proof.
  unfold trans_exprs. intros. red; intros.
  apply in_map_iff in H3. destruct H3 as [? [? ?]].
  apply in_map_iff in H4. destruct H4 as [? [? ?]].
  subst. apply in_split in H5. destruct H5 as [? [? ?]]. subst.
  apply in_split in H6. destruct H6 as [? [? ?]]. subst.
  eapply assign_disjoint_env_match; eauto.
  apply H; apply in_or_app; simpl; auto.
Qed.

Lemma env_match_eval_eqf:
  forall te eh te' eh' a1,
  eval_eqf gc te eh te' eh' a1 ->
  forall se nd e2, env_match nd (mkenv eh se) e2 ->
  sizeof_fld (nd_fld (snd nd)) <= Int.max_signed ->
  te ! OUTSTRUCT = None ->
  env_fld_match prog1 nd (mkenv eh se) ->
  exists e2', eval_eqf gc te e2 te' e2' (trans_eqf (makevar (snd nd)) a1)
    /\ env_match nd (mkenv eh' se) e2'
    /\ te' ! OUTSTRUCT = None
    /\ env_fld_match prog1 nd (mkenv eh' se).
Proof.
  induction 1; intros. generalize H3; intros A.
  eapply env_match_setvarf_exists in H3; eauto.
  destruct H3 as [e2' [? [? ?]]].
  exists e2'. split; auto.
  constructor 1 with v v'; simpl; auto.
  eapply env_match_eval_sexp; eauto.
  repeat rewrite trans_expr_typeof; auto.
  eapply assign_disjoint_env_match; eauto.
  rewrite trans_expr_typeof; auto.
Qed.

Lemma locals_struct_match_getvars_rec:
  forall e1 l vrs,
  Lsem.locenv_getvars e1 l vrs ->
  forall e2 sid fld m,
  svars_fld_match l fld ->
  locals_struct_match e1 fld Int.zero m ->
  e2 ! OUTSTRUCT = Some (m,Tstruct sid fld) ->
  Z_of_nat (length m) = sizeof_fld fld ->
  0 < sizeof_fld fld <= Int.max_signed ->
  has_types vrs (map snd l) ->
  locenv_getvar e2 (OUTSTRUCT,Tstruct sid fld) (Vmvl m)
    /\ vrets_fld_match fld l vrs m Int.zero.
Proof.
  induction 1; intros.
  +split.
   -constructor 1 with m; auto.
    repeat (split; simpl; auto).
    constructor 2; auto.
    generalize Int.max_signed_unsigned.
    unfold sizeof_fld in *. simpl; intros.
    rewrite <- H2. apply loadbytes_full; auto.
    omega.
    rewrite Int.unsigned_zero. exists 0. omega.
   -constructor; auto. constructor.
  +inv H6.
   destruct IHForall2 with e2 sid fld m; auto.
    red; intros. apply H1; simpl; auto.
   split; auto.
   constructor 1; auto.
   destruct x. constructor 2; auto.
   *assert(field_type i fld = OK t).
     apply H1; simpl;auto.
    destruct field_type_offset_exists with fld i t as [delta ?]; auto.
    exists delta. repeat (split; auto).

    destruct H as [m1 [? [? ?]]]. simpl in H, H13.
    destruct H2 with i m1 t as [ofs [? [? ?]]]; auto.
    rewrite H14 in H9. inv H9.
    rewrite H15 in H8. inv H8.
    rewrite Int.add_zero_l in *.
    eapply loadbytes_load_mvl_inv in H16; eauto.
    rewrite Int.add_zero in H16; auto.
    erewrite field_offset_unsigned_repr; eauto.
    eapply field_offset_aligned; eauto.
    generalize Int.max_signed_unsigned. omega.
   *inv H7; auto.
Qed.

Lemma locals_struct_match_getvars:
  forall e1 vrs f e2 m,
  Lsem.locenv_getvars e1 (nd_rets f) vrs ->
  locals_struct_match e1 (nd_fld f) Int.zero m ->
  e2 ! OUTSTRUCT = Some (m, mknstruct f) ->
  Z_of_nat (length m) = sizeof_fld (nd_fld f) ->
  0 < sizeof_fld (nd_fld f) <= Int.max_signed ->
  svars_fld_match (svarsof f) (nd_fld f) ->
  has_types vrs (map snd (nd_rets f)) ->
  locenv_getvars e2 (nd_rets (trans_body f)) (Vmvl m :: nil)
    /\ vrets_fld_match (nd_fld f) (nd_rets f) vrs m Int.zero.
Proof.
  unfold trans_body. intros. simpl.
  eapply locals_struct_match_getvars_rec in H; eauto.
  +destruct H. split; auto.
   constructor 2; eauto.
  +intros. red. intros. apply H4; unfold svarsof.
   apply in_or_app; auto.
Qed.

Lemma env_struct_match_getN:
  forall m o nd e,
  env_struct_match m o nd e ->
  Int.unsigned o + sizeof_fld (nd_fld (snd nd)) <= Z.of_nat (length m) <= Int.max_signed ->
  env_struct_match (getN (nat_of_Z (sizeof_fld (nd_fld (snd nd)))) (nat_of_Z (Int.unsigned o)) m) Int.zero nd e.
Proof.
  intros.
  generalize (Int.unsigned_range o) (sizeof_fld_pos (nd_fld (snd nd))); intros.
  eapply getn_offset_eq_env_struct_match; eauto.
  +rewrite Int.unsigned_zero, <-getN_length, nat_of_Z_eq; try omega.
  +rewrite Int.unsigned_zero. simpl.
   rewrite <-getN_app; auto. f_equal. omega.
Qed.

Lemma eval_lvalue_instance_exists:
  forall te e2 m nid nd fd cdef oid i ehf sef ef' se se' eh lh,
  call_node (node_block prog1) nid cdef nd fd ->
  e2 ! OUTSTRUCT = Some (m, mknstruct (snd nd)) ->
  Z.of_nat (length m) = sizeof_fld (nd_fld (snd nd)) ->
  load_loopid gc te oid (callnum cdef) i ->
  sizeof_fld (nd_fld (snd nd)) <= Int.max_signed ->
  callnd_env cdef i se se' {| le := ehf; sube := sef |} ef' ->
  env_struct_match m Int.zero nd (mkenv eh se) ->
  In cdef (instidof (nd_stmt (snd nd))) ->
  lh = (make_inst oid (makevar (snd nd)) (instid cdef)
       (mkcstruct cdef) (intof_opti (callnum cdef))) ->
  0 < Int.unsigned (intof_opti (callnum cdef)) <= Int.max_signed ->
  0 < sizeof (mknstruct (snd fd)) ->
  exists mv ofs, eval_lvalue gc te e2 lh OUTSTRUCT ofs Sid
    /\ load_env (typeof lh) e2 OUTSTRUCT ofs (Vmvl mv)
    /\ env_match fd (mkenv ehf sef) (PTree.set OUTSTRUCT (mv,mknstruct (snd fd)) empty_locenv)
    /\ (alignof (mknstruct (snd fd)) | Int.unsigned ofs).
Proof.
  intros.
  destruct H as [? [? [? [? [? [? [? [? ?]]]]]]]].
  generalize H11 H11; intros A A1.
  eapply field_type_offset_exists in A; eauto.
  destruct A as [ofs A].
  eapply field_offset_in_range_simpl in A1; eauto.
  generalize (sizeof_pos (match callnum cdef with
       | Some j =>
           Tarray xH (mknstruct (snd fd)) (Int.unsigned j)
       | None => mknstruct (snd fd)
       end)). intros A2.
  unfold make_inst, makevar.
  generalize Int.max_signed_unsigned. intros C.
  assert(C1: 0 <= Int.signed i < Int.unsigned( intof_opti (callnum cdef))).
    eapply callnd_env_range_i in H4; eauto.
    rewrite Int.signed_eq_unsigned; try omega.
  inv H4. inv H5.
  assert(A3: mknstruct (snd fd) = mkcstruct cdef).
     unfold mknstruct,mkcstruct. congruence.
  generalize (sizeof_pos (mknstruct (snd fd))); intros A4.
  inv H2.
  +rewrite <-H4, <-A3 in *; simpl in C.
   remember (mknstruct (snd fd)) as t1.
   simpl in A1, H3,H8,C1. rewrite Z.max_r in A1; try omega.
   generalize (Int.unsigned_range i); intros A5.
   assert(A6: 0 <= sizeof t1 * Int.unsigned i < sizeof t1 * Int.unsigned j).
    split. apply Zmult_le_0_compat; try omega.
    apply Zmult_lt_compat_l; try omega.
    apply signed_unsigned_range in C1; omega.
   assert(A7: range_perm m (Int.unsigned (Int.add (Int.repr ofs) (array_ofs i t1)))
              (Int.unsigned (Int.add (Int.repr ofs) (array_ofs i t1)) + sizeof t1)).
     generalize (Int.unsigned_range (Int.add (Int.repr ofs) (array_ofs i t1))). intros.
     red. split; try omega. split; try omega.
     unfold array_ofs. rewrite int_mul_repr. rewrite <-repr_add_int.
     rewrite Int.unsigned_repr; try omega.
     apply Zle_trans with (ofs + sizeof t1 * (Int.unsigned j)); try omega.
     rewrite Zplus_assoc_reverse. apply Zplus_le_compat_l.
     apply zmul_add_le_mul_lt; try omega. apply signed_unsigned_range; auto.
   econstructor. econstructor. repeat split.
   -econstructor; eauto. econstructor; simpl; eauto.
    constructor 3 with m; eauto. unfold mknstruct; eauto.
    rewrite Int.unsigned_zero. simpl. auto.
    eapply eval_sexp_sexp; eauto.
    simpl; eauto. rewrite Z.max_r; auto. unfold Int.unsigned in *. omega.
    rewrite Int.add_zero_l. simpl. change Int.intval with Int.unsigned.
    rewrite Z.max_r; try omega. rewrite Int.unsigned_repr; try omega.
   -simpl typeof. exists m, (mknstruct (snd nd)).
    rewrite Heqt1 in *. repeat (split; auto).
    constructor 2; auto; rewrite Int.add_zero_l.
    unfold loadbytes. rewrite pred_dec_true; eauto.
    apply Zdivides_plus_int; auto.
    apply alignof_1248.
    erewrite field_offset_unsigned_repr; eauto.
    eapply field_offset_aligned in H11; eauto.
    omega.
    eapply alignof_array_ofs; eauto.
   -econstructor 1; eauto.
    *rewrite PTree.gss, Heqt1; eauto.
    *rewrite <-Heqt1. red in A7. erewrite <-getN_length; try omega; auto.
     rewrite nat_of_Z_eq; try omega.
     rewrite Heqt1. unfold mknstruct, sizeof_fld; simpl; auto.
    *eapply subenv_struct_match_in in H24; eauto.
     rewrite Int.add_zero_l in H24. simpl in H20, H21.
     assert(B: env_list_match m (Int.repr ofs) fd (nat_of_int j) efs).
       clear -H24. inv H24. apply int_unsigned_inj in H3. congruence.
     eapply env_list_match_nth with (i:=nat_of_int i) in B; eauto.
     unfold nat_of_int in B. generalize (Int.unsigned_range i); intros.
     rewrite nat_of_Z_eq in B; try omega.
     unfold array_ofs. rewrite int_mul_repr.
     apply env_struct_match_getN; auto.
     change (sizeof_fld (nd_fld (snd fd))) with (sizeof (mknstruct (snd fd))).
     rewrite <-Heqt1. red in A7. unfold array_ofs in A7.
     rewrite int_mul_repr in A7. omega.
   -rewrite Int.add_zero_l. apply Zdivides_plus_int.
    apply alignof_1248.
    erewrite field_offset_unsigned_repr; eauto.
    eapply field_offset_aligned in H11; eauto.
    omega.
    eapply alignof_array_ofs; eauto.
  +rewrite <-H7 in *. simpl in C.
   assert(A7: range_perm m (Int.unsigned (Int.add Int.zero (Int.repr ofs)))
              (Int.unsigned (Int.add Int.zero (Int.repr ofs)) + sizeof (mknstruct (snd fd)))).
     rewrite Int.add_commut. rewrite Int.add_zero.
     generalize (Int.unsigned_range (Int.repr ofs)); intros.
     red. split; try omega.
     rewrite Int.unsigned_repr; try omega.
   econstructor. econstructor. repeat split.
   -econstructor; eauto. econstructor; simpl; eauto.
    simpl. unfold mknstruct. eauto.
    congruence. rewrite Int.unsigned_zero. simpl. auto.
   -simpl typeof. exists m, (mknstruct (snd nd)).
    repeat (split; auto).
    constructor 2; auto. subst; auto. unfold loadbytes.
    rewrite pred_dec_true; eauto. congruence.
    rewrite Int.add_zero_l.
    erewrite field_offset_unsigned_repr; eauto.
    eapply field_offset_aligned; eauto. congruence.
    omega.
   -econstructor 1; eauto.
    *rewrite PTree.gss; auto.
    *rewrite <-A3. red in A7.
     erewrite <-getN_length; try omega; auto.
     rewrite nat_of_Z_eq; try omega.
     unfold mknstruct, sizeof_fld; auto.
    *eapply subenv_struct_match_in in H24; eauto.
     rewrite Int.add_zero_l in H24.
     unfold nat_of_int in H19. rewrite Int.unsigned_zero in *.
     simpl intof_opti in *. rewrite Int.unsigned_one in *.
     simpl in H19.
     assert(B: efs = mkenv ehf sef :: nil).
       destruct efs; inv H19. simpl length in *. rewrite Nat2Z.inj_succ in H21.
       destruct efs; simpl length in *; auto. rewrite Nat2Z.inj_succ in H21. omega.
     subst efs.
     assert(B: env_struct_match m (Int.repr ofs) fd (mkenv ehf sef)).
       inv H24; auto.
     rewrite <-A3.
     apply env_struct_match_getN; rewrite Int.add_zero_l in *; auto.
     red in A7. unfold mknstruct, sizeof_fld in *.
     simpl in *. omega.
   -rewrite Int.add_zero_l.
    erewrite field_offset_unsigned_repr; eauto.
    eapply field_offset_aligned; eauto.
    omega.
Qed.

Lemma trans_nodes_find_fuct:
  forall id fd l l',
  mmap trans_node l = OK l' ->
  find_funct l id = Some fd ->
  nd_kind (snd fd) = false ->
  find_funct l' id = Some fd.
Proof.
  induction l; simpl; intros; monadInv H; simpl in *; auto.
  unfold trans_node in EQ.
  destruct (nd_kind (snd a)) eqn:?;
  destruct (nd_fld (snd a)) eqn:?;
  try  destruct (_ && _);
  inv EQ; simpl; destruct (identeq _ _); auto.
  inv H0. congruence.
Qed.

Lemma find_funct_func_eq:
  forall id fd,
  find_funct (node_block prog1) id = Some fd ->
  nd_kind (snd fd) = false ->
  find_funct (node_block prog2) id = Some fd.
Proof.
  intros. monadInv TRANSL.
  simpl in *. eapply trans_nodes_find_fuct; eauto.
Qed.

Lemma trans_call_func:
  forall cdef fd,
  Lustre.call_func (node_block prog1) cdef fd ->
  cakind cdef = false ->
  Lustre.call_func (node_block prog2) cdef fd.
Proof.
  unfold Lustre.call_func. intros.
  destruct H as [? [? [? ?]]].
  intuition.
  eapply find_funct_func_eq; eauto.
Qed.

Lemma trans_call_node:
  forall nid cdef nd fd,
  call_node (node_block prog1) nid cdef nd fd ->
  cakind cdef = true ->
  nd_fld (snd fd) <> Fnil ->
  exists fd', trans_node fd = OK fd'
    /\ call_func (node_block prog2) (trans_calldef cdef) fd'.
Proof.
  unfold call_node, call_func. intros.
  destruct H as [? [? [? [? [? [? [? ?]]]]]]].
  monadInv TRANSL. simpl in *.
  eapply find_funcs_monad_exits in H6; eauto. destruct H6 as [fd' [? ?]].
  exists fd'. unfold trans_node in *.
  unfold func in *. rewrite <-H7, H0 in *.
  destruct (nd_fld (snd fd)) eqn:?; try congruence.
  destruct (_ && _); inv H6.
  intuition.
  +simpl. unfold mkcstruct, mknstruct; congruence.
  +unfold trans_node. intros. unfold func in *.
   destruct (nd_kind (snd x0)); try congruence.
   destruct (nd_fld (snd x0)); try congruence.
   destruct (_ && _); inv H9. auto.
Qed.

Lemma trans_nodes_find_fuct_fnil:
  forall id fd l l',
  mmap trans_node l = OK l' ->
  find_funct l id = Some fd ->
  nd_kind (snd fd) = true ->
  nd_fld (snd fd) = Fnil ->
  find_funct l' id = Some fd.
Proof.
  induction l; simpl; intros; monadInv H; simpl in *; auto.
  unfold trans_node in EQ.
  destruct (nd_kind (snd a)) eqn:?;
  destruct (nd_fld (snd a)) eqn:?;
  try  destruct (_ && _);
  inv EQ; simpl; destruct (identeq _ _); auto.
  inv H0. congruence.
Qed.

Lemma find_funct_node_eq:
  forall id fd,
  find_funct (node_block prog1) id = Some fd ->
  nd_kind (snd fd) = true ->
  nd_fld (snd fd) = Fnil ->
  find_funct (node_block prog2) id = Some fd.
Proof.
  intros. monadInv TRANSL.
  simpl in *. eapply trans_nodes_find_fuct_fnil; eauto.
Qed.

Lemma trans_call_node_fnil:
  forall nid cdef nd fd,
  call_node (node_block prog1) nid cdef nd fd ->
  cakind cdef = true ->
  nd_fld (snd fd) = Fnil ->
  call_func (node_block prog2) cdef fd.
Proof.
  unfold call_node, call_func. intros.
  destruct H as [? [? [? [? [? [? [? ?]]]]]]].
  apply find_funct_node_eq in H6; auto.
  unfold func in *. congruence.
Qed.

Lemma eval_lvalue_make_inst_determ_set_right:
  forall te e2 lh ofs oid f cdef (fd: ident*func) m',
  eval_lvalue gc te e2 lh OUTSTRUCT ofs Sid ->
  option_match oid (callnum cdef)->
  lh = make_inst oid (makevar f) (instid cdef)
       (mknstruct (snd fd)) (intof_opti (callnum cdef)) ->
  eval_lvalue gc te (PTree.set OUTSTRUCT (m', mknstruct f) e2) lh OUTSTRUCT ofs Sid.
Proof.
  unfold makevar. intros.
  inv H0; inv H; remember OUTSTRUCT; simpl in *.
  +eapply eval_Saryacc; eauto.
   -inv H3. apply eval_Sfield with sid fld; auto.
    inv H2. constructor 3 with m'; auto.
    rewrite PTree.gss; auto.
   -inv H5. inv H.
    apply eval_Rlvalue with ACG_I Int.zero Lid; auto.
    constructor 1 with m; auto.
    apply eval_Rlvalue with ACG_I Int.zero Gid; auto.
    constructor 2 with m; auto.
  +inv H3. apply eval_Sfield with sid fld; auto.
   constructor 3 with m'; auto.
   rewrite PTree.gss; auto.
Qed.

Lemma eval_lvalue_make_inst_determ_set_left:
  forall te e2 lh ofs oid nd cdef (fd: ident*func) m id,
  eval_lvalue gc te e2 lh OUTSTRUCT ofs Sid ->
  option_match oid (callnum cdef) ->
  lh = make_inst oid (makevar nd) (instid cdef) (mknstruct (snd fd)) (intof_opti (callnum cdef)) ->
  id <> ACG_I ->
  eval_lvalue gc (PTree.set id m te) e2 lh OUTSTRUCT ofs Sid.
Proof.
  unfold makevar. intros.
  inv H0; inv H; remember OUTSTRUCT; simpl in *.
  +eapply eval_Saryacc; eauto.
   -inv H4. apply eval_Sfield with sid fld; auto.
    inv H3. constructor 3 with m0; auto.
   -inv H6. inv H.
    *apply eval_Rlvalue with ACG_I Int.zero Lid; auto.
     constructor 1 with m0; auto. rewrite PTree.gso; auto.
     simpl in *. destruct H0 as [m1 [t1 [? [? ?]]]].
     exists m1,t1; split; auto. rewrite PTree.gso; auto.
    *apply eval_Rlvalue with ACG_I Int.zero Gid; auto.
     constructor 2 with m0; auto. rewrite PTree.gso; auto.
  +inv H4. apply eval_Sfield with sid fld; auto.
    constructor 3 with m0; auto.
Qed.

Lemma getN_eq_vrets_match:
  forall fld m ofs l vl,
  vrets_match fld m ofs l vl ->
  forall m', length m = length m' ->
  Int.unsigned ofs + sizeof_fld fld <= Z_of_nat (length m) <= Int.max_signed ->
  getN (nat_of_Z (sizeof_fld fld)) (nat_of_Z (Int.unsigned ofs)) m' = getN (nat_of_Z (sizeof_fld fld)) (nat_of_Z (Int.unsigned ofs)) m ->
  vrets_match fld m' ofs l vl.
Proof.
  induction 1; simpl; intros.
  +constructor.
  +constructor 2; auto.
   -destruct H as [delta [? [? [? ?]]]].
    exists delta; repeat (split; auto).
    eapply field_offset_in_range_simpl in H; eauto.
    generalize (Int.unsigned_range ofs) (sizeof_fld_pos fld) (sizeof_pos (snd x)); intros.
    unfold sizeof_fld in *. generalize Int.max_signed_unsigned. intros.
    assert(A: Int.unsigned (Int.add ofs (Int.repr delta)) = Int.unsigned ofs + delta).
     rewrite <-repr_add_int_r. rewrite Int.unsigned_repr; try omega.
    apply getN_incl_eq with (o2:=Int.unsigned (Int.add ofs (Int.repr delta))) (n2:=sizeof (snd x))  in H3; try omega.
    eapply getN_incl_eq_load_mvl; eauto; try omega.
   -apply IHForall2; auto.
Qed.

Lemma mvl_mapping_vrets_match:
  forall fld' m ofs l vl isid fld ty delta id ty' delta' m',
  vrets_match fld' m ofs l vl ->
  field_type isid fld = OK ty ->
  field_offset isid fld = OK delta ->
  field_type id fld = OK ty' ->
  field_offset id fld = OK delta' ->
  id <> isid ->
  mvl_mapping m m' (Int.repr delta') ty' ->
  delta <= Int.unsigned ofs ->
  Int.unsigned ofs + sizeof_fld fld' <= delta + sizeof ty ->
  sizeof_fld fld <= Z.of_nat (length m) <= Int.max_signed ->
  length m = length m' ->
  vrets_match fld' m' ofs l vl.
Proof.
  intros. generalize (sizeof_pos ty) (sizeof_pos ty') Int.max_signed_unsigned; intros.
  generalize H1 H3; intros A A1.
  eapply field_offset_in_range_simpl in A; eauto.
  eapply field_offset_in_range_simpl in A1; eauto.
  eapply field_offset_no_overlap with (id1:=isid) in H3; eauto.
  assert(A2: delta = Int.unsigned (Int.repr delta)).
    rewrite Int.unsigned_repr; try omega.
  unfold mvl_mapping in H5. rewrite Int.unsigned_repr in H5; try omega.
  rewrite A2 in H3. apply H5 in H3; try omega.
  eapply getN_eq_vrets_match; eauto; try omega.
  destruct (zlt 0 (sizeof_fld fld')).
  +unfold loadbytes in H3. rewrite pred_dec_true, pred_dec_true in H3.
   inversion H3. eapply getN_incl_eq; eauto; try omega.
   rewrite <-A2 in H14; auto.
   unfold range_perm. omega.
   unfold range_perm. omega.
  +rewrite nat_of_Z_neg; try omega.
   unfold getN, getn; simpl; auto.
Qed.

Lemma eval_lvalue_diff_assign_disjoint:
  forall te e2 a id1 ofs1 lh id2 ofs2 v,
  eval_lvalue gc te e2 lh id1 ofs1 Lid ->
  eval_lvalue gc te e2 a id2 ofs2 Sid ->
  te ! id2 = None ->
  has_type v (typeof a) ->
  assign_disjoint (eval_lvalue gc te e2) lh a.
Proof.
  intros.
  destruct has_type_access_mode with v (typeof a) as [[chunk ?] | ?]; auto.
  +constructor 1 with chunk; auto.
  +econstructor 2; eauto. econstructor; eauto.
   left. apply eval_lvalue_env_some in H.
   destruct H as [? [? ?]]. simpl in *. congruence.
Qed.

Lemma trans_lhs_rets_correct:
  forall te eh lhs vrets te' eh' (fd: ident*func) nid nd lh se' cdef oid delta ty efs,
  LsemF.locenv_setvarfs gc te eh lhs vrets te' eh' ->
  forall rets ofs m e2,
  Forall (lid_disjoint) lhs ->
  vrets_match (nd_fld (snd fd)) m ofs rets vrets ->
  eval_lvalue gc te e2 lh OUTSTRUCT ofs Sid ->
  e2 ! OUTSTRUCT = Some (m, mknstruct (snd nd))  ->
  Z.of_nat (length m) = sizeof_fld (nd_fld (snd nd)) ->
  locals_struct_match eh (nd_fld (snd nd)) Int.zero m ->
  ptree_disjoint eh se' ->
  sizeof_fld (nd_fld (snd nd)) <= Int.max_signed ->
  subenv_struct_match m Int.zero (nd_fld (snd nd)) (instidof (nd_stmt (snd nd))) se' ->
  typeof lh = mknstruct (snd fd) ->
  option_match oid (callnum cdef) ->
  lh = make_inst oid (makevar (snd nd)) (instid cdef) (mknstruct (snd fd)) (intof_opti (callnum cdef)) ->
  field_type (instid cdef) (nd_fld (snd nd)) = OK ty ->
  field_offset (instid cdef) (nd_fld (snd nd)) = OK delta ->
  delta <= Int.unsigned ofs /\ Int.unsigned ofs + sizeof (typeof lh) <= delta + sizeof ty ->
  se' ! (instid cdef) = Some efs ->
  map typeof lhs = map snd rets ->
  te ! OUTSTRUCT = None ->
  eval_casts vrets (map typeof lhs) vrets ->
  exists e2', eval_stmt prog2 gc nid te e2 te' e2'
                 (trans_lhs_rets (combine (trans_exprs (makevar (snd nd)) lhs) rets) lh)
              /\ env_match nd (mkenv eh' se') e2'.
Proof.
  unfold trans_lhs_rets.
  induction 1; intros.
  +simpl fold_right.
   exists e2. split; auto.
   -constructor.
   -constructor 1 with m; auto.
    constructor 1; auto.
  +inv H1. inv H2. inv H17. inv H19. remember OUTSTRUCT as b.
   unfold trans_lhs_ret in *. destruct x as [id t].
   generalize Int.max_signed_unsigned. intros C.
   destruct H21 as [z [? [? [? ?]]]]. simpl in *. inv H.
   -remember (make_inst _ _ _ _ _) as lh.
    assert(A: eval_stmt prog2 gc nid te e2 te1 e2 (Sassign (trans_expr (makevar (snd nd)) lhs) (Sfield lh id (typeof lhs)))).
      eapply locals_struct_match_eval_sexp in H21; eauto; try congruence.
      cut (eval_lvalue gc te e2 (Sfield lh id (typeof lhs)) OUTSTRUCT (Int.add ofs (Int.repr z)) Sid); intros.
      apply eval_Sassign; auto. constructor 1 with v v; auto.
      apply eval_Rlvalue with OUTSTRUCT (Int.add ofs (Int.repr z)) Sid; auto.
      exists m, (mknstruct (snd nd)).
      repeat (split; auto).
      rewrite trans_expr_typeof; auto.
      eapply eval_lvalue_diff_assign_disjoint; eauto.
      rewrite trans_expr_typeof. auto.
      constructor 1 with id0 ofs0; auto.
      rewrite trans_expr_typeof; auto.
      apply eval_Sfield with (nd_sid (snd fd)) (nd_fld (snd fd)); auto.
      eapply field_offset_in_range_simpl in H14; eauto. omega.
    destruct IHlocenv_setvarfs with l ofs m e2 as [e2' [? ?]]; auto.
      eapply eval_lvalue_lid_disjoint_not_loopid in H21; eauto.
      inv H26. eapply eval_lvalue_make_inst_determ_set_left; eauto.
      inv H26. rewrite PTree.gso; congruence.
    exists e2'. split; auto.
    apply eval_Sseq with te1 e2; auto.
   -inv H26. destruct H6 with id0 m0 t as [delta' [? [? ?]]]; auto.
    rewrite Int.add_zero_l in *. generalize H26 (sizeof_pos t) (sizeof_pos ty); intros A A7 A8.
    eapply field_offset_in_range_simpl in A; eauto.
    assert(A4: exists m1',  store_mvl (typeof lhs) m (Int.add (Int.repr delta') ofs0) v m1'
               /\ loadbytes m1' (Int.unsigned (Int.repr delta')) (sizeof t) = Some m').
      eapply loadbytes_store_mvl_exists; eauto.
      erewrite field_offset_unsigned_repr; eauto.
      apply Zdivides_trans with (alignof t).
      eapply eval_lvalue_some_alignof; eauto.
      eapply field_offset_aligned; eauto.
      omega.
    destruct A4 as [m1' [A4 A5]].
    generalize A4; intros A6. eapply store_mvl_length in A6; eauto.
    remember (make_inst _ _ _ _ _) as lh.
    assert (A10: eval_lvalue gc te1 e2 (Sfield lh id (typeof lhs)) OUTSTRUCT (Int.add ofs (Int.repr z)) Sid).
      apply eval_Sfield with (nd_sid (snd fd)) (nd_fld (snd fd)); auto.
      eapply field_offset_in_range_simpl in H14; eauto. omega.
    assert (A11: eval_sexp gc te1 e2 (Sfield lh id (typeof lhs)) v).
      apply eval_Rlvalue with OUTSTRUCT (Int.add ofs (Int.repr z)) Sid; auto.
      exists m, (mknstruct (snd nd)); split; auto.
    generalize H21; intros A12.
    eapply locals_struct_match_eval_sexp in A12; eauto.
    generalize H1; intros A13. eapply field_offset_in_range_simpl in A13; eauto.
    assert(A14: sizeof_fld (nd_fld (snd fd)) = sizeof (typeof lh)).
      rewrite H10. unfold mknstruct. auto.
    assert(A15: Int.unsigned (Int.add ofs (Int.repr z)) = Int.unsigned ofs + z).
      rewrite <-repr_add_int_r. generalize (sizeof_pos (typeof lhs)); intros.
      eapply field_offset_in_range_simpl in H13; eauto.
      rewrite Int.unsigned_repr; try omega.
    assert (A17: id0 <> instid cdef).
      red; intros. subst. apply H7 in H. congruence.
    assert(A18: assign_disjoint (eval_lvalue gc te1 e2) (trans_expr (makevar (snd nd)) lhs) (Sfield lh id (typeof lhs))).
      destruct has_type_access_mode with v (typeof lhs) as [[chunk ?] | ?]; auto.
      constructor 1 with chunk; auto.
      econstructor 2; eauto. econstructor; eauto. right.
      rewrite trans_expr_typeof; auto. simpl typeof.
      eapply eval_lvalue_loadbytes_range_perm in H; eauto.
      destruct H. rewrite H. rewrite A15.
      eapply field_offset_no_overlap in H13; eauto.
      generalize (Int.unsigned_range ofs0) (Int.unsigned_range ofs); intros.
      destruct H13; [left | right]; try omega.
    assert(B: eval_stmt prog2 gc nid te1 e2 te1 (PTree.set OUTSTRUCT (m1',mknstruct (snd nd)) e2) (Sassign (trans_expr (makevar (snd nd)) lhs) (Sfield lh id (typeof lhs)))).
      apply eval_Sassign. constructor 1 with v v; try rewrite trans_expr_typeof; auto.
      constructor 2 with OUTSTRUCT (Int.add (Int.repr delta') ofs0); auto.
      rewrite trans_expr_typeof; auto.
      exists m; auto.
    assert(B1: mvl_mapping m m1' (Int.repr delta') t).
      eapply store_struct_item_mvl_mapping; eauto.
      eapply store_mvl_range_perm2 in H27. red in H27.
      eapply loadbytes_length in H30. rewrite <-H30 in H27.
      rewrite nat_of_Z_eq in H27; try omega.
    assert(B4: vrets_match (nd_fld (snd fd)) m1' ofs l vl).
      rewrite H10 in *. simpl in H15.
      eapply mvl_mapping_vrets_match with (isid:=instid cdef); eauto; try omega.
      unfold sizeof_fld in *. omega.
    destruct IHlocenv_setvarfs with l ofs m1' (PTree.set OUTSTRUCT (m1',mknstruct (snd nd)) e2) as [e2' [? ?]]; auto.
      eapply eval_lvalue_make_inst_determ_set_right; eauto.
      rewrite PTree.gss; auto.
      congruence.
      eapply locals_struct_match_set_loc; eauto.
      eapply ptree_disjoint_set_left; eauto.
      eapply mvl_mapping_subenv_struct_match; eauto.
        unfold sizeof_fld in *. omega.
    exists e2'. split; auto.
    apply eval_Sseq with te1 (PTree.set OUTSTRUCT (m1',mknstruct (snd nd)) e2); auto.
Qed.

Lemma array_ofs_range:
  forall delta size i j,
  0 <= delta /\ delta + size * Z.max 0 j <= Int.max_signed ->
  0 < size ->
  Int.unsigned i < j ->
  delta <= Int.unsigned (Int.add (Int.repr delta) (Int.mul (Int.repr size) i))
  /\ Int.unsigned (Int.add (Int.repr delta) (Int.mul (Int.repr size) i)) + size <=
    delta + size * Z.max 0 j.
Proof.
  intros. generalize (Int.unsigned_range i); intros.
  rewrite Z.max_r in *; try omega.
  rewrite int_mul_repr. rewrite <-repr_add_int.
  assert(A3: 0 <= size * Int.unsigned i < size * j).
    split. apply Zmult_le_0_compat; try omega.
    apply Zmult_lt_compat_l; try omega.
  rewrite Int.unsigned_repr; try omega.
  +split; try omega. rewrite <-Zplus_assoc.
   apply Zplus_le_compat_l. apply zmul_add_le_mul_lt; try omega.
  +generalize Int.max_signed_unsigned. omega.
Qed.

Lemma vrets_fld_match_store_mvl_offset:
  forall fld rets vrets mv ofs sid m m',
  vrets_match fld mv Int.zero rets vrets ->
  store_mvl (Tstruct sid fld) m ofs (Vmvl mv) m' ->
  vrets_match fld m' ofs rets vrets.
Proof.
  induction 1; simpl; intros.
  +constructor.
  +constructor 2; auto.
   -destruct H as [delta [? [? [? ?]]]].
    exists delta; repeat (split;auto).
    rewrite Int.add_zero_l in H4.
    eapply loadbytes_load_mvl_inv with (t:= (Tstruct sid fld)); eauto.
    inv H1; simpl in *; try congruence.
    rewrite H8. eapply loadbytes_storebytes_same; eauto.
    apply Zdivide_trans with (alignof (Tstruct sid fld)).
    simpl. eapply field_type_alignof; eauto.
    eapply store_mvl_div_alignof; eauto.
   -apply IHForall2; auto.
Qed.

Lemma env_list_match_replace_nth_rec:
  forall m o fd j efs,
  env_list_match m o fd j efs ->
  forall m' i ty ef',
  sizeof ty = sizeof_fld (nd_fld (snd fd)) ->
  mvl_mapping m m' (Int.add o (array_ofs (int_of_nat i) ty)) ty ->
  env_struct_match m' (Int.add o (array_ofs (int_of_nat i) ty)) fd ef' ->
  (i < j)%nat ->
  length m = length m' ->
  Int.unsigned o + sizeof_fld (nd_fld (snd fd)) * (Z_of_nat j) <= Z.of_nat (length m) <= Int.max_signed ->
  env_list_match m' o fd j (replace_nth efs i ef').
Proof.
  induction 1; intros.
  +omega.
  +rewrite Nat2Z.inj_succ, <-Zmult_succ_r_reverse in H6.
   generalize (sizeof_pos ty) (Int.unsigned_range o) Int.max_signed_unsigned; intros.
   assert(A: 0 <= sizeof_fld (nd_fld (snd fd)) * Z.of_nat j).
      rewrite <-H1. apply Zmult_le_0_compat; try omega.
   destruct i.
   -unfold replace_nth.
    unfold int_of_nat, array_ofs in H2, H3. simpl in *.
    rewrite Int.mul_zero, Int.add_zero in *.
    constructor 2; auto.
    rewrite <-H1 in *. rewrite <-repr_add_int_r in *.
    eapply getn_offset_eq_env_struct_match; eauto;
    rewrite <-H1; rewrite Int.unsigned_repr; try omega.
    apply mvl_mapping_getN_right; auto. omega.
   -rewrite replace_nth_shift.
    assert(A1: Int.add o (array_ofs (int_of_nat (S i)) ty)=
              Int.add (Int.add o (Int.repr (sizeof_fld (nd_fld (snd fd))))) (array_ofs (int_of_nat i) ty)).
      rewrite <-H1. rewrite Int.add_assoc. f_equal.
      unfold int_of_nat. rewrite Nat2Z.inj_succ.
      replace (Z.succ (Z.of_nat i)) with (1+(Z.of_nat i)); try omega.
      rewrite repr_add_int. unfold array_ofs.
      rewrite Int.mul_add_distr_r. f_equal.
      rewrite Int.mul_one; auto.
    rewrite A1 in *.
    assert(A2: 0 <= sizeof ty * Int.unsigned (int_of_nat i) <= sizeof ty * Z.of_nat j).
      split. apply Zmult_le_0_compat; try omega.
      eapply Int.unsigned_range; eauto.
      apply Zmult_le_compat_l; try omega. unfold int_of_nat.
      apply Zle_trans with (Z.of_nat i).
      apply int_repr_le; try omega. apply Nat2Z.inj_le; try omega.
    constructor 2; auto.
    *eapply getn_offset_eq_env_struct_match; eauto.
     omega.
     omega.
     rewrite <-H1 in *. apply loadbytes_getN_eq; try omega.
     apply H2; try omega. left. rewrite <-repr_add_int_r.
     rewrite Int.add_commut, <-repr_add_int_r.
     unfold array_ofs. rewrite int_mul_repr.
     rewrite Int.unsigned_repr; try omega;
     rewrite Int.unsigned_repr; try omega.
    *apply IHenv_list_match with ty; auto; try omega.
     split; try omega. rewrite <-H1 in *.
     rewrite <-repr_add_int_r. rewrite Int.unsigned_repr; try omega.
Qed.

Lemma env_list_match_replace_nth:
  forall m o fd j efs m' i ty ef',
  env_list_match m o fd (nat_of_int j) efs ->
  mvl_mapping m m' (Int.add o (array_ofs i ty)) ty ->
  env_struct_match m' (Int.add o (array_ofs i ty)) fd ef' ->
  Int.unsigned i < Int.unsigned j ->
  length m = length m' ->
  Int.unsigned o + sizeof_fld (nd_fld (snd fd)) * (Int.unsigned j) <= Z.of_nat (length m) <= Int.max_signed ->
  sizeof ty = sizeof_fld (nd_fld (snd fd)) ->
  env_list_match m' o fd (nat_of_int j) (replace_nth efs (nat_of_int i) ef').
Proof.
  intros. generalize (Int.unsigned_range i); intros.
  apply env_list_match_replace_nth_rec with m ty; auto.
  +rewrite <-int_of_nat_of_int; auto.
  +rewrite <-int_of_nat_of_int; auto.
  +apply Z2Nat.inj_lt in H2; try omega.
   unfold nat_of_int, nat_of_Z, Z.to_nat in *. omega.
  +unfold nat_of_int. rewrite nat_of_Z_eq; try omega.
Qed.

Lemma env_struct_match_store_mvl:
  forall mv' fd ef' m ofs m',
  env_struct_match mv' Int.zero fd ef' ->
  store_mvl (mknstruct (snd fd)) m ofs (Vmvl mv') m' ->
  env_struct_match m' ofs fd ef'.
Proof.
  unfold mknstruct. intros.
  inv H0; simpl in *. congruence.
  apply loadbytes_storebytes_same in H3.
  unfold loadbytes in H3.
  destruct (range_perm_dec _ _ _); try congruence.
  unfold range_perm in *. generalize (Int.unsigned_range ofs); intros.
  eapply getn_offset_eq_env_struct_match; eauto.
  +rewrite Int.unsigned_zero. unfold sizeof_fld. omega.
  +unfold sizeof_fld. omega.
  +rewrite Int.unsigned_zero. unfold sizeof_fld. simpl.
   rewrite H4. rewrite nat_of_Z_of_nat in *. rewrite getN_full.
   congruence.
Qed.

Lemma env_match_struct_match:
  forall fd e1 e2 m,
  env_match fd e1 e2 ->
  e2 ! OUTSTRUCT = Some (m, mknstruct (snd fd)) ->
  env_struct_match m Int.zero fd e1.
Proof.
  induction 1. intros.
  unfold mvl in *. rewrite H in H2.
  congruence.
Qed.

Lemma replace_nth_zero:
  forall efs  (ef: env),
  Z.of_nat (length efs) = Int.unsigned (intof_opti None) ->
  replace_nth efs (nat_of_int Int.zero) ef = ef::nil.
Proof.
  simpl intof_opti. unfold nat_of_int, replace_nth.
  rewrite Int.unsigned_zero, Int.unsigned_one.
  simpl. intros. destruct efs. inv H.
  simpl length in *. rewrite Nat2Z.inj_succ in H.
  destruct efs. auto.
  simpl length in *. rewrite Nat2Z.inj_succ in H. omega.
Qed.

Lemma eval_stmt_trans_lhs_rets_simpl:
  forall nid l te e te' e' s,
  eval_stmt prog2 gc nid te e te' e' (Sseq s (fold_right Sseq Sskip l)) ->
  eval_stmt prog2 gc nid te e te' e' (trans_lhs_rets_simpl s l).
Proof.
  induction l; simpl; intros.
  +inv H. inv H8; auto.
  +apply IHl; auto.
   inv H. inv H8. econstructor; eauto.
   econstructor; eauto.
Qed.

Lemma trans_func_correct:
  forall e1 e1' fd vargs vrets,
  LsemE.eval_node prog1 gc e1 e1' fd vargs vrets ->
  forall eh se eh' se', e1 = mkenv eh se ->
  e1' = mkenv eh' se' ->
  find_funct (node_block prog1) (fst fd) = Some fd ->
  nd_kind (snd fd) = false ->
  eval_node prog2 gc eh eh' fd vargs vrets.
Proof.
  induction 1 using LsemE.eval_node_ind2 with
  ( P0 := fun nid te e1 te' e1' s =>
      forall nd eh se eh' se', e1 = mkenv eh se ->
      e1' = mkenv eh' se' ->
      find_funct (node_block prog1) nid = Some nd ->
      nd_kind (snd nd) = false ->
      eval_stmt prog2 gc nid te eh te' eh' s
  ); intros.
  +inv H8. inv H9.
   constructor 1 with te te1 te2; eauto.
  +inv H0; inv H1. econstructor; eauto.
  +inv H13. inv H14. destruct H1 as [? [? [? [? [? [? [? ?]]]]]]].
   rewrite H15 in *. inv H1.
   unfold func in *. rewrite H16, <-H20, H in *.
   simpl in *. congruence.
  +inv H13. inv H14. destruct ef' as [ef' sef].
   apply eval_Scall with ef ef' vl fd vargs vargs' vrets; auto.
   eapply trans_call_func; eauto.
   destruct H0 as [? [? [? [? [? ?]]]]].
   eapply IHeval_node; eauto.
   eapply find_funct_eq; eauto.
  +inv H1. econstructor; eauto.
  +inv H0. inv H1. econstructor; eauto.
  +inv H3. econstructor; eauto.
  +subst. inv H0. constructor.
  +subst. destruct e1 as [eh1 se1].
   apply eval_Sseq with te1 eh1; eauto.
  +inv H2. econstructor; eauto.
  +inv H2. inv H3. econstructor; eauto.
Qed.

Lemma svars_fld_match_fnil:
  forall l, svars_fld_match l Fnil ->
  l = nil.
Proof.
  unfold svars_fld_match. simpl; intros.
  destruct l; auto. destruct p.
  assert ( In (i, t) ((i, t) :: l)). simpl; auto.
  apply H in H0. congruence.
Qed.

Lemma trans_node_fnil_correct:
  forall e1 e1' fd vargs vrets,
  LsemE.eval_node prog1 gc e1 e1' fd vargs vrets ->
  forall eh se eh' se', e1 = mkenv eh se ->
  e1' = mkenv eh' se' ->
  find_funct (node_block prog1) (fst fd) = Some fd ->
  nd_kind (snd fd) = true ->
  nd_fld (snd fd) = Fnil ->
  eval_node prog2 gc eh eh' fd vargs vrets.
Proof.
  induction 1 using LsemE.eval_node_ind2 with
  ( P0 := fun nid te e1 te' e1' s =>
      forall nd eh se eh' se', e1 = mkenv eh se ->
      e1' = mkenv eh' se' ->
      find_funct (node_block prog1) nid = Some nd ->
      nd_kind (snd nd) = true ->
      nd_fld (snd nd) = Fnil ->
      eval_stmt prog2 gc nid te eh te' eh' s
  ); intros.
  +inv H8. inv H9.
   constructor 1 with te te1 te2; eauto.
  +inv H0; inv H1. econstructor; eauto.
  +inv H13. inv H14. destruct H1 as [? [? [? [? [? [? [? ?]]]]]]].
   rewrite H15 in *. inv H1.
   rewrite H17 in *. simpl in *. congruence.
  +inv H13. inv H14. destruct ef' as [ef' sef].
   apply eval_Scall with ef ef' vl fd vargs vargs' vrets; auto.
   eapply trans_call_func; eauto.
   destruct H0 as [? [? [? [? [? ?]]]]].
   eapply trans_func_correct; eauto.
   eapply find_funct_eq; eauto.
  +inv H1. econstructor; eauto.
  +inv H0. inv H1. econstructor; eauto.
  +inv H3. econstructor; eauto.
  +subst. inv H0. constructor.
  +subst. destruct e1 as [eh1 se1].
   apply eval_Sseq with te1 eh1; eauto.
  +inv H2. econstructor; eauto.
  +inv H2. inv H3. econstructor; eauto.
Qed.

Lemma trans_node_correct:
  forall e1 e1' fd vargs vrets,
  LsemE.eval_node prog1 gc e1 e1' fd vargs vrets ->
  forall e2 fd' i t ftl, env_match fd e1 e2 ->
  find_funct (node_block prog1) (fst fd) = Some fd ->
  trans_node fd = OK fd' ->
  nd_kind (snd fd) = true ->
  nd_fld (snd fd) = Fcons i t ftl ->
  env_fld_match prog1 fd e1 ->
  exists e2' m, eval_node prog2 gc e2 e2' fd' vargs (Vmvl m::nil)
    /\ env_match fd e1' e2'
    /\ vrets_fld_match (nd_fld (snd fd)) (nd_rets (snd fd)) vrets m Int.zero
    /\ e2' ! OUTSTRUCT = Some (m,mknstruct (snd fd))
    /\ env_fld_match prog1 fd e1'.
Proof.
  induction 1 using LsemE.eval_node_ind2 with
  ( P0 := fun nid te e1 te' e1' s =>
      forall e2 nd i t ftl, env_match nd e1 e2 ->
      find_funct (node_block prog1) nid = Some nd ->
      sizeof_fld (nd_fld (snd nd)) <= Int.max_signed ->
      incl (instidof s) (instidof (nd_stmt (snd nd))) ->
      list_norepet (map instid (instidof (nd_stmt (snd nd)))) ->
      te ! OUTSTRUCT = None ->
      env_fld_match prog1 nd e1 ->
      nd_fld (snd nd) = Fcons i t ftl ->
      exists e2', eval_stmt prog2 gc nid te e2 te' e2' (trans_stmt (makevar (snd nd)) s)
        /\ env_match nd e1' e2'
        /\ te' ! OUTSTRUCT = None
        /\ env_fld_match prog1 nd e1'
  ); intros.
 +(*node*)
  unfold trans_node, sizeof_fld in *.
  rewrite H10, H11 in H9. rewrite <-H11 in *.
  destruct (zlt _ _), (zle _ _); inv H9.
  assert(A: ~ In OUTSTRUCT (map fst (lvarsof f))).
    eapply ids_plt_not_in; eauto.
  destruct IHeval_node with e2 (nid,f) i t ftl as [e2' [? [? [? ?]]]]; auto.
    red; intros; auto.
    eapply ids_norepet_instid; eauto.
    erewrite set_new_vars_getid_eq with (eh:= te); eauto.
    erewrite alloc_variables_notin_eq with (e:=empty_locenv); eauto.
    red. intros. apply A. unfold lvarsof. rewrite map_app. apply in_or_app; auto.
  exists e2'. inv H13. inv H21.
  eapply locals_struct_match_getvars in H3; eauto.
  destruct H3. exists m. repeat (split; auto).
  -eapply exec_node; eauto.
   apply trans_body_ids_norepeat; auto.
   change f with (snd (nid,f)). apply ID_RANGE; auto.
   eapply find_funct_in2; eauto.
  -constructor 1 with m; auto.
   constructor; auto.
 +(*Sassign*)
  inv H. generalize H16 Int.max_signed_unsigned; intros A A1.
  eapply env_match_setvarf_exists in H16; eauto.
  destruct H16 as [e2' [? [? [? ?]]]].
  exists e2'. split; auto.
  apply eval_Sassign. constructor 1 with v v'; auto.
  eapply env_match_eval_sexp; eauto.
  repeat rewrite trans_expr_typeof; auto.
  eapply assign_disjoint_env_match; eauto.
  rewrite trans_expr_typeof; auto.
 +(*Scall_node*)
  simpl. rewrite H. generalize H1 H1; intros A C.
  destruct A as [A1 [A2 [A3 [A4 [A5 [A6 [A7 [A8 [A9 A10]]]]]]]]].
  assert(nd0 = nd).
    rewrite H14 in A1. inv A1; auto.
  subst nd0.
  assert(D: env_fld_match prog1 fd ef).
    eapply env_fld_match_sube; eauto. apply H16. simpl.
    unfold cons_inst. rewrite H; simpl; auto.
  generalize Int.max_signed_unsigned.
  generalize (sizeof_fld_pos (nd_fld (snd fd))). intros D1 D2.
  destruct (nd_fld (snd fd)) eqn:?; rewrite A5 in *.

  apply trans_call_node_fnil in H1; auto; try (rewrite Heqf; congruence).
  assert(B: nd_rets (snd fd) = nil /\ lhs = nil).
    inv H5. simpl in *. rewrite Heqf in *. apply svars_fld_match_fnil in H26.
    unfold svarsof in *. apply app_eq_nil in H26. destruct H26 as [B B1].
    rewrite B in *. split; auto. destruct lhs; simpl in *; try congruence.
  destruct B as [B B1]. subst. inv H6.
  assert(B3: ef = empty_env /\ ef' = empty_env).
    inv D. unfold func in *. rewrite Heqf in *. congruence.
    split; auto. eapply eval_node_empty_env; eauto.
  destruct B3. subst.
  assert(B4: se' = se).
    inv H2. apply ptree_set_same. rewrite H6.
    rewrite replace_nth_error_self; auto.
  subst.
  exists e2. split; [| split]; auto.
  apply eval_Scall with empty_locenv empty_locenv nil fd vargs vargs' nil; subst; eauto.
  eapply env_match_eval_sexps; eauto.
  rewrite trans_exprs_typeof; auto.
  constructor.
  unfold func in *. rewrite B. constructor.
  eapply trans_node_fnil_correct with (se:=empty_subenv) (se':=empty_subenv); eauto.
   eapply find_funct_eq; eauto.
  constructor.
  rewrite trans_exprs_typeof; auto.
  constructor.
  red; simpl; intros; tauto.


  apply trans_call_node in H1; auto; try (rewrite Heqf; congruence).
  destruct H1 as [fd' [A11 A12]].
  inv H13. remember (make_inst _ _ _ _ _) as lh.
  destruct ef as [lef sef].
  assert(A14: callid cdef = fst fd).
    eapply find_funct_fid in A6; eauto.
  generalize A3; intros A15.
  apply field_type_offset_exists in A15. destruct A15 as [delta A15].
  assert(A18: mknstruct (snd fd) = mkcstruct cdef).
    unfold mkcstruct, mknstruct. congruence.
  assert(B: exists ehf, lef = ehf).
    inv H5; eauto.
  destruct B as [ehf B]. subst lef.
  generalize Int.max_signed_unsigned; intros A20.
  assert(B: exists mv ofs, eval_lvalue gc te e2 lh OUTSTRUCT ofs Sid
             /\ load_env (typeof lh) e2 OUTSTRUCT ofs (Vmvl mv)
             /\ env_match fd (mkenv ehf sef) (PTree.set OUTSTRUCT (mv,mknstruct (snd fd)) empty_locenv)
             /\ (alignof (mknstruct (snd fd)) | Int.unsigned ofs)).
    subst. eapply eval_lvalue_instance_exists with (i:=i); eauto.
    eapply find_funct_fid in A1. subst; auto. inv H2; auto.
    apply cons_inst_incl; auto.
    unfold trans_node in A11. unfold func in *.
    rewrite <-A7, H in A11. unfold mknstruct.
    rewrite Heqf in *. unfold sizeof_fld in *.
    clear -A11.  simpl in *.
    destruct (zlt 0 _),(zle _ _); inv A11; try omega.
  destruct B as [mv [ofs [B [B1 [B2 BA]]]]].
  unfold func in *. rewrite A9, A14, A6, <-A18, A7 in *.
  destruct IHeval_node with (PTree.set OUTSTRUCT (mv,mknstruct (snd fd))  empty_locenv) fd' i1 t0 f as [ef2' [mv' [? [? [? [A16 A17]]]]]]; auto.

  assert(B3: typeof lh = mknstruct (snd fd)).
    subst. clear -H0. inv H0; simpl; auto.
  assert(B4: loadbytes m (Int.unsigned ofs) (sizeof (typeof lh)) = Some mv).
    destruct B1 as [? [? [? [? B1]]]]. rewrite B3 in *. clear -B1 H22 H24.
    inv B1. simpl in H; try congruence. unfold mvl in *. congruence.
  generalize B4 (sizeof_pos (typeof lh)); intros B5 B6.
  eapply loadbytes_length in B5.
  rewrite B3 in *.
  assert(B7: length mv = length mv').
    rewrite <-B5. clear -H21 Heqf. inv H21. rewrite <-Heqf in *.
    change (sizeof (mknstruct (snd fd))) with (sizeof_fld (nd_fld (snd fd))); auto.
    rewrite <-H0. rewrite nat_of_Z_of_nat; auto.
  assert(B8: range_perm m (Int.unsigned ofs) (Int.unsigned ofs + Z_of_nat (length mv'))).
    rewrite <-B7,<-B5. rewrite nat_of_Z_eq; try omega.
    eapply loadbytes_range_perm; eauto.
  generalize A15; intros B13. eapply field_offset_in_range_simpl in B13; eauto.
  assert(B9: exists m', store_mvl (typeof lh) m  ofs (Vmvl mv') m').
    destruct range_perm_store_bytes with m (Int.unsigned ofs) mv' as [m' ?]; auto.
    exists m'. rewrite B3. constructor 2; auto. rewrite <-B7, <-B5.
    rewrite nat_of_Z_eq; try omega.
  destruct B9 as [m' B9].
  assert(B10: locenv_setvarf gc te e2 lh (Vmvl mv') te (PTree.set OUTSTRUCT (m',mknstruct (snd nd)) e2)).
    constructor 2 with OUTSTRUCT ofs;auto. exists m; auto.
  assert(B11: eh ! (instid cdef) = None).
    inv H2. inv H25. destruct (eh ! (instid cdef)) eqn:?; auto.
    apply H31 in Heqo. congruence.
  assert(B14: ptree_disjoint eh se').
    inv H2. inv H25. eapply ptree_disjoint_set_right; eauto.
  assert(B15: ofs = match callnum cdef with
                    | Some _ => Int.add (Int.repr delta) (array_ofs i (mknstruct (snd fd)))
                    | None => Int.repr delta
                    end).
    rewrite B3 in *. subst. clear -A4 A15 B H0.
    inv H0; try rewrite <-H in *.
    inv B. eapply eval_sexp_sexp with (eh:=e2) in H2; eauto.
    eapply eval_sexpm_determ in H2; eauto.
     inv H2. inv H4. unfold mknstruct in *. inv H3. inv H7.
     rewrite Int.add_zero_l. congruence.
    inv B. unfold mknstruct in *. inv H4. inv H3.
     rewrite Int.add_zero_l. congruence.
  assert(B16: Int.unsigned i < Int.unsigned (intof_opti (callnum cdef))).
    eapply callnd_env_range_i; eauto.
  assert(B17: delta <= Int.unsigned ofs /\
             Int.unsigned ofs + sizeof (typeof lh) <=
               delta + sizeof match callnum cdef with
                       | Some j => Tarray xH (mknstruct (snd fd)) (Int.unsigned j)
                       | None => mknstruct (snd fd) end).
    rewrite B3 in *. rewrite B15. clear -B13 B16 H0 H15 B6 A20 B9.
    apply store_mvl_range_perm2 in B9. red in B9.
    inv H0. rewrite <-H in *. simpl in B13, B16, B6. unfold array_ofs.
    simpl sizeof in *. apply array_ofs_range; try omega.
    rewrite <-H2 in *. simpl in B13, B6. simpl sizeof.
    rewrite Int.unsigned_repr; try omega.
  assert(B18: mvl_mapping m m' ofs (typeof lh)).
    eapply store_mvl_mapping; eauto.
  assert(B19: locals_struct_match eh (nd_fld (snd nd)) Int.zero m').
    inv H25. destruct B17.
    eapply mvl_mapping_local_struct_match with (isid:=instid cdef); eauto.
  assert(B20: length m = length m').
    eapply store_mvl_length; eauto.
  assert(B21: In cdef (instidof (nd_stmt (snd nd)))).
    eapply cons_inst_incl; eauto.
  assert(B22: env_struct_match mv' Int.zero fd ef').
    eapply env_match_struct_match; eauto.
  assert(B23: env_struct_match m' ofs fd ef').
   rewrite B3 in *.
   eapply env_struct_match_store_mvl; eauto.
  assert(B24: subenv_struct_match m' Int.zero (nd_fld (snd nd)) (instidof (nd_stmt (snd nd))) se').
   rewrite B3 in *. inv H2. inv H25. rewrite <-A14 in *.
   eapply mvl_mapping_subenv_struct_match_set with (m:=m);eauto.
   rewrite Int.add_zero_l. inv H0.
    rewrite <-H2 in *. constructor 2; auto.
    eapply env_list_match_replace_nth; eauto.
     eapply subenv_struct_match_in in H32; eauto.
      rewrite Int.add_zero_l in H32. inv H32.
      rewrite int_unsigned_inj with j j0; auto.
     split; try omega.
      apply Zle_trans with (delta + sizeof (Tarray xH (mknstruct (snd fd)) (Int.unsigned j))); try omega.
      unfold sizeof_fld. apply Zplus_le_compat. apply int_repr_le; try omega.
      simpl. apply Zmult_le_compat_l. apply zmax_r_le; try omega.
      rewrite Heqf. unfold sizeof_fld in *. omega.
    rewrite <-H27 in *. erewrite replace_nth_zero; eauto.
     constructor; auto.
   rewrite Int.add_zero_l.
   eapply mvl_mapping_incl;eauto; rewrite Int.unsigned_repr; try omega.
  assert(B25: vrets_match (nd_fld (snd fd)) m' ofs (nd_rets (snd fd)) vrets).
    rewrite B3 in *. inv H21.
    eapply vrets_fld_match_store_mvl_offset; eauto. congruence.
  assert(B26: option_match oid (callnum cdef)).
    eapply load_loopid_option_match; eauto.
  assert(B27: eval_lvalue gc te (PTree.set OUTSTRUCT (m',mknstruct (snd nd)) e2) lh OUTSTRUCT ofs Sid).
    eapply eval_lvalue_make_inst_determ_set_right; eauto.
  assert(C3: exists e2', eval_stmt prog2 gc nid te (PTree.set OUTSTRUCT (m',mknstruct (snd nd)) e2) te' e2'
                 (trans_lhs_rets (combine (trans_exprs (makevar (snd nd)) lhs) (nd_rets (snd fd)))lh)
              /\ env_match nd {| le := eh'; sube := se' |} e2').
    inv H2.
    eapply trans_lhs_rets_correct with eh vrets fd cdef oid delta _ _ _ m'; eauto.
    rewrite PTree.gss; auto.
    rewrite <-B20; auto.
    rewrite PTree.gss; auto.
    inv H5. simpl in *. congruence.
  destruct C3 as [e2' [C3 C4]].
  exists e2'. split; [| split; [| split]]; auto.
  apply eval_stmt_trans_lhs_rets_simpl.
  apply eval_Sseq with te (PTree.set OUTSTRUCT (m',mknstruct (snd nd)) e2); auto.
  apply eval_Scall with (PTree.set OUTSTRUCT (mv,mknstruct (snd fd)) empty_locenv) ef2' (mv::nil) fd' vargs vargs' (Vmvl mv'::nil); auto.
  -eapply env_match_eval_sexps; eauto. econstructor; eauto.
  -rewrite trans_exprs_typeof; auto.
  -constructor 2; auto. constructor 1 with OUTSTRUCT ofs Sid m (mknstruct (snd nd)); auto.
   congruence.
  -clear -B5 B6 B7 B8 A11 H Heqf.
   unfold trans_node in A11. unfold func in *. rewrite H, Heqf in *.
   destruct (_ && _); inv A11.
   simpl nd_rets in *. red in B8.
   rewrite <-B7, <-B5 in *. rewrite nat_of_Z_eq in B8; try omega.
   econstructor 2; eauto. constructor 1; eauto; try omega.
   rewrite <-B5. rewrite nat_of_Z_eq; try omega.
   rewrite <-B5. rewrite nat_of_Z_eq; try omega.
   constructor.
  -econstructor 2; eauto. constructor.
  -constructor 2; auto. subst. unfold make_inst.
   inv H0; simpl; unfold OUTSTRUCT, ACG_I; try split; congruence.
  -unfold trans_node in A11. unfold func in *.
   rewrite H, Heqf in *. destruct (_ && _); inv A11.
   simpl. congruence.
  -rewrite trans_exprs_typeof; auto.
   unfold trans_node in A11. unfold func in *. rewrite H, Heqf in *.
   destruct (_ && _); inv A11. auto.
  -constructor 2; auto. red; intros; tauto. constructor.
  -eapply assign_list_disjoint_env_match_out with (se:=se); eauto.
   constructor 1 with m; auto.
  -simpl. congruence.
  -eapply locenv_setvarfs_id_none; eauto.
  -eapply env_match_setvarfs_env_fld_match; eauto.
   inv H19; try congruence. constructor 1; auto.
   eapply env_fld_match_replace; eauto.
 +(*Scall_func*)
  simpl. rewrite H.
  generalize H0. intros A. destruct A as [A1 [A2 [A3 [A4 A5]]]].
  apply trans_call_func in H0; auto.
  generalize Int.max_signed_unsigned; intros A.
  eapply env_match_setvarfs_func_exists in H6; eauto.
  destruct H6 as [e2' [? [? [? ?]]]].
  exists e2'. split; auto.
  destruct ef' as [ef' sef'].
  apply eval_Scall with ef ef' vl fd vargs vargs' vrets; subst; eauto.
  -eapply env_match_eval_sexps; eauto.
  -rewrite trans_exprs_typeof; auto.
  -inv H13. inv H29. eapply locenv_getmvls_match; eauto.
  -eapply trans_func_correct; eauto.
   eapply find_funct_eq; eauto.
  -eapply trans_exprs_lid_disjoint; eauto.
  -rewrite trans_exprs_typeof; auto.
  -rewrite trans_exprs_typeof; auto.
  -eapply lvalue_list_norepet_env_match; eauto.
  -eapply assign_list_disjoint_env_match; eauto.
 +(*Sfor_start*)
  eapply env_match_eval_eqf in H; eauto.
  destruct H as [e21 [? [? [? ?]]]].
  destruct IHeval_node with e21 nd i t ftl as [e2' [? [? [? ?]]]]; auto.
  exists e2'. split; auto.
  eapply eval_Sfor_start; eauto.
 +(*Sfor_false*)
  exists e2. split; auto.
  apply eval_Sfor_false; auto.
  eapply env_match_eval_sexp; eauto.
 +(*Sfor_loop*)
  destruct IHeval_node with e2 nd i t ftl as [e21 [? [? [? ?]]]]; auto.
  eapply env_match_eval_eqf in H1; eauto.
  destruct H1 as [e22 [? [? [? ?]]]].
  destruct IHeval_node0 with e22 nd i t ftl as [e2' [? [? [? ?]]]]; auto.
  exists e2'. split; auto.
  eapply eval_Sfor_loop; eauto.
  eapply env_match_eval_sexp; eauto.
 +(*Sskip*)
  exists e2. split; auto. constructor.
 +(*Sseq*)
  destruct IHeval_node with e0 nd i t ftl as [e21 [? [? [? ?]]]]; auto.
    eapply incl_app_inv_l; eauto.
  destruct IHeval_node0 with e21 nd i t ftl as [e2' [? [? [? ?]]]]; auto.
    eapply incl_app_inv_r; eauto.
  exists e2'. split; auto.
  apply eval_Sseq with te1 e21; auto.
 +(*Sif*)
  destruct IHeval_node with e2 nd i t ftl as [e2' [? [? [? ?]]]]; auto.
    red; intros. apply H5. apply in_or_app; destruct b; auto.
  exists e2'; split; auto.
  apply eval_Sif with v b; simpl; auto.
  -eapply env_match_eval_sexp; eauto.
  -rewrite trans_expr_typeof; auto.
  -destruct b; auto.
 +(*Scase*)
  destruct IHeval_node with e2 nd i0 t ftl as [e2' [? [? [? ?]]]]; auto.
  exists e2'. split; auto.
  apply eval_Scase with i ((trans_expr (makevar (snd nd))) a); auto.
  -eapply env_match_eval_sexp; eauto.
  -eapply trans_select_case; eauto.
Qed.

Lemma env_struct_match_alloc:
  forall (fd: ident*func) ef size delta,
  env_struct_match (alloc (sizeof_fld (nd_fld (snd fd)))) Int.zero fd ef ->
  0 <= delta ->
  delta + sizeof_fld (nd_fld (snd fd)) <= size <= Int.max_signed->
  env_struct_match (alloc size) (Int.repr delta) fd ef.
Proof.
  intros. generalize (sizeof_fld_pos (nd_fld (snd fd))) Int.max_signed_unsigned; intros.
  eapply getn_offset_eq_env_struct_match with (m:=alloc (sizeof_fld (nd_fld (snd fd)))) (o:=Int.zero); eauto.
  +unfold alloc. rewrite Int.unsigned_zero,length_list_repeat.
   rewrite nat_of_Z_eq; try omega.
  +unfold alloc. rewrite length_list_repeat.
   rewrite nat_of_Z_eq; try omega.
   rewrite Int.unsigned_repr; try omega.
  +rewrite Int.unsigned_zero.
   rewrite Int.unsigned_repr; try omega.
   repeat rewrite getN_alloc_eq; try omega. auto.
Qed.

Lemma env_list_match_alloc:
  forall (fd: ident*func) ef size i delta,
  env_struct_match (alloc (sizeof_fld (nd_fld (snd fd)))) Int.zero fd ef ->
  0 <= delta ->
  delta + sizeof_fld (nd_fld (snd fd)) * (Z_of_nat i) <= size <= Int.max_signed ->
  env_list_match (alloc size) (Int.repr delta) fd i (list_repeat i ef).
Proof.
  induction i; intros.
  +constructor.
  +generalize (sizeof_fld_pos (nd_fld (snd fd))); intros.
   rewrite Nat2Z.inj_succ,<-Zmult_succ_r_reverse in H1.
   assert(A: 0 <= sizeof_fld (nd_fld (snd fd)) * Z.of_nat i).
     apply Zmult_le_0_compat; try omega.
   constructor 2; auto.
   -apply env_struct_match_alloc; auto. omega.
   -rewrite <-repr_add_int.
    apply IHi; auto; try omega.
Qed.

Lemma alloc_variables_locals_struct_match:
  forall al eh fld,
  alloc_variables empty_locenv al eh ->
  list_norepet (map fst al) ->
  svars_fld_match al fld ->
  sizeof_fld fld <= Int.max_signed ->
  (forall ty, In ty (map snd al) -> 0 < sizeof ty) ->
  locals_struct_match eh fld Int.zero (alloc (sizeof_fld fld)).
Proof.
  intros. red; intros.
  eapply alloc_variables_norepeat_ptree_in_exists in H4; eauto.
  destruct H4 as [ty0 [? ?]]. inv H5.
  generalize H4; intros.
  apply H1 in H4. apply in_map with (B:=type) (f:=snd) in H5.
  apply H3 in H5. simpl in *.
  destruct field_type_offset_exists with fld id ty0 as [delta ?]; auto.
  +exists delta; repeat (split; auto).
   subst. rewrite Int.add_zero_l.
   unfold sizeof_fld in *.
   eapply field_offset_in_range_simpl in H6; eauto.
   unfold sizeof_fld in *.
   rewrite Int.unsigned_repr; try omega.
   unfold loadbytes. rewrite pred_dec_true.
   -rewrite getN_alloc_eq; auto; try omega.
   -red. unfold alloc. rewrite length_list_repeat.
    rewrite nat_of_Z_eq; try omega.
   -generalize Int.max_signed_unsigned. omega.
  +rewrite PTree.gempty; auto.
Qed.

Lemma alloc_stmt_empty_env:
  forall nid e e' l,
  alloc_stmt prog1 nid e e' l ->
  forall f m i, e = empty_env ->
  find_funct (node_block prog1) nid = Some (nid,f) ->
  incl l (instidof (nd_stmt f)) ->
  nd_fld f = Fnil ->
  subenv_struct_match m i (nd_fld f) l empty_subenv
   /\ e' = empty_env.
Proof.
  induction 1; intros; auto.
  split; auto. constructor.
  inv H3. destruct H as [? [? [? [? [? [? [? ?]]]]]]].
  rewrite H4 in *. inv H. simpl in *.
  rewrite H6 in *. simpl in *. congruence.
Qed.

Lemma alloc_node_fnil_correct:
  forall e fd m i,
  LsemE.alloc_node prog1 e fd ->
  nd_fld (snd fd) = Fnil ->
  find_funct (node_block prog1) (fst fd) = Some fd ->
  alloc_variables empty_locenv (nd_rets (snd fd)) empty_locenv
    /\ e = empty_env
    /\ env_fld_match prog1 fd empty_env
    /\ env_struct_match m i fd empty_env.
Proof.
  intros. inv H.
  simpl in *. rewrite H0 in *.
  apply svars_fld_match_fnil in H4.
  unfold svarsof in *. apply app_eq_nil in H4.
  destruct H4. rewrite H, H4 in *; auto.
  simpl in *. inv H2.
  eapply alloc_stmt_empty_env with (m:=m) (i:=i) in H6; eauto.
  destruct H6. repeat (split; simpl; auto).
  +constructor.
  +constructor 2; auto.
  +red; intros; auto.
   rewrite PTree.gempty in *. congruence.
  +red; intros. apply PTree.gempty.
  +red; intros; auto.
Qed.

Lemma env_fld_match_repeat:
  forall i fd ef,
  env_fld_match prog1 fd ef ->
  list_fld_match prog1 fd (list_repeat i ef).
Proof.
  induction i; simpl; intros; constructor; auto.
Qed.

Lemma alloc_node_correct:
  forall e1 fd,
  LsemE.alloc_node prog1 e1 fd ->
  forall fd' i t ftl, trans_node fd = OK fd' ->
  find_funct (node_block prog1) (fst fd) = Some fd ->
  nd_kind (snd fd) = true ->
  nd_fld (snd fd) = Fcons i t ftl ->
  exists e2, alloc_variables empty_locenv (nd_rets (snd fd')) e2
    /\ env_match fd e1 e2
    /\ e2 ! OUTSTRUCT = Some (alloc (sizeof_fld (nd_fld (snd fd))), mknstruct (snd fd))
    /\ env_fld_match prog1 fd e1.
Proof.
  induction 1 using LsemE.alloc_node_ind2 with
  ( P0 := fun nid e1 e1' l =>
      forall nd m o eh se se' i t ftl,
      e1 = mkenv eh se ->
      e1' = mkenv eh se' ->
      find_funct (node_block prog1) nid = Some nd ->
      incl l (instidof (nd_stmt (snd nd))) ->
      list_norepet (map instid l) ->
      ptree_disjoint eh se ->
      loadbytes m (Int.unsigned o) (sizeof_fld (nd_fld (snd nd))) = Some (alloc (sizeof_fld (nd_fld (snd nd)))) ->
      ptree_ids_none (map instid l) eh ->
      nd_fld (snd nd) = Fcons i t ftl ->
      ptree_disjoint eh se'
      /\ subenv_struct_match m o (nd_fld (snd nd)) l se'
      /\ subenv_fld_match prog1 (nd_fld (snd nd)) l se'
   ); intros.
 +(*alloc_node*)
  unfold trans_node in *. rewrite H6, H7 in *. rewrite <-H7 in *.
  destruct (zlt _ _), (zle _ _); inv H4.
  generalize (sizeof_fld_pos (nd_fld (snd (nid,f)))); intros.
    destruct IHalloc_node with (nid,f) (alloc (sizeof_fld (nd_fld f))) Int.zero eh empty_subenv se i t ftl
      as [A [A1 A2]]; auto.
      red;intros; auto.
      apply ids_norepet_instid; auto.
      red. intros. rewrite PTree.gempty; auto.
      rewrite Int.unsigned_zero. unfold func in *.
       rewrite <-loadbytes_full; unfold alloc; rewrite length_list_repeat;
       rewrite nat_of_Z_eq; try omega. auto.
     eapply alloc_variables_ptree_ids_none; eauto.
      apply list_disjoint_sym.
      eapply ids_norepet_insts_svars_disjoint; eauto.
  exists (PTree.set OUTSTRUCT (alloc (sizeof_fld (nd_fld f)),mknstruct f) empty_locenv).
  split; [| split; [| split]].
  -unfold trans_body. simpl nd_rets.
    econstructor; eauto. constructor.
  -econstructor; auto.
   *rewrite PTree.gss; auto.
   *unfold alloc. rewrite length_list_repeat.
    generalize (sizeof_fld_pos (nd_fld f)). intros.
    rewrite nat_of_Z_eq; try omega; auto.
   *constructor 1; auto. eapply alloc_variables_locals_struct_match; eauto.
    eapply ids_norepet_rets_svars; eauto.
   -rewrite PTree.gss; auto.
   -constructor; auto. unfold func in *. rewrite H7; congruence.
 +(*nil*)
   subst e. inv H0. split;[| split]; auto; constructor.
 +(*cons*)
  generalize H H; intros A B.
  destruct A as [A1 [A2 [A3 [A4 [A5 [A6 [A7 [A8 A9]]]]]]]].
  assert(nd0 = nd).
    congruence.
  subst nd0.
  inv H3. inv H4.
  assert(A15: cakind c = true).
    apply instidof_cakind_true with (nd_stmt (snd nd)); auto.
    apply H6; simpl; auto.
  simpl in H7. inversion_clear H7.
  generalize A3; intros B3.
  eapply field_type_offset_exists in B3. destruct B3 as [delta B3].
  generalize (sizeof_fld_pos (nd_fld (snd nd))); intros C1.
  generalize B3 H9; intros C2 C4.
  eapply field_offset_in_range_simpl in C2; eauto.
  apply loadbytes_range_perm in C4. unfold range_perm in C4.
  generalize (sizeof_pos (match callnum c with
       | Some j =>
           Tarray xH (mknstruct (snd fd)) (Int.unsigned j)
       | None => mknstruct (snd fd)
       end)). intros C3.
  remember (PTree.set _ _ _) as se1.
  destruct IHalloc_node0 with nd m o eh se1 se' i t ftl as [D1 [D2 D3]]; auto.
    red; intros. apply H6; simpl; auto.
    subst. apply ptree_disjoint_set_right; auto. apply H10; simpl; auto.
    red; intros. apply H10; simpl; auto.
  generalize (sizeof_fld_pos (nd_fld (snd fd))) Int.max_signed_unsigned. intros D4 D5.
  split; auto. destruct (nd_fld (snd fd)) eqn:?.

  apply trans_call_node_fnil in B; auto; try (rewrite Heqf; congruence).
  eapply alloc_node_fnil_correct with (m:=(alloc (sizeof_fld (nd_fld (snd fd))))) (i:=Int.zero) in H0; eauto.
  destruct H0 as [B4 [B5 [B6 B7]]]. subst.
  split; auto.
  econstructor 2 with (list_repeat (nat_of_int (intof_opti (callnum c))) empty_env) delta fd _; simpl; eauto.
   eapply alloc_stmt_notin_eq in H2; eauto. simpl in H2.
   rewrite H2. subst. rewrite PTree.gss; auto.

   eapply getn_offset_eq_env_struct_match with (m:=alloc (sizeof_fld (nd_fld (snd nd)))) (o:=Int.repr delta); eauto.
   destruct (callnum c); constructor; simpl.
    apply env_list_match_alloc; auto; try omega.
      simpl in C2, A9. unfold nat_of_int. rewrite nat_of_Z_eq; try omega.
      unfold sizeof_fld in *. rewrite Z.max_r with 0 (Int.unsigned i0) in C2; omega.
    apply env_struct_match_alloc; auto; try omega.
     unfold sizeof_fld in *. simpl in C2. omega.
    unfold alloc. rewrite length_list_repeat.
     rewrite nat_of_Z_eq; try omega.
     unfold sizeof_fld in *.
     rewrite Int.unsigned_repr; try omega.

    rewrite <-repr_add_int_r. unfold sizeof_fld in *.
     rewrite Int.unsigned_repr; try omega.
    rewrite  <-repr_add_int_r. unfold sizeof_fld in *.
     rewrite Int.unsigned_repr; try omega.
     rewrite Int.unsigned_repr; try omega.
     apply loadbytes_contents in H9. rewrite H9. simpl.
     rewrite <-getN_app. rewrite nat_of_Z_plus; auto; try omega.
     rewrite <-nat_of_Z_plus; try omega.
     apply Z2Nat.inj_le; try omega.
   constructor 2 with (list_repeat (nat_of_int (intof_opti (callnum c))) empty_env) fd; auto.
    eapply alloc_stmt_notin_eq in H2; eauto. simpl in H2.
    rewrite H2. subst. rewrite PTree.gss; auto.
    apply env_fld_match_repeat; auto.
    eapply find_funct_eq; eauto.

  apply trans_call_node in B; auto; try (rewrite Heqf; congruence).
  destruct B as [fd' [B B1]].
  destruct IHalloc_node with fd' i0 t0 f  as [e2 [B4 [B5 [B6 B7]]]]; auto.
    eapply find_funct_eq;eauto.
    unfold func in *. congruence.
  assert(C: env_struct_match (alloc (sizeof_fld (nd_fld (snd fd)))) Int.zero fd ef).
    inv B5. unfold mvl, func in *. congruence.
  split; auto.
  econstructor 2 with (list_repeat (nat_of_int (intof_opti (callnum c))) ef) delta fd _; simpl; eauto.
  -eapply alloc_stmt_notin_eq in H2; eauto. simpl in H2.
   rewrite H2. subst. rewrite PTree.gss; auto.
  -eapply getn_offset_eq_env_struct_match with (m:=alloc (sizeof_fld (nd_fld (snd nd)))) (o:=Int.repr delta); eauto.
   *destruct (callnum c); constructor; simpl.
    apply env_list_match_alloc; auto; try omega.
      simpl in C2, A9. unfold nat_of_int. rewrite nat_of_Z_eq; try omega.
      unfold sizeof_fld in *.
      rewrite Z.max_r with 0 (Int.unsigned i1) in C2; omega.
    apply env_struct_match_alloc; auto; try omega.
     unfold sizeof_fld in *. simpl in C2. omega.
   *unfold alloc. rewrite length_list_repeat.
    rewrite nat_of_Z_eq; try omega.
    unfold sizeof_fld in *.
    rewrite Int.unsigned_repr; try omega.
   *rewrite <-repr_add_int_r. unfold sizeof_fld in *.
    rewrite Int.unsigned_repr; try omega.
   *rewrite  <-repr_add_int_r. unfold sizeof_fld in *.
    rewrite Int.unsigned_repr; try omega.
    rewrite Int.unsigned_repr; try omega.
    apply loadbytes_contents in H9. rewrite H9. simpl.
    rewrite <-getN_app. rewrite nat_of_Z_plus; auto; try omega.
    rewrite <-nat_of_Z_plus; try omega.
    apply Z2Nat.inj_le; try omega.
  -constructor 2 with (list_repeat (nat_of_int (intof_opti (callnum c))) ef) fd; auto.
   eapply alloc_stmt_notin_eq in H2; eauto. simpl in H2.
   rewrite H2. subst. rewrite PTree.gss; auto.
   apply env_fld_match_repeat; auto.
Qed.

Lemma vrets_match_match:
  forall rets al l m delta vl,
  vrets_match (fieldlist_of (al++rets++l)) m Int.zero rets vl->
  list_norepet (map fst rets) ->
  list_disjoint (map fst al) (map fst rets) ->
  sizeof_struct (fieldlist_of al) 0 = delta ->
  Lenv.vrets_match m delta rets vl.
Proof.
  induction rets; simpl; intros.
  +inv H. constructor 1.
  +inv H. inv H0.
   replace (al ++ a :: rets ++ l) with ((al ++ a :: nil) ++ rets ++ l) in *.
   destruct H5 as [? [? [? [? ?]]]]. destruct a. constructor 2; auto.
   -rewrite app_ass in *; simpl in *. unfold field_offset in *.
    rewrite field_offset_rec_fieldlist_of_notin_app_cons in H; auto.
    inv H; auto. rewrite Int.add_zero_l in *. auto.
    apply list_disjoint_notin with (i :: map fst rets); simpl; auto.
    apply list_disjoint_sym; auto.
   -apply IHrets with (al ++ (i, t) :: nil) l; auto.
    *rewrite map_app. red; intros.
     apply in_app_or in H6. destruct H6.
     apply H1; simpl; auto.
     red; intros; subst. simpl in *.
     destruct H6; subst; try tauto.
    *apply sizeof_struct_fieldlist_of_app_cons; auto.
   -rewrite app_ass; auto.
Qed.

Lemma trans_program_node_general:
  forall main1 e1 maxn mass vrss,
  Lenv.exec_prog1 prog1 gc LsemE.eval_node main1 e1 1 maxn mass vrss ->
  forall e2 main2 i t ftl, env_match main1 e1 e2 ->
  find_funct (node_block prog1) (fst main1) = Some main1 ->
  trans_node main1 = OK main2 ->
  svars_field_match (nd_rets (snd main1)) (nd_fld (snd main1)) ->
  nd_kind (snd main1) = true ->
  nd_fld (snd main1) = Fcons i t ftl ->
  env_fld_match prog1 main1 e1 ->
  exists mrss, LsemD.exec_prog prog2 gc LsemD.eval_node main2 e2 1 maxn mass mrss
    /\ Lenv.vrets_matchss (nd_rets (snd main1)) vrss mrss.
Proof.
  induction 1; intros.
  +exists mrss. split; auto. constructor 1; auto.
  +generalize H1; intros C.
   eapply trans_node_correct in H1; eauto.
   destruct H1 as [e2' [m [A [A1 [A2 [A3 A4]]]]]].
   destruct IHexec_prog1 with e2' main2 i t ftl as [mrss [B B1]]; auto.
   exists (Cons (m::nil) mrss). split; auto.
   -constructor 2 with e2'; auto.
    unfold trans_node in H5. unfold func in *. rewrite H7, H8 in *.
    destruct (_ && _); inv H5. auto.
   -destruct (nd_rets (snd main1)) eqn:?.
    *constructor 2; auto.
    *constructor 1; simpl; auto. omega.
     rewrite <-Heqp in *.
     inv A2. destruct H6 as [l ?].
     constructor 1 with m; auto.
     apply vrets_match_match with nil l; simpl; auto.
     unfold func in *. congruence.
     apply ids_norepet_rets_norepet; auto.
     inv C; auto.
     red; intros; tauto.
     simpl. inv B1; auto.
     congruence.
Qed.

Lemma trans_program_node_fnil_general:
  forall main1 e1 maxn mass vrss,
  Lenv.exec_prog1 prog1 gc LsemE.eval_node main1 e1 1 maxn mass vrss ->
  forall eh1 se1, e1 = mkenv eh1 se1 ->
  find_funct (node_block prog1) (fst main1) = Some main1 ->
  nd_kind (snd main1) = true ->
  nd_fld (snd main1) = Fnil ->
  exists mrss, LsemD.exec_prog prog2 gc LsemD.eval_node main1 eh1 1 maxn mass mrss
    /\ Lenv.vrets_matchss (nd_rets (snd main1)) vrss mrss.
Proof.
  induction 1; intros.
  +exists mrss. split; auto. constructor 1; auto.
  +subst. generalize H1; intros C.
   destruct e' as [eh' se'].
   eapply trans_node_fnil_correct in H1; eauto.
   destruct IHexec_prog1 with eh' se' as [mrss [B B1]]; auto.
   cut (Streams.hd vrss = nil). intros A. rewrite A in *.
   exists (Cons nil mrss). split; auto.
   -constructor 2 with eh'; auto.
   -inv C. simpl in *. inv H14. constructor 2; auto.
   -inv C. simpl in *. rewrite H6 in *.
    apply svars_fld_match_fnil in H15.
    unfold func in *. unfold svarsof in *.
    apply app_eq_nil in H15. destruct H15. rewrite H3 in *.
    inv H14; auto.
Qed.

End NODE_CORRECT.

Lemma init_genvc_none:
  forall gc,
  init_genvc (const_block prog1) = Some gc ->
  gc ! OUTSTRUCT = None.
Proof.
  intros. eapply init_genvc_notin_none; eauto.
  apply ids_plt_le_notin with ACG_EQU; auto.
  unfold Ple, OUTSTRUCT, ACG_EQU. omega.
Qed.

Lemma env_match_node_match:
  forall (f1 f2: ident*func) e1 e2,
  env_match f1 e1 e2 ->
  node_match prog1 f1 f2 ->
  env_match f2 e1 e2.
Proof.
  intros. inv H. inv H0.
  constructor 1 with m; auto.
  +rewrite H1. unfold mknstruct.
   unfold func in *. congruence.
  +unfold func in *. congruence.
  +eapply env_struct_match_node_match; eauto.
   constructor 1; auto.
Qed.

Lemma initial_node_state_match:
  forall gc main1 e1 i t ftl,
  LsemE.initial_node_state prog1 gc main1 e1 ->
  nd_kind (snd main1) = true ->
  nd_fld (snd main1) = Fcons i t ftl ->
  exists main2 e2, LsemD.initial_state prog2 gc LsemD.eval_node main2 e2
    /\ env_match main1 e1 e2
    /\ find_funct (node_block prog1) (fst main1) = Some main1
    /\ trans_node main1 = OK main2
    /\ gc ! OUTSTRUCT = None
    /\ env_fld_match prog1 main1 e1.
Proof.
  intros. inv H.
  generalize trans_node_correct; intros A.
  monadInv TRANSL.
  generalize H3 H4; intros A1 A2.
  eapply find_funcs_monad_exits in H3; eauto.
  destruct H3 as [fi2 [A3 A4]].
  eapply find_funcs_monad_exits in H4; eauto.
  destruct H4 as [main2 [A5 A6]]. exists main2.
  assert(A8: gc ! OUTSTRUCT = None).
    apply init_genvc_none; auto.
  eapply alloc_node_correct in H7; eauto.
  destruct H7 as [e2 [B [B1 [B2 B3]]]].
  apply A with (e2:=e2) (fd':= fi2) (i:=i) (t:=t) (ftl:=ftl) in H8; auto.
  destruct H8 as [e2' [m [C [C1 [C2 [C3 C4]]]]]].
  exists e2'. repeat (split; auto).
  +unfold trans_node in *.
   inv H5. unfold func in *. rewrite H, H0, H1, H3 in *.
   destruct (zlt _ _), (zle _ _); inv A3. inv A5.
   constructor 1 with e2 (fst fi, trans_body (snd fi)) (Vmvl m::nil); auto.
   -simpl. unfold mknstruct. unfold func in *. congruence.
   -split; constructor; simpl; auto.
    constructor; simpl; auto.
    rewrite H1. simpl in *. auto.
  +apply env_match_node_match with fi; auto.
  +eapply find_funct_eq; eauto.
  +eapply env_fld_match_node_match; eauto.
  +apply env_match_node_match with main1; auto.
   apply node_match_sym; auto.
  +eapply find_funct_eq; eauto.
  +inv H5. unfold func in *. congruence.
  +inv H5. unfold func in *. congruence.
  +eapply env_fld_match_node_match; eauto.
   apply node_match_sym; auto.
  +eapply find_funct_eq; eauto.
  +unfold trans_node. intros.
   destruct (nd_kind (snd x0)); try congruence.
   destruct (nd_fld (snd x0)); try congruence.
   destruct (_ &&_ _) in H; inv H. auto.
  +unfold trans_node. intros.
   destruct (nd_kind (snd x0)); try congruence.
   destruct (nd_fld (snd x0)); try congruence.
   destruct (_ && _) in H; inv H. auto.
Qed.

Lemma initial_node_state_match_fnil:
  forall gc main1 eh1 se1,
  LsemE.initial_node_state prog1 gc main1 (mkenv eh1 se1) ->
  nd_kind (snd main1) = true ->
  nd_fld (snd main1) = Fnil ->
  LsemD.initial_state prog2 gc LsemD.eval_node main1 eh1
    /\ find_funct (node_block prog1) (fst main1) = Some main1.
Proof.
  intros. inv H.
  inv H5. unfold func in *. rewrite H0,H1 in *.
  generalize H3 H4; intros A1 A2.
  apply find_funct_node_eq in H3; auto.
  apply find_funct_node_eq in H4; auto.
  destruct e as [eh se].
  generalize H7; intros A3.
  eapply alloc_node_fnil_correct with (m:=nil) (i:=Int.zero) in H7; eauto.
  destruct H7 as [? [B1 [B2 B3]]]. subst.
  eapply trans_node_fnil_correct in H8; eauto.
  monadInv TRANSL; simpl in *. split.
  constructor 1 with empty_locenv fi nil; auto.
  +inv A3. simpl in *. rewrite H1 in *.
   apply svars_fld_match_fnil in H15.
   unfold func in *. unfold svarsof in *.
   apply app_eq_nil in H15. destruct H15. rewrite H7.
   inv H8. inv H21; auto.
  +inv A3. simpl in *. rewrite H1 in *.
   apply svars_fld_match_fnil in H15.
   unfold func in *. unfold svarsof in *.
   apply app_eq_nil in H15. destruct H15. rewrite H7.
   split; constructor. simpl; omega.
  +eapply find_funct_eq; eauto.
  +eapply find_funct_eq; eauto.
  +eapply find_funct_eq; eauto.
Qed.

Lemma trans_program_correct:
  forall gc main1 e1 maxn mass vrss,
  LsemE.initial_node_state prog1 gc main1 e1 ->
  Lenv.exec_prog1 prog1 gc LsemE.eval_node main1 e1 1 maxn mass vrss ->
  svars_field_match (nd_rets (snd main1)) (nd_fld (snd main1)) ->
  nd_kind (snd main1) = true ->
  exists mrss main2 e2, LsemD.initial_state prog2 gc LsemD.eval_node main2 e2
    /\ LsemD.exec_prog prog2 gc LsemD.eval_node main2 e2 1 maxn mass mrss
    /\ Lenv.vrets_matchss (nd_rets (snd main1)) vrss mrss.
Proof.
  intros.
  destruct (nd_fld (snd main1)) eqn:?.
  +destruct e1 as [eh1 se1].
   apply initial_node_state_match_fnil in H; auto. destruct H.
   eapply trans_program_node_fnil_general in H0; eauto.
   destruct H0 as [mrss [? ?]].
   exists mrss, main1, eh1. repeat (split; auto).
  +destruct initial_node_state_match with gc main1 e1 i t f
    as [main2 [e2 [A [A1 [A2 [A3 [A4 A5]]]]]]]; auto.
   eapply trans_program_node_general in H0; eauto.
   destruct H0 as [mrss [? ?]].
   exists mrss, main2, e2. repeat (split; auto).
   unfold func in *. congruence.
Qed.

End CORRECTNESS.
