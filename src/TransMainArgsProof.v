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
Require Import Inclusion.
Require Import Maps.
Require Import List.
Require Import ExtraList.
Require Import Lint.
Require Import Lident.
Require Import Lustre.
Require Import LustreR.
Require Import Lvalues.
Require Import Cltypes.
Require Import Ltypes.
Require Import Lenv.
Require Import Lsem.
Require Import Lenvmatch.
Require Import LsemR.
Require Import TransMainArgs.

Section CORRECTNESS.

Variable prog1 prog2: program.

Hypothesis TRANSL:
  trans_program prog1 = OK prog2.

Hypothesis NODES_TOPOSORT:
  topo_sorted (deps_of_nodes (node_block prog1)).

Hypothesis ID_RANGE:
  ids_range INSTRUCT (node_block prog1).

Hypothesis GID_RANGE:
  ids_plt ACG_EQU (globidspltof prog1).

Section NODE_CORRECT.

Variable gc: locenv.

Hypothesis GENV_NONE:
  gc ! INSTRUCT = None.

Lemma prog_simpl:
  forall main1, find_funct (node_block prog1) (node_main prog1) = Some main1 ->
  exists l1 l2 sty, prog1 = mkprog1 prog1 l1 l2 main1 nil
     /\ prog2 = mkprog1 prog1 l1 l2 (trans_node main1) sty
     /\ trans_sty (node_main prog1) (node_block prog1) = OK sty.
Proof.
  intros.
  destruct node_block_simpl with (node_block prog1) (node_main prog1) main1
    as [l1 [l2 [? ?]]]; auto.
  subst. unfold mkprog1.
  exists l1, l2. monadInv TRANSL.
  destruct (list_in_list _ _); inv EQ0.
  unfold trans_sty in *. rewrite H, H0 in *.
  destruct (beq_nat _ _) eqn:? ;monadInv EQ.
  -exists nil. destruct prog1.
   repeat split; simpl in *;f_equal; auto.
   apply app_nil_end; auto.
  -rewrite EQ0. simpl.
   exists (x0::nil). destruct prog1.
   repeat split; simpl in *;f_equal; auto.
   apply app_nil_end; auto.
Qed.

Definition args_env_match(id: ident)(ty: type)(delta: Z)(e1: locenv)(m: mvl): Prop :=
  exists mv, e1!id = Some (mv,ty)
    /\ loadbytes m (Int.unsigned (Int.repr delta)) (sizeof ty) = Some mv.

Definition args_struct_match(fld: fieldlist)(e1: locenv)(m: mvl) : Prop :=
  forall id delta,field_offset id fld = OK delta  ->
    exists ty, field_type id fld = OK ty
      /\ args_env_match id ty delta e1 m.

Definition vars_match (fld: fieldlist)(e1 e2: locenv) : Prop :=
  forall id msg, field_offset id fld = Error msg -> id <> INSTRUCT -> e1!id = e2!id.

Inductive locenv_match(fd: ident*node): locenv -> locenv -> Prop :=
  | locenv_match_intros: forall e1 e2 m,
      args_struct_match (fieldlist_of (nd_args (snd fd))) e1 m ->
      vars_match (fieldlist_of (nd_args (snd fd))) e1 e2 ->
      e1 ! INSTRUCT = None ->
      e2 ! INSTRUCT = Some (m,mkstruct fd) ->
      Z_of_nat (length m) = sizeof (mkstruct fd) ->
      locenv_disjoint gc e1 e2 ->
      locenv_match fd e1 e2.

Definition varg_from_struct(fld: fieldlist)(m: mvl)(a: ident*type)(v: val): Prop :=
  exists delta, field_offset (fst a) fld = OK delta
    /\ field_type (fst a) fld = OK (snd a)
    /\ load_argv (snd a) m (Int.repr delta) v.

Definition vargs_match(fld: fieldlist)(m: mvl)(al: list (ident*type))(vl: list val): Prop :=
  Forall2 (varg_from_struct fld m) al vl.

Inductive varg_fld_match(fld: fieldlist)(al: list (ident*type))(vl: list val): val -> Prop :=
  | varg_fld_match_: forall m,
      vargs_match fld m al vl ->
      Z_of_nat (length m) = sizeof_fld fld ->
      varg_fld_match fld al vl (Vmvl m).

Lemma locenv_match_eval_var1:
  forall t e1 id ofs k v,
  eval_var gc t e1 id ofs k v ->
  forall fd e2 msg, field_offset id (fieldlist_of (nd_args (snd fd))) = Error msg ->
  locenv_match fd e1 e2 ->
  eval_var gc t e2 id ofs k v.
Proof.
  induction 1; intros.
  +constructor 1; auto.
  +constructor 2; auto.
   destruct H as [m [t1 [? [? ?]]]].
   exists m, t1. split; auto. inv H1.
   unfold vars_match in *.
   rewrite <-H5 with id msg; auto.
   red. intros. subst. congruence.
Qed.

Lemma locenv_match_eval_var2:
  forall t e1 id ofs v,
  eval_var gc t e1 id ofs Lid v ->
  forall fd e2 delta ty m,
  field_offset id (fieldlist_of (nd_args (snd fd))) = OK delta ->
  field_type id (fieldlist_of (nd_args (snd fd))) = OK ty ->
  args_env_match id ty delta e1 m ->
  e2 ! INSTRUCT = Some (m, mkstruct fd) ->
  sizeof (mkstruct fd) = Z.of_nat (length m) ->
  (alignof t | alignof ty) ->
  sizeof (mkstruct fd) <= Int.max_signed ->
  eval_var gc t e2 INSTRUCT (Int.add (Int.repr delta) ofs) Lid v.
Proof.
  intros. inv H. constructor 2.
  destruct H7 as [m1 [t1 [? [? ?]]]].
  destruct H2 as [m2 [? ?]].
  rewrite H in H2. inv H2.
  exists m, (mkstruct fd). repeat (split; auto).
  eapply loadbytes_load_mvl_inv; eauto.
  erewrite field_offset_unsigned_repr; eauto.
  apply Zdivide_trans with (alignof ty); auto.
  eapply field_offset_aligned; eauto.
  generalize Int.max_signed_unsigned. intros.
  unfold sizeof_fld. simpl in *. unfold node in *. omega.
Qed.

Lemma locenv_match_eval_sexp:
forall e1,
(
  forall a v,
  eval_sexp gc e1 a v ->
  forall fd e2, locenv_match fd e1 e2 ->
  sizeof (mkstruct fd) <= Int.max_signed ->
  eval_sexp gc e2 (trans_expr (makevar fd) a) v
)
/\
(
  forall a id ofs k,
  eval_lvalue gc e1 a id ofs k ->
  forall fd e2, locenv_match fd e1 e2 ->
  sizeof (mkstruct fd) <= Int.max_signed ->
  match k with
  | Gid =>
    eval_lvalue gc e2 (trans_expr (makevar fd) a) id ofs Gid
  | Lid =>
    match field_offset id (fieldlist_of (nd_args (snd fd))) with
    | Error msg =>
      eval_lvalue gc e2 (trans_expr (makevar fd) a) id ofs Lid
    | OK ofs' =>
      eval_lvalue gc e2 (trans_expr (makevar fd) a) INSTRUCT (Int.add (Int.repr ofs') ofs)  Lid
    end
  | _ => False
  end
).
Proof.
  intros until e1.
  apply eval_sexp_lvalue_ind; intros; simpl.
  +apply eval_Sconst; auto.
  +apply eval_Sunop with v1; auto.
   rewrite trans_expr_typeof; auto.
  +apply eval_Sbinop with v1 v2; auto;
   repeat rewrite trans_expr_typeof; auto.
  +apply eval_Scast with v1; auto.
   rewrite trans_expr_typeof; auto.
  +generalize H3; intros A.
   apply H0 in A; auto. destruct k; try tauto.
   -apply eval_Rlvalue with id ofs Gid; auto;
    rewrite trans_expr_typeof; auto.
    inv H1. constructor 1; auto.
   -destruct (field_offset _ _) eqn:?.
    *apply eval_Rlvalue with INSTRUCT (Int.add (Int.repr z) ofs) Lid; auto;
     rewrite trans_expr_typeof; auto.
     inv H3. unfold args_struct_match in *.
     destruct H5 with id z as [ty [? ?]]; auto.
     eapply locenv_match_eval_var2; eauto.
     destruct H11 as [? [? ?]].
     eapply eval_lvalue_some_alignof; eauto.
    *apply eval_Rlvalue with id ofs Lid; auto;
     rewrite trans_expr_typeof; auto.
     eapply locenv_match_eval_var1; eauto.
  +destruct (field_offset _ _) eqn:?.
   -unfold makevar, trans_v.
    rewrite field_offset_in_list_true with _ _ z; auto.
    rewrite Int.add_commut.
    destruct H0. destruct H0 with id z as [ty1 [? ?]]; auto.
    destruct H8 as [m1 [? ?]].
    apply eval_Sfield with (in_struct_type (fst fd)) (fieldlist_of (nd_args (snd fd))); auto.
    apply eval_Svar with m0; auto.
    congruence.
   -unfold makevar, trans_v.
    rewrite field_offset_in_list_false with _ _ e; auto.
    apply eval_Svar with m; auto.
    destruct H0. erewrite <- H2; eauto. congruence.
  +unfold makevar, trans_v. destruct (in_list _ _) eqn:?.
   -inv H1. red in H3.
    apply in_list_field_offset_exists in Heqb. destruct Heqb.
    destruct H3 with id x as [? [? [? [? ?]]]]; auto.
    congruence.
   -apply eval_Scvar with m; auto.
    inv H1. apply H8 with (m,ty); auto.
  +generalize H6; intros A. apply H0 in A; auto.
   destruct vk; try tauto.
   -apply eval_Saryacc with aid z; eauto;
    rewrite trans_expr_typeof; auto.
   -destruct (field_offset _ _) eqn:?.
    *rewrite <-Int.add_assoc.
     apply eval_Saryacc with aid z; auto.
     rewrite trans_expr_typeof; auto.
     inv H6. apply eval_lvalue_eval_offset with (m:=m) (ty:=mkstruct fd) in A; auto.
     apply A in H11. apply eval_offset_pos in H11. omega.
    *apply eval_Saryacc with aid z; auto;
     rewrite trans_expr_typeof; auto.
  +generalize H5; intros A. apply H0 in A; auto.
   destruct vk; try tauto.
   -apply eval_Sfield with sid fld; auto;
    rewrite trans_expr_typeof; auto.
   -destruct (field_offset l _) eqn:?.
    *rewrite <-Int.add_assoc.
     apply eval_Sfield with sid fld; auto.
     rewrite trans_expr_typeof; auto.
     inv H5. apply eval_lvalue_eval_offset with (m:=m) (ty:=mkstruct fd) in A; auto.
     apply A in H10. apply eval_offset_pos in H10. omega.
    *apply eval_Sfield with sid fld; auto;
     rewrite trans_expr_typeof; auto.
Qed.

Lemma locenv_match_eval_sexps:
  forall e1 al vl,
  eval_sexps gc e1 al vl ->
  forall fd e2, locenv_match fd e1 e2 ->
  sizeof (mkstruct fd) <= Int.max_signed ->
  eval_sexps gc e2 (trans_exprs (makevar fd) al) vl.
Proof.
  induction 1; simpl; intros.
  +constructor.
  +constructor 2; auto.
   eapply locenv_match_eval_sexp; eauto.
   eapply IHForall2; eauto.
Qed.

Lemma locenv_match_set_args:
  forall fd e1 e2 b z ty m mv m' mv' t ofs v,
  locenv_match fd e1 e2 ->
  field_offset b (fieldlist_of (nd_args (snd fd))) = OK z ->
  field_type b (fieldlist_of (nd_args (snd fd))) = OK ty ->
  loadbytes m' (Int.unsigned (Int.repr z)) (sizeof ty) = Some mv'->
  e1 ! b = Some (mv,ty) ->
  e2 ! INSTRUCT = Some (m,mkstruct fd) ->
  store_mvl t mv ofs v mv' ->
  store_mvl t m (Int.add (Int.repr z) ofs) v m' ->
  sizeof (mkstruct fd) <= Int.max_signed ->
  locenv_match fd (PTree.set b (mv',ty) e1) (PTree.set INSTRUCT (m',mkstruct fd) e2).
Proof.
  intros. inv H. constructor 1 with m'; auto.
  +red; intros. generalize H; intros A.
   apply H8 in H.
   destruct H as [t1 [? ?]].
   exists t1. split; auto.
   generalize (sizeof_pos t1) (sizeof_pos ty) (sizeof_pos t) Int.max_signed_unsigned;
   intros A4 A5 A6 A7.
   destruct H14 as [m1 [? ?]].
   rewrite H11 in *. inv H4.
   -compare b id; intros; subst.
    *rewrite H14 in *. inv H3.
     exists mv'; split; auto.
     rewrite PTree.gss; auto.
     rewrite H0, H1 in *. inv H. inv A. auto.
    *exists m1. rewrite PTree.gso; auto. split; auto.
     rewrite <-H15.
     apply loadbytes_store_mvl_other with t (Int.add (Int.repr z) ofs) v; auto.
     generalize H0; intros A1.
      eapply field_offset_in_range with (sid:=xH) in A1; eauto.
      eapply field_offset_no_overlap in H0; eauto.
      eapply field_offset_in_range with (sid:=xH) in A; eauto.
      simpl in A, A1. unfold mkstruct in *. simpl sizeof in *.
      destruct A1 as [A2 A3]. destruct A as [A A1].
      rewrite Int.add_unsigned in *.
      assert (A8: (Int.unsigned (Int.repr z) = z)).
       rewrite Int.unsigned_repr;try omega.
      rewrite A8 in *.
      assert(A9: Int.unsigned ofs + sizeof t <= sizeof ty).
        generalize H5; intros A9.
        apply store_mvl_range_perm in H5. red in H5.
        apply loadbytes_length in H2.
        rewrite <-H2 in H5.
        rewrite nat_of_Z_eq in H5; try omega.
      rewrite Int.unsigned_repr;try omega.
      generalize (Int.unsigned_range_2 ofs); intros.
      repeat rewrite Int.unsigned_repr; try omega.
  +red. intros.
   compare id b; intros; subst; try congruence.
   apply H9 in H.
   repeat rewrite PTree.gso; auto.
  +rewrite PTree.gso; auto.
   red; intros; subst. congruence.
  +rewrite PTree.gss; auto.
  +apply store_mvl_length in H6. congruence.
  +apply locenv_disjoint_set_left.
   apply locenv_disjoint_set_right; auto.
Qed.

Lemma locenv_match_set_other:
  forall fd e1 e2 b msg m m',
  locenv_match fd e1 e2 ->
  field_offset b (fieldlist_of (nd_args (snd fd))) = Error msg ->
  e1 ! b = Some m ->
  locenv_match fd (PTree.set b m' e1) (PTree.set b m' e2).
Proof.
  intros. inv H. constructor 1 with m0; auto.
  +unfold args_struct_match in *. intros.
   compare id b; intros.
   -subst. congruence.
   -apply H2 in H. destruct H as [ty [? ?]].
    exists ty. split; auto.
    destruct H8 as [m1 [? ?]].
    exists m1. rewrite PTree.gso; auto.
  +red; intros. apply H3 in H.
   compare id b; intros.
   -subst. repeat rewrite PTree.gss; auto.
   -repeat rewrite PTree.gso; auto.
  +rewrite PTree.gso; auto.
   red; intros. subst. congruence.
  +rewrite PTree.gso; auto.
   red; intros. subst. congruence.
  +apply locenv_disjoint_set_same; auto.
Qed.

Lemma locenv_match_setlvar_exists:
  forall eh1 lh v eh1',
  locenv_setlvar gc eh1 lh v eh1' ->
  forall fd eh2, locenv_match fd eh1 eh2 ->
  sizeof (mkstruct fd) <= Int.max_signed ->
  exists eh2',locenv_setlvar gc eh2 (trans_expr (makevar fd) lh) v eh2'
    /\ locenv_match fd eh1' eh2'.
Proof.
  induction 1; intros.
  generalize H; intros A.
  eapply locenv_match_eval_sexp in H; eauto.
  destruct (field_offset _ _) eqn:?.
  +generalize H1. intros A1.
   inv H1. unfold args_struct_match in *.
   destruct H3 with b z as [ty [? ?]]; auto.
   inv H0. destruct H9 as [m1 [? ?]].
   rewrite H10 in H0. inv H0.
   destruct loadbytes_store_mvl_exists
     with (typeof var) m1 ofs v m' m (Int.repr z) (sizeof ty)
     as [m0' [? ?]]; auto.
     apply Zdivide_trans with (alignof ty).
     eapply eval_lvalue_some_alignof; eauto.
     erewrite field_offset_unsigned_repr; eauto.
     eapply field_offset_aligned; eauto.
     apply Zle_trans with Int.max_signed; auto.
     generalize Int.max_signed_unsigned. omega.
   exists (PTree.set INSTRUCT (m0',mkstruct fd)  eh2). split.
   -constructor 1 with INSTRUCT (Int.add (Int.repr z) ofs); auto.
    constructor 1 with m; auto.
    rewrite trans_expr_typeof; auto.
   -eapply locenv_match_set_args; eauto.
  +inv H0. exists (PTree.set b (m',t) eh2). split.
   -constructor 1 with b ofs; auto.
    rewrite trans_expr_typeof; auto.
    constructor 1 with m; auto.
    inv H1. rewrite <-H6 with _ e0; auto.
    red; intros; subst. congruence.
   -eapply locenv_match_set_other; eauto.
Qed.

Lemma trans_expr_lid_disjoint:
  forall lhs (fd: ident*node),
  lid_disjoint lhs ->
  ~ In ACG_I (map fst (nd_args (snd fd))) ->
  lid_disjoint (trans_expr (makevar fd) lhs).
Proof.
  induction lhs; simpl; intros; auto.
  +unfold makevar, trans_v.
   destruct (in_list _ _); simpl; auto.
   unfold INSTRUCT, ACG_I. congruence.
  +destruct lhs2; auto. destruct H; subst.
   generalize H0. intros.
   apply in_list_false_notin in H0; auto.
   unfold makevar. unfold trans_v. simpl. rewrite H0.
   eapply IHlhs1 in H; eauto.
Qed.

Lemma trans_exprs_lid_disjoint:
  forall l (fd: ident*node),
  Forall (lid_disjoint) l ->
  ~ In ACG_I (map fst (nd_args (snd fd))) ->
  Forall (lid_disjoint) (trans_exprs (makevar fd) l).
Proof.
  induction 1; simpl; intros; auto.
  constructor 2; auto.
  apply trans_expr_lid_disjoint; auto.
Qed.

Lemma locenv_match_setlvars_exists:
  forall eh1 lhs vrets eh1',
  locenv_setlvars gc eh1 lhs vrets eh1' ->
  forall fd eh2, locenv_match fd eh1 eh2 ->
  sizeof (mkstruct fd) <= Int.max_signed  ->
  ~ In ACG_I (map fst (nd_args (snd fd))) ->
  exists eh2',locenv_setlvars gc eh2 (trans_exprs (makevar fd) lhs) vrets eh2'
    /\ locenv_match fd eh1' eh2'.
Proof.
  induction 1; intros.
  +exists eh2. split; auto. constructor.
  +eapply locenv_match_setlvar_exists in H; eauto.
   destruct H as [eh21 [? ?]].
   destruct IHlocenv_setlvars with fd eh21 as [eh2' [? ?]]; auto.
   exists eh2'; split; auto.
   constructor 2 with eh21; auto.
Qed.

Lemma load_loopid_locenv_match:
  forall e1 oid oj i,
  load_loopid gc e1 oid oj i ->
  forall fd e2, ~ In ACG_I (map fst (nd_args (snd fd))) ->
  locenv_match fd e1 e2 ->
  sizeof (mkstruct fd) <= Int.max_signed  ->
  load_loopid gc e2 oid oj i.
Proof.
  intros. inv H; simpl.
  constructor 1.
  eapply locenv_match_eval_sexp in H3; eauto.
  unfold makevar, trans_v in *. simpl in H3.
  apply in_list_false_notin in H0.
  unfold node in *. rewrite H0 in H3; auto.
  constructor 2.
Qed.

Lemma node_ids_instruct_notin:
  ~ In INSTRUCT (flat_map filter_type (type_block prog1) ++ (map fst (node_block prog1))).
Proof.
  apply ids_plt_le_notin with ACG_EQU; auto.
  unfold Ple, INSTRUCT,ACG_EQU. omega.
  red; intros. apply GID_RANGE.
  apply in_or_app. auto.
Qed.

Lemma alloc_variables_exists_rec:
  forall e fd e1',
  alloc_variables e (nd_args (snd fd)) e1' ->
  ~ In INSTRUCT (map fst (nd_args (snd fd))) ->
  e ! INSTRUCT = None ->
  list_norepet (map fst (nd_args (snd fd))) ->
  sizeof (mkstruct fd) <= Int.max_signed ->
  (forall id ty, In (id, ty) (nd_args (snd fd)) -> 0 < sizeof ty) ->
  exists e2', alloc_variables e ((INSTRUCT,mkstruct fd):: nil) e2'
    /\ locenv_match fd e1' e2'.
Proof.
  intros.
  exists (PTree.set INSTRUCT (alloc (sizeof (mkstruct fd)),(mkstruct fd)) e). split.
  +constructor 2. constructor.
  +constructor 1 with (alloc (sizeof (mkstruct fd))); auto.
   -red. intros.
    destruct field_offset_type_exists with (fieldlist_of (nd_args (snd fd))) id delta as [ty ?]; auto.
    exists ty; split; auto.
    cut (0 < sizeof ty). intros A.
    generalize Int.max_signed_unsigned; intros A1.
    constructor 1 with (alloc (sizeof ty)); split; auto.
    *eapply alloc_variables_norepeat_in_eq; eauto.
     eapply fieldlist_list_in; eauto.
    *unfold mkstruct in *. simpl sizeof in *.
     apply loadbytes_alloc; auto; try omega.
     eapply field_offset_in_range with (sid:=xH) in H5; eauto.
     simpl in H5. split; auto.
      apply Zle_trans with (delta+sizeof ty); try omega.
      rewrite Int.unsigned_repr; try omega.
      apply Int.unsigned_range; auto.
    *apply H4 with id. apply fieldlist_list_in; auto.
   -red. intros. rewrite PTree.gso; auto.
    eapply alloc_variables_notin_eq; eauto.
    eapply fieldlist_list_notin; eauto.
   -rewrite alloc_variables_notin_eq with (e:=e) (al:=nd_args (snd fd)); auto.
   -rewrite PTree.gss; auto.
   -unfold alloc. rewrite length_list_repeat.
    rewrite nat_of_Z_eq; auto.
    generalize (sizeof_pos (mkstruct fd)); omega.
   -apply locenv_disjoint_set_right; auto.
    eapply alloc_variables_locenv_disjoint; eauto.
    red; intros; auto.
Qed.

Lemma alloc_variables_match_set:
  forall e1 l e1',
  alloc_variables e1 l e1' ->
  forall fd e2, list_disjoint (map fst (nd_args (snd fd))) (map fst l) ->
  ~ In INSTRUCT (map fst l) ->
  locenv_match fd e1 e2 ->
  exists e2', alloc_variables e2 l e2'
    /\ locenv_match fd e1' e2'.
Proof.
  induction 1; simpl; intros.
  +exists e2; split; auto. constructor.
  +destruct IHalloc_variables with fd (PTree.set id (alloc (sizeof ty),ty) e0) as [e2' [? ?]]; auto.
   -red; intros. apply H0; simpl; auto.
   -inv H2. constructor 1 with m; auto.
    *red; intros. generalize H2; intros. apply H3 in H2.
     destruct H2 as [ty0 [? ?]].
     exists ty0. split; auto.
     apply fieldlist_list_id_in in H9.
     destruct H10 as [m1 [? ?]].
     constructor 1 with m1; auto.
      rewrite PTree.gso; auto.
      apply H0; simpl; auto.
    *red; intros. compare id id0; intros.
     subst. repeat rewrite PTree.gss; auto.
     repeat rewrite PTree.gso; eauto.
    *rewrite PTree.gso; auto.
    *rewrite PTree.gso; auto.
    *apply locenv_disjoint_set_same; auto.
   -exists e2'; split; auto.
    constructor; auto.
Qed.

Lemma alloc_variables_exists:
  forall f e1,
  alloc_variables empty_locenv (allvarsof f) e1 ->
  forall fid, ~ In INSTRUCT (allidsof f ++ predidof f) ->
  ids_norepet f ->
  sizeof_fld (fieldlist_of (nd_args f)) <= Int.max_signed ->
  (forall id ty, In (id, ty) (nd_args f) -> 0 < sizeof ty) ->
  exists e2, alloc_variables empty_locenv (allvarsof (trans_body (fid,f))) e2
    /\ locenv_match (fid,f) e1 e2
    /\ exists m, e2 ! INSTRUCT = Some (m,mkstruct (fid,f))
    /\ Z.of_nat (length m) = sizeof (mkstruct (fid,f))
    /\ (forall id ty, In (id, ty) (nd_args f) ->
          exists mv : mvl, e1 ! id = Some (mv,ty)
           /\ Z.of_nat (length mv) = sizeof ty).
Proof.
  unfold ids_norepet, trans_body, allidsof, allvarsof.
  simpl nd_vars. simpl nd_args. simpl nd_rets. intros.
  rewrite <-app_assoc in *. repeat rewrite map_app in *.
  generalize H; intros A5.
  apply alloc_variables_app in H.
  destruct H as [e [A A1]].
  apply alloc_variables_app in A1.
  destruct A1 as [e0 [A1 A2]].
  apply not_in_app in H0. destruct H0. apply not_in_app in H. destruct H.
  apply not_in_app in H4. destruct H4.
  destruct H1 as [? [? ?]].
  generalize H1; intros A4.
  apply list_norepet_app in H1. destruct H1 as [? [? ?]].
  apply list_norepet_app in H8. destruct H8 as [? [? ?]].
  assert(A3: e ! INSTRUCT = None ).
    erewrite alloc_variables_notin_eq with (e:=empty_locenv); eauto.
  change f with (snd (fid, f)) in A1.
  apply alloc_variables_exists_rec with _ _ _ in A1; auto.
  destruct A1 as [e0' [? ?]].
  apply alloc_variables_match_set with _ _ _ (fid,f) e0' in A2; auto.
  destruct A2 as [e2' [? ?]]; auto.
  exists e2'. split; [| split]; auto.
  apply alloc_variables_trans with e; auto.
  apply alloc_variables_trans with e0'; auto.

  exists (alloc (sizeof (mkstruct (fid,f)))). split.
  erewrite alloc_variables_notin_eq; eauto.
  inv H12. inv H21. rewrite PTree.gss; auto.

  split. unfold alloc. rewrite length_list_repeat.
  rewrite nat_of_Z_eq; auto.
  generalize (sizeof_pos (mkstruct (fid,f))); omega.

  intros. exists (alloc (sizeof ty)). split.
  eapply alloc_variables_norepeat_in_eq in A5; eauto.
  apply in_or_app; right. apply in_or_app; auto.
  repeat rewrite map_app in *. auto.
  unfold alloc. rewrite length_list_repeat.
  rewrite nat_of_Z_eq; auto.
  generalize (sizeof_pos ty); omega.
Qed.

Lemma locenv_setvars_vargs_match_loadbytes_exists:
  forall e al vas e',
  locenv_setvars e al vas e' ->
  forall fld m id delta ty mv, vargs_match fld m al vas ->
  field_offset id fld = OK delta ->
  In (id,ty) al ->
  list_norepet (map fst al) ->
  e ! id = Some (mv,ty) ->
  Z_of_nat (length mv) = sizeof ty ->
  exists mv', e' ! id = Some (mv',ty)
    /\ loadbytes m (Int.unsigned (Int.repr delta)) (sizeof ty) = Some mv'.
Proof.
  induction 1; simpl; intros.
  +inv H1.
  +inv H2. inv H5.
   destruct H4.
   -inv H2. destruct H11 as [delta1 [? [? ?]]].
    simpl in *. rewrite H2 in H3. inv H3.
    inv H0. rewrite H3 in H6. inv H6.
    exists m'; split; auto.
    eapply set_new_vars_getid_eq in H1; eauto.
     rewrite H1. rewrite PTree.gss; auto.
    eapply load_argv_loadbytes_app in H5; eauto.
    rewrite <-H7. rewrite nat_of_Z_of_nat. auto.
   -simpl in *. eapply IHlocenv_setvars; eauto.
    inv H0. rewrite PTree.gso; auto.
    red; intros. subst. apply H9; auto.
    change id with (fst (id,ty0)).
    apply in_map; auto.
Qed.

Lemma locenv_match_setvar_exists:
  forall e1 vas1 e1' fid f,
  locenv_setvars e1 (nd_args f) vas1 e1' ->
  forall e2 v2 m, locenv_match (fid,f) e1 e2 ->
  varg_fld_match (fieldlist_of (nd_args f)) (nd_args f) vas1 v2 ->
  e2 ! INSTRUCT = Some (m,mkstruct (fid,f)) ->
  ~ In INSTRUCT (allidsof f ++ predidof f) ->
  Z_of_nat (length m) = sizeof (mkstruct (fid,f)) ->
  0 < sizeof (mkstruct (fid,f))  <= Int.max_signed ->
  ids_norepet f ->
  (forall id ty, In (id,ty) (nd_args f) ->
    exists mv,  e1 ! id = Some (mv,ty) /\ Z_of_nat (length mv) = sizeof ty) ->
  exists e2', locenv_setvars e2 (nd_args (trans_body (fid,f))) (v2::nil) e2'
    /\ locenv_match (fid,f) e1' e2'.
Proof.
  unfold ids_norepet, trans_body, allidsof, allvarsof.
  simpl nd_args. intros.
  rewrite <-app_assoc in *. repeat rewrite map_app in *.
  apply not_in_app in H3. destruct H3. apply not_in_app in H3. destruct H3.
  apply not_in_app in H9. destruct H9.
  destruct H6 as [? [? ?]].
  apply list_norepet_app in H6. destruct H6 as [? [? ?]].
  apply list_norepet_app in H13. destruct H13 as [? [? ?]].
  inv H1.
  exists (PTree.set INSTRUCT (m0,mkstruct (fid,f)) e2).
  inv H0. generalize (sizeof_pos (mkstruct (fid,f))); intros. split.
  +constructor 2 with (PTree.set INSTRUCT (m0,mkstruct (fid,f)) e2) m1; auto.
   -exists m; auto.
    unfold sizeof_fld in *.
    constructor 2; auto.
    rewrite Int.unsigned_zero.
    simpl in H4, H0, H5. rewrite <-H4 in *.
    generalize Int.max_signed_unsigned; intros.
    apply storebytes_full; try omega.
    rewrite Int.unsigned_zero. exists 0. omega.
   -constructor.
  +constructor 1 with m0; auto.
   -red. intros.
    destruct field_offset_type_exists with (fieldlist_of (nd_args f)) id delta as [ty ?]; auto.
    exists ty; split; auto.
    assert (In (id,ty) (nd_args f)).
      eapply fieldlist_list_in; eauto.
    destruct H7 with id ty as [mv [? ?]]; auto.
    eapply locenv_setvars_vargs_match_loadbytes_exists with (fld:=fieldlist_of (nd_args f)) (m:=m0) (mv:=mv) in H; eauto.
   -red. intros. rewrite PTree.gso; auto.
    rewrite <-H19 with _ msg; auto.
    eapply set_new_vars_getid_eq; eauto.
    eapply fieldlist_list_notin; eauto.
   -erewrite set_new_vars_getid_eq with (eh:=e1); eauto.
   -rewrite PTree.gss; auto.
   -apply locenv_disjoint_set_right; auto.
    eapply locenv_setvars_locenv_disjoint; eauto.
Qed.

Lemma locenv_match_getvars:
  forall e1 l vrs e2,
  locenv_getvars e1 l vrs ->
  forall fd,list_disjoint (map fst (nd_args (snd fd))) (map fst l) ->
  ~ In INSTRUCT  (map fst l) ->
  locenv_match fd e1 e2 ->
  locenv_getvars e2 l vrs.
Proof.
  induction 1; simpl; intros.
  +constructor 1.
  +constructor 2.
   -inv H3. destruct H as [m1 [? [? ?]]].
    exists m1. split; auto.
    destruct fieldlist_list_notin_inv with (nd_args (snd fd)) (fst x) 0 as [msg ?]; auto.
     red; intros. red in H1. eapply H1 in H11; simpl; eauto.
    rewrite <-H5 with _ msg; auto.
   -apply IHForall2 with fd; auto.
    red; intros. apply H1; simpl; auto.
Qed.

Lemma eval_lvaule_args_env_match_range_perm:
  forall e a id o m fd z ty,
  eval_lvalue gc e a id o Lid ->
  args_env_match id ty z e m ->
  field_type id (fieldlist_of (nd_args (snd fd))) = OK ty ->
  field_offset id (fieldlist_of (nd_args (snd fd))) = OK z ->
  sizeof (mkstruct fd) <= Int.max_signed ->
  Int.unsigned (Int.add (Int.repr z) o) = z + Int.unsigned o
    /\ Int.unsigned o + sizeof (typeof a) <= sizeof ty.
Proof.
  intros. generalize Int.max_signed_unsigned. intros.
  destruct H0 as [mv1 [? ?]].
  eapply eval_lvalue_eval_offset in H; eauto.
  eapply eval_offset_pos in H; eauto.
  rewrite Int.add_commut. rewrite <-repr_add_int_r.
  erewrite field_offset_unsigned_repr in H5; eauto.
  apply loadbytes_range_perm in H5. red in H5.
  generalize (sizeof_pos (typeof a)); intros.
  rewrite Int.unsigned_repr; try omega.
  unfold mkstruct, sizeof_fld in *. simpl in *.
  unfold node in *. omega.
Qed.

Lemma lvalue_disjoint_locenv_match:
  forall e1 e2 a1 a2 fd,
  lvalue_disjoint (eval_lvalue gc e1) a1 a2 ->
  locenv_match fd e1 e2 ->
  sizeof (mkstruct fd) <= Int.max_signed ->
  lvalue_disjoint (eval_lvalue gc e2) (trans_expr (makevar fd) a1) (trans_expr (makevar fd) a2).
Proof.
  intros. inv H.
  generalize H2 H3 H0. intros A A1 A2. inv H0.
  eapply locenv_match_eval_sexp in A; eauto.
  eapply locenv_match_eval_sexp in A1; eauto.
  destruct k1, H4; try congruence; try tauto.
  destruct k2; try tauto;
  destruct (field_offset id1 _) eqn:?.
  +econstructor 1; try rewrite trans_expr_typeof; eauto.
   left. apply eval_lvalue_env_some in H3; auto. destruct H3. congruence.
  +econstructor 1; try repeat rewrite trans_expr_typeof; eauto.
  +destruct (field_offset id2 _) eqn:?;
   econstructor 1; try repeat rewrite trans_expr_typeof; eauto.
   -right. destruct H with id1 z as [ty1 [B1 B2]]; auto.
    destruct H with id2 z0 as [ty2 [B3 B4]]; auto.
    eapply eval_lvaule_args_env_match_range_perm in B2; eauto.
    eapply eval_lvaule_args_env_match_range_perm with (a:=a2) in B4; eauto.
    destruct B2 as [B2 ?]. destruct B4 as [B4 ?].
    rewrite B2, B4.
    compare id1 id2; intros; subst.
    *rewrite Heqr in Heqr0. inv Heqr0.
     destruct H5; try congruence. omega.
    *eapply field_offset_no_overlap in B1; eauto.
     generalize (Int.unsigned_range o1) (Int.unsigned_range o2); intros.
     destruct B1; [right | left]; try omega.
   -left. apply eval_lvalue_env_some in H3; auto. destruct H3. congruence.
  +destruct (field_offset id2 _) eqn:?;
   econstructor 1; try repeat rewrite trans_expr_typeof; eauto.
   left. apply eval_lvalue_env_some in H2; auto. destruct H2. congruence.
Qed.

Lemma assign_disjoint_locenv_match:
  forall e1 e2 a1 a2 fd,
  assign_disjoint (eval_lvalue gc e1) a1 a2 ->
  locenv_match fd e1 e2 ->
  sizeof (mkstruct fd) <= Int.max_signed ->
  assign_disjoint (eval_lvalue gc e2) (trans_expr (makevar fd) a1) (trans_expr (makevar fd) a2).
Proof.
  intros. inv H.
  +constructor 1 with chunk; auto.
   rewrite trans_expr_typeof; auto.
  +constructor; auto. rewrite trans_expr_typeof; auto.
   eapply lvalue_disjoint_locenv_match; eauto.
Qed.

Lemma locenv_match_eval_eqf:
  forall eh1 eh1' a1,
  eval_eqf gc eh1 eh1' a1 ->
  forall fd eh2, locenv_match fd eh1 eh2 ->
  sizeof (mkstruct fd) <= Int.max_signed ->
  exists eh2', eval_eqf gc eh2 eh2' (trans_eqf (makevar fd) a1)
    /\ locenv_match fd eh1' eh2'.
Proof.
  induction 1; intros.
  generalize H2; intros A.
  eapply locenv_match_setlvar_exists in H2; eauto.
  destruct H2 as [eh2' [? ?]].
  exists eh2'. split; auto.
  apply locenv_setlvar_getmvl_exists in A.
  destruct A as [mv ?].
  constructor 1 with v v'; simpl; auto.
  eapply locenv_match_eval_sexp; eauto.
  repeat rewrite trans_expr_typeof; auto.
  rewrite trans_expr_typeof; auto.
  eapply assign_disjoint_locenv_match; eauto.
Qed.

Lemma locenv_getmvl_match:
  forall e1 lh v,
  locenv_getmvl gc e1 lh v ->
  forall e2 fd,
  locenv_match fd e1 e2 ->
  sizeof (mkstruct fd) <= Int.max_signed ->
  locenv_getmvl gc e2 (trans_expr (makevar fd) lh) v.
Proof.
  intros. inv H.
  eapply locenv_match_eval_sexp in H1; eauto.
  destruct (field_offset _ _) eqn:?.
  -destruct H0. destruct H with id z as [ty [? ?]]; auto.
   destruct H10 as [m1 [? ?]].
   constructor 1 with INSTRUCT (Int.add (Int.repr z) ofs) m0 (mkstruct fd); auto.
   eapply loadbytes_loadbytes_app; eauto.
   rewrite trans_expr_typeof; auto. congruence.
  -destruct H0. constructor 1 with id ofs m t; auto.
   rewrite <-H0 with id e; auto.
   red; intros. subst. congruence.
   rewrite trans_expr_typeof; auto.
Qed.

Lemma locenv_getmvls_match:
  forall e1 lhs vl,
  locenv_getmvls gc e1 lhs vl ->
  forall e2 fd,
  locenv_match fd e1 e2 ->
  sizeof (mkstruct fd) <= Int.max_signed ->
  locenv_getmvls gc e2 (trans_exprs (makevar fd) lhs) vl.
Proof.
  induction 1; simpl; intros.
  +constructor.
  +simpl. constructor 2; auto.
   eapply locenv_getmvl_match; eauto.
   eapply IHForall2; eauto.
Qed.

Lemma assign_list_disjoint_match:
  forall e1 lhs args,
  assign_list_disjoint (eval_lvalue gc e1) lhs args ->
  forall fd e2,
  locenv_match fd e1 e2 ->
  sizeof (mkstruct fd) <= Int.max_signed ->
  assign_list_disjoint (eval_lvalue gc e2) (trans_exprs (makevar fd) lhs) (trans_exprs (makevar fd) args).
Proof.
  unfold trans_exprs. intros. red; intros.
  apply in_map_iff in H2. destruct H2 as [? [? ?]].
  apply in_map_iff in H3. destruct H3 as [? [? ?]].
  subst. apply in_split in H4. destruct H4 as [? [? ?]]. subst.
  apply in_split in H5. destruct H5 as [? [? ?]]. subst.
  eapply assign_disjoint_locenv_match; eauto.
  apply H; apply in_or_app; simpl; auto.
Qed.

Lemma lvalue_list_norepet_match:
  forall e1 l,
  lvalue_list_norepet (eval_lvalue gc e1) l ->
  forall fd e2,
  locenv_match fd e1 e2 ->
  sizeof (mkstruct fd) <= Int.max_signed ->
  lvalue_list_norepet (eval_lvalue gc e2) (trans_exprs (makevar fd) l).
Proof.
  induction 1; intros.
  +constructor.
  +simpl. constructor 2; eauto.
   unfold trans_exprs. red; intros.
   apply in_map_iff in H3. destruct H3 as [? [? ?]]. subst.
   apply in_split in H4. destruct H4 as [? [? ?]]. subst.
   eapply lvalue_disjoint_locenv_match; eauto.
   apply H. apply in_or_app; simpl; auto.
Qed.

Lemma locenv_match_ptree_id_none:
  forall fd te1 te2 id,
  locenv_match fd te1 te2 ->
  id <> INSTRUCT ->
  te1 ! id = None ->
  te2 ! id = None.
Proof.
  intros. inv H.
  destruct (field_offset id (fieldlist_of (nd_args (snd fd)))) eqn:?.
  +apply H2 in Heqr. destruct Heqr as [? [? [? [? ?]]]].
   congruence.
  +erewrite <-H3; eauto.
Qed.

Lemma eval_typecmp_trans:
  forall fd te1 te2 a1 a2 b,
  eval_typecmp gc (type_block prog1) te1 a1 a2 b ->
  locenv_match fd te1 te2 ->
  sizeof (mkstruct fd) <= Int.max_signed ->
  eval_typecmp gc (type_block prog1) te2 (trans_expr (makevar fd) a1) (trans_expr (makevar fd) a2) b.
Proof.
  intros until te2.
  induction 1 using eval_typecmp_ind2 with
  ( P0 := fun a1 a2 num aty i b =>
      locenv_match fd te1 te2 ->
      sizeof (mkstruct fd) <= Int.max_signed ->
      eval_arycmp gc (type_block prog1) te2 (trans_expr (makevar fd) a1) (trans_expr (makevar fd) a2) num aty i b)
  ( P1 := fun a1 a2 fld ftl b =>
      locenv_match fd te1 te2 ->
      sizeof (mkstruct fd) <= Int.max_signed ->
      eval_strcmp gc (type_block prog1) te2 (trans_expr (makevar fd) a1) (trans_expr (makevar fd) a2) fld ftl b);
  intros; try (econstructor; eauto; fail).
 +eapply eval_typecmp_chunk with chunk v; eauto;
  repeat rewrite trans_expr_typeof; auto.
  eapply locenv_match_eval_sexp in H1; eauto.
 +apply eval_typecmp_array with aid aty num v1 v2; auto;
  try (repeat rewrite trans_expr_typeof; auto;
    eapply locenv_match_eval_sexp; eauto).
  eapply locenv_match_ptree_id_none; eauto.
  eapply find_funct_in2 in H1; eauto.
  eapply flat_map_filter_type_in in H1; eauto.
  red; intros A. apply node_ids_instruct_notin; auto.
  rewrite <-A. apply in_or_app; auto.
 +eapply eval_typecmp_struct; eauto;
  try (repeat rewrite trans_expr_typeof; auto;
    eapply locenv_match_eval_sexp; eauto).
  eapply locenv_match_ptree_id_none; eauto.
  eapply find_funct_in2 in H1; eauto.
  eapply flat_map_filter_type_in in H1; eauto.
  red; intros A. apply node_ids_instruct_notin; auto.
  rewrite <-A. apply in_or_app; auto.
Qed.

Lemma trans_stmt_correct:
  forall p nk te1 e te1' e' s,
  eval_stmt true p gc nk te1 e te1' e' s ->
  forall fd te2, locenv_match fd te1 te2 ->
   ~ In ACG_I (map fst (nd_args (snd fd))) ->
  sizeof_fld (fieldlist_of (nd_args (snd fd))) <= Int.max_signed ->
   ~ In INSTRUCT (map fst (fbyvarsof s)) ->
  incl (node_block p) (node_block prog1) ->
  type_block p = type_block prog1 ->
  exists te2', eval_stmt true p gc true te2 e te2' e' (trans_stmt (makevar fd) s)
    /\ locenv_match fd te1' te2'.
Proof.
  induction 1; intros.
  +(*Sassign*)
   eapply locenv_match_eval_eqf in H; eauto.
   destruct H as [te2' [? ?]].
   exists te2'; split; auto.
   apply eval_Sassign; auto.
  +(*Scall*)
   eapply locenv_match_setlvars_exists in H6; eauto.
   destruct H6 as [te2' [? ?]].
   exists te2'. split; auto.
   apply eval_Scall with ef ef' fd vl vargs vargs' vrets i; eauto.
    *eapply load_loopid_locenv_match; eauto.
    *eapply locenv_match_eval_sexps; eauto.
    *rewrite trans_exprs_typeof; auto.
    *eapply trans_exprs_lid_disjoint; eauto.
    *rewrite trans_exprs_typeof; auto.
    *rewrite trans_exprs_typeof; auto.
    *eapply locenv_getmvls_match; eauto.
    *eapply lvalue_list_norepet_match; eauto.
    *eapply assign_list_disjoint_match; eauto.
    *eapply locenv_match_ptree_id_none; eauto. destruct H1.
     erewrite <- find_funct_fid with (fid:=callid cdef) (fd:=fd); eauto.
     red; intros A. apply node_ids_instruct_notin; auto.
     rewrite <-A. apply in_or_app; right.
     apply in_map. eapply find_funct_in2 in H1; eauto.
  +(*Sfor_start*)
   eapply locenv_match_eval_eqf in H; eauto.
   destruct H as [te21 [? ?]].
   destruct IHeval_stmt with fd te21 as [te2' [? ?]]; auto.
   exists te2'; split; auto.
   eapply eval_Sfor_start; eauto.
  +(*Sfor_false*)
   exists te2. split; auto.
   apply eval_Sfor_false; auto.
   eapply locenv_match_eval_sexp; eauto.
  +(*Sfor_loop*)
   destruct IHeval_stmt1 with fd te0 as [te21 [? ?]]; auto.
   eapply locenv_match_eval_eqf in H1; eauto.
   destruct H1 as [te22 [? ?]].
   destruct IHeval_stmt2 with fd te22 as [te2' [? ?]]; auto.
   exists te2'; split; auto.
   apply eval_Sfor_loop with te21 te22 e1;auto.
   eapply locenv_match_eval_sexp; eauto.
  +(*Sskip*)
   exists te2; split; auto.
   apply eval_Sskip; auto.
  +(*Sseq*)
   destruct IHeval_stmt1 with fd te0 as [te21 [? ?]]; auto.
    red; intros. apply H4; simpl. rewrite map_app. apply in_or_app; auto.
   destruct IHeval_stmt2 with fd te21 as [te2' [? ?]]; auto.
    red; intros. apply H4; simpl. rewrite map_app. apply in_or_app; auto.
   exists te2'; split; auto.
   apply eval_Sseq with te21 e1; auto.
  +(*Sifs*)
   destruct IHeval_stmt with fd te2 as [te2' [? ?]]; auto.
    red; intros. apply H5; simpl. rewrite map_app. destruct b; apply in_or_app; auto.
   exists te2'; split; auto.
   apply eval_Sif with v b; eauto.
   eapply locenv_match_eval_sexp; eauto.
   rewrite trans_expr_typeof; auto.
   destruct b; auto.
  +(*Scase*)
   destruct IHeval_stmt with fd te2 as [te2' [? ?]]; auto.
   exists te2'. split; auto.
   apply eval_Scase with i (trans_expr (makevar fd) a); auto.
   eapply locenv_match_eval_sexp; eauto.
   apply trans_select_case; auto.
  +(*Sfby_1*)
   eapply locenv_match_eval_eqf in H0; eauto.
   destruct H0 as [te2' [? ?]].
   exists te2'; split; auto.
   eapply eval_Sfby_cycle_1; eauto.
  +(*Sfby_n*)
   eapply locenv_match_setlvar_exists in H3; eauto.
   destruct H3 as [te2' [? ?]].
   exists te2'; split; auto.
   apply eval_Sfby_cycle_n with v1 v; auto.
   -rewrite trans_expr_typeof; auto.
   -repeat rewrite trans_expr_typeof; auto.
   -rewrite trans_expr_typeof; auto.
   -destruct trans_expr_get_lids with fd lh as [A | A]; try congruence.
    rewrite A. red; simpl; intros A1. apply H8; simpl.
    destruct A1; auto.
  +(*Sfbyn_1*)
   eapply locenv_match_setlvar_exists in H9; eauto.
   destruct H9 as [te2' [? ?]].
   exists te2'; split; auto.
   apply eval_Sfbyn_cycle_1 with eh1 sa aty v1 v2 v; auto;
   repeat rewrite trans_expr_typeof; auto.
   -eapply locenv_match_eval_sexp; eauto.
   -cut (~ In id1 (INSTRUCT::nil)); intros A.
    red; intros A1. apply in_app_or in A1. destruct A1 as [A1 | A1].
    *destruct trans_expr_get_lids with fd a2 as [A2 | A2].
     apply H10. apply in_or_app. left. congruence.
     rewrite A2 in A1. auto.
    *destruct trans_expr_get_lids with fd lh as [A2 | A2].
     apply H10. apply in_or_app. right. congruence.
     rewrite A2 in A1. auto.
    *apply H14. simpl in *. destruct A; auto.
  +(*Sfbyn_n*)
   eapply locenv_match_setlvar_exists in H6; eauto.
   destruct H6 as [te2' [? ?]].
   exists te2'; split; auto.
   apply eval_Sfbyn_cycle_n with sa aty v1 v; auto;
   repeat rewrite trans_expr_typeof; auto.
   destruct trans_expr_get_lids with fd lh as [A | A]; try congruence.
   rewrite A. red; simpl; intros A1. apply H11; simpl. destruct A1; auto.
  +(*Sarrow*)
   eapply locenv_match_eval_eqf in H1; eauto.
   destruct H1 as [te2' [? ?]].
   exists te2'; split; auto.
   eapply eval_Sarrow; eauto.
   destruct b; auto.
  +(*Stypecmp*)
   eapply locenv_match_setlvar_exists in H4; eauto.
   destruct H4 as [te2' [? ?]].
   exists te2'. split; auto.
   apply eval_Stypecmp with b; auto.
   -rewrite H10 in *. eapply eval_typecmp_trans; eauto.
   -apply trans_expr_lid_disjoint; auto.
   -rewrite trans_expr_typeof; auto.
   -eapply assign_list_disjoint_match with (fd:=fd) in H3; eauto.
Qed.

Lemma trans_get_lids_list_disjoint:
  forall i fd s,
  list_disjoint (i::nil) (get_lids s) ->
  i <> INSTRUCT ->
  list_disjoint (i::nil) (get_lids (trans_expr (makevar fd) s)).
Proof.
  induction s; simpl; intros; auto.
  unfold makevar, trans_v.
  destruct (in_list _ _); simpl; auto.
  red; simpl; intros. destruct H1,H2; subst; tauto.
Qed.

Lemma trans_stmt_eval_fbyeqs:
  forall s fd te1 eh eh' te2,
  eval_fbyeqs gc te1 eh eh' (fbyeqof s) ->
  locenv_match fd te1 te2 ->
  ~ (In INSTRUCT (map fst (fbyvarsof s))) ->
  sizeof (mkstruct fd) <= Int.max_signed ->
  eval_fbyeqs gc te2 eh eh' (fbyeqof (trans_stmt (makevar fd) s)).
Proof.
  induction s; simpl; intros; eauto; try (inv H; econstructor; eauto; fail).
  +eapply eval_fbyeqs_app_inv in H; eauto. destruct H as [eh1 [? ?]]; auto.
   rewrite map_app in H1. apply not_in_app in H1. destruct H1.
   eapply eval_fbyeqs_app with eh1; eauto.
  +inv H. inv H8. inv H7. constructor 2 with eh'; auto.
   constructor 1 with v v';auto.
   eapply locenv_match_eval_sexp; eauto.
   rewrite trans_expr_typeof; auto.
   rewrite trans_expr_typeof; auto.
   apply trans_get_lids_list_disjoint; auto.
   constructor.
  +destruct p. destruct p. inv H. inv H8. inv H9.
   constructor 2 with e1; auto.
   -inv H7. constructor 1 with v v';auto.
    eapply locenv_match_eval_sexp; eauto.
    rewrite trans_expr_typeof; auto.
    rewrite trans_expr_typeof; auto.
    simpl in *. apply trans_get_lids_list_disjoint; auto.
   -constructor 2 with eh'; auto.
    inv H6. constructor 2; auto.
    rewrite trans_expr_typeof; auto.
    constructor.
  +inv H. inv H7. inv H8. constructor 2 with eh'; constructor.
  +eapply eval_fbyeqs_app_inv in H; eauto. destruct H as [eh1 [? ?]]; auto.
   rewrite map_app in H1. apply not_in_app in H1. destruct H1.
   eapply eval_fbyeqs_app with eh1; eauto.
Qed.

Lemma trans_main_correct:
  forall p e e' node vargs1 vrets,
  eval_node true p gc e e' node vargs1 vrets ->
  forall varg2,
  varg_fld_match (fieldlist_of (nd_args (snd node))) (nd_args (snd node)) vargs1 varg2 ->
  ids_plt INSTRUCT (allidsof (snd node) ++ predidof (snd node)) ->
  0 < sizeof_fld (fieldlist_of (nd_args (snd node))) <= Int.max_signed ->
  incl (node_block p) (node_block prog1) ->
  type_block p = type_block prog1 ->
  eval_node true p gc e e' (fst node,trans_body node) (varg2::nil) vrets.
Proof.
  induction 1; intros.
  generalize H1, Int.max_signed_unsigned ; intros A A2.
  apply trans_body_ids_norepeat with _ nid in H1; eauto.
  apply ids_plt_le_notin with INSTRUCT _ _ in H7; try (unfold Ple; omega).
  apply alloc_variables_exists with _ _ nid in H; auto.
  destruct H as [te21 [? [? [m [? [? ?]]]]]].

  apply locenv_match_setvar_exists with _ _ _ nid _ te21 varg2 m in H0; auto.
  destruct H0 as [te22 [? ?]].
  destruct A as [A [A1 [A3 A4]]].
  apply not_in_app in H7. destruct H7 as [? A5].
  apply not_in_app in A5. destruct A5 as [A5 A6].
  unfold allidsof, allvarsof in *. repeat rewrite map_app in *.
  apply trans_stmt_correct with (fd:=(nid,f)) (te2:=te22) in H2; auto.
  destruct H2 as [te2' [? ?]].
  eapply locenv_match_getvars in H4; eauto.
  apply exec_node with te21 te22 te2' eh1; auto.
  +unfold trans_body, makevar in *. simpl in *.
   inv H3. constructor 1 with eh0; auto.
   eapply trans_stmt_eval_fbyeqs in H17; eauto.
   unfold makevar in *; auto.
   unfold mkstruct, sizeof_fld in *. simpl in *. omega.
   rewrite trans_stmt_fbyeqof_length; auto.
  +simpl. apply list_norepet_app in A.
   destruct A as [? [? A]]. eapply list_disjoint_app_left; eauto.
  +red; intros. apply H7. simpl. in_tac.
  +red; intros. apply A4. in_tac.
  +omega.
  +simpl in *. omega.
  +eapply locenv_setvars_sizeof; eauto.
Qed.

Lemma mkprog_ids_range:
  forall l1 l2 node,
  prog1 = mkprog1 prog1 l1 l2 node nil ->
  ids_plt INSTRUCT (allidsof (snd node) ++ predidof (snd node)).
Proof.
  clear TRANSL.
  unfold mkprog1. intros. unfold ids_range in ID_RANGE.
  apply ID_RANGE; auto.
  rewrite H in *. simpl in *.
  apply in_or_app; simpl; auto.
Qed.

Lemma trans_node_all_correct:
  forall e e' node vargs1 vrets,
  eval_node true prog1 gc e e' node vargs1 vrets ->
  forall varg2,
  find_funct (node_block prog1) (node_main prog1) = Some node ->
  varg_fld_match (fieldlist_of (nd_args (snd node))) (nd_args (snd node)) vargs1 varg2 ->
  beq_nat (length (nd_args (snd node))) 0 = false ->
  eval_node true prog2 gc e e' (fst node,trans_body node) (varg2::nil) vrets.
Proof.
  intros.
  destruct prog_simpl with node as [l1 [l2 [sty [A [A1 A3]]]]]; auto.
  monadInv TRANSL.
  unfold trans_node in *. rewrite H2 in *.
  destruct (list_in_list _ _); try congruence.
  inversion EQ0. subst prog2. rewrite A in *.
  apply eval_node_nocycle2 in H; auto.
  eapply trans_main_correct in H; eauto.
  apply eval_node_nocycle_app1 with (mkprog prog1 l1 sty) ((fst node, trans_body node)::l2); eauto.
  eapply eval_node_program_dep; eauto.
  simpl in *. inversion H4. auto.

  apply mkprog_ids_range with l1 l2; auto.

  unfold mkprog1, trans_sty, mksdef, sizeof_fld in *. simpl in *.
  rewrite H0, H2 in *.
  destruct (zlt _ _ ), (zle _ _); simpl in EQ; monadInv EQ. omega.
  rewrite A. simpl. red. intros. apply in_or_app; auto.
Qed.

Lemma vargs_match_match:
  forall m delta args vl,
  Lenv.vargs_match m delta args vl ->
  forall al, list_norepet (map fst args) ->
  list_disjoint (map fst al) (map fst args) ->
  sizeof_struct (fieldlist_of al) 0 = delta ->
  vargs_match (fieldlist_of (al++args)) m args vl.
Proof.
  induction 1; simpl; intros.
  +constructor 1.
  +inv H1.
   replace (al0 ++ (id, ty) :: al) with ((al0 ++ (id, ty) :: nil) ++ al).
   constructor 2; auto.
   -exists (align (sizeof_struct (fieldlist_of al0) 0) (alignof ty)).
    repeat (split; auto).
    *rewrite app_ass. simpl.
     unfold field_offset. apply field_offset_rec_fieldlist_of_notin_app_cons; auto.
     apply list_disjoint_notin with (id :: map fst al); simpl; auto.
     apply list_disjoint_sym; auto.
    *rewrite app_ass.
     rewrite field_type_notin_app; auto.
     simpl. rewrite peq_true; auto.
     apply list_disjoint_notin with (id :: map fst al); simpl; auto.
     apply list_disjoint_sym; auto.
   -apply IHvargs_match; auto.
    *rewrite map_app. red; intros.
     apply in_app_or in H1. destruct H1.
     apply H2; simpl; auto.
     red; intros; subst. simpl in *.
     destruct H1; subst; try tauto.
    *apply sizeof_struct_fieldlist_of_app_cons; auto.
   -rewrite app_ass; auto.
Qed.

Lemma trans_stmt_kind:
  forall p gc nk te e te' e' s,
  eval_stmt true p gc nk te e te' e' s ->
  eval_stmt true p gc true te e te' e' s.
Proof.
  induction 1; intros; try (econstructor; eauto; fail).
  +eapply eval_Sfby_cycle_n; eauto.
  +eapply eval_Sfbyn_cycle_n; eauto.
Qed.

Lemma trans_main_kind:
  forall p e e' node vargs vrets,
  eval_node true p gc e e' node vargs vrets ->
  eval_node true p gc e e' (trans_node_kind node) vargs vrets.
Proof.
  induction 1; intros.
  econstructor 1; eauto. simpl.
  eapply trans_stmt_kind; eauto.
Qed.

Lemma trans_node_kind_correct:
  forall e e' node vargs vrets,
  eval_node true prog1 gc e e' node vargs vrets ->
  find_funct (node_block prog1) (node_main prog1) = Some node ->
  eval_node true prog2 gc e e' (trans_node_kind node) vargs vrets.
Proof.
  intros.
  destruct prog_simpl with node as [l1 [l2 [sty [A [A1 A3]]]]]; auto.
  subst prog2. rewrite A in *.
  apply eval_node_nocycle2 in H; auto.
  eapply trans_main_kind in H; eauto.
  apply eval_node_nocycle_app1 with (mkprog prog1 l1 nil) (trans_node node::l2); simpl; eauto.
Qed.

Lemma mvl_type_struct:
  forall m main,
  mvl_type true m (Tstruct 1%positive (fieldlist_of (nd_args (snd main)))) ->
  mvl_type true m (mkstruct main).
Proof.
  unfold mkstruct. intros.
  inv H; simpl in *; try congruence; unfold node in *.
  constructor 3; auto.
Qed.

Theorem exec_prog_correct_general:
  forall e main vass vrss n maxn,
  exec_prog prog1 gc (eval_node true) main e n maxn vass vrss ->
  forall mass,
  find_funct (node_block prog1) (node_main prog1) = Some main ->
  vargs_matchss (nd_args (snd main)) vass mass ->
  exec_prog1 prog2 gc (eval_node true) (trans_node main) e n maxn mass vrss.
Proof.
  induction 1; intros.
  +constructor 1 with mrss; trivial.
   unfold trans_node. destruct (beq_nat _ _); auto.
  +inversion_clear H3; inversion_clear H5.
   -assert (A: beq_nat (length (nd_args (snd main))) 0 = false).
      destruct (length (nd_args (snd main))); simpl in *.
      omega. auto.
    unfold trans_node, node in *.  rewrite A in *.
    apply trans_node_all_correct with (varg2:=Vmvl m) in H0; auto.
    constructor 2 with e'; simpl; auto.
    *rewrite H6. constructor 2; simpl; auto. unfold node in *.
     apply mvl_type_struct; auto.
    *rewrite H6. eauto.
    *apply IHexec_prog; auto.
     constructor 1; auto.
    *econstructor; eauto.
     apply vargs_match_match with (al:=nil) in H3; auto.
     apply ids_norepet_args_norepet; auto. inv H0; auto.
     red; intros. tauto.
     apply mvl_type_length in H7. unfold sizeof_fld.
     simpl in *. unfold node in *. auto.
   -unfold trans_node, node in *. rewrite H4 in *. simpl in *.
    constructor 2 with e'; simpl; auto; unfold node in *.
    *rewrite H4, H3. constructor.
    *rewrite H3, H6 in *. eapply trans_node_kind_correct; eauto.
    *apply IHexec_prog; auto.
     constructor 2; auto.
Qed.

Lemma find_funct_trans:
  forall main1,
  find_funct (node_block prog1) (node_main prog1) = Some main1 ->
  find_funct (node_block prog2) (node_main prog2) = Some (trans_node main1).
Proof.
  monadInv TRANSL.
  destruct (list_in_list _ _); inv EQ0. simpl in *.
  clear. destruct prog1; simpl.
  induction node_block; simpl; intros.
  +congruence.
  +destruct (identeq (fst a) node_main) eqn:?; simpl.
   -inv H. unfold trans_node.
    destruct (beq_nat _ _); simpl; rewrite Heqb; auto.
   -rewrite Heqb. auto.
Qed.

Lemma init_stmt_kind:
  forall p nk e e' s,
  init_stmt p nk e e' s ->
  init_stmt p true e e' s.
Proof.
  induction 1; intros; auto.
  +constructor.
  +constructor 2 with se1 fd ef; auto.
Qed.

Lemma alloc_main_correct:
  forall p e fd,
  init_node p e fd ->
  ids_plt INSTRUCT (allidsof (snd fd) ++ predidof (snd fd)) ->
  init_node p e (trans_node fd).
Proof.
  induction 1; simpl; intros.
  generalize H; intros A. unfold trans_node.
  destruct (beq_nat _ _) eqn:?; constructor 1; simpl; auto.
  +eapply init_stmt_kind; eauto.
  +eapply trans_body_ids_norepeat; eauto.
  +rewrite trans_stmt_fbyeqof_length.
   rewrite <-trans_body_fbyvarsof with (fd:=(nid,f)) in H0; eauto.
  +intros. apply H1.
   rewrite trans_body_fbyvarsof with (fd:=(nid,f)) in H4; eauto.
  +rewrite trans_stmts_instidof_eq; auto.
   eapply init_stmt_kind; eauto.
Qed.

Lemma init_node_correct:
  forall e fd,
  init_node prog1 e fd ->
  find_funct (node_block prog1) (node_main prog1) = Some fd ->
  init_node prog2 e (trans_node fd).
Proof.
  intros.
  destruct prog_simpl with fd as [l1 [l2 [sty [A [A1 A3]]]]]; auto.
  monadInv TRANSL. destruct (list_in_list _ _); try congruence.
  rewrite A, A1 in *.
  apply init_node_nocycle2 in H; auto.
  eapply alloc_main_correct in H; eauto.
  apply init_node_nocycle_app1 with (mkprog prog1 l1 sty) ((trans_node fd)::l2); eauto.
  eapply init_node_program_dep; eauto.
  apply mkprog_ids_range with l1 l2; auto.
Qed.

End NODE_CORRECT.

Lemma init_genvc_none:
  forall gc,
  init_genvc (const_block prog1) = Some gc ->
  gc ! INSTRUCT = None.
Proof.
  intros. eapply init_genvc_notin_none; eauto.
  apply ids_plt_le_notin with ACG_EQU; auto.
  unfold Ple, INSTRUCT, ACG_EQU. omega.
  red; intros. apply GID_RANGE. apply in_or_app; auto.
Qed.

Lemma mksdef_args_prop:
  forall main1 a,
  mksdef (fst main1) (snd main1) = OK a ->
  args_prop ((INSTRUCT, mkstruct main1) :: nil).
Proof.
  unfold mksdef, mkstruct. intros.
  destruct (zlt _ _), (zle _ _); simpl in *; try congruence.
  split; auto. constructor 2; auto.
  split; auto.
Qed.

Lemma initial_states_match:
  forall gc main1 e,
  Lenv.initial_state prog1 gc init_node main1 e ->
  exists main2, Lenv.initial_state1 prog2 gc init_node main2 e
    /\ main2 = (trans_node main1)
    /\ gc ! INSTRUCT = None.
Proof.
  intros. exists (trans_node main1).
  assert(A: node_main prog1 = fst main1).
    inv H; eapply find_funct_fid in H1; eauto.
  inversion_clear H; generalize H1; intros A1;
  apply find_funct_trans in A1; auto.
  +split;[| split]; auto.
   -constructor 1; simpl; auto.
    *monadInv TRANSL. destruct (list_in_list _ _); inv EQ0.
     destruct prog1. simpl; auto.
    *monadInv TRANSL. destruct (list_in_list _ _); inv EQ0.
     unfold trans_sty in EQ. unfold node in *.
     rewrite H1 in EQ. unfold trans_node.
     destruct (beq_nat _ _) eqn:?; monadInv EQ; simpl.
     destruct (nd_args _); simpl in *; try congruence.
      split; constructor. simpl; omega.
     eapply mksdef_args_prop; eauto.
    *apply init_node_correct in H2; auto.
   -apply init_genvc_none; auto.
Qed.

Theorem trans_program_correct:
  forall gc e main1 vass mass vrss maxn,
  Lenv.initial_state prog1 gc init_node main1 e->
  exec_prog prog1 gc (eval_node true) main1 e 1 maxn vass vrss ->
  vargs_matchss (nd_args (snd main1)) vass mass ->
  exists main2, Lenv.initial_state1 prog2 gc init_node main2 e
    /\ nd_rets (snd main2) = nd_rets (snd main1)
    /\ nd_kind (snd main2) = true
    /\ exec_prog1 prog2 gc (eval_node true) main2 e 1 maxn mass vrss.
Proof.
  intros.
  destruct initial_states_match with gc main1 e as [main2 [A [A1 A2]]]; auto.
  exists main2. subst main2. repeat (split; auto).
  +unfold trans_node. destruct (beq_nat _ _); auto.
  +unfold trans_node. destruct (beq_nat _ _); auto.
  +apply exec_prog_correct_general with vass; auto.
   inversion_clear H; auto.
Qed.

End CORRECTNESS.
