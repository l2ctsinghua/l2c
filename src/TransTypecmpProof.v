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

(** Correctness proof for type compare. *)

Require Import Coqlib.
Require Import AST.
Require Import Errors.
Require Import Maps.
Require Import Integers.
Require Import Inclusion.
Require Import List.
Require Import ExtraList.
Require Import Cop.
Require Import Cltypes.
Require Import Lident.
Require Import Ltypes.
Require Import Lop.
Require Import Lint.
Require Import Lustre.
Require Import LustreR.
Require Import Lint.
Require Import Lvalues.
Require Import Lenv.
Require Import Lenvmatch.
Require Import Lsem.
Require Import LsemR.
Require Import Toposort.
Require Import TransTypecmp.

Section CORRECTNESS.

Variable prog1: LustreR.program.
Variable prog2: program.

Variable gc: locenv.

Hypothesis TRANS:
  trans_program prog1 = OK prog2.

Hypothesis GID_NOREPET:
  list_norepet (Lustre.globidsof prog1).

Hypothesis GID_RANGE:
  ids_plt ACG_EQU (globidspltof prog1).

Let tdl := type_block prog1.

Lemma comp_funcs_node_block_disjoint:
  forall l,
  list_in_list l (Lustre.globidsof prog1) = false ->
  list_disjoint l (map fst (node_block prog1)).
Proof.
  intros.
  apply list_in_list_disjoint in H; auto.
  red; intros. eapply H; eauto.
  apply in_or_app. auto.
Qed.

Lemma trans_call_func:
  forall cdef fd,
  call_func (node_block prog1) cdef fd ->
  exists fd', call_func (node_block prog2) cdef fd'
    /\ trans_node tdl fd = OK fd'.
Proof.
  unfold call_func. intros.
  destruct H as [? [? [? [? ?]]]]. monadInv TRANS.
  destruct (list_in_list _ _) eqn:?; try congruence.
  inv EQ0. simpl.
  eapply find_funcs_monad_exits in EQ; eauto.
  destruct EQ as [fd' [? ?]].
  exists fd'. repeat (split; auto).
  +rewrite find_funct_app_notin_right; auto.
   red; intros. eapply comp_funcs_node_block_disjoint; eauto.
   rewrite <-find_funct_fid with (fd:=fd) (l:=node_block prog1) (fid:=callid cdef); auto.
   apply in_map. eapply find_funct_in2; eauto.
  +monadInv H4. monadInv EQ; auto.
  +monadInv H4. monadInv EQ; auto.
  +monadInv H4. monadInv EQ; auto.
  +intros. monadInv H4; auto.
Qed.

Lemma find_funct_array_comp_rec:
  forall l id aty num,
  find_funct l id = Some (id, Tarray id aty num) ->
  find_funct (comp_functions l) (comp_funcs_id id) = Some (array_comp id aty num).
Proof.
  induction l; simpl; intros.
  +congruence.
  +destruct a. simpl in *.
   destruct (identeq _ _) eqn:?.
   -inv H. simpl. rewrite Pos.eqb_refl. auto.
   -destruct t; simpl; eauto; unfold comp_funcs_id in *;
    rewrite identeq_shift, Heqb; eauto.
Qed.

Lemma find_funct_array_comp:
  forall id aty num,
  find_funct (type_block prog1) id = Some (id, Tarray id aty num) ->
  find_funct (node_block prog2) (comp_funcs_id id) = Some (array_comp id aty num).
Proof.
  intros. monadInv TRANS.
  destruct (list_in_list _ _) eqn:?; inv EQ0.
  simpl. apply find_funct_app.
  eapply find_funct_array_comp_rec; eauto.
Qed.

Lemma find_funct_array_call:
  forall aid aty num,
  find_funct (type_block prog1) aid = Some (aid, Tarray aid aty num) ->
  call_func (node_block prog2) (comp_cdef aid (Tarray aid aty num)) (array_comp aid aty num).
Proof.
  intros. repeat (split; auto); simpl.
  simpl. eapply find_funct_array_comp; eauto.
  simpl intof_opti. rewrite Int.unsigned_one. unfold Int.max_signed; simpl; omega.
Qed.

Lemma find_funct_struct_comp_rec:
  forall l id fld,
  find_funct l id = Some (id, Tstruct id fld) ->
  find_funct (comp_functions l) (comp_funcs_id id) = Some (struct_comp id fld).
Proof.
  induction l; simpl; intros.
  +congruence.
  +destruct a. simpl in *.
   destruct (identeq _ _) eqn:?.
   -inv H. simpl. rewrite Pos.eqb_refl. auto.
   -destruct t; simpl; eauto;
    unfold comp_funcs_id in *;
    rewrite identeq_shift, Heqb; eauto.
Qed.

Lemma find_funct_struct_comp:
  forall id fld,
  find_funct tdl id = Some (id, Tstruct id fld) ->
  find_funct (node_block prog2) (comp_funcs_id id) = Some (struct_comp id fld).
Proof.
  intros. monadInv TRANS. simpl.
  destruct (list_in_list _ _) eqn:?; inv EQ0.
  simpl. apply find_funct_app.
  eapply find_funct_struct_comp_rec; eauto.
Qed.

Lemma find_funct_struct_call:
  forall sid fld,
  find_funct (type_block prog1) sid = Some (sid, Tstruct sid fld) ->
  call_func (node_block prog2) (comp_cdef sid (Tstruct sid fld)) (struct_comp sid fld).
Proof.
  intros. repeat (split; auto).
  simpl. eapply find_funct_struct_comp; eauto.
  simpl intof_opti. rewrite Int.unsigned_one. unfold Int.max_signed; simpl; omega.
Qed.

Lemma eval_result_getvars:
  forall e v,
  eval_sexp gc e result v ->
  locenv_range_perm_vars e cmp_rets ->
  locenv_getvars e cmp_rets (v :: nil).
Proof.
  unfold result, cmp_rets. intros.
  constructor; auto. inv H. inv H1.
  -inv H2. destruct H as [? [? [? [? ?]]]].
   rewrite H in H8. inv H8.
   constructor 1 with m; auto.
  -destruct H0 with ACG_EQU type_bool as [? [? ?]]; simpl; auto. congruence.
Qed.

Lemma eval_loop_init_val:
  forall e e1,
  eval_eqf gc e e1 loop_init ->
  eval_sexp gc e1 (Svar ACG_I type_int32s) (Vint Int.zero).
Proof.
  intros. inv H. inv H7. inv H. inv H2.
  apply eval_Rlvalue with ACG_I Int.zero Lid; auto.
  +inv H0. constructor 1 with m'; auto.
   rewrite PTree.gss; auto. congruence.
  +inv H4. unfold sem_cast in *. simpl in *. inv H1.
   constructor 2.
   eapply store_env_load_int_eq; eauto.
   simpl in *. destruct H; congruence.
  +inv H.
Qed.

Lemma eval_loop_cond_true:
  forall e i num,
  eval_sexp gc e (Svar ACG_I type_int32s) (Vint i) ->
  Int.unsigned i < num <= Int.max_signed ->
  eval_sexp gc e (loop_cond (Int.repr num)) Vtrue.
Proof.
  intros. apply eval_Sbinop with (Vint i) (Vint (Int.repr num)); simpl; auto.
  constructor. simpl; auto.
  unfold Int.lt. rewrite Int.signed_repr; try omega.
  unfold Int.signed, Int.max_signed in *.
  destruct (zlt (Int.unsigned i) Int.half_modulus); try omega.
  destruct (zlt _ _); try omega. auto.
  unfold Int.min_signed. simpl.
  generalize (Int.unsigned_range i). omega.
Qed.

Lemma eval_result_init_val:
  forall e e1,
  eval_eqf gc e e1 (result, Sconst (Cbool true) type_bool) ->
  eval_sexp gc e1 result Vtrue.
Proof.
  intros. inv H. inv H7. inv H. inv H2.
  apply eval_Rlvalue with ACG_EQU Int.zero Lid; auto.
  +inv H0. constructor 1 with m'; auto.
   rewrite PTree.gss; auto. congruence.
  +inv H4. unfold sem_cast in *. simpl in *. inv H1.
   constructor 2.
   eapply store_env_load_bool_eq; eauto.
   simpl in *. destruct H; congruence.
  +inv H.
Qed.

Lemma eval_loop_cond_false:
  forall e i,
  eval_sexp gc e (Svar ACG_I type_int32s) (Vint i) ->
  eval_sexp gc e (loop_cond i) Vfalse.
Proof.
  intros. apply eval_Sbinop with (Vint i) (Vint i); simpl; auto.
  constructor. simpl; auto.
  unfold Int.lt.
  destruct (zlt _ _); try omega. auto.
Qed.

Lemma eval_loop_add_val:
  forall e e1 i,
  eval_sexp gc e (Svar ACG_I type_int32s) (Vint i) ->
  eval_eqf gc e e1 loop_add ->
  Int.unsigned i + 1 <= Int.max_signed ->
  eval_sexp gc e1 (Svar ACG_I type_int32s) (Vint (Int.repr (Int.unsigned i + 1))).
Proof.
  intros. inv H0. inv H4. inv H11.
  eapply eval_sexp_determ in H;eauto. subst.
  simpl in *. inv H14. inv H9. inv H.
  +apply eval_Rlvalue with ACG_I Int.zero Lid; auto.
   inv H0. constructor 1 with m'; auto.
   rewrite PTree.gss; auto. congruence.
   constructor 2; auto.
   apply eval_cast_int32s in H6. subst.
   eapply store_env_load_int_eq; eauto.
  +inv H0.
  +inv H0.
Qed.

Lemma eval_casts_array:
  forall v1 v2 ty,
  is_arystr ty = true ->
  eval_casts (v1::v2::nil) (ty :: ty :: nil) (v1::v2::nil).
Proof.
  unfold is_arystr. intros.
  destruct ty; try congruence; constructor 2; auto;
  try (constructor 2; auto; fail);
  constructor 2; auto;
  try (constructor 2; auto; fail); constructor.
Qed.

Lemma local_result_lid_disjoint:
  Forall lid_disjoint (local_result :: nil).
Proof.
  constructor; auto. red; simpl.
  unfold ACG_LOCAL, ACG_I. congruence.
Qed.

Lemma struct_cmp_vars_sizeof:
  forall id ty sty,
  In (id,ty) (str_vars ++ cmp_paras sty ++ cmp_rets)->
  0 < sizeof sty <= Int.max_signed ->
  0 < sizeof ty <= Int.max_signed.
Proof.
  simpl. intros.
  destruct H as [ | [ | [ | [ | ]]]]; inv H; simpl; auto; try omega.
Qed.

Lemma array_cmp_vars_sizeof:
  forall id ty sty,
  In (id,ty) (ary_vars ++ cmp_paras sty ++ cmp_rets)->
  0 < sizeof sty <= Int.max_signed ->
  0 < sizeof ty <= Int.max_signed.
Proof.
  simpl. intros.
  destruct H as [ | [ | [ | [ | [|] ]]]]; inv H; simpl; auto; try omega;
  unfold Int.max_signed; simpl; try omega.
Qed.

Lemma range_perm_store_mvl:
  forall ty m v,
  range_perm m 0 (sizeof ty) ->
  has_type v ty ->
  exists m', store_mvl ty m Int.zero v m'.
Proof.
  intros. destruct has_type_access_mode with v ty as [ [c ?] | ?]; auto.
  +erewrite <-sizeof_chunk_eq in H; eauto.
   destruct valid_access_store with m c 0 v as [m' ?]; auto.
   split; auto. exists 0. auto.
   exists m'; auto. constructor 1 with c; auto.
  +destruct has_type_access_mode_mvl with v ty as [m1 [? ?]]; auto.
   subst. generalize (sizeof_pos ty); intros.
   apply mvl_type_length in H3.
   destruct range_perm_store_bytes with m 0 m1 as [m' ?];auto.
   rewrite H3. auto.
   exists m'. constructor 2; auto.
   rewrite Int.unsigned_zero. exists 0. auto.
Qed.

Lemma locenv_setvars_exists:
  forall e v1 v2 ty,
  locenv_range_perm_vars e (cmp_paras ty) ->
  has_type v1 ty ->
  has_type v2 ty ->
  is_arystr ty = true ->
  exists e1, locenv_setvars e (cmp_paras ty) (v1::v2::nil) e1
    /\ eval_sexp gc e1 (Svar ACG_C1 ty) v1
    /\ eval_sexp gc e1 (Svar ACG_C2 ty) v2.
Proof.
  unfold cmp_paras. intros.
  assert(A:ACG_C1 <> ACG_C2).
    unfold ACG_C2, ACG_C1. congruence.
  destruct H with ACG_C1 ty as [? [? [? ?]]]; simpl; auto.
  destruct H with ACG_C2 ty as [? [? [? ?]]]; simpl; auto.
  destruct range_perm_store_mvl with ty x v1; auto.
  destruct range_perm_store_mvl with ty x0 v2; auto.
  econstructor. split; [| split].
  +econstructor 2; eauto. econstructor 1 with x; eauto.
   econstructor 2; eauto. rewrite PTree.gso; eauto.
   econstructor 1 with x0; eauto.
   rewrite PTree.gso; eauto.
   constructor.
  +econstructor; eauto. econstructor; eauto.
   rewrite PTree.gso; eauto. rewrite PTree.gss; eauto.
   constructor 2. exists x1, ty; auto.
   rewrite PTree.gso, PTree.gss; auto.
   repeat (split; auto).
   eapply store_mvl_length in H9;eauto. congruence.
   simpl. eapply store_mvl_load_arystr; eauto.
  +econstructor; eauto. econstructor; eauto.
   rewrite PTree.gss; eauto.
   constructor 2. exists x2, ty; auto.
   rewrite PTree.gss; auto.
   repeat (split; auto).
   eapply store_mvl_length in H10;eauto. congruence.
   simpl. eapply store_mvl_load_arystr; eauto.
Qed.

Lemma eval_result_val_eq:
  forall e e1 e' (b0 b: bool),
  eval_sexp gc e result (if b0 then Vtrue else Vfalse) ->
  locenv_setlvar gc e local_result (if b then Vtrue else Vfalse) e1 ->
  eval_eqf gc e1 e' (result, Sbinop Oand result local_result type_bool) ->
  eval_sexp gc e' result (if (b0 && b) then Vtrue else Vfalse).
Proof.
  intros. inv H1.
  inv H9. apply eval_Rlvalue with b1 ofs Lid; auto.
  +inv H1. inv H2. constructor 1 with m'; auto.
   rewrite PTree.gss. congruence.
  +constructor 2. simpl in *. inv H1.
   apply store_env_load_bool_eq with e1; auto.
   cut (v' = if b0 && b then Vtrue else Vfalse). intros. subst; auto.
   eapply locenv_setlvar_eval_sexp_disjoint in H; eauto.
   -inv H4. eapply eval_sexp_determ in H; eauto. subst.
    cut (v2 = if b then Vtrue else Vfalse). intros. subst.
    *inv H6. unfold sem_cast in *.
     destruct b0, b; simpl in H15; inv H15; inv H1; auto.
     simpl in *. destruct H; congruence.
    *inv H0. simpl in H1. inv H.
     eapply eval_sexp_determ; eauto.
     apply eval_Rlvalue with ACG_LOCAL Int.zero Lid; simpl; auto.
     inv H1. constructor 1 with m'; auto.
     rewrite PTree.gss; auto. congruence.
     constructor 2; auto.
     apply store_env_load_bool_eq in H1; auto.
     destruct b; auto.
     destruct b; simpl; auto.
    *inv H1.
   -simpl. unfold ACG_LOCAL, ACG_EQU.
    red; simpl; intros. destruct H1, H3; subst; congruence.
   -destruct b0, b; auto.
  +destruct b0, b; simpl; auto.
Qed.

Lemma eval_saryacc_trans:
  forall e1 e2 a1 id v v1 aid aty i num,
  eval_sexp gc e1 a1 v ->
  eval_sexp gc e2 (Svar id (Tarray aid aty num)) v ->
  eval_sexp gc e1 (Saryacc a1 (Sconst (Cint i) type_int32s) aty) v1 ->
  eval_sexp gc e2 (Svar ACG_I type_int32s) (Vint i) ->
  0 <= Int.signed i < Z.max 0 num ->
  typeof a1 = Tarray aid aty num ->
  eval_sexp gc e2 (Saryacc (Svar id (Tarray aid aty num)) (Svar ACG_I type_int32s) aty) v1.
Proof.
  clear.
  intros. rewrite <-H4 in *. inv H1. inv H5.
  generalize H; intros.
  apply eval_sexp_has_type in H1.
  rewrite H12 in *. destruct v; try tauto.
  eapply eval_sexp_aryacc; simpl; eauto.
  inv H11. simpl in *.
  destruct eval_sexp_exists_lvalue with gc e1 a1 m as [id2 [o2 [k2 ?]]]; auto.
  eapply eval_sexp_determ in H10; eauto.
  destruct H10 as [? [? ?]]. subst.
  eapply eval_sexp_lvalue_var in H5; eauto.
  eapply eval_var_app_inv; eauto.
  inv H4. rewrite H12.
  apply array_ofs_add_le; auto.
  apply signed_unsigned_range; auto.
  rewrite H12. simpl. exists 1; omega.
  inv H5.
Qed.

Lemma eval_sfield_trans:
  forall e1 e2 a1 id v v1 aid sid fld ty,
  eval_sexp gc e1 a1 v ->
  eval_sexp gc e2 (Svar id (Tstruct sid fld)) v ->
  eval_sexp gc e1 (Sfield a1 aid ty) v1 ->
  typeof a1 = Tstruct sid fld ->
  eval_sexp gc e2 (Sfield (Svar id (Tstruct sid fld)) aid ty) v1.
Proof.
  intros. rewrite <-H2 in *. inv H1. inv H3.
  rewrite H9 in H2. inv H2.
  generalize H; intros.
  apply eval_sexp_has_type in H1.
  rewrite H9 in *. destruct v; try tauto.
  eapply eval_sexp_field; simpl; eauto.
  simpl in *.
  destruct eval_sexp_exists_lvalue with gc e1 a1 m as [id2 [o2 [k2 ?]]]; auto.
  eapply eval_sexp_determ in H8; eauto.
  destruct H8 as [? [? ?]]. subst.
  eapply eval_sexp_lvalue_var in H; eauto.
  constructor 1 with delta; auto.
  eapply eval_var_app_inv; eauto.
  eapply field_offset_in_range_simpl in H14; eauto.
  apply Zle_trans with (delta + sizeof ty).
  apply Zplus_le_compat_r; try omega.
  apply int_repr_le. omega. rewrite H9.
  unfold sizeof_fld in *. simpl in *. omega.
  rewrite H9. simpl. eapply field_type_alignof; eauto.
Qed.

Lemma assign_list_disjoint_aryacc_trans:
  forall e e1 ai ty aty v v1 v2,
  eval_sexp gc e (Saryacc (Svar ACG_C1 ty) ai aty) v1 ->
  eval_sexp gc e (Saryacc (Svar ACG_C2 ty) ai aty) v2 ->
  locenv_setlvar gc e local_result v e1 ->
  assign_list_disjoint (eval_lvalue gc e) (local_result :: nil)
    (Saryacc (Svar ACG_C1 ty) ai aty :: Saryacc (Svar ACG_C2 ty) ai aty :: nil).
Proof.
  intros. inv H. inv H0. inv H1.
  red. simpl. intros.
  destruct has_type_access_mode with v1 aty as [[chunk ?] | ]; auto.
  +destruct H1; destruct H8 as [ | [ | ]]; subst; try tauto;
   constructor 1 with chunk; auto.
  +destruct H1; destruct H8 as [ | [ | ]]; subst; try tauto;
   econstructor 2; eauto; econstructor; eauto; left.
   inv H0. inv H2. inv H10. unfold ACG_LOCAL, ACG_C1. congruence. congruence.
   inv H0. inv H. inv H10. unfold ACG_LOCAL, ACG_C2. congruence. congruence.
Qed.

Lemma assign_list_disjoint_field_trans:
  forall e e1 id ty aty v v1 v2,
  eval_sexp gc e (Sfield (Svar ACG_C1 ty) id aty) v1 ->
  eval_sexp gc e (Sfield (Svar ACG_C2 ty) id aty) v2 ->
  locenv_setlvar gc e local_result v e1 ->
  assign_list_disjoint (eval_lvalue gc e) (local_result :: nil)
    (Sfield (Svar ACG_C1 ty) id aty :: Sfield (Svar ACG_C2 ty) id aty :: nil).
Proof.
  intros. inv H. inv H0. inv H1.
  red. simpl. intros.
  destruct has_type_access_mode with v1 aty as [[chunk ?] | ]; auto.
  +destruct H1; destruct H8 as [ | [ | ]]; subst; try tauto;
   constructor 1 with chunk; auto.
  +destruct H1; destruct H8 as [ | [ | ]]; subst; try tauto;
   econstructor 2; eauto; econstructor; eauto; left.
   inv H0. inv H2. inv H10. unfold ACG_LOCAL, ACG_C1. congruence. congruence.
   inv H0. inv H. inv H10. unfold ACG_LOCAL, ACG_C2. congruence. congruence.
Qed.

Lemma locenv_setlvar_range_perm_vars:
  forall e e1 a v l,
  locenv_setlvar gc e a v e1 ->
  locenv_range_perm_vars e l ->
  locenv_range_perm_vars e1 l.
Proof.
  intros. inv H.
  eapply store_env_range_perm_vars; eauto.
Qed.

Lemma eval_eqf_locenv_range_perm_vars:
  forall e e1 a l,
  eval_eqf gc e e1 a ->
  locenv_range_perm_vars e l ->
  locenv_range_perm_vars e1 l.
Proof.
  intros. inv H.
  eapply locenv_setlvar_range_perm_vars; eauto.
Qed.

Lemma eval_eqf_result_exists:
  forall e1 ty l,
  locenv_range_perm_vars e1 (l ++ cmp_paras ty ++ cmp_rets) ->
  exists e2, eval_eqf gc e1 e2 (result, Sconst (Cbool true) type_bool).
Proof.
  intros.
  assert(A: locenv_range_perm_vars e1 ((ACG_EQU, type_bool) :: nil)).
    red; simpl; intros. destruct H0; inv H0. apply H.
    apply in_or_app. right. apply in_or_app. right. simpl. auto.
  destruct has_type_store_env_exists with e1 Vtrue type_bool ACG_EQU as [e2 ?]; simpl; auto.
  exists e2. constructor 1 with Vtrue Vtrue; auto.
  +constructor. simpl; auto.
  +constructor 1 with Mint8unsigned; auto.
  +constructor 1 with ACG_EQU Int.zero; auto.
   inv H0. constructor 1 with m; auto.
   destruct A with ACG_EQU type_bool as [? [? [? ?]]]; auto.
    simpl; auto. congruence.
  +constructor 1 with Mint8unsigned; auto.
Qed.

Lemma assign_result_exists:
  forall e e1 (b b0: bool) l ty,
  eval_sexp gc e result (if b0 then Vtrue else Vfalse) ->
  locenv_setlvar gc e local_result (if b then Vtrue else Vfalse) e1 ->
  locenv_range_perm_vars e1 ((ACG_LOCAL, type_bool) :: l ++ cmp_paras ty ++ cmp_rets) ->
  exists e2, eval_eqf gc e1 e2 (result, Sbinop Oand result local_result type_bool).
Proof.
  intros. inv H0.
  assert(A: eval_sexp gc e1 result (if b0 then Vtrue else Vfalse)).
    inv H3. eapply eval_sexp_setnew; eauto.
    simpl. inv H2. unfold ACG_EQU, ACG_LOCAL. red; intros.
    destruct H2; congruence.
  destruct H1 with ACG_LOCAL type_bool as [? [? [? ?]]]; simpl; auto.
  assert(A1: eval_sexp gc e1 local_result (if b then Vtrue else Vfalse)).
    inv H2. apply eval_Rlvalue with ACG_LOCAL Int.zero Lid; auto.
    inv H3. constructor 1 with m'; auto.
    rewrite PTree.gss. congruence.
    constructor 2. simpl. eapply store_env_load_bool_eq; eauto.
    destruct b; auto.
    destruct b; simpl; auto.
  assert(A2: locenv_range_perm_vars e1 ((ACG_EQU, type_bool) :: nil)).
    red; simpl; intros. destruct H6; inv H6. apply H1.
    simpl. right. apply in_or_app. right. simpl. right. auto.
  destruct has_type_store_env_exists with e1 (if (b0 && b) then Vtrue else Vfalse) type_bool ACG_EQU as [e2 ?]; simpl; auto.
    destruct b0, b; simpl; auto.
  exists e2. constructor 1 with (if (b0 && b) then Vtrue else Vfalse) (if (b0 && b) then Vtrue else Vfalse); auto.
  +apply eval_Sbinop with (if b0 then Vtrue else Vfalse) (if b then Vtrue else Vfalse); auto.
   simpl. destruct b0, b; auto.
   destruct b0, b; simpl; auto.
  +constructor 1 with Mint8unsigned; auto.
   destruct (_ && _); auto.
  +constructor 1 with ACG_EQU Int.zero; auto.
   inv A. inv H7. constructor 1 with m; auto.
   destruct A2 with ACG_EQU type_bool as [? [? ?]]; simpl; auto. congruence.
  +constructor 1 with Mint8unsigned; auto.
Qed.

Lemma locenv_setlvar_local_result_exists:
  forall e1 l (b: bool),
  locenv_range_perm_vars e1 ((ACG_LOCAL , type_bool) :: l) ->
  exists e2, locenv_setlvar gc e1 local_result (if b then Vtrue else Vfalse) e2.
Proof.
  intros.
  destruct has_type_store_env_exists with e1 (if b then Vtrue else Vfalse) type_bool ACG_LOCAL as [e2 ?]; simpl; auto.
    destruct b; simpl; auto.
    red; simpl; intros. destruct H0; inv H0; auto. apply H; simpl; auto.
  exists e2. constructor 1 with ACG_LOCAL Int.zero; auto.
  inv H0. constructor 1 with m; auto.
  destruct H with ACG_LOCAL type_bool as [? [? [? ?]]]; auto.
    simpl; auto. congruence.
Qed.

Lemma eval_loop_init_exists:
  forall e,
  locenv_range_perm_var e ACG_I type_int32s ->
  exists e1, eval_eqf gc e e1 loop_init.
Proof.
  intros.
  destruct has_type_store_env_exists with e (Vint Int.zero) type_int32s ACG_I as [e2 ?]; simpl; auto.
    red; simpl; intros. destruct H0; inv H0; auto.
  exists e2. constructor 1 with (Vint Int.zero) (Vint Int.zero); simpl; auto.
  constructor. simpl; auto.
  constructor 1 with Mint32; auto.
  constructor 1 with ACG_I Int.zero; auto.
  destruct H as [? [? [? ?]]]. constructor 1 with x; auto.
  constructor 1 with Mint32; auto.
Qed.

Lemma eval_loop_add_exists:
  forall e i,
  locenv_range_perm_var e ACG_I type_int32s ->
  eval_sexp gc e (Svar ACG_I type_int32s) (Vint i) ->
  exists e1, eval_eqf gc e e1 loop_add.
Proof.
  intros.
  destruct has_type_store_env_exists with e (Vint (Int.add i Int.one)) type_int32s ACG_I as [e2 ?]; simpl; auto.
    red; simpl; intros. destruct H1; inv H1; auto.
  exists e2. constructor 1 with (Vint (Int.add i Int.one)) (Vint (Int.add i Int.one)); simpl; auto.
  apply eval_Sbinop with (Vint i) (Vint Int.one); simpl; auto.
  constructor. simpl; auto.
  constructor 1 with Mint32; auto.
  constructor 1 with ACG_I Int.zero; auto.
  destruct H as [? [? [? ?]]]. constructor 1 with x; auto.
  constructor 1 with Mint32; auto.
Qed.

Lemma list_disjoint_cons_cons:
  forall (id1: ident) id2, id1 <> id2 ->
  list_disjoint (id1 :: nil) (id2 :: nil).
Proof.
  intros.
  red; simpl; intros ? ? A A1; destruct A, A1; try congruence.
Qed.

Lemma eval_sexps_split_determ:
  forall gc te a1 a2 v1 v2 v3 v4,
  eval_sexp gc te a1 v1 ->
  eval_sexp gc te a2 v2 ->
  eval_sexps gc te (a1:: a2 :: nil) (v3 :: v4 :: nil) ->
  v1 = v3 /\ v2 = v4.
Proof.
  intros. inv H1. inv H7. split.
  eapply eval_sexp_determ; eauto.
  eapply eval_sexp_determ; eauto.
Qed.

Lemma comp_funcs_ids_locvas_disjoint:
  list_disjoint (flat_map filter_type (type_block prog1)) (ACG_LOCAL :: ACG_I :: ACG_C1 :: ACG_C2 :: ACG_EQU :: nil).
Proof.
  unfold ACG_LOCAL, ACG_I,ACG_C1, ACG_C2, ACG_EQU in *.
  red; simpl; intros.
  cut (Plt 24 x). intros.
  red; intros. subst. unfold Plt in *.
  destruct H0 as [ | [ | [ | [ | [ | ]]]]];
  subst; try omega; try tauto.
  apply GID_RANGE. apply in_or_app. right.
  apply in_or_app; auto.
Qed.

Lemma bool_val_eval_cast:
  forall v b,
  bool_val v type_bool = Some b ->
  eval_cast v type_bool (if b then Vtrue else Vfalse).
Proof.
  intros.
  constructor 1 with Mint8unsigned; auto.
  destruct v; inv H. unfold sem_cast; simpl.
  destruct (Int.eq i Int.zero); auto.
Qed.

Lemma  eval_typecmp_eval_stmt:
  forall te a1 a2 b,
  eval_typecmp gc (type_block prog1) te a1 a2 b ->
  match (typeof a1) with
  | Tarray aid aty num =>
    exists v1 v2, eval_sexps gc te (a1 :: a2 :: nil) (v1 :: v2 :: nil)
      /\ eval_node false prog2 gc empty_env empty_env (array_comp aid aty num) (v1::v2::nil)
        ((if b then Vtrue else Vfalse)::nil)
  | Tstruct sid fld =>
    exists v1 v2, eval_sexps gc te (a1 :: a2 :: nil) (v1 :: v2 :: nil)
      /\ eval_node false prog2 gc empty_env empty_env (struct_comp sid fld) (v1::v2::nil)
        ((if b then Vtrue else Vfalse)::nil)
  | _ =>
    exists v, eval_sexp gc te (Sbinop Oeq a1 a2 type_bool) v
      /\ bool_val v type_bool = Some b
  end.
Proof.
  intros te.
  induction 1 using eval_typecmp_ind2 with
  ( P0 := fun a1 a2 num aty i b =>
      forall e aid v1 v2 (b0:bool), typeof a1 = Tarray aid aty num ->
      eval_sexp gc te a1 v1 ->
      eval_sexp gc e (Svar ACG_C1 (Tarray aid aty num)) v1 ->
      eval_sexp gc te a2 v2 ->
      eval_sexp gc e (Svar ACG_C2 (Tarray aid aty num)) v2 ->
      eval_sexp gc e (Svar ACG_I type_int32s) (Vint i) ->
      eval_sexp gc e result (if b0 then Vtrue else Vfalse) ->
      typeof a1 = typeof a2 ->
      locenv_range_perm_vars e (ary_vars ++ cmp_paras (Tarray aid aty num) ++ cmp_rets) ->
      ptree_ids_none (flat_map filter_type (type_block prog1)) e ->
      exists e', eval_stmt false prog2 gc false e empty_env e' empty_env (array_comp_stmt aid aty num)
        /\ eval_sexp gc e' result (if (b0 && b) then Vtrue else Vfalse)
        /\ locenv_range_perm_vars e' (ary_vars ++ cmp_paras (Tarray aid aty num) ++ cmp_rets))
  ( P1 := fun a1 a2 fld ftl b =>
      forall e sid v1 v2 (b0:bool), typeof a1 = Tstruct sid fld ->
      eval_sexp gc te a1 v1 ->
      eval_sexp gc e (Svar ACG_C1 (Tstruct sid fld)) v1 ->
      eval_sexp gc te a2 v2 ->
      eval_sexp gc e (Svar ACG_C2 (Tstruct sid fld )) v2 ->
      eval_sexp gc e result (if b0 then Vtrue else Vfalse) ->
      typeof a1 = typeof a2 ->
      locenv_range_perm_vars e (str_vars ++ cmp_paras (Tstruct sid fld ) ++ cmp_rets) ->
      ptree_ids_none (flat_map filter_type (type_block prog1)) e ->
      exists e', eval_stmt false prog2 gc false e empty_env e' empty_env (struct_comp_stmt_rec (Svar ACG_C1 (Tstruct sid fld)) (Svar ACG_C2 (Tstruct sid fld)) ftl)
        /\ eval_sexp gc e' result (if (b0 && b) then Vtrue else Vfalse)
        /\ locenv_range_perm_vars e' (str_vars ++ cmp_paras (Tstruct sid fld ) ++ cmp_rets));
  intros.
 +(*val_cmp*)
  destruct (typeof a1) eqn:?; simpl in *; try congruence.
  -exists v. split; auto.
  -exists v. split; auto.
 +(*ary_cmp*)
  rewrite H0.
  destruct alloc_variables_exists with (ary_vars ++ cmp_paras (Tarray aid aty num) ++ cmp_rets) empty_locenv
    as [e A].
  assert(A1: locenv_range_perm_vars e (ary_vars ++ cmp_paras (Tarray aid aty num) ++ cmp_rets)).
    eapply alloc_variables_range_perm; simpl; eauto.
    apply array_cmp_vars_norepet.
    intros. apply array_cmp_vars_sizeof with id (Tarray aid aty num); eauto.
    rewrite <-H0. eapply eval_sexp_type_size; eauto.
  destruct locenv_setvars_exists with e v1 v2 (Tarray aid aty num) as [e1 [A2 [A3 ?]]]; auto.
    red; intros. apply A1. apply in_or_app. right. apply in_or_app; auto.
    rewrite <-H0. eapply eval_sexp_has_type; eauto.
    rewrite <-H0, H. eapply eval_sexp_has_type; eauto.
  eapply locenv_setvars_locenv_range_perm in A1; eauto.
  destruct eval_eqf_result_exists with e1 (Tarray aid aty num) ary_vars as [e2 A4]; auto.
  eapply eval_eqf_locenv_range_perm_vars in A1; eauto.
  destruct eval_loop_init_exists with e2 as [e3 A5]; auto.
    apply A1. apply in_or_app. left. simpl; auto.
  eapply eval_eqf_locenv_range_perm_vars in A1; eauto.
  assert(A6: eval_sexp gc e3 (Svar ACG_I type_int32s) (Vint Int.zero)).
    eapply eval_loop_init_val; eauto.
  destruct IHeval_typecmp with e3 aid v1 v2 true as [e' [A7 [A8 A9]]]; auto.
    eapply eval_eqf_eval_sexp_disjoint; simpl; eauto.
    unfold loop_init, ACG_I, ACG_C1. simpl.
      apply list_disjoint_cons_cons; congruence.
    eapply eval_eqf_eval_sexp_disjoint; eauto.
    simpl. unfold ACG_EQU, ACG_C1. apply list_disjoint_cons_cons; congruence.
    eapply eval_eqf_eval_sexp_disjoint; simpl; eauto.
    unfold loop_init, ACG_I, ACG_C2. simpl. apply list_disjoint_cons_cons; congruence.
    eapply eval_eqf_eval_sexp_disjoint; eauto.
    simpl. unfold ACG_EQU,ACG_C2. apply list_disjoint_cons_cons. congruence.
    eapply eval_eqf_eval_sexp_disjoint; simpl; eauto.
    unfold loop_init, ACG_I, ACG_EQU. simpl. apply list_disjoint_cons_cons; congruence.
    eapply eval_result_init_val; eauto.
    eapply eval_eqf_ptree_ids_none; eauto.
    eapply eval_eqf_ptree_ids_none; eauto.
    eapply locenv_setvars_ptree_ids_none; eauto.
    eapply alloc_variables_ptree_ids_none; eauto.
    simpl. eapply comp_funcs_ids_locvas_disjoint; eauto.
    simpl. red; intros. eapply comp_funcs_ids_locvas_disjoint; eauto.
    in_tac.
  exists v1, v2. split. constructor 2; auto.
  apply exec_node with e e1 e' empty_locenv; eauto.
  -apply array_comp_body_ids_norepet; auto.
  -apply eval_Sseq with e2 empty_env; auto.
   econstructor 1; eauto.
   apply eval_Sfor_start with e3; auto.
  -simpl. destruct aty; simpl; auto; constructor 1 with empty_locenv; simpl; constructor.
  -simpl. apply eval_result_getvars; auto.
   red; intros. apply A9. apply in_or_app. right. apply in_or_app; auto.
  -simpl. constructor 2; auto. destruct b; simpl; auto.
 +(*str_cmp*)
  rewrite H0.
  destruct alloc_variables_exists with (str_vars ++ cmp_paras (Tstruct sid fld) ++ cmp_rets) empty_locenv
    as [e A].
  assert(A1: locenv_range_perm_vars e (str_vars ++ cmp_paras (Tstruct sid fld) ++ cmp_rets)).
    eapply alloc_variables_range_perm; simpl; eauto.
    apply struct_cmp_vars_norepet.
    intros. apply struct_cmp_vars_sizeof with id (Tstruct sid fld); eauto.
    rewrite <-H0. eapply eval_sexp_type_size; eauto.
  destruct locenv_setvars_exists with e v1 v2 (Tstruct sid fld) as [e1 [A2 [A3 ?]]]; auto.
    red; intros. apply A1. apply in_or_app. right. apply in_or_app; auto.
    rewrite <-H0. eapply eval_sexp_has_type; eauto.
    rewrite <-H0, H. eapply eval_sexp_has_type; eauto.
  eapply locenv_setvars_locenv_range_perm in A1; eauto.
  destruct eval_eqf_result_exists with e1 (Tstruct sid fld) str_vars as [e2 A4]; auto.
  eapply eval_eqf_locenv_range_perm_vars in A1; eauto.
  destruct IHeval_typecmp with e2 sid v1 v2 true as [e' [A5 [A6 A7]]]; auto.
    eapply eval_eqf_eval_sexp_disjoint; eauto.
    simpl. unfold ACG_EQU,ACG_C1. apply list_disjoint_cons_cons; congruence.
    eapply eval_eqf_eval_sexp_disjoint; eauto.
    simpl. unfold ACG_EQU,ACG_C2. apply list_disjoint_cons_cons; congruence.
    eapply eval_result_init_val; eauto.
    eapply eval_eqf_ptree_ids_none; eauto.
    eapply locenv_setvars_ptree_ids_none; eauto.
    eapply alloc_variables_ptree_ids_none; eauto.
    simpl. red; intros. eapply comp_funcs_ids_locvas_disjoint; eauto. in_tac.
    simpl. red; intros. eapply comp_funcs_ids_locvas_disjoint; eauto. in_tac.
  exists v1, v2. split. constructor 2; auto.
  apply exec_node with e e1 e' empty_locenv; auto.
  -apply struct_comp_body_ids_norepet; auto.
  -apply eval_Sseq with e2 empty_env; auto.
   econstructor 1; eauto.
  -simpl. unfold struct_comp_stmt.
   rewrite struct_comp_stmt_rec_fbyeqof; auto.
   constructor 1 with empty_locenv; simpl; auto; constructor.
  -simpl. apply eval_result_getvars; auto.
   red; intros. apply A7. apply in_or_app. right. apply in_or_app; auto.
  -simpl. constructor 2; auto. destruct b; simpl; auto.
 +(*eval_arycmp_loop*)
  simpl in *.
  destruct locenv_setlvar_local_result_exists with e ((ACG_I,type_int32s):: (ACG_C1, Tarray aid aty num) :: (ACG_C2, Tarray aid aty num) :: cmp_rets) b1
    as [e1 A3]; auto.
  eapply locenv_setlvar_range_perm_vars in H10; eauto.
  destruct assign_result_exists with e e1 b1 b0 ((ACG_I,type_int32s)::nil) (Tarray aid aty num)
    as [e2 A4]; auto.
  eapply eval_eqf_locenv_range_perm_vars in H10; eauto.
  assert (A9: eval_sexp gc e2 (Svar ACG_I type_int32s) (Vint i)).
    eapply eval_eqf_eval_sexp_disjoint; simpl; eauto.
    unfold loop_add, ACG_I. simpl. unfold ACG_EQU. apply list_disjoint_cons_cons; congruence.
    eapply locenv_setlvar_eval_sexp_disjoint; eauto.
    unfold local_result, ACG_LOCAL, ACG_I. simpl. apply list_disjoint_cons_cons; congruence.
  destruct eval_loop_add_exists with e2 i as [e3 A5]; auto.
    apply H10. simpl. auto.
  eapply eval_eqf_locenv_range_perm_vars in H10; eauto.
  destruct IHeval_typecmp0 with e3 aid v1 v2 (b0 && b1)
     as [e' [A6 A7]]; auto.
    eapply eval_eqf_eval_sexp_disjoint; simpl; eauto.
    unfold loop_add, ACG_I, ACG_C1. simpl. apply list_disjoint_cons_cons; congruence.
    eapply eval_eqf_eval_sexp_disjoint; eauto.
    simpl. unfold ACG_EQU,ACG_C1. apply list_disjoint_cons_cons; congruence.
    eapply locenv_setlvar_eval_sexp_disjoint; eauto.
    unfold local_result, ACG_LOCAL, ACG_C1. simpl. apply list_disjoint_cons_cons; congruence.
    eapply eval_eqf_eval_sexp_disjoint; simpl; eauto.
    unfold loop_add, ACG_I, ACG_C2. simpl. apply list_disjoint_cons_cons; congruence.
    eapply eval_eqf_eval_sexp_disjoint; eauto.
    simpl. unfold ACG_EQU,ACG_C2. apply list_disjoint_cons_cons; congruence.
    eapply locenv_setlvar_eval_sexp_disjoint; eauto.
    unfold local_result, ACG_LOCAL, ACG_C2. simpl. apply list_disjoint_cons_cons; congruence.
    apply eval_loop_add_val with e2; eauto; try omega.
    eapply eval_eqf_eval_sexp_disjoint; simpl; eauto.
    unfold loop_add, ACG_I, ACG_EQU. simpl. apply list_disjoint_cons_cons; congruence.
    eapply eval_result_val_eq; eauto.
    eapply eval_eqf_ptree_ids_none; eauto.
    eapply eval_eqf_ptree_ids_none; eauto.
    eapply locenv_setlvar_ptree_ids_none; eauto.
  cut (0 <= Int.signed i < Z.max 0 num). intros A8.
  exists e'. split.
  apply eval_Sfor_loop with e2 e3 empty_env; auto.
  eapply eval_loop_cond_true; eauto.
  apply eval_Sseq with e1 empty_env; auto.
  unfold arystr_comp_stmt.
  inv H0; simpl in *; subst.
  -destruct aty; simpl in *; inv H13.
   *constructor; auto. constructor 1 with v (if b1 then Vtrue else Vfalse); auto.
    inv H14. apply eval_Sbinop with v0 v3; simpl; auto.
      apply eval_saryacc_trans with te a1 v1 i; auto.
      apply eval_saryacc_trans with te a2 v2 i; auto. congruence.
      inv H0.
    simpl. eapply bool_val_eval_cast; eauto.
    constructor 1 with Mint8unsigned; simpl; auto.
   *constructor; auto. constructor 1 with v (if b1 then Vtrue else Vfalse); auto.
    inv H14. apply eval_Sbinop with v0 v3; simpl; auto.
      apply eval_saryacc_trans with te a1 v1 i; auto.
      apply eval_saryacc_trans with te a2 v2 i; auto. congruence.
      inv H0.
    simpl. eapply bool_val_eval_cast; eauto.
    constructor 1 with Mint8unsigned; simpl; auto.
  -destruct IHeval_typecmp as [v5 [v6 [B B1]]].
   generalize A3; intros B2.
   eapply locenv_setlvar_getmvl_exists in B2; eauto.
   destruct B2 as [mv B2].
   assert(B3: v0=v5 /\ v3 = v6).
     eapply eval_sexps_split_determ; eauto.
   destruct B3; subst.
   apply eval_Scall with empty_env empty_env (array_comp aid0 aty0 num0) (mv::nil) (v5::v6::nil) (v5::v6::nil) ((if b1 then Vtrue else Vfalse) :: nil) Int.zero; simpl; auto.
     constructor 2.
     eapply find_funct_array_call; eauto.
     constructor 2; auto.
     constructor 2; auto. apply eval_saryacc_trans with te a1 v1 i; auto.
       constructor 2; auto. apply eval_saryacc_trans with te a2 v2 i; auto.
       congruence.
     apply eval_casts_array; auto.
     constructor 2 with e1; auto. constructor.
     apply local_result_lid_disjoint.
     constructor 2; auto.
     constructor. red; intros. tauto. constructor.
     eapply assign_list_disjoint_aryacc_trans with (v1:=v5) (v2:=v6); eauto.
     apply eval_saryacc_trans with te a1 v1 i; auto.
     apply eval_saryacc_trans with te a2 v2 i; auto. congruence.
     apply H11. apply flat_map_filter_type_in with (Tarray aid0 aty0 num0); auto.
      eapply find_funct_in2; eauto.
  -destruct IHeval_typecmp as [v5 [v6 [B B1]]].
   generalize A3; intros B2.
   eapply locenv_setlvar_getmvl_exists in B2; eauto.
   destruct B2 as [mv B2].
   assert(B3: v0=v5 /\ v3 = v6).
     eapply eval_sexps_split_determ; eauto.
   destruct B3; subst.
   apply eval_Scall with empty_env empty_env (struct_comp sid fld) (mv::nil) (v5::v6::nil) (v5::v6::nil) ((if b1 then Vtrue else Vfalse) :: nil) Int.zero; simpl; auto.
     constructor 2.
     eapply find_funct_struct_call; eauto.
     constructor 2; auto.
     constructor 2; auto. apply eval_saryacc_trans with te a1 v1 i; auto.
       constructor 2; auto. apply eval_saryacc_trans with te a2 v2 i; auto.
       congruence.
     apply eval_casts_array; auto.
     constructor 2 with e1; auto. constructor.
     apply local_result_lid_disjoint.
     constructor 2; auto.
     constructor. red; intros. tauto. constructor.
     eapply assign_list_disjoint_aryacc_trans with (v1:=v5) (v2:=v6); eauto.
       apply eval_saryacc_trans with te a1 v1 i; auto.
       apply eval_saryacc_trans with te a2 v2 i; auto. congruence.
     apply H11. apply flat_map_filter_type_in with (Tstruct sid fld); auto.
      eapply find_funct_in2; eauto.
  -constructor; auto.
  -destruct b0, b1, b2; auto.
  -generalize (Int.unsigned_range i). intros.
   rewrite Z.max_r; try omega.
   rewrite Int.signed_eq_unsigned; omega.
 +(*eval_arycmp_false*)
  simpl in *. subst. exists e. split.
  apply eval_Sfor_false.
  -eapply eval_loop_cond_false; eauto.
   rewrite Int.repr_unsigned; auto.
  -destruct b0; auto.
 +(*eval_strcmp_cons*)
  simpl in *.
  destruct locenv_setlvar_local_result_exists with e ((ACG_C1, Tstruct sid fld) :: (ACG_C2, Tstruct sid fld) :: cmp_rets) b1
    as [e1 A3]; auto.
  eapply locenv_setlvar_range_perm_vars in H9; eauto.
  destruct assign_result_exists with e e1 b1 b0 (@nil (ident*type)) (Tstruct sid fld)
    as [e2 A4]; auto.
  eapply eval_eqf_locenv_range_perm_vars in H9; eauto.
  destruct IHeval_typecmp0 with e2 sid v1 v2 (b0 && b1)
     as [e' [A6 A7]]; auto.
    eapply eval_eqf_eval_sexp_disjoint; eauto.
    simpl. unfold ACG_EQU,ACG_C1. apply list_disjoint_cons_cons; congruence.
    eapply locenv_setlvar_eval_sexp_disjoint; eauto.
    unfold local_result, ACG_LOCAL, ACG_C1. simpl. apply list_disjoint_cons_cons; congruence.
    eapply eval_eqf_eval_sexp_disjoint; eauto.
    simpl. unfold ACG_EQU,ACG_C2. apply list_disjoint_cons_cons; congruence.
    eapply locenv_setlvar_eval_sexp_disjoint; eauto.
    unfold local_result, ACG_LOCAL, ACG_C2. simpl. apply list_disjoint_cons_cons; congruence.
    apply eval_result_val_eq with e e1; auto.
    eapply eval_eqf_ptree_ids_none; eauto.
    eapply locenv_setlvar_ptree_ids_none; eauto.
  exists e'. split.
  apply eval_Sseq with e2 empty_env; auto.
  apply eval_Sseq with e1 empty_env; auto.
  unfold arystr_comp_stmt.
  inv H; simpl in *.
  -destruct ty; simpl in *; inv H12.
   *constructor; auto. constructor 1 with v (if b1 then Vtrue else Vfalse); auto.
    inv H13. apply eval_Sbinop with v0 v3; simpl; auto.
      apply eval_sfield_trans with te a1 v1; auto.
      apply eval_sfield_trans with te a2 v2; auto.
      congruence.
      inv H.
    simpl. eapply bool_val_eval_cast; eauto.
    constructor 1 with Mint8unsigned; simpl; auto.
   *constructor; auto. constructor 1 with v  (if b1 then Vtrue else Vfalse); auto.
    inv H13. apply eval_Sbinop with v0 v3; simpl; auto.
      apply eval_sfield_trans with te a1 v1; auto.
      apply eval_sfield_trans with te a2 v2; auto.
      congruence.
      inv H.
    simpl. eapply bool_val_eval_cast; eauto.
    constructor 1 with Mint8unsigned; simpl; auto.
  -subst. destruct IHeval_typecmp as [v5 [v6 [B B1]]].
   generalize A3; intros B2.
   eapply locenv_setlvar_getmvl_exists in B2; eauto.
   destruct B2 as [mv B2].
   assert(B3: v0=v5 /\ v3 = v6).
     eapply eval_sexps_split_determ; eauto.
   destruct B3; subst.
   apply eval_Scall with empty_env empty_env (array_comp aid aty num) (mv::nil) (v5::v6::nil) (v5::v6::nil) ((if b1 then Vtrue else Vfalse) :: nil) Int.zero; simpl; auto.
     constructor 2.
     eapply find_funct_array_call; eauto.
     constructor 2; auto.
     constructor 2; auto. apply eval_sfield_trans with te a1 v1; auto.
       constructor 2; auto. apply eval_sfield_trans with te a2 v2; auto.
     congruence.
     apply eval_casts_array; auto.
     constructor 2 with e1; auto. constructor.
     apply local_result_lid_disjoint.
     constructor 2; auto.
     constructor. red; intros. tauto. constructor.
     eapply assign_list_disjoint_field_trans with (v1:=v5) (v2:=v6); eauto.
       apply eval_sfield_trans with te a1 v1; auto.
       apply eval_sfield_trans with te a2 v2; auto.
     congruence.
     apply H10. apply flat_map_filter_type_in with (Tarray aid aty num); auto.
      eapply find_funct_in2; eauto.
  -subst. destruct IHeval_typecmp as [v5 [v6 [B B1]]].
   generalize A3; intros B2.
   eapply locenv_setlvar_getmvl_exists in B2; eauto.
   destruct B2 as [mv B2].
   assert(B3: v0=v5 /\ v3 = v6).
     eapply eval_sexps_split_determ; eauto.
   destruct B3; subst.
   apply eval_Scall with empty_env empty_env (struct_comp sid0 fld0) (mv::nil) (v5::v6::nil) (v5::v6::nil) ((if b1 then Vtrue else Vfalse) :: nil) Int.zero; simpl; auto.
     constructor 2.
     eapply find_funct_struct_call; eauto.
     constructor 2; auto.
     constructor 2; auto. apply eval_sfield_trans with te a1 v1; auto.
       constructor 2; auto. apply eval_sfield_trans with te a2 v2; auto.
     congruence.
     apply eval_casts_array; auto.
     constructor 2 with e1; auto. constructor.
     apply local_result_lid_disjoint.
     constructor 2; auto.
     constructor. red; intros. tauto. constructor.
     eapply assign_list_disjoint_field_trans with (v1:=v5) (v2:=v6); eauto.
       apply eval_sfield_trans with te a1 v1; auto.
       apply eval_sfield_trans with te a2 v2; auto.
     congruence.
     apply H10. apply flat_map_filter_type_in with (Tstruct sid0 fld0); auto.
      eapply find_funct_in2; eauto.
  -constructor; auto.
  -destruct b0,b1,b2;auto.
 +(*eval_strcmp_nil*)
  simpl in *. exists e. split. constructor.
  destruct b0;auto.
Qed.

Lemma trans_node_all_correct:
  forall e e' fd vargs vrets,
  LsemR.eval_node true prog1 gc e e' fd vargs vrets ->
  forall fd', trans_node tdl fd = OK fd' ->
  eval_node false prog2 gc e e' fd' vargs vrets.
Proof.
  induction 1 using LsemR.eval_node_ind2 with
  ( P0 := fun nid te e te' e' s =>
      forall s',
      trans_stmt tdl s = OK s' ->
      eval_stmt false prog2 gc nid te e te' e' s');
  intros.
 +(*node*)
  monadInv H6.
  eapply trans_body_ids_norepet in H1; eauto.
  unfold trans_body in EQ. monadInv EQ.
  apply exec_node with te te1 te2 eh1; simpl; eauto.
  erewrite trans_stmt_fby_eq; eauto.
 +(*Sassign*)
  inv H0. apply eval_Sassign; auto.
 +(*Scall_node*)
  inv H14.
  generalize H1; intros A.
  apply trans_call_func in H1; auto.
  destruct H1 as [fd' [A1 A2]].
  apply eval_Scall with ef ef' fd' vl vargs vargs' vrets i; auto.
  -monadInv A2. monadInv EQ. auto.
  -monadInv A2. monadInv EQ. auto.
  -monadInv A2. monadInv EQ. auto.
 +(*Sfor_start*)
  monadInv H1.
  apply eval_Sfor_start with te1; auto.
  generalize (IHeval_node (Sfor None a2 a3 x)); simpl; auto.
  rewrite EQ. simpl; auto.
 +(*Sfor_false*)
  monadInv H0.
  apply eval_Sfor_false; auto.
 +(*Sfor_loop*)
  monadInv H3.
  apply eval_Sfor_loop with te1 te2 e1; auto.
  -generalize (IHeval_node0 (Sfor None a2 a3 x)); simpl; auto.
   rewrite EQ. simpl; auto.
 +(*Sskip*)
  inv H. constructor.
 +(*Sseq*)
  monadInv H1.
  eapply eval_Sseq; eauto.
 +(*Sif*)
  monadInv H2.
  apply eval_Sif with v b; auto.
  destruct b; auto.
 +(*Scase*)
  inv H2. eapply eval_Scase; eauto.
 +(*Sfby_1*)
  inv H1. eapply eval_Sfby_cycle_1; eauto.
 +(*Sfby_n*)
  inv H5. eapply eval_Sfby_cycle_n; eauto.
 +(*Sfbyn_1*)
  inv H11. eapply eval_Sfbyn_cycle_1; eauto.
 +(*Sfbyn_n*)
  inv H8. eapply eval_Sfbyn_cycle_n; eauto.
 +(*Sarrow*)
  inv H2. eapply eval_Sarrow; eauto.
 +(*Stypecmp*)
  generalize H0 H4. intros A A1.
  eapply eval_typecmp_eval_stmt in H0; eauto.
  eapply locenv_setlvar_getmvl_exists in A1; eauto.
  destruct A1 as [mv A1].
  monadInv H5. inv A.
  -destruct (typeof a1); simpl in *; congruence.
  -(*array_comp*)
   rewrite H6 in *. inv EQ. destruct H0 as [v3 [v4 [? ?]]].
   destruct e as [eh se].
   apply eval_Scall with empty_env empty_env (array_comp x aty num) (mv::nil)
       (v3::v4::nil) (v3::v4::nil)
       ((if b then Vtrue else Vfalse)::nil) Int.zero; auto.
   *simpl. constructor 2; auto.
   *simpl. destruct nk; auto.
   *eapply find_funct_array_call; eauto.
   *constructor 2; auto.
   *simpl. rewrite <-H5, H6.
    apply eval_casts_array; auto.
   *constructor 2 with te'; auto. constructor.
   *simpl. congruence.
   *simpl. congruence.
   *constructor 2; auto.
   *constructor; auto. red; simpl; intros. tauto. constructor.
 -(*struc_comp*)
   rewrite H6 in *. inv EQ. destruct H0 as [v3 [v4 [? ?]]].
   destruct e as [eh se].
   apply eval_Scall with empty_env empty_env  (struct_comp x fld) (mv::nil)
       (v3::v4::nil) (v3::v4::nil)
       ((if b then Vtrue else Vfalse)::nil) Int.zero; auto.
   *simpl. constructor 2; auto.
   *simpl. destruct nk; auto.
   *eapply find_funct_struct_call; eauto.
   *constructor 2; auto.
   *simpl. rewrite <-H5, H6.
    apply eval_casts_array; auto.
   *constructor 2 with te'; auto. constructor.
   *simpl. congruence.
   *simpl. congruence.
   *constructor 2; auto.
   *constructor; auto. red; simpl; intros. tauto. constructor.
Qed.

Lemma init_node_correct:
  forall e fd,
  LsemR.init_node prog1 e fd ->
  forall fd', trans_node tdl fd = OK fd' ->
  init_node prog2 e fd'.
Proof.
  induction 1 using LsemR.init_node_ind2 with
  ( P0 := fun e1 e2 l =>
      init_stmt prog2 e1 e2 l
   ); intros.
 +(*init_node*)
  monadInv H3. simpl in *.
  eapply trans_body_ids_norepet in H; eauto.
  monadInv EQ. constructor 1; simpl in *; auto.
  -erewrite trans_stmt_fby_eq; eauto.
   erewrite trans_stmt_fbysvarsof; eauto.
  -intros. apply H1. erewrite <-trans_stmt_fbysvarsof; eauto.
  -erewrite trans_stmt_instidof_eq; eauto.
 +(*nil*)
  constructor.
 +(*cons*)
  destruct trans_call_func with c fd as [fd' [A A1]]; auto.
  constructor 2 with se1 fd' ef; auto.
  monadInv A1. monadInv EQ; auto.
Qed.

Theorem exec_prog_node_correct:
  forall e main1 vass vrss n maxn,
  exec_prog1 prog1 gc (LsemR.eval_node true) main1 e n maxn vass vrss ->
  forall main2, trans_node tdl main1 = OK main2 ->
  exec_prog1 prog2 gc (eval_node false) main2 e n maxn vass vrss.
Proof.
  induction 1; intros; try congruence.
  +constructor 1 with mrss; trivial.
   monadInv H1. monadInv EQ; auto.
  +constructor 2 with e'; auto.
   monadInv H3. monadInv EQ. auto.
   apply trans_node_all_correct with main1; auto.
Qed.

Lemma initial_states_match_node:
  forall main1 e,
  Lenv.initial_state1 prog1 gc LsemR.init_node main1 e ->
  exists main2, Lenv.initial_state1 prog2 gc init_node main2 e
    /\ trans_node tdl main1 = OK main2.
Proof.
  induction 1; intros; try congruence.
  generalize TRANS. intros.
  monadInv TRANS. destruct (list_in_list _ _) eqn:?; try congruence.
  destruct find_funcs_monad_exits with LustreR.node node (node_block prog1) x (trans_node tdl) (node_main prog1) main1
     as [main2 [? ?]]; auto.
     intros. monadInv H3; auto.
  apply comp_funcs_node_block_disjoint in Heqb.
  cut (fst main2 = node_main prog1). intros A.
  rewrite <-A in *.
  exists main2. split; auto. constructor 1; simpl; auto.
  +inv EQ0. simpl. auto.
  +inv EQ0. simpl in *.
   rewrite find_funct_app_notin_right;auto.
   apply find_funct_in2 in H4.
   apply in_map with (f:=fst) in H4.
   red; intros. eapply Heqb; eauto.
   apply trans_nodes_fids_eq in EQ. rewrite EQ.
   rewrite <-A. auto.
   intros. monadInv H6; auto.
  +inv EQ0. monadInv H3. monadInv EQ0. auto.
  +eapply init_node_correct; eauto.
  +eapply find_funct_fid; eauto.
Qed.

Theorem trans_program_node_correct:
  forall e main1 mass vrss maxn,
  Lenv.initial_state1 prog1 gc LsemR.init_node main1 e->
  exec_prog1 prog1 gc (LsemR.eval_node true) main1 e 1 maxn mass vrss ->
  exists main2, Lenv.initial_state1 prog2 gc init_node main2 e
    /\ exec_prog1 prog2 gc (eval_node false) main2 e 1 maxn mass vrss
    /\ nd_kind (snd main1) = nd_kind (snd main2)
    /\ nd_rets (snd main1) = nd_rets (snd main2).
Proof.
  intros.
  destruct initial_states_match_node with main1 e as [main2 [A A1]]; auto.
  exists main2. repeat (split; auto).
  eapply exec_prog_node_correct; eauto.
  monadInv A1. monadInv EQ. auto.
  monadInv A1. monadInv EQ. auto.
Qed.

End CORRECTNESS.
