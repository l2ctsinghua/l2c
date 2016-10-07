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
Require Import Events.
Require Import List.
Require Import ExtraList.
Require Import Lvalues.
Require Import Lident.
Require Import Maps.
Require Import Memory.
Require Import Globalenvs.
Require Import Integers.
Require Import Floats.
Require Import Bool.
Require Import Lint.
Require Import Values.
Require Import Clop.
Require Import Cltypes.
Require Import Cop.
Require Import Ctypes.
Require Import Lenv.
Require Import Lenvmatch.
Require Import Ctemp.
Require Import CtempProof.
Require Import Clight.
Require Import ClightBigstep.
Require Import Csem.
Require Import CtempGen.
Require Import ClightGen.

Set Implicit Arguments.

Section CORRECTNESS.

Variable prog1: Ctemp.program.
Variable prog2: program.

Hypothesis TRANS:
  trans_program prog1 = prog2.

Let ge1 := Genv.globalenv prog1.
Let ge2 := Genv.globalenv prog2.

Section FUNDEF_CORRECT.

Definition env_match(e1: Ctemp.env)(e2: env): Prop :=
  forall id b t, e1 ! id = Some (b,t) -> e2 ! id = Some (b,trans_type t).

Definition env_none(e1: Ctemp.env)(e2: env): Prop :=
  forall id, e1 ! id = None -> e2 ! id = None.

Definition temp_env_match(le1: Ctemp.temp_env)(le2: temp_env): Prop :=
  forall id v t, le1 ! id = Some (v,t) -> le2 ! id = Some v.

Lemma trans_type_alignof:
  forall ty, Cltypes.alignof ty = alignof (trans_type ty)
with trans_struct_alignof:
  forall fld, Cltypes.alignof_fields fld = alignof_fields (trans_fields fld).
Proof.
 +induction ty; simpl; intros; auto.
 +induction fld; simpl; intros; auto.
  f_equal; auto.
Qed.

Lemma trans_type_sizeof:
  forall ty, Cltypes.sizeof ty = sizeof (trans_type ty)
with trans_struct_sizeof:
  forall fld pos, Cltypes.sizeof_struct fld pos = sizeof_struct (trans_fields fld) pos.
Proof.
 +induction ty; simpl; intros; auto.
  -f_equal; auto.
  -f_equal; auto. apply trans_struct_alignof; auto.
 +induction fld; simpl; intros; auto.
  rewrite trans_type_alignof, trans_type_sizeof; auto.
Qed.

Lemma sem_unary_operation_match:
  forall op v1 t v,
  Clop.sem_unary_operation op v1 t = Some v ->
  sem_unary_operation op v1 (trans_type t) = Some v.
Proof.
  destruct op, t; simpl; intros; auto.
  destruct i; auto.
Qed.

Lemma trans_type_typeconv:
  forall t, typeconv (trans_type t) = trans_type (Cltypes.typeconv t).
Proof.
  destruct t; simpl; auto.
  destruct i; auto.
Qed.

Definition trans_binarith_cases(c: Clop.binarith_cases) :=
  match c with
  | Clop.bin_case_i s => bin_case_i s
  | Clop.bin_case_f => bin_case_f
  | Clop.bin_case_s => bin_case_s
  | Clop.bin_default => bin_default
  end.

Lemma classify_binarith_match:
  forall t1 t2,
  classify_binarith (trans_type t1) (trans_type t2) = trans_binarith_cases (Clop.classify_binarith t1 t2).
Proof.
  unfold classify_binarith, Clop.classify_binarith.
  unfold trans_binarith_cases.
  destruct t1, t2; simpl; auto;
  try (destruct i, s; auto; fail);
  try (destruct f; auto; fail).
  destruct i, i0, s, s0; auto.
  destruct i, s,f;auto.
  destruct f, f0; auto.
Qed.

Lemma binarith_type_match:
  forall c, binarith_type (trans_binarith_cases c) = trans_type (Clop.binarith_type c).
Proof.
  destruct c; auto.
Qed.

Lemma sem_cast_match:
  forall v1 t1 t2 v,
  Clop.sem_cast v1 t1 t2 = Some v ->
  sem_cast v1 (trans_type t1) (trans_type t2) = Some v.
Proof.
  clear.
  unfold Clop.sem_cast, sem_cast, Clop.classify_cast, classify_cast.
  destruct t1, t2; simpl; intros; try congruence.
 +destruct i, v1; inv H; auto.
 +destruct f, v1; inv H; auto.
 +destruct i0, v1; inv H; auto.
 +destruct f, v1; inv H; auto.
 +destruct i,f, v1; inv H; auto.
 +destruct f0,f, v1; inv H; auto.
 +destruct i, v1; inv H; auto.
 +destruct f, v1; inv H; auto.
 +destruct i0, v1; inv H; auto.
 +destruct f, v1; inv H; auto.
 +destruct i, v1; inv H; auto.
 +destruct f, v1; inv H; auto.
 +destruct i0, v1; inv H; auto.
 +destruct f0, v1; inv H; auto.
 +destruct v1; try congruence.
  destruct (ident_eq _ _); simpl in *; auto.
  destruct (Cltypes.fieldlist_eq f f0) eqn:?; inv H.
  unfold proj_sumbool. rewrite pred_dec_true; auto.
Qed.

Lemma sem_binarith_match:
  forall f1 f2 f3 f4 v1 t1 v2 t2 v,
  Clop.sem_binarith f1 f2 f3 f4 v1 t1 v2 t2 = Some v ->
  sem_binarith f1 f2 f3 f4 v1 (trans_type t1) v2 (trans_type t2) = Some v.
Proof.
  clear.
  unfold Clop.sem_binarith, sem_binarith. intros.
  rewrite classify_binarith_match.
  rewrite binarith_type_match.
  destruct (Clop.sem_cast v1 _ _) eqn:?; try congruence.
  apply sem_cast_match in Heqo. rewrite Heqo.
  destruct (Clop.sem_cast v2 _ _) eqn:?; try congruence.
  apply sem_cast_match in Heqo0. rewrite Heqo0.
  destruct (Clop.classify_binarith t1 t2); inv H; auto.
Qed.

Definition trans_add_cases(c: Clop.classify_add_cases) : classify_add_cases :=
  match c with
  | Clop.add_case_pi ty => add_case_pi (trans_type ty)
  | Clop.add_case_ip ty => add_case_ip (trans_type ty)
  | Clop.add_default => add_default
  end.

Lemma trans_classify_add:
  forall t1 t2,
  classify_add (trans_type t1) (trans_type t2) = trans_add_cases (Clop.classify_add t1 t2).
Proof.
  unfold classify_add, Clop.classify_add. intros.
  repeat rewrite trans_type_typeconv.
  destruct (Cltypes.typeconv t1), (Cltypes.typeconv t2); auto.
Qed.

Lemma sem_add_match:
  forall v1 t1 v2 t2 v,
  Clop.sem_add v1 t1 v2 t2 = Some v ->
  sem_add v1 (trans_type t1) v2 (trans_type t2) = Some v.
Proof.
  unfold Clop.sem_add, sem_add. intros.
  rewrite trans_classify_add.
  destruct (Clop.classify_add _ _) eqn:?; simpl;
  try rewrite <-trans_type_sizeof; auto.
  apply sem_binarith_match; auto.
Qed.

Definition trans_sub_cases(c: Clop.classify_sub_cases) : classify_sub_cases :=
  match c with
  | Clop.sub_case_pi ty => sub_case_pi (trans_type ty)
  | Clop.sub_case_pp ty => sub_case_pp (trans_type ty)
  | Clop.sub_default => sub_default
  end.

Lemma trans_classify_sub:
  forall t1 t2,
  classify_sub (trans_type t1) (trans_type t2) = trans_sub_cases (Clop.classify_sub t1 t2).
Proof.
  unfold classify_sub, Clop.classify_sub. intros.
  repeat rewrite trans_type_typeconv.
  destruct (Cltypes.typeconv t1), (Cltypes.typeconv t2); auto.
Qed.

Lemma sem_sub_match:
  forall v1 t1 v2 t2 v,
  Clop.sem_sub v1 t1 v2 t2 = Some v ->
  sem_sub v1 (trans_type t1) v2 (trans_type t2) = Some v.
Proof.
  unfold Clop.sem_sub, sem_sub. intros.
  rewrite trans_classify_sub.
  destruct (Clop.classify_sub _ _) eqn:?; simpl;
  try rewrite <-trans_type_sizeof; auto.
  apply sem_binarith_match; auto.
Qed.

Lemma classify_shift_match:
  forall t1 t2,
  classify_shift (trans_type t1) (trans_type t2) = Clop.classify_shift t1 t2.
Proof.
  unfold classify_shift, Clop.classify_shift. intros.
  repeat rewrite trans_type_typeconv.
  destruct (Cltypes.typeconv t1); auto;
  destruct (Cltypes.typeconv t2); simpl; auto.
Qed.

Lemma sem_shift_match:
  forall f1 f2 v1 t1 v2 t2 v,
  Clop.sem_shift f1 f2 v1 t1 v2 t2 = Some v ->
  sem_shift f1 f2 v1 (trans_type t1) v2 (trans_type t2) = Some v.
Proof.
  unfold Clop.sem_shift, sem_shift. intros.
  rewrite classify_shift_match; auto.
Qed.

Lemma classify_cmp_match:
  forall t1 t2,
  classify_cmp (trans_type t1) (trans_type t2) = Clop.classify_cmp t1 t2.
Proof.
  unfold classify_cmp, Clop.classify_cmp. intros.
  repeat rewrite trans_type_typeconv.
  destruct (Cltypes.typeconv t1); auto;
  destruct (Cltypes.typeconv t2); simpl; auto.
Qed.

Lemma sem_cmp_match:
  forall c v1 t1 v2 t2 m v,
  Clop.sem_cmp c v1 t1 v2 t2 m = Some v ->
  sem_cmp c v1 (trans_type t1) v2 (trans_type t2) m = Some v.
Proof.
  unfold Clop.sem_cmp, sem_cmp. intros.
  rewrite classify_cmp_match.
  destruct (Clop.classify_cmp t1 t2) eqn:?; auto.
  apply sem_binarith_match; auto.
Qed.

Lemma sem_binary_operation_match:
  forall op v1 t1 v2 t2 m v,
  Clop.sem_binary_operation op v1 t1 v2 t2 m = Some v ->
  sem_binary_operation op v1 (trans_type t1) v2 (trans_type t2) m = Some v.
Proof.
  destruct op; simpl; intros;
  try (apply sem_binarith_match; auto);
  try (apply sem_cmp_match; auto).
 +apply sem_add_match; auto.
 +apply sem_sub_match; auto.
 +apply sem_shift_match; auto.
 +apply sem_shift_match; auto.
Qed.

Lemma trans_type_bool_val:
  forall v t,
  bool_val v (trans_type t) = Clop.bool_val v t.
Proof.
  unfold bool_val, Clop.bool_val, classify_bool, Clop.classify_bool.
  destruct v, t; simpl; auto.
  destruct i; auto.
  destruct i0; auto.
  destruct i0; auto.
  destruct i; auto.
  destruct i; auto.
  destruct i0; auto.
Qed.

Lemma classify_fun_match:
  forall ty tyl cconv,
  Clop.classify_fun ty = Clop.fun_case_f tyl Cltypes.Tvoid cconv ->
  classify_fun (trans_type ty) = fun_case_f (trans_typelist tyl) Tvoid cconv.
Proof.
  clear.
  destruct ty; simpl; intros; try congruence.
 +destruct ty; simpl; try congruence. inv H. auto.
 +inv H. auto.
Qed.

Lemma trans_fields_offset:
  forall fld i pos,
  field_offset_rec i (trans_fields fld) pos = Cltypes.field_offset_rec i fld pos.
Proof.
  induction fld; simpl; intros; auto.
  destruct (ident_eq _ _); rewrite trans_type_alignof; auto.
  rewrite trans_type_sizeof; auto.
Qed.

Lemma trans_type_access_mode:
  forall t, access_mode (trans_type t) =  Cltypes.access_mode t.
Proof.
  destruct t; simpl; auto.
Qed.

Lemma deref_loc_match:
  forall t m loc ofs v,
  Ctemp.deref_loc t m loc ofs v ->
  deref_loc (trans_type t) m loc ofs v.
Proof.
  induction 1; intros.
 +constructor 1 with chunk; auto.
  rewrite trans_type_access_mode; auto.
 +constructor 2; auto.
  rewrite trans_type_access_mode; auto.
 +constructor 3; auto.
  rewrite trans_type_access_mode; auto.
Qed.

Definition fundef_match(f1: Ctemp.fundef)(f2: fundef) : Prop :=
  f2 = trans_fundef f1.

Definition type_match(t1: Cltypes.type)(t2: type) : Prop :=
  t2 = trans_type t1.

Lemma trans_match_program:
  match_program fundef_match type_match nil (prog_main prog1) prog1 prog2.
Proof.
  unfold match_program. subst. split; auto.
  exists (prog_defs (trans_program prog1)).
  rewrite <-app_nil_end. split; auto.
  unfold transform_program. simpl.
  induction (prog_defs prog1); simpl.
  constructor.
  constructor 2; auto.
  destruct a. destruct g; simpl.
  constructor 1; auto. unfold fundef_match; auto.
  unfold trans_globvar. destruct v. simpl.
   constructor 2; auto. unfold type_match. auto.
Qed.

Lemma find_symbol_match:
  forall id, Genv.find_symbol ge2 id = Genv.find_symbol ge1 id.
Proof.
  generalize trans_match_program. intros.
  eapply Genv.find_symbol_match; eauto.
Qed.

Lemma eval_expr_match:
  forall e le te m,
  (
   forall a v,
   Ctemp.eval_expr ge1 e le te m a v ->
   forall e2 le2, temp_env_match le le2 ->
   temp_env_match te le2 ->
   env_match e e2 ->
   env_none e e2 ->
   eval_expr ge2 e2 le2 m (trans_expr a) v
  )
/\
  (
   forall a loc ofs,
   Ctemp.eval_lvalue ge1 e le te m a loc ofs ->
   forall e2 le2, temp_env_match le le2 ->
   temp_env_match te le2 ->
   env_match e e2 ->
   env_none e e2 ->
   eval_lvalue ge2 e2 le2 m (trans_expr a) loc ofs
  ).
Proof.
 intros until m.
 apply Ctemp.eval_expr_lvalue_ind; simpl; intros.
 +econstructor.
 +econstructor.
 +econstructor.
 +econstructor. apply H0 with ty; auto.
 +constructor. apply H1 with ty; auto.
 +constructor; auto.
 +apply eval_Eunop with v1; auto.
  rewrite trans_expr_typeof; auto.
  apply sem_unary_operation_match; auto.
 +apply eval_Ebinop with v1 v2; auto.
  repeat rewrite trans_expr_typeof; auto.
  apply sem_binary_operation_match; auto.
 +apply eval_Ecast with v1; auto.
  rewrite trans_expr_typeof; auto.
  apply sem_cast_match; auto.
 +rewrite trans_type_sizeof. constructor.
 +rewrite trans_type_alignof. constructor.
 +apply eval_Elvalue with loc ofs; auto.
  rewrite trans_expr_typeof; auto.
  apply deref_loc_match; auto.
 +constructor 1; auto.
 +constructor 2; auto.
  rewrite find_symbol_match; auto.
 +constructor 3; auto.
 +constructor 4 with id (trans_fields fList) noattr; auto.
  rewrite trans_expr_typeof, H1; simpl; auto.
  unfold field_offset. rewrite trans_fields_offset; auto.
Qed.

Lemma eval_exprs_match:
  forall e le te m al tl vl,
  Ctemp.eval_exprlist ge1 e le te m al tl vl ->
  forall e2 le2, temp_env_match le le2 ->
  temp_env_match te le2 ->
  env_match e e2 ->
  env_none e e2 ->
  eval_exprlist ge2 e2 le2 m (trans_exprs al) (trans_typelist tl) vl.
Proof.
  induction 1; simpl; intros.
  constructor 1.
  constructor 2 with v1; auto.
  eapply eval_expr_match; eauto.
  rewrite trans_expr_typeof; auto.
  apply sem_cast_match; auto.
Qed.

Lemma trans_lblstmt_select_switch:
  forall n sl,
  select_switch (Int.unsigned n) (trans_lblstmt sl) = trans_lblstmt (Ctemp.select_switch n sl).
Proof.
  induction sl; simpl; auto.
  unfold select_switch. simpl. unfold Int.eq.
  destruct (zeq _ _) eqn:?; simpl in *; auto.
Qed.

Lemma temp_env_match_setsame:
  forall le1 le2 i v t,
  temp_env_match le1 le2 ->
  temp_env_match (PTree.set i (v, t) le1) (PTree.set i v le2).
Proof.
  clear TRANS.
  intros. red. intros.
  compare i id; intros; subst.
  rewrite PTree.gss in *; auto. congruence.
  rewrite PTree.gso in *; auto. apply H with t0;auto.
Qed.

Lemma bind_parameter_temps_match:
  forall l vl le1 le1',
  Ctemp.bind_parameter_temps l vl le1 = Some le1' ->
  forall le2, temp_env_match le1 le2 ->
  exists le2', bind_parameter_temps (map trans_var l) vl le2 = Some le2'
    /\ temp_env_match le1' le2'.
Proof.
  clear TRANS.
  induction l; simpl; intros.
  +destruct vl; inv H. eauto.
  +destruct a. destruct vl; try congruence.
   destruct IHl with vl (PTree.set i (v, t) le1) le1' (PTree.set i v le2) as [le2' [? ?]]; auto.
   apply temp_env_match_setsame; auto.
   exists le2'. split; auto.
Qed.

Lemma bind_parameter_temps_app:
  forall l1 vargs le le1 l2 vrets le2,
  bind_parameter_temps l1 vargs le = Some le1 ->
  bind_parameter_temps l2 vrets le1 = Some le2 ->
  bind_parameter_temps (l1 ++ l2) (vargs ++ vrets) le = Some le2.
Proof.
  clear TRANS.
  induction l1; simpl; intros.
  +destruct vargs; inv H; simpl; auto.
  +destruct a. destruct vargs; try congruence.
   simpl. eapply IHl1; eauto.
Qed.

Lemma bind_parameter_temps_match_right:
  forall l vl le1 le2 le,
  bind_parameter_temps l vl le1 = Some le2 ->
  ptree_ids_none (map fst l) le ->
  temp_env_match le le1 ->
  temp_env_match le le2.
Proof.
  clear TRANS.
  induction l; simpl; intros; auto.
  +destruct vl; inv H; auto.
  +destruct a. destruct vl; try congruence.
   eapply IHl; eauto.
   red; intros. apply H0; simpl; auto.
   red; intros. rewrite PTree.gso; auto.
   apply H1 with t0; auto.
   red; intros; subst. rewrite H0 in H2; simpl; auto.
   congruence.
Qed.

Lemma trans_lblstmt_simpl:
  forall s e le m t le' m' out,
  exec_stmt ge2 e le m (trans_stmt (Ctemp.seq_of_labeled_statement s)) t le' m' out ->
  exec_stmt ge2 e le m (seq_of_labeled_statement (trans_lblstmt s)) t le' m' out.
Proof.
  clear TRANS.
  induction s; simpl; intros.
  +destruct out.
   apply exec_Sseq_2; auto. congruence.
   apply exec_Sseq_2; auto. congruence.
   rewrite <-E0_right with t.
    apply exec_Sseq_1 with le' m'; auto. constructor.
   apply exec_Sseq_2; auto. congruence.
  +inv H.
   -apply exec_Sseq_1 with le1 m1; auto.
   -apply exec_Sseq_2; auto.
Qed.

Definition trans_outcome(out: Ctemp.outcome) : outcome :=
  match out with
  | Ctemp.Out_break => Out_break
  | Ctemp.Out_normal => Out_normal
  | Ctemp.Out_return None => Out_return None
  | Ctemp.Out_return (Some (v, t)) => Out_return (Some (v, trans_type t))
  end.

Lemma out_break_or_return_match:
  forall o1 o2,
  Ctemp.out_break_or_return o1 o2 ->
  out_break_or_return (trans_outcome o1) (trans_outcome o2).
Proof.
  induction 1; simpl; auto.
  constructor.
  destruct ov; try constructor.
  destruct p; constructor.
Qed.

Lemma trans_outcome_switch:
  forall out, trans_outcome (Ctemp.outcome_switch out) = outcome_switch (trans_outcome out).
Proof.
  destruct out; simpl; auto.
  destruct o; auto. destruct p; auto.
Qed.

Lemma trans_type_alignof_blockcopy:
  forall ty, Cltypes.alignof_blockcopy ty = alignof_blockcopy (trans_type ty).
Proof.
  induction ty; simpl; auto.
  rewrite <-trans_struct_alignof; auto.
   generalize (alignof_fields_range f); intros. rewrite Z.min_r; omega.
Qed.

Lemma assign_loc_match:
  forall t m loc ofs v m',
  Ctemp.assign_loc t m loc ofs v m' ->
  assign_loc (trans_type t) m loc ofs v m'.
Proof.
  induction 1; intros.
  constructor 1 with chunk; auto.
  rewrite trans_type_access_mode; auto.
  constructor 2 with bytes; auto.
  rewrite trans_type_access_mode; auto.
  rewrite <-trans_type_alignof_blockcopy, <-trans_type_sizeof; auto.
  rewrite <-trans_type_alignof_blockcopy, <-trans_type_sizeof; auto.
  rewrite <-trans_type_sizeof; auto.
  rewrite <-trans_type_sizeof; auto.
Qed.

Fixpoint typelist_app(tyl1 tyl2: typelist) : typelist :=
  match tyl1 with
  | Tnil => tyl2
  | Tcons ty tyl => Tcons ty (typelist_app tyl tyl2)
  end.

Lemma eval_exprlist_app:
  forall e le m al tyargs vargs,
  eval_exprlist ge2 e le m al tyargs vargs ->
  forall rets tyrets vrets,
  eval_exprlist ge2 e le m rets tyrets vrets ->
  eval_exprlist ge2 e le m (al++ rets) (typelist_app tyargs tyrets) (vargs ++ vrets).
Proof.
  induction 1; simpl; intros; auto.
  constructor 2 with v1; auto.
Qed.

Lemma trans_typelist_app:
  forall l1 l2,
  trans_typelist (Ctemp.typelist_app l1 l2) = typelist_app (trans_typelist l1) (trans_typelist l2).
Proof.
  induction l1; simpl; intros; auto.
  f_equal; auto.
Qed.

Lemma bind_parameter_temps_app_match:
  forall l1 vargs le l2 vrets te,
  Ctemp.bind_parameter_temps l1 vargs empty_temp = Some le ->
  Ctemp.bind_parameter_temps l2 vrets empty_temp = Some te ->
  list_norepet (Ctemp.var_names (l1 ++ l2)) ->
  exists le2, bind_parameter_temps (map trans_var (l1++l2)) (vargs++vrets) (PTree.empty val) = Some le2
    /\ temp_env_match le le2
    /\ temp_env_match te le2.
Proof.
  unfold Ctemp.var_names. intros.
  rewrite map_app in *. apply list_norepet_app in H1.
  destruct H1 as [? [? ?]].
  destruct bind_parameter_temps_match with l1 vargs empty_temp le (PTree.empty val) as [le1 [A A1]]; auto.
    red. intros. rewrite PTree.gempty in *. congruence.
  destruct bind_parameter_temps_match with l2 vrets empty_temp te le1 as [le2 [A2 A3]]; auto.
    red. intros. rewrite PTree.gempty in *. congruence.
  exists le2. repeat (split; auto).
  eapply bind_parameter_temps_app; eauto.
  eapply bind_parameter_temps_match_right; eauto.
  red; intros. erewrite bind_parameter_temps_notin_eq; eauto.
  rewrite PTree.gempty; auto.
  eapply list_disjoint_notin; eauto.
  apply list_disjoint_sym; auto.
  rewrite map_map; auto.
Qed.

Definition element_match(x: block*Cltypes.type)(y: block*type): Prop :=
  fst x = fst y /\ sizeof (snd y) = sizeof (trans_type (snd x)).

Lemma env_match_blocks_of_env:
  forall e1 e2,
  env_match e1 e2 ->
  env_none e1 e2 ->
  Ctemp.blocks_of_env e1 = blocks_of_env e2.
Proof.
  clear.
  unfold blocks_of_env, Ctemp.blocks_of_env. intros.
  exploit (PTree.elements_canonical_order element_match e1 e2).
    intros. destruct x. exists (b, trans_type t). repeat split; auto.
    intros. destruct y. destruct (e1 ! i) eqn:?.
     destruct p. apply H in Heqo. rewrite H1 in Heqo. inv Heqo.
      exists (b0,t0). repeat split; auto.
     apply H0 in Heqo. congruence.
  generalize (PTree.elements e1) (PTree.elements e2). clear.
  induction 1; simpl; intros; auto.
  destruct a1, b1, H; simpl in *; subst.
  destruct p0, p2. destruct H1. simpl in *. subst.
  rewrite H1. rewrite trans_type_sizeof.
  f_equal; auto.
Qed.

Lemma alloc_variables_match:
  forall e1 m l e1' m',
  Ctemp.alloc_variables e1 m l e1' m' ->
  forall e2, env_match e1 e2 ->
  env_none e1 e2 ->
  exists e2', alloc_variables e2 m (map trans_var l) e2' m'
    /\ env_match e1' e2'
    /\ env_none e1' e2'.
Proof.
  clear.
  induction 1; simpl; intros.
  +exists e2. split; auto. constructor.
  +destruct IHalloc_variables with (PTree.set id (b1, trans_type ty) e0) as [e2' [? [? ?]]]; auto.
   -red. intros. compare id id0; intros; subst.
    rewrite PTree.gss in *; congruence.
    rewrite PTree.gso in *; auto.
   -red. intros. compare id id0; intros; subst.
    rewrite PTree.gss in *; congruence.
    rewrite PTree.gso in *; auto.
   -exists e2'. split; auto.
    constructor 2 with m1 b1; auto.
    rewrite <-trans_type_sizeof; auto.
Qed.

Lemma trans_fundef_correct:
  (
   forall e le1 te1 m s t m' out,
   Ctemp.exec_stmt ge1 e le1 te1 m s t m' out ->
   forall e2 le2,
   temp_env_match le1 le2 ->
   temp_env_match te1 le2 ->
   env_match e e2 ->
   env_none e e2 ->
   exec_stmt ge2 e2 le2 m (trans_stmt s) t le2 m' (trans_outcome out)
  )
/\
  (
   forall m f vargs vrets t m' vr,
   Ctemp.eval_funcall ge1 m f vargs vrets t m' vr ->
   eval_funcall ge2 m (trans_fundef f) (vargs++vrets) t m' vr
  ).
Proof.
 apply (Ctemp.exec_stmt_funcall_ind ge1); simpl; intros.
 +constructor.
 +apply exec_Sassign with loc ofs v2 v; auto.
  eapply eval_expr_match; eauto.
  eapply eval_expr_match; eauto.
  repeat rewrite trans_expr_typeof; auto.
  apply sem_cast_match; auto.
  rewrite trans_expr_typeof; auto.
  apply assign_loc_match; auto.
 +change le2 with (set_opttemp None vres le2) at 2.
  apply exec_Sbuiltin with (Vptr bdst odst :: Vptr bsrc osrc ::nil); auto.
  -clear TRANS. subst. inv H1. inv H13. inv H15.
   constructor 2 with v1; auto.
   eapply eval_expr_match; eauto.
   rewrite trans_expr_typeof; auto.
   apply sem_cast_match; auto.
   constructor 2 with v0; auto.
   eapply eval_expr_match; eauto.
   rewrite trans_expr_typeof; auto.
   apply sem_cast_match; auto.
   constructor.
  -simpl. clear TRANS. inversion H. inversion H0.
   rewrite H10, H13.
   *inv H2. econstructor; eauto.
   *inv H7.
   *inv H7.
 +change le2 with (set_opttemp None Vundef le2) at 2.
  apply exec_Scall with (trans_typelist (Ctemp.typelist_app tyargs tyrets)) Tvoid cconv vf (vargs++vrets) (trans_fundef f); auto.
  -rewrite trans_expr_typeof; auto.
   apply classify_fun_match; auto.
  -eapply eval_expr_match; eauto.
  -unfold trans_exprs. rewrite map_app.
   rewrite trans_typelist_app.
   apply eval_exprlist_app; auto; eapply eval_exprs_match; eauto.
  -generalize trans_match_program. intros A.
   apply Genv.find_funct_match with (v:=vf) (f:=f) in A; auto.
   destruct A as [? [? A]]. unfold fundef_match in A.
   subst x; auto.
  -clear -H4. destruct f; simpl in *.
   unfold type_of_function, Ctemp.type_of_function, trans_func in *.
   simpl. inv H4. rewrite H1. f_equal; auto. clear.
   induction (Ctemp.fn_params f ++ Ctemp.fn_temps f); simpl; intros; auto.
   destruct a. simpl. f_equal; auto.
 +apply exec_Sseq_1 with le2 m1; auto.
 +apply exec_Sseq_2; auto.
  destruct out; simpl; try congruence.
  destruct o; try congruence. destruct p; congruence.
 +apply exec_Sifthenelse with v1 b; auto.
  eapply eval_expr_match; eauto.
  rewrite trans_expr_typeof; auto.
  rewrite trans_type_bool_val; auto.
  destruct b; auto.
 +apply exec_Sreturn_none; auto.
 +rewrite <-trans_expr_typeof. apply exec_Sreturn_some.
  eapply eval_expr_match; eauto.
 +constructor.
 +clear TRANS. unfold Sfor in *.
  generalize (H3 e2 le2 H4 H5 H6 H7). intros.
  inv H8. inv H14; auto. econstructor; eauto.
  inv H14. congruence.
 +unfold Sfor. change E0 with (E0 ** E0).
  apply exec_Sseq_1 with le2 m; auto. constructor.
  apply exec_Sloop_stop1 with Out_break.
  constructor; auto.
  apply exec_Sifthenelse with v false; auto.
  eapply eval_expr_match; eauto.
  rewrite trans_expr_typeof; auto.
  rewrite trans_type_bool_val; auto.
  constructor. congruence. constructor.
 +clear TRANS. unfold Sfor.
  change t with (E0 ** t).
  apply exec_Sseq_1 with le2 m; auto.
  constructor.
  apply exec_Sloop_stop1 with (trans_outcome out1); auto.
  change t with (E0 ** t).
  apply exec_Sseq_1 with le2 m; auto.
  apply exec_Sifthenelse with v true; auto.
  eapply eval_expr_match; eauto.
  rewrite trans_expr_typeof; auto.
  rewrite trans_type_bool_val; auto.
  constructor.
  apply out_break_or_return_match; auto.
 +unfold Sfor in *.
  change (t1 ** t2 ** t3) with (E0 ** t1 ** t2 ** t3).
  apply exec_Sseq_1 with le2 m; auto.
  constructor.
  eapply exec_Sloop_loop; eauto.
  change t1 with (E0 ** t1).
  apply exec_Sseq_1 with le2 m; auto.
  apply exec_Sifthenelse with v true; auto.
  eapply eval_expr_match; eauto.
  rewrite trans_expr_typeof; auto.
  rewrite trans_type_bool_val; auto.
  constructor.
  clear TRANS. inv H3; simpl; constructor.
  generalize (H6 e2 le2 H7 H8 H9 H10). intros.
  clear TRANS. inv H11. inv H17. auto.
  inv H17. congruence.
 +simpl. rewrite trans_outcome_switch; auto.
  apply exec_Sswitch with (Vint n) (Int.unsigned n); auto.
  eapply eval_expr_match; eauto.
  rewrite trans_expr_typeof; auto. destruct (Ctemp.typeof a); simpl; auto.
  rewrite trans_lblstmt_select_switch.
  apply trans_lblstmt_simpl; auto.
 +eapply bind_parameter_temps_app_match with (l1:=Ctemp.fn_params f) in H3; eauto.
  destruct H3 as [le2 [? [? ?]]].
  apply alloc_variables_match with (e2:= empty_env) in H1.
  destruct H1 as [e2 [? [? ?]]].
  constructor 1 with le2 e2 le2 m1 m2 (trans_outcome out); simpl; auto.
  -unfold var_names. rewrite map_map. auto.
  -unfold var_names. rewrite map_map. auto.
  -unfold var_names. repeat rewrite map_map.
   simpl. red; intros; auto.
  -clear -H6. destruct out; simpl in *; auto.
   destruct (Ctemp.fn_return f); auto.
   destruct o; auto.
   destruct p. simpl. destruct H6. split.
   destruct (Ctemp.fn_return f); simpl in *; try congruence.
   apply sem_cast_match; auto.
   destruct (Ctemp.fn_return f); auto.
  -erewrite <-env_match_blocks_of_env; eauto.
  -red. intros. rewrite PTree.gempty in *. congruence.
  -red. intros. apply PTree.gempty.
Qed.

End FUNDEF_CORRECT.


Section PROGRAM_CORRECT.

Lemma trans_program_correct_general:
  forall bi bo main1 m n maxn vass vrss,
  Ctemp.exec_prog prog1 bi bo main1 m n maxn vass vrss ->
  exec_prog prog2 bi bo (trans_fundef main1) m n maxn vass vrss.
Proof.
  induction 1; intros.
  +constructor 1; auto.
  +constructor 2 with b1 b2 m1 mv1 mv2 m'; auto.
   apply trans_fundef_correct in H3; auto.
Qed.

Lemma prog_main_match:
  prog_main prog2 = prog_main prog1.
Proof.
  subst prog2. auto.
Qed.

Lemma type_of_fundef_case_match:
  forall f fi ity oty b,
  Ctemp.type_of_fundef_case (Ctemp.type_of_fundef f) (Ctemp.type_of_fundef fi) ity oty b ->
  type_of_fundef_case (type_of_fundef (trans_fundef f))
    (type_of_fundef (trans_fundef fi)) (trans_type ity) (trans_type oty) b.
Proof.
  destruct f,fi. simpl.
  unfold trans_func, Ctemp.type_of_function, type_of_function.
  destruct f, f0; simpl. clear. intros. inv H.
  +destruct (fn_params ++ fn_temps); simpl in *.
   destruct (fn_params0 ++ fn_temps0); simpl in *.
   constructor 1; auto. destruct p; inv H4.
   destruct p; inv H1.
  +destruct (fn_params ++ fn_temps); simpl in *; try congruence.
   destruct (fn_params0 ++ fn_temps0); simpl in *; try congruence.
   destruct p, p0. inv H1. inv H4.
   destruct l; simpl in *. destruct l0; simpl in *.
   constructor 2; auto. destruct p; inv H1.
   destruct p; inv H2.
  +destruct (fn_params ++ fn_temps); simpl in *; try congruence.
   destruct p; inv H1.
   destruct (fn_params0 ++ fn_temps0); simpl in *.
   destruct l; simpl in *.
   constructor 3; auto. destruct p; inv H2.
   destruct p; inv H4.
  +destruct (fn_params ++ fn_temps); simpl in *; try congruence.
   destruct (fn_params0 ++ fn_temps0); simpl in *; try congruence.
   destruct p, p0. inv H1. inv H4.
   destruct l; simpl in *; try congruence. destruct p; inv H2.
   destruct l0; simpl in *. destruct l; simpl in *.
   constructor 4; auto. destruct p; inv H3.
   destruct p; inv H1.
Qed.

Lemma initial_states_match:
  forall bi bo main1 m,
  Ctemp.initial_state prog1 bi bo main1 m ->
  Csem.initial_state prog2 bi bo (trans_fundef main1) m.
Proof.
  induction 1; intros.
  generalize trans_match_program. intros A.
  constructor 1 with b1 b2 (trans_fundef fi) m_init m0 m1 (trans_type ity) (trans_type oty) b; auto.
  -apply Genv.init_mem_match with (m:=m_init) in A; auto.
  -rewrite prog_main_match. rewrite find_symbol_match; auto.
  -rewrite prog_main_match. rewrite find_symbol_match; auto.
  -apply Genv.find_funct_match with (v:=Vptr b1 Int.zero) (f:=fi) in A; auto.
   destruct A as [? [? ?]]. unfold fundef_match in H9.
   subst; auto.
  -apply Genv.find_funct_match with (v:=Vptr b2 Int.zero) (f:=main1) in A; auto.
   destruct A as [? [? ?]]. unfold fundef_match in *.
   subst; auto.
  -apply type_of_fundef_case_match; auto.
  -rewrite <-trans_type_sizeof; auto.
  -rewrite <-trans_type_sizeof; auto.
  -apply trans_fundef_correct in H7. subst ge2 prog2. auto.
Qed.

Theorem trans_program_correct:
  forall bi bo main1 m n maxn vass vrss,
  Ctemp.initial_state prog1 bi bo main1 m ->
  Ctemp.exec_prog prog1 bi bo main1 m n maxn vass vrss ->
  exists main2, Csem.initial_state prog2 bi bo main2 m
    /\ Csem.exec_prog prog2 bi bo main2 m n maxn vass vrss.
Proof.
  intros.
  exists (trans_fundef main1). split.
  apply initial_states_match; auto.
  apply trans_program_correct_general; auto.
Qed.

End PROGRAM_CORRECT.

End CORRECTNESS.
