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
Require Import Maps.
Require Import Memory.
Require Import Globalenvs.
Require Import Integers.
Require Import Floats.
Require Import Bool.
Require Import Ltypes.
Require Import Lustre.
Require Import LustreF.
Require Import Lint.
Require Import Lvalues.
Require Import Lop.
Require Import Lenv.
Require Import Lenvmatch.
Require Import Lsem.
Require Import LsemD.
Require Import LsemC.
Require Import Values.
Require Import Cop.
Require Import Ctypes.
Require Import Clop.
Require Import Cltypes.
Require Import Clight.
Require Import ClightBigstep.
Require Import Ctemp.
Require Import MemProof.
Require Import CtempProof.
Require Import CtempGen.
Require Import Lident.

(*Set Implicit Arguments.*)

Section CORRECTNESS.

Variable progL: LustreF.program.
Variable progC: program.

Hypothesis TRANS:
  trans_program progL = progC.

Hypothesis GLOBAL_IDS_NOREPET:
   list_norepet (map fst (const_block progL) ++ map fst (node_block progL)).

Let geC := Genv.globalenv progC.

Section NODE_CORRECT.

Variable gcL: locenv.

Variable bi bo: block.

Hypothesis BLOCK_LT:
  Plt bi bo.

Definition locvars_match(te: locenv)(eC: env)(m: mem)(bs: block)(bl: list (block*(int*type))) : Prop :=
  forall id mv ty, te!id = Some (mv,ty) ->
  exists b, eC!id = Some (b, ty)
   /\ Ple bs b
   /\ ~ In b (map (@fst block (int*type)) bl)
   /\ Mem.loadbytes m b 0 (sizeof ty) = Some mv.

Definition locvars_none(te: locenv)(eC: env): Prop :=
  forall id, te ! id = None -> eC ! id = None.

Definition locrets_match(e: locenv)(teC: temp_env)(m: mem)(bl: list (block*(int*type))) : Prop :=
  forall id mv ty, e!id = Some (mv,ty) ->
  exists l o, teC!id = Some (Vptr l o,Tpointer ty)
   /\ In (l,(o,ty)) bl
   /\ Int.unsigned o + Z_of_nat (length mv) <= Int.max_signed
   /\ Mem.loadbytes m l (Int.unsigned o) (sizeof ty) = Some mv
   /\ Mem.range_perm m l (Int.unsigned o) (Int.unsigned o + sizeof ty) Cur Writable
   /\ (alignof ty | Int.unsigned o).

Definition locargs_match(ta: locenv)(leC: temp_env)(m: mem)(bs: block)(bl: list (block*(int*type))) : Prop :=
  forall id mv ty, ta!id = Some (mv,ty) ->
  exists v vc, load_mvl ty mv Int.zero v
   /\ leC!id = Some (vc,trans_ptype ty)
   /\ arg_blocks_range bs bl vc ty
   /\ val_match m ty v vc.

Definition globconsts_match(m: mem): Prop :=
  forall id mv ty, gcL ! id = Some (mv,ty) ->
  exists l, Genv.find_symbol geC id = Some l
    /\ Plt l bi
    /\ Mem.loadbytes m l 0 (Z_of_nat (length mv)) = Some mv.

Definition env_match(ta te e: locenv)(eC: env)(leC teC: temp_env)(m: mem)(bs: block)(bl: list (block*(int*type))): Prop :=
  globconsts_match m
   /\ locvars_match te eC m bs bl
   /\ locrets_match e teC m bl
   /\ locargs_match ta leC m bs bl
   /\ locvars_none te eC.

Inductive retval_match(e: locenv)(m: mem): ident*type -> block*(int*type) -> Prop :=
  | retval_match_: forall id ty l o mv,
     e ! id = Some (mv, ty) ->
     Int.unsigned o + Z.of_nat (length mv) <= Int.max_signed ->
     Mem.loadbytes m l (Int.unsigned o) (sizeof ty) = Some mv ->
     Mem.range_perm m l (Int.unsigned o) (Int.unsigned o + sizeof ty) Cur Writable ->
     (alignof ty | Int.unsigned o) ->
     sizeof ty > 0 ->
     retval_match e m (id,ty) (l, (o, ty)).

Definition retvals_match(e: locenv)(m: mem)(rets: list (ident*type))(bl: list (block*(int*type))): Prop :=
  Forall2 (retval_match e m) rets bl.

Lemma locvars_match_empty:
  forall eC m bs bl, locvars_match empty_locenv eC m bs bl.
Proof.
  unfold locvars_match. intros.
  rewrite PTree.gempty in H. congruence.
Qed.

Lemma const_block_names_norepet:
  list_norepet (map fst (const_block progL)).
Proof.
  apply list_norepet_app in GLOBAL_IDS_NOREPET. intuition.
Qed.

Lemma func_block_names_eq:
  prog_defs_names progC = map fst (const_block progL) ++ map fst (node_block progL).
Proof.
  unfold prog_defs_names. inversion TRANS. simpl.
  rewrite map_app, map_map. simpl. rewrite map_map. auto.
Qed.

Lemma globfuncs_match:
  forall id f, find_funct (node_block progL) id = Some (id,f) ->
  exists l, Genv.find_symbol geC id = Some l
    /\ Genv.find_funct geC (Vptr l Int.zero) = Some (trans_body f).
Proof.
  intros.
  destruct Genv.find_funct_ptr_exists with fundef type progC id (trans_body f) as [l [? ?]]; auto.
  +rewrite func_block_names_eq. auto.
  +apply find_funct_in2 in H. inversion TRANS. simpl.
    apply in_map with (f:=trans_node) in H; auto.
    apply in_or_app. simpl; auto.
  +exists l. repeat (split; auto).
Qed.

Lemma eval_aryacc_match:
  forall eC leC teC m a l ofs aid ty z a1 i,
  eval_lvalue geC eC leC teC m (trans_expr a) l ofs ->
  Lustre.typeof a = Tarray aid ty z ->
  eval_expr geC eC leC teC m (trans_expr a1) (Vint i) ->
  has_type (Lvalues.Vint i) (Lustre.typeof a1) ->
  eval_lvalue geC eC leC teC m (Eindex (trans_expr a) (trans_expr a1) ty) l (Int.add ofs (array_ofs i ty)).
Proof.
  clear.
  unfold Eindex; intros.
  apply eval_Ederef; auto.
  apply eval_Ebinop with (Vptr l ofs) (Vint i); auto.
  *apply eval_Elvalue with l ofs; auto.
   rewrite trans_expr_typeof.
   rewrite H0. simpl. constructor 2; auto.
  *repeat rewrite trans_expr_typeof. rewrite H0. simpl.
   destruct (Lustre.typeof a1); inv H2. simpl.
   apply sem_add_ptr_eq; auto.
Qed.

Lemma eval_field_match:
  forall eC leC teC m a l ofs sid fld i delta ty,
  eval_lvalue geC eC leC teC m (trans_expr a) l ofs ->
  Lustre.typeof a = Tstruct sid fld ->
  field_offset i fld = OK delta ->
  eval_lvalue geC eC leC teC m (Efield (trans_expr a) i ty) l (Int.add ofs (Int.repr delta)).
Proof.
  intros.
  apply eval_Efield_struct with sid fld; auto.
  +apply eval_Elvalue with l ofs; auto.
   rewrite trans_expr_typeof.
   rewrite H0. simpl. constructor 3; auto.
  +rewrite trans_expr_typeof, H0; auto.
Qed.

Lemma eval_lvalue_match_aid_val:
  forall ta te e a id o k eC leC teC m mv t bs bl,
  LsemC.eval_lvalue gcL ta te e a id o k ->
  env_match ta te e eC leC teC m bs bl ->
  k = Aid ->
  ta ! id = Some (mv, t) ->
  is_arystr t = false ->
  exists v vc,  leC ! id = Some (vc,trans_ptype t)
    /\ load_mvl (Lustre.typeof a) mv o v
    /\ val_match m t v vc
    /\ a = Savar id t.
Proof.
  clear.
  induction 1; simpl; intros; subst; try congruence.
  -(*Aid*)
   rewrite H in H2. inv H2.
   destruct H0 as [? [? [? [? ?]]]].
   destruct H5 with id mv t as [v [vc [? [? [? ?]]]]]; auto.
   exists v, vc. repeat (split; auto).
  -(*Sarray*)
   destruct IHeval_lvalue as [v [vc [? [? [? ?]]]]]; auto.
   subst. simpl in *. subst. simpl in *. inv H5.
  -(*Sfield*)
   destruct IHeval_lvalue as [v [vc [? [? [? ?]]]]]; auto.
   subst. simpl in *. subst. simpl in *. inv H6.
Qed.

Lemma eval_expr_match:
  forall ta te e,
  (
    forall a v,
    eval_sexp gcL ta te e a v ->
    forall eC leC teC m bs bl,
    env_match ta te e eC leC teC m bs bl ->
    exists vc, eval_expr geC eC leC teC m (trans_expr a) vc
      /\ val_match m (Lustre.typeof a) v vc
  )
/\
  (
    forall a id o k,
    LsemC.eval_lvalue gcL ta te e a id o k ->
    forall eC leC teC m bs bl,
    env_match ta te e eC leC teC m bs bl ->
    match k with
    | Gid =>
       forall mv t, gcL ! id = Some (mv, t) ->
       exists l, eval_lvalue geC eC leC teC m (trans_expr a) l o
         /\ Genv.find_symbol geC id = Some l
         /\ Plt l bi
    | Lid =>
       forall mv t, te ! id = Some (mv, t) ->
       exists l, eval_lvalue geC eC leC teC m (trans_expr a) l o
         /\ eC!id = Some (l, t)
         /\ Ple bs l
         /\ ~ In l (map (@fst block (int*type)) bl)
    | Sid =>
       forall mv t, e ! id = Some (mv, t) ->
       exists l o', eval_lvalue geC eC leC teC m (trans_expr a) l (Int.add o' o)
         /\ teC ! id = Some (Vptr l o',Tpointer t)
         /\ In (l,(o',t)) bl
    | Aid =>
      forall mv t, ta ! id = Some (mv, t) ->
      is_arystr t = true ->
      exists l o', eval_lvalue geC eC leC teC m (trans_expr a) l (Int.add o' o)
        /\ leC ! id = Some (Vptr l o', trans_ptype t)
        /\ arg_blocks_range bs bl (Vptr l o') t
    end
  ).
Proof.
  clear.
  intros until e.
  apply eval_sexp_lvalue_ind; intros.
(*sexp*)
 +(*const*)
  exists (valof (eval_const c)).
  destruct c; split; try constructor; destruct b; constructor.
 +(*unop*)
  destruct H0 with eC leC teC m bs bl as [vc1 [? ?]]; auto.
  simpl. eapply trans_unop_correct; eauto; rewrite trans_expr_typeof; auto.
 +(*binop*)
  destruct H0 with eC leC teC m bs bl as [vc1 [? ?]]; auto.
  destruct H2 with eC leC teC m bs bl as [vc2 [? ?]]; auto.
  apply trans_binop_correct with v1 v2 vc1 vc2 (Lustre.typeof a2); auto.
  -rewrite <-H3; auto.
  -simpl; auto. congruence.
  -repeat rewrite trans_expr_typeof; auto.
  -rewrite trans_expr_typeof; auto.
 +(*cast*)
  destruct H0 with eC leC teC m bs bl  as [vc1 [? ?]]; auto.
  exists (valof v). split.
  apply eval_Ecast with vc1; auto.
  -rewrite trans_expr_typeof in *; auto.
   apply eval_sem_cast_correct with v1 m; auto.
  -destruct v; try constructor.
   apply sem_cast_not_mvl in H1. inv H1.
(*lvalue1*)
 +generalize H3 H3 H. intros ? C C1. destruct H3 as [A [A1 [A2 [A3 A4]]]].
  destruct H1 as [mv [t [B [B1 B2]]]].
  apply H0 with (eC:=eC) (leC:=leC) (teC:=teC) (m:=m) (bs:=bs) (bl:=bl) in C; auto.
  destruct k; subst; simpl in *.
  -(*Gid*)
   destruct C with mv t as [l [? [? ?]]]; auto.
   destruct A with id mv t as [l0 [? [? ?]]]; auto.
   rewrite H6 in H3. inv H3.
   apply load_mvl_loadbytes_deref_loc_exists with (m:=m) (l:=l) in B2; auto.
   destruct B2 as [vc [? ?]].
   exists vc. split; auto.
   apply eval_Elvalue with l ofs; auto.
   rewrite trans_expr_typeof; auto.
  -(*Lid*)
   destruct C with mv t as [l [? [? [? ?]]]]; auto.
   destruct A1 with id mv t as [l0 [? [? [? ?]]]]; auto.
   rewrite H7 in H3. inv H3.
   rewrite B1 in H10.
   apply load_mvl_loadbytes_deref_loc_exists with (m:=m) (l:=l) in B2; auto.
   destruct B2 as [vc [? ?]].
   exists vc. split; auto.
   apply eval_Elvalue with l ofs; auto.
   rewrite trans_expr_typeof; auto.
  -(*Sid*)
   destruct C with mv t as [l [o' [? [? ?]]]]; auto.
   red in A2.
   destruct A2 with id mv t as [l1 [o1 [? [? [? [? [? ?]]]]]]]; auto.
   rewrite H6 in H3. inv H3.
   rewrite B1 in H9.
   apply load_mvl_loadbytes_deref_loc_exists_rec with (m:=m) (l:=l) (o':=o') in B2; auto.
   destruct B2 as [vc [? ?]].
   exists vc. split; auto.
   apply eval_Elvalue with l (Int.add o' ofs); auto.
   rewrite trans_expr_typeof; auto.
   apply Zdivide_trans with (alignof t); auto.
   eapply eval_lvalue_some_alignof; eauto.
  -(*Aid*)
   remember (is_arystr t). destruct b.
   *destruct C with mv t as [l [o' [? [? ?]]]]; auto.
    destruct A3 with id mv t as [v' [vc [? [? [? ?]]]]]; auto.
    rewrite H7 in H3. inv H3. inv H9.
    apply load_mvl_full in H6; auto. subst.
    apply load_mvl_loadbytes_deref_loc_exists_rec  with (m:=m) (l:=l) (o':=o') in B2; auto.
    destruct B2 as [vc [? ?]].
    exists vc. split; auto.
    apply eval_Elvalue with l (Int.add o' ofs); auto.
    rewrite trans_expr_typeof; auto.
    apply Zdivide_trans with (alignof t); auto.
    eapply eval_lvalue_some_alignof; eauto.
   *apply eval_lvalue_match_aid_val with (eC:=eC) (leC:=leC) (teC:=teC) (m:=m) (mv:=mv) (t:=t) (bs:=bs) (bl:=bl) in C1; auto.
    destruct C1 as [v1 [vc [? [? [? ?]]]]]. subst.
    apply load_mvl_determ with (v1:=v1) in B2; auto. subst.
    exists vc; split; auto. simpl.
    unfold trans_v. unfold trans_ptype in H1. rewrite <- Heqb in *.
    apply eval_Etempvar; auto.
(*lvalue*)
 +(*Lid*)
  rewrite H in H1. inv H1.
  destruct H0 as [? [? ?]].
  destruct H1 with id mv t as [b [? [? [? ?]]]]; auto.
  exists b; repeat (split; auto).
  constructor 1; auto.
 +(*Gid*)
  rewrite H0 in H2. inv H2.
  destruct H1 as [? [? [? [? ?]]]].
  destruct H1 with id mv t as [l [? [? ?]]]; auto.
  exists l; split; auto.
  constructor 2; auto.
 +(*Sid*)
  rewrite H in H1. inv H1.
  destruct H0 as [? [? [? ?]]].
  destruct H2 with id mv t as [l [o' [? [? ?]]]]; auto.
  exists l, o'. split; auto.
  unfold mkderef. apply eval_Ederef; auto.
  rewrite Int.add_zero.
  apply eval_Etempret; auto.
 +(*Aid*)
  rewrite H in H1. inv H1.
  destruct H0 as [? [? [? [? ?]]]].
  destruct H4 with id mv t as [v [vc [? [? [? ?]]]]]; auto.
  simpl. unfold trans_v, mkderef. unfold trans_ptype in *. rewrite H2 in *.
  destruct load_mvl_is_arystr_vptr with t mv Int.zero v m0 vc as [l [o' ?]]; auto.
  subst. exists l, o'. split; auto.
  apply eval_Ederef; auto. rewrite Int.add_zero; auto.
  apply eval_Etempvar; auto.
 +(*Sarray*)
  generalize H4; intros C.
  apply H0 with (eC:=eC) (leC:=leC) (teC:=teC) (m:=m) (bs:=bs) (bl:=bl) in C; eauto.
  destruct H2 with eC leC teC m bs bl as [vi [? ?]]; auto.
  apply eval_sexp_has_type in H1. inv H6.
  destruct k; intros.
  -destruct C with mv t as [l0 [? ?]]; auto.
   exists l0. split; auto.
   apply eval_aryacc_match with aid z; auto.
  -destruct C with mv t as [l0 [? ?]]; auto.
   exists l0. split; auto.
   apply eval_aryacc_match with aid z; auto.
  -destruct C with mv t as [l0 [o' [? ?]]]; auto.
   exists l0, o'. split; auto.
   rewrite <-Int.add_assoc.
   apply eval_aryacc_match with aid z; auto.
  -destruct C with mv t as [l0 [o' [? ?]]]; auto.
   exists l0, o'. split; auto.
   rewrite <-Int.add_assoc.
   apply eval_aryacc_match with aid z; auto.
 +(*Sfield*)
  destruct k; intros.
  -destruct H0 with eC leC teC m bs bl mv t as [l0 [? ?]]; auto.
   exists l0; split; auto.
   apply eval_field_match with sid fld; auto.
  -destruct H0 with eC leC teC m bs bl mv t as [l0 [? ?]]; auto.
   exists l0; split; auto.
   apply eval_field_match with sid fld; auto.
  -destruct H0 with eC leC teC m bs bl mv t as [l0 [o' [? ?]]]; auto.
   exists l0, o'; split; auto.
   rewrite <-Int.add_assoc.
   apply eval_field_match with sid fld; auto.
  -destruct H0 with eC leC teC m bs bl mv t as [l0 [o' [? ?]]]; auto.
   exists l0, o'; split; auto.
   rewrite <-Int.add_assoc.
   apply eval_field_match with sid fld; auto.
Qed.

Lemma eval_expr_lvalue_inv:
  forall ta te e v eC leC teC m l o a,
  eval_sexp gcL ta te e a v ->
  eval_expr geC eC leC teC m (trans_expr a) (Vptr l o) ->
  is_arystr (Lustre.typeof a) = true ->
  eval_lvalue geC eC leC teC m (trans_expr a) l o.
Proof.
  clear.
  intros. generalize H; intros.
  apply eval_sexp_has_type in H2.
  destruct has_type_access_mode_mvl with v (Lustre.typeof a) as [mv [? ?]]; auto.
    apply is_arystr_true_access_mode; auto.
  subst.
  destruct eval_sexp_exists_lvalue with gcL ta te e a  mv as [id [ofs [k [? [? ?]]]]]; auto.
  destruct a; simpl in *; try (inv H3; fail);
  unfold trans_v in *; try rewrite H1 in *;
  try (inv H0; simpl in *;
       apply is_arystr_deref_loc_vtpr_eq in H8; auto;
       destruct H8; congruence; fail).
Qed.

Lemma trans_arg_match:
  forall ta te e a v eC leC teC m bs bl,
  eval_sexp gcL ta te e a v ->
  env_match ta te e eC leC teC m bs bl ->
  exists vc, eval_expr geC eC leC teC m (trans_arg a) vc
                /\ val_match m (Lustre.typeof a) v vc.
Proof.
  clear.
  unfold trans_arg, mkaddr. intros.
  rewrite trans_expr_typeof.
  remember (is_arystr (Lustre.typeof a)). destruct b.
  +generalize H H; intros.
   eapply eval_expr_match in H; eauto.
   destruct H as [vc [? ?]].
   exists vc; split; auto.
   apply eval_sexp_has_type in H1.
   destruct has_type_is_arystr_vptr with v (Lustre.typeof a) m vc as [l [o ?]]; auto.
   subst. apply eval_Eaddrof; auto.
   eapply eval_expr_lvalue_inv; eauto.
  +apply eval_expr_match with ta te e bs bl; auto.
Qed.

Lemma eval_sexps_casts_exists:
  forall args vargs te ta e,
  eval_sexps gcL ta te e args vargs ->
  forall m vinC,
  vals_match m (map Lustre.typeof args) vargs vinC ->
  exists vinC', eval_casts vinC (map typeof (map trans_arg args)) vinC'.
Proof.
  clear.
  induction 1; simpl; intros.
  +inv H. exists nil. constructor.
  +inv H1. apply eval_sexp_has_type in H.
   destruct has_type_casts_exist with x y m vc as [vc' ?]; auto.
   destruct IHForall2 with m vcl as [vinC' ?]; auto.
   exists (vc'::vinC'). constructor 2; auto.
Qed.

Lemma locvars_none_set_left:
  forall te eC id mt,
  locvars_none te eC ->
  locvars_none (PTree.set id mt te) eC.
Proof.
  clear.
  intros. red; intros. apply H.
  compare id id0; intros; subst.
  rewrite PTree.gss in H0; congruence.
  rewrite PTree.gso in H0; auto.
Qed.

Lemma trans_paras_length_eq:
  forall ta f vas vas' ta1 m tyl1 tyl2 vinC vinC',
  locenv_setvars ta (nd_args f) vas' ta1 ->
  vals_match m (map snd (nd_args f)) vas vinC ->
  Lsem.eval_casts vas tyl1 vas' ->
  eval_casts vinC tyl2 vinC' ->
  length (trans_paras f) = length vinC'.
Proof.
  unfold trans_paras. intros.
  rewrite map_length.
  erewrite locenv_setvars_length_eq; eauto.
  apply eval_casts_length in H2. destruct H2.
  erewrite <-eval_casts_length_l; eauto.
  apply vals_match_length in H0. destruct H0. omega.
Qed.

Lemma trans_rets_length_eq:
  forall voutC tys bl e m f,
  blockof_vptrs voutC tys bl ->
  retvals_match e m (nd_rets f) bl ->
  length (trans_rets f) = length voutC.
Proof.
  unfold trans_rets. intros.
  rewrite map_length.
  erewrite blockof_vptrs_length1; eauto.
  eapply Forall2_length; eauto.
Qed.

Lemma alloc_variables_globconsts_match:
  forall eC m al eC1 m1,
  alloc_variables eC m al eC1 m1 ->
  globconsts_match m ->
  globconsts_match m1.
Proof.
  intros. red; intros.
  destruct H0 with id mv ty as [l [? [? ?]]]; auto.
  exists l. repeat (split; auto).
  eapply c_alloc_variables_loadbytes; eauto.
Qed.

Lemma alloc_variables_locvars_none:
  forall te l te',
  Lsem.alloc_variables te l te' ->
  forall eC eC' m m',
  alloc_variables eC m l eC' m' ->
  locvars_none te eC ->
  locvars_none te' eC'.
Proof.
  clear.
  induction 1; simpl; intros.
  +inv H; auto.
  +inv H0. eapply IHalloc_variables; eauto.
   red; intros.
   compare id id0; intros; subst.
   -rewrite PTree.gss in *. inv H0.
   -rewrite PTree.gso in *; auto.
Qed.

Lemma alloc_variables_locrets_match:
  forall e leC m eC al eC1 m1 bl,
  locrets_match e leC m bl ->
  alloc_variables eC m al eC1 m1 ->
  locrets_match e leC m1 bl.
Proof.
  unfold locrets_match. intros.
  destruct H with id mv ty as [l [o [? [? [? [? [? ?]]]]]]]; auto.
  exists l, o. repeat (split; auto).
  eapply c_alloc_variables_loadbytes; eauto.
  eapply c_alloc_variables_range_perm; eauto.
Qed.

Lemma alloc_variables_locargs_match:
  forall ta leC m eC al eC1 m1 bs bl,
  locargs_match ta leC m bs bl ->
  alloc_variables eC m al eC1 m1 ->
  locargs_match ta leC m1 bs bl.
Proof.
  unfold locargs_match. intros.
  destruct H with id mv ty as [v [vc [? [? [? ?]]]]]; auto.
  exists v, vc. repeat (split; auto).
  eapply alloc_variables_val_match; eauto.
Qed.

Lemma locenv_setmvls_other_retval_match:
  forall e al vl e',
  locenv_setmvls e al vl e' ->
  forall m a p,
  retval_match e m a p ->
  ~ In (fst a) (map fst al) ->
  retval_match e' m a p.
Proof.
  clear.
  intros. inv H0.
  constructor 1 with mv; auto.
  erewrite locenv_setmvls_notin_eq; eauto.
Qed.

Lemma locenv_setmvl_retval_match:
  forall e a mv e1 m b o,
  locenv_setmvl e a mv e1 ->
  val_match m (snd a) (Vmvl mv) (Vptr b o) ->
  block_range_perm m (b, (o,snd a)) ->
  retval_match e1 m a (b, (o,snd a)).
Proof.
  clear.
  intros. inv H. inv H0.
  simpl in *. destruct H1.
  constructor 1 with mv; auto.
  +rewrite PTree.gss; auto.
  +rewrite H2. auto.
  +omega.
Qed.

Lemma locenv_setmvls_retvals_match:
  forall e rets vl e',
  locenv_setmvls e rets vl e' ->
  forall m voutC bl,
  vals_match m (map snd rets) (map Vmvl vl) voutC ->
  blockof_vptrs voutC (map (fun x => snd x) rets) bl ->
  list_norepet (map fst rets) ->
  blocks_range_perm m bl ->
  retvals_match e' m rets bl.
Proof.
  clear.
  induction 1; simpl; intros.
  +inv H. inv H0. constructor.
  +inv H1. inv H3. inv H2. inv H4. constructor 2; auto.
   -eapply locenv_setmvls_other_retval_match; eauto.
    eapply locenv_setmvl_retval_match; eauto.
   -eapply IHlocenv_setmvls; eauto.
Qed.

Lemma free_list_globconsts_match:
  forall eC m m',
  Mem.free_list m (blocks_of_env eC) = Some m' ->
  forall be, Plt bo be  ->
  le_env eC be ->
  globconsts_match m ->
  globconsts_match m'.
Proof.
  unfold globconsts_match. intros.
  destruct H2 with id mv ty as [l [? [? ?]]]; auto.
  exists l. repeat (split; auto).
  erewrite free_list_loadbytes_eq; eauto.
  eapply le_env_lt_notin; eauto.
  apply Plt_trans with bi; auto.
  apply Plt_trans with bo; auto.
Qed.

Lemma free_list_disjoint_retvals_match:
  forall e m rets bl,
  retvals_match e m rets bl ->
  forall l m', Mem.free_list m l = Some m' ->
  list_disjoint (map (@fst block (int*type)) bl) (map (fun x => fst (fst x)) l) ->
  retvals_match e m' rets bl.
Proof.
  clear.
  induction 1; simpl; intros.
  +constructor.
  +constructor 2; auto.
   -inv H. constructor 1 with mv; auto.
    erewrite free_list_loadbytes_eq; eauto.
    eapply list_disjoint_notin;eauto. simpl; auto.
    eapply free_list_range_perm; eauto.
    eapply list_disjoint_notin;eauto. simpl; auto.
   -eapply IHForall2; eauto.
    eapply list_disjoint_cons_left; eauto.
Qed.

Lemma range_perm_valid_block_sizeof:
  forall m l o ty p,
  Mem.range_perm m l o (o + sizeof ty) Cur p ->
  sizeof ty > 0 ->
  Plt l (Mem.nextblock m).
Proof.
  intros.
  apply range_perm_valid_block2 with o  (o + sizeof ty); auto.
  red; intros. apply H in H1. eauto with mem. omega.
Qed.

Lemma retvals_match_blocks_lt_nextblock:
  forall e m rets bl,
  retvals_match e m rets bl ->
  (forall b, In b (map (fst (B:=int*type)) bl) -> Plt b (Mem.nextblock m)).
Proof.
  clear.
  induction 1; simpl; intros.
  inv H.
  destruct H1; auto.
  subst. inv H. simpl.
  apply Mem.loadbytes_range_perm in H3.
  eapply range_perm_valid_block_sizeof; eauto.
Qed.

Lemma retvals_match_le_env_block_disjoint:
  forall e m rets bl eC,
  retvals_match e m rets bl ->
  le_env eC (Mem.nextblock m) ->
  Plt bo (Mem.nextblock m)->
  list_disjoint (map (fst (B:=int*type)) bl) (map (fun x : block * Z * Z => fst (fst x)) (blocks_of_env eC)).
Proof.
  clear.
  intros. apply le_env_infer in H0.
  red in H0. unfold blocks_of_env. rewrite map_map.
  red; intros. apply in_map_iff in H3.
  destruct H3 as [? [? ?]]. destruct x0. destruct p.
  simpl in *. subst. apply H0 in H4.
  cut (Plt x (Mem.nextblock m)). intros.
  red; intros. subst. unfold Plt, Ple in *. omega.
  eapply retvals_match_blocks_lt_nextblock; eauto.
Qed.

Lemma locenv_getvars_retvals_match:
  forall leC m2 e1 rets vrs,
  locenv_getvars e1 rets vrs ->
  forall voutC bl bl',
  locrets_match e1 leC m2 bl' ->
  tempenv_getvars leC (map trans_ret rets) voutC ->
  blockof_vptrs voutC (map (fun x => snd x) rets) bl ->
  list_norepet (map fst rets) ->
  incl bl bl' ->
  retvals_match e1 m2 rets bl.
Proof.
  clear.
  induction 1; simpl; intros.
  +inv H0. simpl in *. inv H1. constructor.
  +inv H2. inv H4. inv H3.
   constructor 2; auto.
   -destruct H as [mv [? [? ?]]].
    red in H1. destruct H1 with (fst x) mv (snd x) as [l1 [o1 [? [? [? [? [? ?]]]]]]]; auto.
    rewrite H8 in H4. inv H4.
    simpl in *.
    destruct x. simpl in *.
    constructor 1 with mv; auto.
    apply load_mvl_range_perm in H3. red in H3. omega.
   -eapply IHForall2; eauto.
    red; intros. apply H5; simpl; auto.
Qed.

Lemma blocks_incl_range_lt:
  forall bl bl' bs bs' l,
  blocks_incl bl bl' bs bs' ->
  blocks_range bl bo bs ->
  In l (map (@fst block (int*type)) bl') ->
  Plt bo bs /\ Ple bs bs'->
  Plt bi l.
Proof.
  clear TRANS.
  intros. apply in_map_iff in H1. destruct H1 as [? [? ?]].
  subst. apply H in H3. destruct H3.
  +destruct H1 as [bot1 [? ?]].
   destruct H3 as [? [? ?]]. simpl in *.
   red in H0. apply H0 in H1. rewrite <-H3.
   unfold Plt, Ple in *. omega.
  +unfold Plt, Ple in *. omega.
Qed.

Lemma alloc_variables_locvars_match:
  forall te l te',
  Lsem.alloc_variables te l te' ->
  forall eC m eC' m' bs bs' bl bl',
  alloc_variables eC m l eC' m' ->
  locvars_match te eC m bs' bl' ->
  Plt bo bs /\ Ple bs bs' ->
  Ple bs' (Mem.nextblock m) ->
  blocks_incl bl bl' bs bs' ->
  blocks_range bl bo bs ->
  locvars_match te' eC' m' bs' bl'.
Proof.
  clear.
  induction 1; simpl; intros.
  +inv H. auto.
  +inv H0. eapply IHalloc_variables; eauto.
   red. intros.
   compare id id0; intros; subst.
   -rewrite PTree.gss in *. inv H0.
    exists b1. repeat (split; auto).
    *apply Mem.alloc_result in H13. subst.
     unfold Ple, Plt in *. omega.
    *apply Mem.alloc_result in H13. subst.
     red; intros.
     apply in_map_iff in H0. destruct H0 as [? [? ?]].
     destruct x. simpl in *. subst. destruct H2.
     eapply blocks_incl_bot_range_lt with (l:=Mem.nextblock m) in H5; eauto.
     unfold Plt, Ple in *. omega.
    *apply alloc_loadbytes_same with m; auto.
   -rewrite PTree.gso in *; auto.
    destruct H1 with id0 mv ty0 as [b [? [? [? ?]]]]; auto.
    exists b; repeat (split; auto).
    eapply loadbytes_alloc_other; eauto.
   -apply Mem.nextblock_alloc in H13.
    rewrite H13. apply Ple_trans with (Mem.nextblock m); auto.
    apply Plt_Ple. apply Plt_succ.
Qed.

Lemma bind_parameter_temps_locrets_match:
  forall al vl leC leC' bl e m,
  bind_parameter_temps (map trans_ret al) vl leC = Some leC' ->
  blockof_vptrs vl (map (fun x => snd x) al) bl ->
  retvals_match e m al bl ->
  locenv_rets_match e al ->
  list_norepet (map fst al) ->
  locrets_match e leC' m bl.
Proof.
  clear.
  intros. red; intros.
  generalize H4; intros A.
  apply H2 in H4.
  apply in_split in H4. destruct H4 as [l1 [l2 ?]].
  subst. apply Forall2_app_inv_l in H1.
  destruct H1 as [bl1 [bl2 [? [? ?]]]]. subst.
  inv H4. inv H7. rewrite H6 in A. inv A.
  exists l, o. rewrite map_app in *.
  apply blockof_vptrs_app_inv_left in H0.
  destruct H0 as [vl1 [vl2 [? [? [? [? ?]]]]]]. subst.
  destruct H5. apply app_length_equal_inv in H4.
  destruct H4. subst.
  apply bind_parameter_temps_app_inv in H.
  destruct H as [? [? [leC1 [? [? ?]]]]].
  apply app_length_equal_inv in H7.
  destruct H7; subst x x0. simpl in *.
  destruct vl2; try congruence. inv H5.
  apply list_norepet_app in H3. destruct H3 as [? [? ?]]. inv H5.
  repeat (split; auto).
  +erewrite bind_parameter_temps_notin_eq; eauto.
   rewrite PTree.gss; auto.
   rewrite map_map.
   rewrite map_ext with (g:=fst); auto.
  +apply in_or_app. simpl; auto.
  +left. apply bind_parameter_temps_length in H. rewrite <-H.
   rewrite map_length. erewrite blockof_vptrs_length2; eauto.
   rewrite map_length; auto.
  +left. rewrite map_length. apply Forall2_length in H1.
   erewrite <-blockof_vptrs_length2; eauto.
   erewrite blockof_vptrs_length1; eauto.
Qed.

Lemma bind_parameter_temps_locargs_match:
  forall al vl vl' leC leC' ta vas vas' ta1 m bs bl,
  bind_parameter_temps (map trans_para al) vl' leC = Some leC' ->
  Lsem.alloc_variables empty_locenv al ta ->
  locenv_setvars ta al vas' ta1 ->
  vals_match m (map snd al) vas vl ->
  Lsem.eval_casts vas (map (snd (B:=type)) al) vas' ->
  eval_casts vl (map (snd (B:=type)) (map trans_para al)) vl' ->
  list_norepet (map fst al) ->
  args_blocks_range bs bl vl' (map (fun x =>snd x) al)  ->
  has_types vas (map (snd (B:=type)) al) ->
  locargs_match ta1 leC' m bs bl.
Proof.
  clear.
  intros.
  eapply alloc_variables_locenv_sets_match in H0; eauto.
  eapply locenv_setvars_locenv_sets_match in H0; eauto.
  red; intros. generalize H8; intros.
  apply H0 in H8. apply in_split in H8.
  destruct H8 as [al1 [al2 ?]]. subst.
  rewrite map_app in *.
  apply bind_parameter_temps_app_inv in H.
  destruct H as [vl1 [vl2 [leC1 [? [? ?]]]]].
  subst. apply list_norepet_app in H5. destruct H5 as [? [? ?]].
  inv H10. rewrite map_app in *.
  apply eval_casts_app_inv_l in H4. destruct H4 as [vl3 [vl4 [? [? ?]]]].
  subst. simpl in *. inv H10. rewrite trans_para_eq in *.
  apply vals_match_app_inv_r in H2.
  destruct H2 as [vas1 [vas2 [? [? ?]]]]. subst.
  inv H10. simpl in *.
  assert(A: length al1 = length vas1).
    apply vals_match_length in H2. destruct H2.
    apply eval_casts_length in H19.
    apply bind_parameter_temps_length in H.
    rewrite map_length in H2. omega.
  apply eval_casts_app_inv_r in H3. destruct H3 as [vas'1 [vas'2 [? [? ?]]]].
  subst.
  generalize H1; intros.
  apply locenv_setvars_trans_exists in H1; auto. destruct H1 as [ta0 ?].
  generalize H1; intros.
  eapply locenv_setvars_trans_rev in H1; eauto.
  inv H1. inv H10. inv H27. rewrite H1 in H24. inv H24.
  erewrite set_new_vars_getid_eq in H9; eauto.
  rewrite PTree.gss in H9. inv H9.
  apply Forall2_app_inv in H7. destruct H7. inv H9.
  exists v0, v2; repeat (split; auto).
  +eapply store_mvl_eval_cast_load; eauto.
  +erewrite bind_parameter_temps_notin_eq; eauto.
   rewrite PTree.gss; auto.
   rewrite map_map. rewrite map_ext with (g:=fst); auto.
   intros. rewrite trans_para_eq; auto.
  +apply Forall2_app_inv in H6. destruct H6. inv H9; auto.
   rewrite map_length. apply bind_parameter_temps_length in H.
   rewrite <-H, map_length; auto.
  +eapply eval_cast_val_match; eauto.
  +rewrite map_length. omega.
  +erewrite <-eval_casts_length_r; eauto.
   rewrite map_length; auto.
  +rewrite map_length; auto.
  +apply eval_casts_length in H4. destruct H4.
   repeat rewrite map_length in *. auto.
  +rewrite map_length.
   eapply bind_parameter_temps_length; eauto.
Qed.

Lemma alloc_variables_match:
  forall f ta ta1 te e eC leC teC m m1 vas vas' vinC vinC' voutC bs bs' bl bl',
  Lsem.alloc_variables empty_locenv (nd_args f) ta ->
  Lsem.alloc_variables empty_locenv (nd_vars f) te ->
  locenv_setvars ta (nd_args f) vas' ta1 ->
  alloc_variables empty_env m (nd_vars f) eC m1 ->
  vals_match m (map snd (nd_args f)) vas vinC ->
  Lsem.eval_casts vas (map (snd (B:=type)) (nd_args f)) vas' ->
  eval_casts vinC (map (snd (B:=type)) (map trans_para (nd_args f))) vinC' ->
  blockof_vptrs voutC (map (fun x => snd x) (nd_rets f)) bl' ->
  retvals_match e m (nd_rets f) bl' ->
  globconsts_match m ->
  Plt bo bs /\ Ple bs bs' ->
  Ple bs' (Mem.nextblock m) ->
  bind_parameter_temps (trans_paras f) vinC' empty_temp = Some leC ->
  bind_parameter_temps (trans_rets f) voutC empty_temp = Some teC ->
  locenv_rets_match e (nd_rets f) ->
  list_norepet (map fst (nd_args f)) ->
  list_norepet (map fst (nd_rets f)) ->
  blocks_incl bl bl' bs bs' ->
  blocks_range bl bo bs ->
  args_blocks_range bs' bl' vinC' (map (fun x => snd x) (nd_args f)) ->
  has_types vas (map (snd (B:=type)) (nd_args f)) ->
  env_match ta1 te e eC leC teC m1 (Mem.nextblock m) bl'.
Proof.
  clear. intros. repeat split.
  +eapply alloc_variables_globconsts_match; eauto.
  +eapply alloc_variables_locvars_match with (bs:=bs); eauto.
   apply locvars_match_empty.
   unfold Plt, Ple in *. omega.
   unfold Plt, Ple in *. omega.
   red; intros. apply H16 in H20. destruct H20; subst; auto.
   right. unfold Plt, Ple in *. omega.
  +eapply alloc_variables_locrets_match; eauto.
   eapply bind_parameter_temps_locrets_match; eauto.
  +eapply alloc_variables_locargs_match; eauto.
   eapply bind_parameter_temps_locargs_match; eauto.
   eapply args_blocks_range_trans; eauto.
  +eapply alloc_variables_locvars_none; eauto.
   red; intros. rewrite PTree.gempty; auto.
Qed.

Lemma assign_loc_globconsts_match:
  forall ty m l ofs v m',
  assign_loc ty m l ofs v m' ->
  globconsts_match m ->
  Plt bi l ->
  globconsts_match m'.
Proof.
  clear TRANS. intros. red; intros.
  destruct H0 with id mv ty0 as [l0 [? [? ?]]]; auto.
  exists l0. repeat (split; auto).
  rewrite <-H5. change 0 with (Int.unsigned Int.zero).
  eapply assign_loc_loadbytes_other; eauto.
  left. red; intros; subst.
  unfold Plt, Ple in *. omega.
Qed.

Lemma assign_loc_locargs_match:
  forall ty m l ofs v m' ta leC bs' bl',
  assign_loc ty m l ofs v m' ->
  locargs_match ta leC m bs' bl' ->
  Ple bs' l \/ block_ofs_ty_incl_in bl' (l,(ofs,ty)) ->
  locargs_match ta leC m' bs' bl'.
Proof.
  clear TRANS. intros. red; intros.
  destruct H0 with id mv ty0 as [v0 [vc [? [? [? ?]]]]]; auto.
  exists v0, vc. repeat (split; auto).
  inv H6; constructor; auto.
  rewrite <-H7. simpl in *. destruct H5.
  erewrite <-load_mvl_size; eauto.
  eapply assign_loc_loadbytes_other; eauto.
  eapply block_ofs_ty_disjoints_incl_in_trans_or_uneq; eauto.
Qed.

Lemma assign_loc_in_locvars_match:
  forall ty m l ofs v m' te eC bs' bl',
  assign_loc ty m l ofs v m' ->
  locvars_match te eC m bs' bl' ->
  In l (map (@fst block (int*type)) bl') ->
  locvars_match te eC m' bs' bl'.
Proof.
  intros. red; intros.
  destruct H0 with id mv ty0 as [b [? [? [? ?]]]]; auto.
  exists b. repeat (split; auto).
  rewrite <-H6. change 0 with (Int.unsigned Int.zero).
  eapply assign_loc_loadbytes_other; eauto.
  left. congruence.
Qed.

Lemma assign_loc_le_locrets_match:
  forall ty m l ofs v m' e leC bs bs' bl bl',
  assign_loc ty m l ofs v m' ->
  locrets_match e leC m bl' ->
  Ple bs bs' /\ Ple bs' l ->
  blocks_incl bl bl' bs bs' ->
  blocks_range bl bo bs ->
  locrets_match e leC m' bl'.
Proof.
  clear TRANS. intros. red; intros.
  destruct H0 with id mv ty0 as [l0 [o [? [? [? [? [? ?]]]]]]]; auto.
  exists l0, o.
  repeat (split; auto).
  +rewrite <-H8. eapply assign_loc_loadbytes_other; eauto.
   left. eapply blocks_incl_bot_range_lt in H2; eauto.
   red; intros. subst. red in H2. omega.
  +eapply assign_loc_range_perm; eauto.
Qed.

Lemma storebytes_globconsts_match:
  forall m l o bytes m',
  Mem.storebytes m l o bytes = Some m' ->
  globconsts_match m ->
  Ple bi l ->
  globconsts_match m'.
Proof.
  clear TRANS. intros. red; intros.
  destruct H0 with id mv ty as [l0 [? [? ?]]]; auto.
  exists l0. repeat (split; auto).
  rewrite <-H5. generalize (sizeof_pos ty); intros.
  eapply Mem.loadbytes_storebytes_other; eauto.
  omega.
  left. red; intros; subst.
  unfold Plt, Ple in *. omega.
Qed.

Lemma storebytes_le_locrets_match:
  forall m l o bytes m' e leC bs bs' bl bl',
  Mem.storebytes m l o bytes = Some m' ->
  locrets_match e leC m bl' ->
  Ple bs bs' /\ Ple bs' l ->
  blocks_incl bl bl' bs bs' ->
  blocks_range bl bo bs ->
  locrets_match e leC m' bl'.
Proof.
  clear TRANS. intros. red; intros.
  destruct H0 with id mv ty as [l0 [o0 [? [? [? [? [? ?]]]]]]]; auto.
  exists l0, o0.
  generalize (sizeof_pos ty); intros.
  repeat (split; auto).
  +rewrite <-H8.
   eapply Mem.loadbytes_storebytes_other; eauto.
   left. eapply blocks_incl_bot_range_lt in H2; eauto.
   red; intros. subst. red in H2. omega.
  +red; intros. eapply Mem.perm_storebytes_1; eauto.
Qed.

Lemma storebytes_locargs_match:
  forall m l o bytes m' ty ta leC bs' bl',
  Mem.storebytes m l (Int.unsigned o) bytes = Some m' ->
  locargs_match ta leC m bs' bl' ->
  sizeof ty = Z_of_nat (length bytes) ->
  Ple bs' l  \/ block_ofs_ty_incl_in bl' (l,(o,ty)) ->
  locargs_match ta leC m' bs' bl'.
Proof.
  clear TRANS. intros. red; intros.
  destruct H0 with id mv ty0 as [v0 [vc [? [? [? ?]]]]]; auto.
  exists v0, vc. repeat (split; auto).
  inv H7; constructor; auto.
  rewrite <-H8. erewrite <-load_mvl_size; eauto. simpl in *.
  destruct H6. inv H4. apply load_vmvl_false in H12. tauto.
  generalize (sizeof_pos ty0); intros.
  eapply Mem.loadbytes_storebytes_other; eauto; eauto.
  rewrite <-H1. eapply block_ofs_ty_disjoints_incl_in_trans_or_uneq; eauto.
Qed.

Lemma storebytes_in_locvars_match:
  forall m l ofs bytes m' te eC bs' bl',
  Mem.storebytes m l ofs bytes = Some m' ->
  locvars_match te eC m bs' bl' ->
  In l (map (@fst block (int*type)) bl') ->
  locvars_match te eC m' bs' bl'.
Proof.
  clear TRANS. intros. red; intros.
  destruct H0 with id mv ty as [b [? [? [? ?]]]]; auto.
  exists b. repeat (split; auto).
  rewrite <-H6.
  eapply Mem.loadbytes_storebytes_other; eauto.
  generalize (sizeof_pos ty); intros. omega.
  left. red; intros; subst; auto.
Qed.

Lemma storebytes_same_locvar_match:
  forall te eC m bs' bl' ty mv ofs m1 mv' t l m' id,
  locvars_match te eC m bs' bl' ->
  store_mvl ty mv ofs (Vmvl m1) mv' ->
  te ! id = Some (mv, t) ->
  eC ! id = Some (l, t) ->
  is_arystr ty = true ->
  env_diff_id_diff_b eC ->
  Mem.storebytes m l (Int.unsigned ofs) m1 = Some m' ->
  locvars_match (PTree.set id (mv', t) te) eC m' bs' bl'.
Proof.
  clear TRANS. intros.
  generalize H0; intros A.
  apply store_mvl_length in A. red; intros.
  inv H0. unfold is_arystr in *.
  destruct ty; simpl in *; try congruence.
  compare id id0; intros; subst.
  +rewrite PTree.gss in H6. inv H6.
   destruct H with id0 mv ty0 as [l1 [? [? [? ?]]]]; auto.
   rewrite H0 in H2. inv H2.
   exists l. repeat (split; auto).
   generalize (Int.unsigned_range ofs); intros.
   eapply storebytes_same_loadbytes; eauto; omega.
  +rewrite PTree.gso in H6; auto.
   destruct H with id0 mv0 ty0 as [l1 [? [? [? ?]]]]; auto.
   exists l1. repeat (split; auto).
   rewrite <-H13. generalize (sizeof_pos ty0); intros.
   eapply Mem.loadbytes_storebytes_other; eauto.
Qed.

Lemma store_same_locrets_match:
  forall e teC m bl' ty mv ofs v vc mv' t l o m' id,
  locrets_match e teC m bl' ->
  store_mvl ty mv ofs v mv' ->
  e ! id = Some (mv, t) ->
  teC ! id = Some (Vptr l o, Tpointer t) ->
  is_arystr ty = false ->
  has_type v ty ->
  val_match m ty v vc ->
  Mem.loadbytes m l (Int.unsigned o) (sizeof t) = Some mv ->
  assign_loc ty m l (Int.add o ofs) vc m' ->
  ret_env_diff_id_disjoint teC ->
  Int.unsigned o + Z.of_nat (length mv) <= Int.max_signed ->
  locrets_match (PTree.set id (mv', t) e) teC m' bl'.
Proof.
  clear TRANS. intros.
  generalize H0 H0; intros A A1.
  apply store_mvl_length in A.
  apply store_mvl_range_perm2 in A1.
  red in A1.
  generalize (Int.unsigned_range o) (Int.unsigned_range ofs) Int.max_signed_unsigned; intros A2 A3 A4.
  red; intros.
  inv H0. generalize H11. intros A5.
  rewrite access_mode_eq in H11.
  inv H7; try congruence. rewrite H0 in H11. inv H11.
  compare id id0; intros; subst.
  +rewrite PTree.gss in H10. inv H10.
   destruct H with id0 mv ty0 as [l1 [o1 [? [? [? [? [? ?]]]]]]]; auto.
   rewrite H7 in H2. inv H2.
   exists l,o. repeat (split; auto). congruence.
   *eapply store_same_loadbytes; eauto; try omega.
    rewrite <-H13. simpl; f_equal.
    unfold Int.add. rewrite Int.unsigned_repr; omega.
   *red; intros. eapply Mem.perm_store_1; eauto.
  +rewrite PTree.gso in H10; auto.
   destruct H with id0 mv0 ty0 as [l1 [o1 [? [? [? [? [? ?]]]]]]]; auto.
   exists l1, o1. repeat (split; auto).
   *rewrite <-H15. generalize (sizeof_pos t) (sizeof_pos ty0); intros.
    eapply Mem.loadbytes_store_other; eauto.
    eapply H8 in n; eauto. red in n.
    erewrite sizeof_chunk_eq; eauto.
    erewrite Mem.loadbytes_length in A1, H9; eauto.
    rewrite nat_of_Z_eq in A1, H9; try omega.
    destruct n; [left | right]; auto. right.
    unfold Int.add. rewrite Int.unsigned_repr; try omega.
   *red; intros. eapply Mem.perm_store_1; eauto.
  +left. eauto.
  +unfold is_arystr in *.
   destruct ty; try tauto; simpl in *; try congruence.
Qed.

Lemma store_same_locvar_match:
  forall te eC m bs' bl' ty mv ofs v vc mv' t l m' id,
  locvars_match te eC m bs' bl' ->
  store_mvl ty mv ofs v mv' ->
  te ! id = Some (mv, t) ->
  eC ! id = Some (l, t) ->
  is_arystr ty = false ->
  env_diff_id_diff_b eC ->
  has_type v ty ->
  val_match m ty v vc ->
  assign_loc ty m l ofs vc m' ->
  locvars_match (PTree.set id (mv', t) te) eC m' bs' bl'.
Proof.
  clear TRANS. intros.
  generalize H0; intros A.
  apply store_mvl_length in A. red; intros.
  inv H0. generalize H9; intros A1. rewrite access_mode_eq in H9.
  inv H7; try congruence. rewrite H0 in H9. inv H9.
  compare id id0; intros; subst.
  +rewrite PTree.gss in H8. inv H8.
   destruct H with id0 mv ty0 as [l1 [? [? [? ?]]]]; auto.
   rewrite H7 in H2. inv H2.
   exists l. repeat (split; auto).
   generalize (Int.unsigned_range ofs); intros.
   eapply store_same_loadbytes; eauto; try omega.
  +rewrite PTree.gso in H8; auto.
   destruct H with id0 mv0 ty0 as [l1 [? [? [? ?]]]]; auto.
   exists l1. repeat (split; auto).
   rewrite <-H13. generalize (sizeof_pos ty0); intros.
   eapply Mem.loadbytes_store_other; eauto.
  +left. eauto.
  +unfold is_arystr in *.
   destruct ty; inv H5; simpl in *; try congruence.
Qed.

Lemma eval_lvalue_arystr:
  forall ta te e a id ofs k,
  LsemC.eval_lvalue gcL ta te e a id ofs k ->
  is_arystr (Lustre.typeof a) = true ->
  exists m t, (case_env gcL ta te e k) ! id = Some (m, t)
    /\ is_arystr t = true.
Proof.
  induction 1; simpl; intros; eauto.
  +apply IHeval_lvalue. rewrite H1. unfold is_arystr. auto.
  +apply IHeval_lvalue. rewrite H0. unfold is_arystr. auto.
Qed.

Lemma range_perm_unsigned_add_simpl:
  forall o1 o2 t1 t2,
  0 <= Int.unsigned o2 < Int.unsigned o2 + sizeof t1 /\ Int.unsigned o2 + sizeof t1 <= sizeof t2 <= Int.max_signed ->
  Int.unsigned o1 + sizeof t2 <= Int.max_signed ->
  Int.unsigned (Int.add o1 o2) = Int.unsigned o1 + Int.unsigned o2.
Proof.
  intros. unfold Int.add.
  generalize (Int.unsigned_range o1) Int.max_signed_unsigned; intros.
  rewrite Int.unsigned_repr; try omega.
Qed.

Lemma assign_disjoint_eval_lvalue_disjoint:
  forall ta te e a1 a2 v1 mv eC leC teC m bs bs' bl bl' b1 b2 o1 o2,
  assign_disjoint (LsemC.eval_lvalue gcL ta te e) a1 a2 ->
  locenv_getmvl gcL ta te e a1 v1 ->
  eval_sexp gcL ta te e a2 (Vmvl mv) ->
  env_match ta te e eC leC teC m bs' bl' ->
  env_diff_id_diff_b eC ->
  ret_env_diff_id_disjoint teC ->
  blocks_incl bl bl' bs bs' ->
  blocks_range bl bo bs ->
  is_arystr (Lustre.typeof a2) = true ->
  eval_lvalue geC eC leC teC m (trans_expr a1) b1 o1 ->
  eval_lvalue geC eC leC teC m (trans_expr a2) b2 o2 ->
  Plt bo bs /\ Ple bs bs' ->
  eval_lvalue_disjoint b2 b1 o2 o1 (Lustre.typeof a2) (Lustre.typeof a1).
Proof.
  clear TRANS. intros. inv H.
  apply is_arystr_true_access_mode in H7. destruct H7; congruence.
  repeat rewrite sizeof_eq in *.
  inv H12. generalize H H13 H H13; intros A A2 A4 A5.
  apply eval_lvalue_arystr in A2; auto. destruct A2 as [m2 [t2 [A2 A3]]].
  apply eval_lvalue_env_some in A; auto. destruct A as [m1 [t1 A]].
  apply eval_sexp_exists_lvalue in H1. destruct H1 as [id4 [o4 [k4 [B [B1 B2]]]]].
  eapply LsemC.eval_sexp_determ in B; eauto.
  destruct B as [? [? ?]]. subst id4 o4 k4.
  destruct B1 as [m3 [t3 [B3 [B4 B5]]]]. rewrite A2 in B3.
  symmetry in B3. inv B3.
  apply load_mvl_range_perm in B5. red in B5.
  eapply eval_expr_match in A4; eauto.
  eapply eval_expr_match in A5; eauto.
  generalize H2; intros C. destruct C as [C1 [C2 [C3 [C4 C5]]]].
  inv H0; simpl in *.
  eapply LsemC.eval_sexp_determ with (id1:=id1) in H1; eauto.
  destruct H1 as [? [? ?]]; subst.
  destruct H14; subst; simpl in *.
  +destruct A4 with m1 t1 as [l1 [? [? [? ?]]]]; auto.
   eapply eval_expr_determ in H8; eauto.
   destruct H8; subst.
   destruct k2; simpl in *.
   -destruct A5 with m2 t2 as [l2 [? [? ?]]]; auto.
    eapply eval_expr_determ in H9; eauto.
    destruct H9; subst.
    red. compare id id2; intros; subst.
    *destruct H15; try congruence. auto.
    *left. red; intros; subst. unfold Plt, Ple in *. omega.
   -destruct A5 with m2 t2 as [l2 [? [? [? ?]]]]; auto.
    eapply eval_expr_determ in H9; eauto.
    destruct H9; subst.
    red. compare id id2; intros; subst.
    *destruct H15; try congruence. auto.
    *left. eapply H3; eauto.
   -destruct A5 with m2 t2 as [l2 [o' [? [? ?]]]]; auto.
    eapply eval_expr_determ in H9; eauto.
    destruct H9; subst.
    apply in_map with (f:=(@fst block (int*type))) in H20. simpl in *.
    left. congruence.
   -destruct A5 with m2 t2 as [l2 [o' [? [? [? ?]]]]]; auto.
    eapply eval_expr_determ in H9; eauto.
    destruct H9; subst. left.
    red; intros; subst. unfold Plt, Ple in *. omega.
  +destruct A4 with m1 t1 as [l1 [? [? [? ?]]]]; auto.
   eapply eval_expr_determ in H8; eauto.
   destruct H8; subst.
   destruct k2; simpl in *.
   -destruct A5 with m2 t2 as [l2 [? [? ?]]]; auto.
    eapply eval_expr_determ in H9; eauto.
    destruct H9; subst.
    apply in_map with (f:=(@fst block (int*type))) in H14. simpl in *.
    eapply blocks_incl_range_lt in H5; eauto.
    left. red; intros; subst. unfold Plt, Ple in *. omega.
   -destruct A5 with m2 t2 as [l2 [? [? [? ?]]]]; auto.
    eapply eval_expr_determ in H9; eauto.
    destruct H9; subst.
    apply in_map with (f:=(@fst block (int*type))) in H14. simpl in *.
    left. congruence.
   -destruct A5 with m2 t2 as [l2 [o' [? [? ?]]]]; auto.
    eapply eval_expr_determ in H9; eauto.
    destruct H9; subst. rewrite A in H16. inv H16.
    destruct C3 with id m0 t as [l1 [o1 [? [? [? [? ?]]]]]]; auto.
    rewrite H1 in H9. inv H9.
    destruct C3 with id2 m2 t2 as [l2 [o2 [? [? [? [? ?]]]]]]; auto.
    rewrite H18 in H9. inv H9.
    apply loadbytes_range_perm in H17. red in H17.
    apply cloadbytes_length2 in H21. apply cloadbytes_length2 in H25.
    rewrite H21, H25 in *.
    generalize (sizeof_pos (Lustre.typeof a1)) (sizeof_pos (Lustre.typeof a2))
               (Int.unsigned_range o1) (Int.unsigned_range o2); intros.
    red; repeat erewrite range_perm_unsigned_add_simpl; eauto.
    compare id id2; intros; subst.
    *destruct H15; try congruence. rewrite H1 in H18. inv H18.
     right. destruct H15; [left | right]; omega.
    *red in H4. eapply H4 in H1; eauto.
     destruct H1; [left | right]; auto.
     clear H15. destruct H1; [left | right]; omega.
   -destruct A5 with m2 t2 as [l2 [o' [? [? [? ?]]]]]; auto.
    eapply eval_expr_determ in H9; eauto.
    destruct H9; subst. rewrite A in H16. inv H16.
    apply H20 in H14. red in H14. simpl in *.
    destruct C3 with id m0 t as [l1 [o1 [? [? [? [? ?]]]]]]; auto.
    rewrite H1 in H9. inv H9.
    destruct C4 with id2 m2 t2 as [l2 [v2 [? [? [? ?]]]]]; auto.
    rewrite H18 in H24. inv H24.
    apply loadbytes_range_perm in H17. red in H17.
    apply cloadbytes_length2 in H22. inv H26.
    apply load_mvl_size in H9.
    rewrite <-H9, H22 in *.
    generalize (sizeof_pos (Lustre.typeof a1)) (sizeof_pos (Lustre.typeof a2))
               (Int.unsigned_range o1) (Int.unsigned_range o') Int.max_signed_unsigned; intros.
    red; erewrite range_perm_unsigned_add_simpl; eauto.
    clear H15.
    assert (D1: Int.unsigned (Int.add o' o3) = Int.unsigned o' + Int.unsigned o3).
      unfold Int.add. rewrite Int.unsigned_repr; try omega.
    destruct H14 as [D2 | D2]; [left | right]; auto.
    rewrite D1. destruct D2; [left | right]; omega.
Qed.

Lemma storebytes_same_locrets_match:
  forall e teC m bl' ty mv ofs m1 mv' t l o m' id,
  locrets_match e teC m bl' ->
  store_mvl ty mv ofs (Vmvl m1) mv' ->
  e ! id = Some (mv, t) ->
  sizeof t = Z.of_nat (length mv) ->
  teC ! id = Some (Vptr l o, Tpointer t) ->
  In (l, (o, t)) bl' ->
  is_arystr ty = true ->
  Mem.loadbytes m l (Int.unsigned o) (sizeof t) = Some mv ->
  Mem.storebytes m l (Int.unsigned (Int.add o ofs)) m1 = Some m' ->
  ret_env_diff_id_disjoint teC ->
  Int.unsigned o + Z.of_nat (length mv) <= Int.max_signed ->
  locrets_match (PTree.set id (mv', t) e) teC m' bl'.
Proof.
  clear TRANS. intros.
  generalize H0 H0; intros A A1.
  apply store_mvl_length in A.
  apply store_mvl_range_perm2 in A1.
  red in A1.
  generalize (Int.unsigned_range o) (Int.unsigned_range ofs) Int.max_signed_unsigned; intros A2 A3 A4.
  red; intros.
  inv H0. unfold is_arystr in *.
  destruct ty; simpl in *; try congruence.
  compare id id0; intros; subst.
  +rewrite PTree.gss in H10. inv H10.
   destruct H with id0 mv ty0 as [l1 [o1 [? [? [? [? [? ?]]]]]]]; auto.
   rewrite H0 in H3. inv H3.
   exists l,o. repeat (split; auto). congruence.
   *eapply storebytes_same_loadbytes; eauto; try omega.
    rewrite <-H7. unfold Int.add. f_equal.
    rewrite Int.unsigned_repr; try omega.
   *red; intros. eapply Mem.perm_storebytes_1; eauto.
  +rewrite PTree.gso in H10; auto.
   destruct H with id0 mv0 ty0 as [l1 [o1 [? [? [? [? [? ?]]]]]]]; auto.
   exists l1, o1. repeat (split; auto).
   *rewrite <-H17. generalize (sizeof_pos t) (sizeof_pos ty0); intros.
    eapply Mem.loadbytes_storebytes_other; eauto.
    eapply H8 in n; eauto. red in n.
    rewrite <-H14.
    erewrite Mem.loadbytes_length in A1, H9; eauto.
    rewrite nat_of_Z_eq in A1, H9; try omega.
    destruct n; [left | right]; auto.
    erewrite range_perm_unsigned_add_simpl; eauto.
    omega.
   *red; intros. eapply Mem.perm_storebytes_1; eauto.
Qed.

Lemma trans_assign_lhs_correct:
  forall eC leC teC m a l ofs,
  eval_lvalue geC eC leC teC m a l ofs ->
  eval_expr geC eC leC teC m (trans_assign_lhs a) (Vptr l ofs).
Proof.
  clear TRANS. intros.
  destruct a; simpl; try (inv H; fail);
  try (constructor; auto; fail).
  destruct a; try (constructor; auto; fail).
  inv H; auto.
Qed.

Lemma trans_assign_lhs_sem_cast_vptr:
  forall l ofs a,
  is_arystr (Lustre.typeof a) = true ->
  sem_cast (Vptr l ofs) (typeof (trans_assign_lhs (trans_expr a))) type_pvoid = Some (Vptr l ofs).
Proof.
  unfold sem_cast, trans_assign_lhs; intros.
  destruct a; simpl in *; auto.
  +destruct c; simpl; auto.
  +unfold trans_v. rewrite H; auto.
  +unfold trans_binop_expr.
   destruct (classify_binop _ _); auto.
Qed.

Lemma trans_assign_expr_correct:
  forall eC leC teC m a l ofs,
  eval_lvalue geC eC leC teC m (trans_expr a) l ofs ->
  is_arystr (Lustre.typeof a) = true ->
  eval_expr geC eC leC teC m (trans_assign_expr a) (Vptr l ofs).
Proof.
  clear TRANS.
  destruct a; simpl;intros; try (inv H; fail);
  try (constructor; auto; fail).
  +econstructor; simpl; eauto. econstructor; eauto.
   unfold sem_cast; simpl; auto.
  +inv H; auto.
  +unfold trans_v in *. rewrite H0 in *.
   inv H; auto.
Qed.

Lemma trans_assign_expr_sem_cast_vptr:
  forall l ofs a,
  sem_cast (Vptr l ofs) (typeof (trans_assign_expr a)) type_pvoid = Some (Vptr l ofs).
Proof.
  unfold sem_cast, trans_assign_expr; intros.
  destruct a; simpl in *; auto.
Qed.

Lemma alignof_range:
  forall t, 0 <= alignof t <= 8.
Proof.
  clear TRANS.
  intros. destruct alignof_1248 with t as [ | [ | [ | ]]]; subst; omega.
Qed.

Lemma eval_lvalue_disjoint_sym:
  forall b1 b2 o1 o2 t1 t2,
  eval_lvalue_disjoint b2 b1 o2 o1 t2 t1 ->
  eval_lvalue_disjoint b1 b2 o1 o2 t1 t2.
Proof.
  intros. destruct H; [left | right]; auto.
  destruct H; auto.
Qed.

Lemma eval_cast_arystr:
  forall v t v',
  eval_cast v t v' ->
  is_arystr t = true ->
  v' = v.
Proof.
  induction 1; intros; auto.
  destruct ty; simpl in *; try congruence.
Qed.

Lemma eval_eqf_match:
  forall ta te e eq te' e' eC leC teC m bs bs' be bl bl',
  eval_eqf gcL ta te e te' e' eq ->
  env_match ta te e eC leC teC m bs' bl' ->
  env_diff_id_diff_b eC ->
  le_env eC bs' ->
  Plt bo bs /\ Ple bs bs' ->
  Ple bs' be ->
  env_mem_prop eC m be ->
  blocks_incl bl bl' bs bs' ->
  blocks_range bl bo bs ->
  ret_env_diff_id_disjoint teC ->
  exists m', exec_stmt geC eC leC teC m (trans_eqf eq) E0 m' Out_normal
    /\ env_match ta te' e' eC leC teC  m' bs' bl'
    /\ env_mem_prop eC m' be
    /\ mem_mapping m m' bs' bl'.
Proof.
  clear TRANS.
  intros. inv H. unfold trans_eqf. simpl.
  unfold assign_check.
  generalize H9 H9 H5; intros A A3 B.
  apply eval_sexp_has_type in A.
  eapply eval_expr_match in H9; eauto.
  destruct H9 as [vc [A1 A2]].
  destruct B as [B [B1 B2]]. rewrite <- H10 in *.
  generalize H0; intros B3. destruct B3 as [B3 [B4 [B5 [B6 B7]]]].
  inv H13. generalize H Int.max_signed_unsigned; intros B8 B9.
  eapply eval_expr_match in H; eauto.
  inv H14.
  +(*Lid*)
   inv H21. destruct H with m0 t as [l [C [C1 [C2 C3]]]]; auto.
   destruct (is_arystr (typeof (trans_expr a1))) eqn:?.
   -(*memcpy*)
    rewrite trans_expr_typeof in *.
    destruct has_type_is_arystr_vptr with v (Lustre.typeof a1) m vc as [l1 [o1 ?]]; auto.
    subst. inv A2. generalize H14 H14; intros D2 D3.
    apply store_mvl_range_perm in D2. red in D2.
    apply store_mvl_length in D3.
    apply has_type_mvl_inv in A. destruct A as [A A6].
    generalize A ;intros A7. apply mvl_type_length in A7.
    unfold make_memcpy.
    destruct Mem.range_perm_storebytes with m l (Int.unsigned ofs) m1 as [m'0 ?]; auto.
     red in B1. apply B1 with (p:=Writable) in C1.
     eapply range_perm_sube; eauto. omega.
    generalize H14; intros C5.
    apply store_mvl_sizeof in C5.
    assert(C6: Int.unsigned (Int.repr (sizeof (Lustre.typeof a1))) = sizeof (Lustre.typeof a1)).
      generalize Int.max_signed_unsigned. intros.
      rewrite Int.unsigned_repr; try omega.
    apply eval_cast_arystr in H12; auto. subst v'.
    exists m'0. split; [| split; [repeat (split; auto) | split]].
    *eapply exec_Smemcpy with (bdst:=l) (odst:=ofs) (bsrc:=l1) (osrc:=o1); eauto.
     econstructor; eauto.
     econstructor; eauto.
     constructor 2 with (Vptr l ofs); auto.
       apply trans_assign_lhs_correct; auto.
       apply trans_assign_lhs_sem_cast_vptr; auto.
     constructor 2 with (Vptr l1 o1); auto.
       apply trans_assign_expr_correct; auto.
       apply eval_expr_lvalue_inv with ta te e' (Vmvl m1); try congruence.
       congruence.
       apply trans_assign_expr_sem_cast_vptr; auto.
     constructor.
     generalize (alignof_range (Lustre.typeof a1)). intros C7.
     generalize (alignof_1248 (Lustre.typeof a1)). intros C8.
     cut (0 <= alignof (Lustre.typeof a1) <= Int.max_signed). intros C9.
     cut (eval_lvalue_disjoint l1 l o1 ofs (Lustre.typeof a2) (Lustre.typeof a1)). intros C10.
     constructor 1 with m1; intros; try rewrite Int.unsigned_repr; try omega; auto.
      apply Zdivide_unsigned_repr; auto. apply sizeof_alignof_compat.
      eapply store_mvl_div_alignof; eauto.
     rewrite H10 at 1.
     eapply eval_lvalue_disjoint_sym in C10; eauto.
     red in C10. destruct C10; [left | right]; auto.
     congruence.
     eapply assign_disjoint_eval_lvalue_disjoint; eauto.
     econstructor; eauto. unfold loadbytes. rewrite pred_dec_true; eauto.
       eapply store_mvl_range_perm2; eauto.
      congruence.
      apply eval_expr_lvalue_inv with ta te e' (Vmvl m1); auto. congruence.
     unfold Int.max_signed. simpl. omega.
    *eapply storebytes_globconsts_match; eauto.
     apply H5 in C1. unfold Plt, Ple in *. omega.
    *eapply storebytes_same_locvar_match; eauto.
    *eapply storebytes_le_locrets_match; eauto.
     apply H5 in C1. unfold Plt, Ple in *. omega.
    *eapply storebytes_locargs_match; eauto.
    *apply locvars_none_set_left; auto.
    *eapply storebytes_env_mem_prop; eauto.
    *eapply storebytes_mem_mapping; eauto.
   -(*assign*)
    rewrite trans_expr_typeof in *.
    cut (has_type v' (Lustre.typeof a1)). intros C4.
    cut (sem_cast vc (Lustre.typeof a1) (Lustre.typeof a1) = Some (valof v')). intros C5.
    destruct assign_loc_value_exits with (Lustre.typeof a1) l ofs v (valof v') m as [m'0 ?]; auto.
      eapply store_mvl_div_alignof; eauto.
      red in B1. apply B1 with (p:=Writable) in C1; auto.
      eapply range_perm_sube; eauto.
      generalize H14; intros D3. apply store_mvl_length in D3.
      apply store_mvl_range_perm in H14.
      red in H14. omega.
    exists m'0. split; [| split; [repeat (split; auto) | split]].
    *apply exec_Sassign with l ofs vc (valof v'); auto.
     repeat rewrite trans_expr_typeof; auto. congruence.
     rewrite trans_expr_typeof; auto.
    *eapply assign_loc_globconsts_match; eauto.
     apply H5 in C1. unfold Plt, Ple in *. omega.
    *eapply store_same_locvar_match; eauto.
     eapply eval_cast_val_match; eauto.
     unfold trans_ptype. rewrite Heqb. auto.
    *eapply assign_loc_le_locrets_match; eauto.
     apply H5 in C1. unfold Plt, Ple in *. omega.
    *eapply assign_loc_locargs_match; eauto.
    *apply locvars_none_set_left; auto.
    *eapply assign_loc_env_mem_prop; eauto.
    *eapply assign_loc_mem_mapping; eauto.
    *eapply eval_sem_cast_correct; eauto.
     destruct is_arystr_by_value with v (Lustre.typeof a1) as [chunk ?]; auto.
     inv H12; auto. destruct H17; congruence.
    *eapply eval_cast_has_type; eauto.
  +(*Sid*)
   inv H21. destruct H with m0 t as [l [o' [C [C1 C2]]]]; auto.
   destruct B5 with id m0 t as [l' [o [C3 [? [? [? [? ?]]]]]]]; auto.
   rewrite C1 in C3. inv C3.
   apply in_map with (f:=(fst (B:=int*type))) in H16.
   rewrite trans_expr_typeof in *.
   generalize H14 H14 (Int.unsigned_range o); intros D2 D3 D4.
   apply store_mvl_range_perm in D2. red in D2.
   apply store_mvl_length in D3.
   assert(D6: block_ofs_ty_incl_in bl' (l', (Int.add o ofs, Lustre.typeof a1))).
      exists (l', (o, t)). split; auto.
     red. simpl. red. apply store_mvl_range_perm2 in H14.
     red in H14. rewrite <-D3 in *. split; auto.
     unfold Int.add. rewrite Int.unsigned_repr; try omega.
   cut ((alignof (Lustre.typeof a1) | Int.unsigned (Int.add o ofs))). intros D7.
   destruct (is_arystr (Lustre.typeof a1)) eqn:?.
   -(*memcpy*)
    destruct has_type_is_arystr_vptr with v (Lustre.typeof a1) m vc as [l1 [o1 ?]]; auto.
    subst. inv A2.
    apply has_type_mvl_inv in A. destruct A as [A A6].
    generalize A ;intros A7. apply mvl_type_length in A7.
    unfold make_memcpy.
    destruct Mem.range_perm_storebytes with m l' (Int.unsigned (Int.add o ofs)) m1 as [m'0 ?]; auto.
      eapply range_perm_sube; eauto.
      unfold Int.add. rewrite Int.unsigned_repr; try omega.
    generalize H14; intros C5.
    apply store_mvl_sizeof in C5.
    assert(C6: Int.unsigned (Int.repr (sizeof (Lustre.typeof a1))) = sizeof (Lustre.typeof a1)).
      generalize Int.max_signed_unsigned. intros.
      rewrite Int.unsigned_repr; try omega.
    apply eval_cast_arystr in H12; auto. subst v'.
    exists m'0. split; [| split; [repeat (split; auto) | split]].
    *eapply exec_Smemcpy with (bdst:=l') (odst:=Int.add o ofs) (bsrc:=l1) (osrc:=o1); eauto.
     econstructor; eauto.
     econstructor; eauto.
     constructor 2 with (Vptr l' (Int.add o ofs)); auto.
       apply trans_assign_lhs_correct; auto.
       apply trans_assign_lhs_sem_cast_vptr; auto.
     constructor 2 with (Vptr l1 o1); auto.
       apply trans_assign_expr_correct; auto.
       apply eval_expr_lvalue_inv with ta te' e (Vmvl m1); try congruence.
       congruence.
       apply trans_assign_expr_sem_cast_vptr; auto.
     constructor.
     generalize (alignof_range (Lustre.typeof a1)). intros C7.
     generalize (alignof_1248 (Lustre.typeof a1)). intros C8.
     cut (0 <= alignof (Lustre.typeof a1) <= Int.max_signed). intros C9.
     cut (eval_lvalue_disjoint l1 l' o1 (Int.add o ofs) (Lustre.typeof a2) (Lustre.typeof a1)). intros C10.
     constructor 1 with m1; intros; try rewrite Int.unsigned_repr; try omega; auto.
      apply Zdivide_unsigned_repr; auto. apply sizeof_alignof_compat.
     rewrite H10 at 1.
     eapply eval_lvalue_disjoint_sym in C10; eauto.
     red in C10. destruct C10; [left | right]; auto.
     congruence.
     eapply assign_disjoint_eval_lvalue_disjoint; eauto.
     econstructor; eauto. unfold loadbytes. rewrite pred_dec_true; eauto.
       eapply store_mvl_range_perm2; eauto.
      congruence.
      apply eval_expr_lvalue_inv with ta te' e (Vmvl m1); auto. congruence.
     unfold Int.max_signed. simpl. omega.
    *eapply storebytes_globconsts_match; eauto.
     eapply blocks_incl_range_lt in H6; eauto. simpl in *.
     unfold Plt, Ple in *. omega.
    *eapply storebytes_in_locvars_match; eauto.
    *eapply storebytes_same_locrets_match; eauto.
    *eapply storebytes_locargs_match; eauto.
    *eapply storebytes_env_mem_prop; eauto.
    *eapply storebytes_mem_mapping; eauto.
   -(*assign*)
    cut (has_type v' (Lustre.typeof a1)). intros C4.
    cut (sem_cast vc (Lustre.typeof a1) (Lustre.typeof a1) = Some (valof v')). intros C5.
    destruct assign_loc_value_exits with (Lustre.typeof a1) l' (Int.add o ofs) v (valof v') m as [m'0 ?]; auto.
      apply range_perm_sube with (Int.unsigned o) (Int.unsigned o +sizeof t); auto.
      unfold Int.add. rewrite Int.unsigned_repr; try omega.
    exists m'0. split; [| split; [repeat (split; auto) | split]].
    *apply exec_Sassign with l' (Int.add o ofs) vc (valof v'); auto.
     repeat rewrite trans_expr_typeof; auto. congruence.
     rewrite trans_expr_typeof; auto.
    *eapply assign_loc_globconsts_match; eauto.
     eapply blocks_incl_range_lt; eauto.
    *eapply assign_loc_in_locvars_match; eauto.
    *eapply store_same_locrets_match; eauto.
     eapply eval_cast_val_match; eauto.
     unfold trans_ptype. rewrite Heqb. auto.
    *eapply assign_loc_locargs_match; eauto.
    *eapply assign_loc_env_mem_prop; eauto.
    *eapply assign_loc_mem_mapping; eauto.
    *eapply eval_sem_cast_correct; eauto.
     destruct is_arystr_by_value with v (Lustre.typeof a1) as [chunk ?]; auto.
     inv H12; auto. destruct H22; congruence.
    *eapply eval_cast_has_type; eauto.
   -eapply Zdivides_plus_int; eauto.
    apply alignof_1248.
    eapply Zdivide_trans with (alignof t); auto.
    eapply eval_lvalue_some_alignof; eauto.
    eapply store_mvl_div_alignof; eauto.
Qed.

Lemma trans_ret_match:
  forall ta te e lh mv eC leC teC m bs bs' bl bl' be,
  locenv_getmvl gcL ta te e lh mv ->
  env_match ta te e eC leC teC m bs' bl' ->
  Plt bo bs /\ Ple bs bs' ->
  blocks_incl bl bl' bs bs' ->
  blocks_range bl bo bs ->
  env_mem_prop eC m be ->
  exists b o, eval_expr geC eC leC teC m (mkaddr (trans_expr lh)) (Vptr b o)
    /\ val_match m (Lustre.typeof lh) (Vmvl mv) (Vptr b o)
    /\ (block_ofs_ty_incl_in bl' (b, (o,typeof (trans_expr lh))) \/ Ple bs' b )
    /\ block_range_perm m (b,(o,(Lustre.typeof lh))).
Proof.
  clear TRANS. unfold mkaddr.
  induction 1; simpl; intros.
  generalize H; intros C. eapply eval_expr_match in H; eauto.
  destruct H3 as [? [? [? [? ?]]]].
  generalize (sizeof_pos t)
    (sizeof_pos (Lustre.typeof lh)) H2 H2; intros A A1 A3 A4.
  apply loadbytes_range_perm in A3; red in A3.
  apply loadbytes_length2 in A4.
  destruct H0; subst.
  +destruct H with m0 t as [l [? [? [? ?]]]]; auto.
   cut ((alignof (Lustre.typeof lh) | Int.unsigned ofs)). intros A5.
   exists l, ofs; split; auto.
   -apply eval_Eaddrof; auto.
   -destruct H8 with id m0 t as [l1 [? [? [? ?]]]]; auto.
    rewrite H15 in H12. inv H12. split; [| split; [| split]]; auto.
    constructor 4; auto.
    *apply loadbytes_simpl in H2.
     apply cloadbytes_simpl in H18; try omega.
     eapply loadbytes_loadbytes_match_simpl; eauto.
    *omega.
    *red; simpl. destruct H7 as [B [B1 B2]].
     red in B1. apply B1 with (p:=Writable) in H15.
     apply range_perm_sube with 0 (sizeof t); auto.
     apply Mem.loadbytes_length in H18. rewrite H18 in A3.
     generalize (sizeof_pos t); intros.
     rewrite nat_of_Z_eq in A3; try omega.
    -eapply eval_lvalue_alignof_ofs; eauto.
  +destruct H with m0 t as [l [o [? [? ?]]]]; auto.
   exists l, (Int.add o ofs); split; auto.
   -apply eval_Eaddrof; auto.
   -destruct H9 with id m0 t as [l1 [o1 [? [? [? [? [? ?]]]]]]]; auto.
    rewrite H14 in H12. inv H12.
    cut ((alignof (Lustre.typeof lh) | Int.unsigned (Int.add o ofs))). intros A5.
    generalize (Int.unsigned_range o) Int.max_signed_unsigned; intros A6 A7.
    split; [| split; [ | split]]; auto. constructor 4; auto.
    *apply cloadbytes_simpl in H17; try omega.
     apply loadbytes_loadbytes_match with m0; eauto; try omega.
     eapply loadbytes_simpl; eauto.
    *unfold Int.add. rewrite Int.unsigned_repr; try omega.
    *rewrite trans_expr_typeof.
     left. exists (l, (o, t)); split; auto.
     red; simpl. red. split; auto.
     unfold Int.add. rewrite Int.unsigned_repr; try omega.
     erewrite Mem.loadbytes_length in A3; eauto.
     rewrite nat_of_Z_eq in A3; try omega.
    *red. simpl fst. simpl snd.
     apply range_perm_sube with (Int.unsigned o) (Int.unsigned o + sizeof t); auto.
     apply Mem.loadbytes_length in H17.
     apply loadbytes_range_perm in H2. red in H2.
     rewrite H17 in *.
     generalize (sizeof_pos t); intros.
     rewrite nat_of_Z_eq in *; try omega.
     simpl. unfold Int.add. rewrite Int.unsigned_repr; try omega.
    *eapply Zdivides_plus_int; eauto.
     apply alignof_1248.
     apply Zdivide_trans with (alignof t); auto.
     eapply eval_lvalue_some_alignof; eauto.
     eapply eval_lvalue_alignof_ofs; eauto.
Qed.

Lemma trans_args_exists:
  forall args vargs te ta e bs' bl1,
  eval_sexps gcL ta te e args vargs ->
  forall eC leC teC m,
  env_match ta te e eC leC teC m bs' bl1 ->
  exists vinC, eval_exprs geC eC leC teC m (map (trans_arg) args) vinC
    /\ vals_match m (map Lustre.typeof args) vargs vinC.
Proof.
  induction 1; simpl; intros.
  +exists nil. split; constructor.
  +destruct trans_arg_match with ta te e x y eC leC teC m bs' bl1 as [vc [? ?]]; auto.
   destruct IHForall2 with eC leC teC m as [vinC [? ?]]; auto.
   exists (vc :: vinC). split; auto.
   *constructor 2; auto.
   *constructor 2; auto.
Qed.

Lemma locenv_getmvl_lvalue_disjoint_block_ofs_ty_disjoint:
  forall ta te e a1 a2 v1 v2 eC leC teC m bs' bl1 b1 b2 o1 o2,
  locenv_getmvl gcL ta te e a1 v1 ->
  locenv_getmvl gcL ta te e a2 v2 ->
  lvalue_disjoint (LsemC.eval_lvalue gcL ta te e) a1 a2 ->
  env_match ta te e eC leC teC m bs' bl1 ->
  ret_env_diff_id_disjoint teC ->
  env_diff_id_diff_b eC ->
  eval_lvalue geC eC leC teC m (trans_expr a1) b1 o1 ->
  eval_lvalue geC eC leC teC m (trans_expr a2) b2 o2 ->
  block_ofs_ty_disjoint (b1, (o1, Lustre.typeof a1)) (b2, (o2, Lustre.typeof a2)).
Proof.
  clear TRANS.
  intros. red. simpl. inv H1.
  inv H; inv H0.
  eapply LsemC.eval_sexp_determ in H7; eauto.
  destruct H7 as [? [? ?]]; subst.
  eapply LsemC.eval_sexp_determ in H8; eauto.
  destruct H8 as [? [? ?]]; subst.
  eapply eval_expr_match in H1; eauto.
  eapply eval_expr_match in H; eauto.
  destruct H11, H14; subst.
  +destruct H1 with m0 t as [l1 [? [? [? ?]]]]; auto.
   eapply eval_expr_determ in H5; eauto.
   destruct H5; subst.
   destruct H with m1 t0 as [l2 [? [? [? ?]]]]; auto.
   eapply eval_expr_determ in H6; eauto.
   destruct H6; subst.
   red. compare id1 id2; intros; subst.
   -destruct H10; try congruence. rewrite H14 in H7.
    inv H7. right. repeat rewrite sizeof_eq in *. omega.
   -left. eapply H4; eauto.
  +destruct H1 with m0 t as [l1 [? [? [? ?]]]]; auto.
   eapply eval_expr_determ in H5; eauto.
   destruct H5; subst.
   destruct H with m1 t0 as [l2 [o' [? [? ?]]]]; auto.
   eapply eval_expr_determ in H6; eauto.
   destruct H6; subst.
   apply in_map with (f:= (@fst block (int*type))) in H17.
   red. left. simpl in *. congruence.
  +destruct H1 with m0 t as [l1 [o' [? [? ?]]]]; auto.
   eapply eval_expr_determ in H5; eauto.
   destruct H5; subst.
   destruct H with m1 t0 as [l2 [? [? [? ?]]]]; auto.
   eapply eval_expr_determ in H6; eauto.
   destruct H6; subst.
   apply in_map with (f:= (@fst block (int*type))) in H8.
   red. left. simpl in *. congruence.
  +destruct H1 with m0 t as [l1 [o1' [? [? ?]]]]; auto.
   eapply eval_expr_determ in H5; eauto.
   destruct H5; subst.
   destruct H with m1 t0 as [l2 [o2' [? [? ?]]]]; auto.
   eapply eval_expr_determ in H6; eauto.
   destruct H6; subst.
   destruct H2 as [B [B1 [B2 [B3 B4]]]].
   destruct B2 with id1 m0 t as [? [? [? [? [? [? ?]]]]]]; auto.
   destruct B2 with id2 m1 t0 as [? [? [? [? [? [? ?]]]]]]; auto.
   rewrite H20 in H11. inv H11. rewrite H2 in H7. inv H7.
   repeat rewrite sizeof_eq in *.
   apply loadbytes_range_perm in H16. red in H16.
   apply loadbytes_range_perm in H13. red in H13.
   erewrite cloadbytes_length2 in H13, H16; eauto.
   erewrite cloadbytes_length2 in H17, H22; eauto.
   generalize (sizeof_pos t) (sizeof_pos t0)
              (Int.unsigned_range o1')  (Int.unsigned_range o2'); intros.
   compare id1 id2; intros; subst.
   -destruct H10; try congruence.
    rewrite H12 in H15. inv H15.
    rewrite H20 in H2. inv H2.
    right. erewrite range_perm_unsigned_add_simpl; eauto.
    erewrite range_perm_unsigned_add_simpl; eauto.
    omega.
   -red in H3. eapply H3 in H20; eauto.
    destruct H20; [left | right]; auto.
    erewrite range_perm_unsigned_add_simpl; eauto.
    erewrite range_perm_unsigned_add_simpl; eauto.
    clear H10. omega.
Qed.

Lemma lvalue_disjoints_eval_exprs_block_disjoints:
  forall ta te e a v l l' eC leC teC m vl bl' bl1 bs' b o,
  locenv_getmvl gcL ta te e a v ->
  Forall2 (locenv_getmvl gcL ta te e) l l' ->
  eval_exprs geC eC leC teC m (map mkaddr (map trans_expr l)) vl ->
  blockof_vptrs vl (map (fun x : sexp => Lustre.typeof x) l) bl' ->
  env_match ta te e eC leC teC m bs' bl1 ->
  lvalue_disjoints (LsemC.eval_lvalue gcL ta te e) a l ->
  ret_env_diff_id_disjoint teC ->
  env_diff_id_diff_b eC ->
  eval_expr geC eC leC teC m (mkaddr (trans_expr a)) (Vptr b o) ->
  block_ofs_ty_disjoints bl' (b, (o, Lustre.typeof a)).
Proof.
  clear TRANS.
  intros. inv H7; try (inv H8; fail).
  red; intros x B.
  apply in_split in B. destruct B as [bl'1 [bl'2 ?]]. subst.
  apply blockof_vptrs_app_inv_left in H2.
  destruct H2 as [vl1 [vl2 [tyl1 [tyl2 [B1 [B2 [B3 B4]]]]]]].
  subst. apply map_app_inv in B2.
  destruct B2 as [l1 [l2 [C1 [C2 C3]]]]. subst.
  rewrite map_app, map_app in H1.
  apply Forall2_app_inv in H1; auto. destruct H1.
  apply Forall2_app_inv_l in H0.
  destruct H0 as [l1' [l2' [? [? ?]]]]. subst.
  inv B4. destruct l2; inv H8. inv H2. inv H7.
  inv H13; try (inv H2; fail).
  eapply locenv_getmvl_lvalue_disjoint_block_ofs_ty_disjoint; eauto.
  apply H4; apply in_or_app; simpl; auto.
  rewrite map_length, map_length.
  erewrite blockof_vptrs_length2; eauto.
  rewrite map_length; auto.
Qed.

Lemma trans_rets_correct:
  forall ta te e l ml eC leC teC m bs bs' bl bl1 be,
  locenv_getmvls gcL ta te e l ml ->
  env_match ta te e eC leC teC m bs' bl1 ->
  Plt bo bs /\ Ple bs bs' ->
  blocks_incl bl bl1 bs bs' ->
  blocks_range bl bo bs ->
  env_mem_prop eC m be ->
  lvalue_list_norepet (LsemC.eval_lvalue gcL ta te e) l ->
  ret_env_diff_id_disjoint teC ->
  env_diff_id_diff_b eC ->
  exists vl bl', eval_exprs geC eC leC teC m (map mkaddr (map trans_expr l)) vl
    /\ vals_match m (map Lustre.typeof l) (map Vmvl ml) vl
    /\ blockof_vptrs vl (map Lustre.typeof l) bl'
    /\ blocks_incl bl1 bl' bs' (Mem.nextblock m)
    /\ blocks_range_perm m bl'
    /\ block_ofs_ty_list_norepet bl'.
Proof.
  clear TRANS.
  induction 1; simpl; intros.
  +exists nil, nil. repeat split; try constructor; auto.
   destruct H7.
  +inv H6.
   destruct trans_ret_match with ta te e x y eC leC teC m bs bs' bl bl1 be as [b [o [? [? [? ?]]]]]; auto.
   destruct IHForall2 as [vl [bl' [? [? [? [? [? ?]]]]]]]; auto.
   exists (Vptr b o :: vl), ((b,(o,Lustre.typeof x))::bl').
   simpl. split; [| split; [| split; [| split; [| split]]]]; auto.
   -constructor 2; auto.
   -constructor 2; auto.
   -constructor 2; auto.
   -red; simpl; intros. rewrite trans_expr_typeof in H10.
    destruct H10; destruct H20; subst; simpl in *; auto.
    right. split; auto. inv H9.
    eapply loadbytes_valid_block; eauto.
    eapply locenv_getmvl_mvl_length; eauto.
   -constructor; auto.
   -constructor; auto.
    eapply lvalue_disjoints_eval_exprs_block_disjoints; eauto.
Qed.

Lemma blocks_incl_range:
  forall bl bl' bs bs',
  blocks_incl bl bl' bs bs' ->
  blocks_range bl bo bs ->
  Plt bo bs /\ Ple bs bs'  ->
  blocks_range bl' bo bs'.
Proof.
  intros. red; intros.
  apply H in H2. destruct H2.
  destruct H2 as [? [? ?]].
  apply H0 in H2. destruct H3 as [? [? ?]].
  rewrite H3 in *. unfold Plt, Ple in *. omega.
  unfold Plt, Ple in *. omega.
Qed.

Lemma mem_mapping_locargs_match:
  forall m m' bs' bl' bl'' ta leC,
  mem_mapping m m' (Mem.nextblock m) bl'' ->
  locargs_match ta leC m bs' bl' ->
  blocks_incl bl' bl'' bs' (Mem.nextblock m) ->
  blocks_range bl' bo bs' ->
  locargs_match ta leC m' bs' bl'.
Proof.
  clear TRANS.
  unfold locargs_match. intros.
  destruct H0 with id mv ty as [v [vc [? [? [? ?]]]]]; auto.
  red in H. exists v, vc. repeat (split; auto).
  inv H4.
  +inv H7; try constructor; auto.
   apply load_vmvl_false in H9. tauto.
  +inv H7. constructor 4; auto.
   rewrite <-H11. erewrite <-loadbytes_length2; eauto.
   generalize (sizeof_pos ty) (Int.unsigned_range ofs); intros B B1.
    apply H; auto; try omega.
   cut(Plt b (Mem.nextblock m)). split; auto.
   -red; intros. destruct H6.
    apply H1 in H7. destruct H7.
    *destruct H7 as [bot1 [A A1]]. apply H14 in A.
     destruct A1 as [A1 [A2 A3]]. rewrite <-A1 in *.
     destruct A; auto. right. simpl in *. destruct H7; omega.
    *destruct bot as [? [? ?]]. simpl in *.
     left. red; intros; subst. unfold Plt, Ple in *. omega.
   -eapply loadbytes_valid_block; eauto.
    erewrite <-loadbytes_length2; eauto.
    apply loadbytes_range_perm in H9. red in H9. omega.
Qed.

Lemma eval_casts_args_blocks_range:
  forall be bl vl args vl',
  args_blocks_range be bl vl (map Lustre.typeof args) ->
  eval_casts vl (map typeof (map trans_arg args)) vl' ->
  args_blocks_range be bl vl' (map Lustre.typeof args).
Proof.
  clear TRANS.
  induction vl; simpl; intros.
  +inv H. destruct args; inv H0. constructor.
  +inv H. destruct args; inv H0. inv H3.
   constructor 2; auto.
   -unfold trans_arg in H8. rewrite trans_expr_typeof in *.
    destruct (is_arystr (Lustre.typeof s)) eqn:?; unfold is_arystr in *;
    simpl in *; rewrite trans_expr_typeof in *; unfold sem_cast in *.
    *destruct a; simpl in *; inv H8; auto.
    *destruct (classify_cast (Lustre.typeof s) (Lustre.typeof s)) eqn:?;
     destruct a; simpl in *; inv H8; simpl; auto.
     destruct (cast_float_int si2 f); inv H0; auto.
     destruct (cast_single_int si2 f); inv H0; auto.
     destruct (cast_float_long si2 f); inv H0; auto.
     destruct (cast_single_long si2 f); inv H0; auto.
     destruct (_ && _); inv H0; auto.
     destruct (_ && _); inv H0; auto.
   -eapply IHvl; eauto.
Qed.

Lemma assign_list_disjoint_args_blocks_range:
  forall ta te e eC leC teC m bs bs' bl bl' bl'' lhs voutC args vinC vargs vl,
  assign_list_disjoint (LsemC.eval_lvalue gcL ta te e) lhs args ->
  env_match ta te e eC leC teC m bs' bl' ->
  env_diff_id_diff_b eC ->
  ret_env_diff_id_disjoint teC ->
  blocks_incl bl bl' bs bs' ->
  blocks_range bl bo bs ->
  eval_exprs geC eC leC teC m (map trans_arg args) vinC ->
  eval_exprs geC eC leC teC m (map mkaddr (map trans_expr lhs)) voutC ->
  blockof_vptrs voutC (map Lustre.typeof lhs) bl'' ->
  has_types vargs (map Lustre.typeof args) ->
  vals_match m (map Lustre.typeof args) vargs vinC ->
  locenv_getmvls gcL ta te e lhs vl ->
  eval_sexps gcL ta te e args vargs ->
  Plt bo bs /\ Ple bs bs'  ->
  args_blocks_range (Mem.nextblock m) bl'' vinC (map Lustre.typeof args).
Proof.
  clear TRANS.
  induction args; simpl; intros.
  +inv H5. constructor.
  +inv H5. inv H9. inv H8. inv H11. constructor 2.
   -clear IHargs. unfold trans_arg in *.
    rewrite trans_expr_typeof in *.
    destruct (is_arystr (Lustre.typeof a)) eqn:?.
    *destruct has_type_access_mode_mvl with v (Lustre.typeof a) as [mv [? ?]]; auto.
     apply is_arystr_true_access_mode; auto.
     subst. inv H18. simpl.
     generalize (sizeof_pos (Lustre.typeof a)) H8; intros A A0.
     apply mvl_type_length in A0.
     split.
     eapply loadbytes_valid_block; eauto.
      rewrite A0. apply eval_sexp_type_size in H13. omega.
     red; intros ? A1. apply in_split in A1. destruct A1 as [bl1'' [bl2'' A1]].
     subst. apply blockof_vptrs_app_inv_left in H7.
     destruct H7 as [vl1 [vl2 [tyl1 [tyl2 [A2 [A3 [A4 A5]]]]]]].
     subst. rewrite map_map in *. apply map_app_inv in A3.
     destruct A3 as [lhs1 [lhs2 [A7 [A8 A9]]]]. subst.
     rewrite map_app in H6. apply Forall2_app_inv_l in H10.
     destruct H10 as [l1' [l2' [B [B1 B2]]]].
     apply Forall2_app_inv in H6; auto.
     destruct H6. inv A5. destruct lhs2; inv H7. inv H6. inv B1.
     red; simpl.
     inv H23; try (inv H6; fail). inv H15; try (inv H6; fail).
     eapply assign_disjoint_eval_lvalue_disjoint; eauto.
     apply H; simpl; auto. apply in_or_app; simpl; auto.

     erewrite blockof_vptrs_length2; eauto. repeat rewrite map_length; auto.

    *unfold is_arystr in *.
     destruct (Lustre.typeof a), v; simpl in *; try inv H14; inv H18;
     try congruence; simpl; auto.
   -eapply IHargs; eauto.
    red; intros. apply H; simpl; auto.
Qed.

Lemma locenv_setvaddrs_vars_none:
  forall te e l vl te' e' eC,
  locenv_setvaddrs te e l vl te' e' ->
  locvars_none te eC ->
  locvars_none te' eC.
Proof.
  clear TRANS.
  induction 1; intros; auto.
  inv H; auto. apply IHlocenv_setvaddrs.
  inv H2. apply locvars_none_set_left; auto.
Qed.

Inductive vaddr_match(eC: env)(teC: temp_env): vaddr -> block*(int*type) -> Prop :=
  | vaddr_match_lid: forall id o ty l t,
     eC ! id = Some (l, t)->
     Int.unsigned o + sizeof ty <= sizeof t ->
     vaddr_match eC teC (mkvaddr id o ty Lid) (l, (o,ty))
  | vaddr_match_sid: forall id o ty l ofs t,
     teC ! id = Some (Vptr l ofs, Tpointer t) ->
     Int.unsigned ofs + Int.unsigned o <= Int.max_signed ->
     Int.unsigned o + sizeof ty <= sizeof t ->
     vaddr_match eC teC (mkvaddr id o ty Sid) (l, (Int.add ofs o, ty)).

Definition vaddr_matchs(eC: env)(teC: temp_env)(dl: list vaddr)(bl: list (block*(int*type))): Prop :=
  Forall2 (vaddr_match eC teC) dl bl.

Lemma retvals_match_type_map:
  forall ef m rets bl,
  retvals_match ef m rets bl ->
  map (fun x => snd (snd x)) bl = map (snd (B:=type)) rets.
Proof.
  clear TRANS.
  induction 1; simpl; auto.
  f_equal;auto. inv H; auto.
Qed.

Lemma locenv_setvaddr_vaddr_match:
  forall ta te e a d,
  eval_vaddr gcL ta te e a d ->
  forall m bs' bl' x v eC leC teC,
  eval_expr geC eC leC teC m (mkaddr (trans_expr a)) (Vptr (fst x) (fst (snd x))) ->
  snd (snd x) = Lustre.typeof a ->
  env_match ta te e eC leC teC m bs' bl' ->
  locenv_getmvl gcL ta te e a v ->
  vaddr_match eC teC d x.
Proof.
  clear TRANS.
  intros. inv H. destruct x as [? [? ?]].
  inv H0; try (inv H; fail).
  generalize H4. intros. apply eval_lvalue_env_some in H0.
  destruct H0 as [mv [t1 ?]].
  generalize H2; intros A.
  destruct A as [A [A1 [A2 [A3 A4]]]].
  inv H3. eapply LsemC.eval_sexp_determ in H4; eauto.
  destruct H4 as [? [? ?]]; subst; simpl in *.
  eapply eval_expr_match in H0; eauto.
  destruct H6; subst; simpl in *.
  +destruct A1 with id mv t1 as [l [? [? [? ?]]]]; auto.
   destruct H0 with mv t1 as [l1 [? [? [? ?]]]]; auto.
   rewrite H1 in H10. inv H10. rewrite H in H7. inv H7.
   eapply eval_expr_determ in H5; eauto.
   destruct H5. subst.
   constructor 1 with t0; auto.
   apply loadbytes_range_perm in H8.
   red in H8. erewrite cloadbytes_length2 in H8; eauto. omega.
  +destruct A2 with id mv t1 as [l [o' [? [? [? [? ?]]]]]]; auto.
   destruct H0 with mv t1 as [l1 [o1' [? [? ?]]]]; auto.
   rewrite H1 in H11. inv H11. rewrite H in H7. inv H7.
   eapply eval_expr_determ in H5; eauto.
   destruct H5. subst.
   apply loadbytes_range_perm in H8.
   red in H8. erewrite cloadbytes_length2 in *; eauto.
   constructor 2 with t0; auto; omega.
Qed.

Lemma locenv_setvaddrs_vaddr_matchs:
  forall ta te e lhs dl,
  eval_vaddrs gcL ta te e lhs dl ->
  forall m bs' bl' bl'' vl eC leC teC,
  eval_exprs geC eC leC teC m (map mkaddr (map trans_expr lhs)) (map (fun x => Vptr (fst x) (fst (snd x))) bl'') ->
  map (fun x => snd (snd x)) bl'' = map Lustre.typeof lhs ->
  env_match ta te e eC leC teC m bs' bl' ->
  locenv_getmvls gcL ta te e lhs vl ->
  vaddr_matchs eC teC dl bl''.
Proof.
  clear TRANS.
  induction 1; simpl; intros.
  +destruct bl''; inv H. constructor.
  +destruct bl''; inv H1. inv H4. inv H2. constructor 2; auto.
   -eapply locenv_setvaddr_vaddr_match; eauto.
   -eapply IHForall2; eauto.
Qed.

Lemma locenv_setvaddr_same_locrets_match:
  forall te e d v te1 e1 eC teC m m' bl bl' bs' l' o' mv,
  locenv_setvaddr te e d v te1 e1 ->
  locrets_match e teC m bl ->
  locvars_match te eC m bs' bl ->
  vaddr_match eC teC d (l', (o', ad_type d)) ->
  mem_mapping m m' (Mem.nextblock m) ((l', (o', ad_type d))::nil) ->
  blocks_incl bl bl' bs' (Mem.nextblock m) ->
  blocks_range bl bo bs' ->
  range_perm_keep m m' ->
  load_mvl (ad_type d) mv Int.zero v ->
  Z.of_nat (length mv) = sizeof (ad_type d) ->
  Mem.storebytes m l' (Int.unsigned o') mv = Some m' ->
  env_diff_id_diff_b eC ->
  ret_env_diff_id_disjoint teC ->
  locrets_match e1 teC m' bl /\  locvars_match te1 eC m' bs' bl.
Proof.
  clear TRANS.
  intros. generalize (Int.unsigned_range o'); intros A1.
  inv H; inv H2; split; simpl in *; inv H12; red; intros.
  +destruct H0 with id mv0 ty0 as [l1 [o1 [? [? [? [? [? ?]]]]]]]; auto.
   exists l1, o1. repeat (split; auto).
   -rewrite <-H19. destruct (zlt 0 (sizeof ty0)).
    apply H3; try omega. split.
    *eapply range_perm_valid_block_sizeof; eauto. omega.
    *destruct H1 with b m0 t0 as [l2 [? [? [? ?]]]]; auto.
     rewrite H14 in H22. inv H22.
     apply in_map with (f:=(@fst block (int*type))) in H16.
     red. simpl in *. intros ? B. destruct B; try tauto; subst.
     left. simpl. red; intros; subst. congruence.
    *repeat rewrite Mem.loadbytes_empty; auto; omega.
   -destruct (zlt 0 (sizeof ty0)). apply H6; auto. omega.
    red; intros. omega.
  +compare b id; intros; subst.
   -rewrite PTree.gss in H12. inv H12.
    destruct H1 with id m0 ty0 as [l2 [? [? [? ?]]]]; auto.
    rewrite H12 in H14. inv H14.
    exists l'. repeat (split; auto).
    eapply storebytes_same_loadbytes; eauto; try omega.
    eapply store_mvl_storebytes_eq; eauto.
   -rewrite PTree.gso in H12; auto.
    destruct H1 with id mv0 ty0 as [l2 [? [? [? ?]]]]; auto.
    exists l2. repeat (split; auto).
    rewrite <-H19. destruct (zlt 0 (sizeof ty0)).
    *change 0 with (Int.unsigned Int.zero).
     apply H3; try omega. split.
     apply Mem.loadbytes_range_perm in H19.
      eapply range_perm_valid_block_sizeof; eauto. omega.
     red; simpl; intros ? B. destruct B; try tauto; subst.
     simpl. left. eapply H10; eauto.
    *repeat rewrite Mem.loadbytes_empty; auto; omega.
  +compare b id; intros; subst.
   -rewrite PTree.gss in H12. inv H12.
    destruct H0 with id m0 ty0 as [l2 [o2 [? [? [? [? [? ?]]]]]]]; auto.
    rewrite H12 in H16. inv H16.
    exists l', ofs0. repeat (split; auto).
    *erewrite <-store_mvl_length; eauto.
    *destruct (zlt 0 (sizeof t)).
     generalize (Int.unsigned_range ofs0) (Int.unsigned_range ofs) Int.max_signed_unsigned; intros.
      unfold Int.add in H9. rewrite Int.unsigned_repr in H9; try omega.
      eapply storebytes_same_loadbytes; eauto; try omega.
      eapply store_mvl_storebytes_eq; eauto.
     rewrite Mem.loadbytes_empty in *; try omega.
      inv H17. apply store_mvl_range_perm2 in H13.
      red in H13. simpl in *. omega.
    *destruct (zlt 0 (sizeof t)).
     apply H6; auto. omega.
     red; intros. omega.
   -rewrite PTree.gso in H12; auto.
    destruct H0 with id mv0 ty0 as [l2 [o2 [? [? [? [? [? ?]]]]]]]; auto.
    exists l2, o2. repeat (split; auto).
    *destruct (zlt 0 (sizeof ty0)).
     rewrite <-H20. apply H3; try omega. split.
      eapply range_perm_valid_block_sizeof; eauto. omega.
      red; simpl; intros ? B. destruct B; try tauto; subst.
       simpl. generalize (Int.unsigned_range ofs) (Int.unsigned_range ofs0) Int.max_signed_unsigned; intros.
       red in H11. eapply H11 in H16; eauto.
       red in H16. unfold Int.add. rewrite Int.unsigned_repr; try omega.
       destruct H16; [left | right]; auto. omega.
     rewrite Mem.loadbytes_empty in *; try omega; auto.
    *destruct (zlt 0 (sizeof ty0)).
     apply H6; auto. omega.
     red; intros. omega.
  +destruct H1 with id mv0 ty0 as [l1 [? [? [? ?]]]]; auto.
   exists l1. repeat (split; auto).
   rewrite <-H20. destruct (zlt 0 (sizeof ty0)).
   -change 0 with (Int.unsigned Int.zero).
    apply H3; try omega. split.
    *apply Mem.loadbytes_range_perm in H20.
     eapply range_perm_valid_block_sizeof; eauto. omega.
    *destruct H0 with b m0 t0 as [l2 [o2 [? [? [? [? ?]]]]]]; auto.
     rewrite H16 in H21. inv H21.
     apply in_map with (f:=(@fst block (int*type))) in H22.
     red. simpl in *. intros ? C. destruct C; try tauto; subst.
     left. simpl. red; intros; subst. congruence.
   -repeat rewrite Mem.loadbytes_empty; try omega; auto.
Qed.

Lemma locenv_setvaddrs_locrets_match:
  forall te e dl vrets te' e',
  locenv_setvaddrs te e dl vrets te' e' ->
  forall eC teC bl bl' bs' m m' ef rets,
  vaddr_matchs eC teC dl bl' ->
  mem_mapping m m' (Mem.nextblock m) bl' ->
  blocks_incl bl bl' bs' (Mem.nextblock m) ->
  blocks_range bl bo bs' ->
  range_perm_keep m m' ->
  range_perm_keep_inv m' m ->
  locrets_match e teC m bl ->
  locvars_match te eC m bs' bl ->
  block_ofs_ty_list_norepet bl' ->
  vaddr_list_norepet dl ->
  locenv_getvars ef rets vrets ->
  retvals_match ef m' rets bl' ->
  map ad_type dl = map (snd (B:=type)) rets ->
  env_diff_id_diff_b eC ->
  ret_env_diff_id_disjoint teC ->
  Ple bs' (Mem.nextblock m) ->
  locrets_match e' teC m' bl /\ locvars_match te' eC m' bs' bl.
Proof.
  clear TRANS.
  induction 1; simpl; intros.
  +inv H. split; red; intros.
   -destruct H5 with id mv ty as [l [o [? [? [? [? [? ?]]]]]]]; auto.
    generalize (Int.unsigned_range o); intros A4.
    exists l, o. repeat (split; auto); destruct (zlt 0 (sizeof ty)).
    *rewrite <-H18. apply H0; auto; try omega. split.
     eapply range_perm_valid_block_sizeof; eauto. omega.
     red; intros. tauto.
    *rewrite Mem.loadbytes_empty in *; try omega; auto.
    *apply H3; auto. omega.
    *red; intros; omega.
   -destruct H6 with id mv ty as [l [? [? [? ?]]]]; auto.
    exists l. repeat (split; auto).
    destruct (zlt 0 (sizeof ty)).
    *rewrite <-H18. change 0 with (Int.unsigned Int.zero).
     apply H0; auto; try omega. split.
     eapply loadbytes_valid_block ; eauto.
     red; intros. tauto.
    *rewrite Mem.loadbytes_empty in *; try omega; auto.
  +inv H1. inv H9. inv H10. inv H11. inv H12. inv H13. inv H18.
   simpl in *. subst.
   assert(A: Z.of_nat (length mv) = sizeof (ad_type a)).
     eapply cloadbytes_length2;eauto.
   generalize (sizeof_pos (ad_type a)); intros A0.
   assert(A1: Mem.range_perm m l0 (Int.unsigned o) (Int.unsigned o + sizeof (ad_type a)) Cur Writable).
     apply H6; auto. omega.
     eapply blocks_incl_bot_range_lt with (o':=(o, ad_type a)); eauto.
     unfold Plt, Ple in *. omega.
     simpl; auto.
   assert(A2: exists m1, Mem.storebytes m l0 (Int.unsigned o) mv = Some m1).
     rewrite <-A in A1. apply Mem.range_perm_storebytes in A1.
     destruct A1 as [m1 ?]. exists m1; auto.
   destruct A2 as [m1 A2].
   assert(A3: Mem.nextblock m1 = Mem.nextblock m).
     eapply Mem.nextblock_storebytes; eauto.
   assert(B: mem_mapping m m1 (Mem.nextblock m) ((l0, (o, ad_type a)) :: nil)).
     red; intros. eapply storebytes_mem_mapping with (ty:=ad_type a); eauto.
     right. apply block_ofs_ty_incl_in_in; simpl; auto.
   assert(B1: range_perm_keep m m1).
     eapply cstorebytes_range_perm_keep; eauto.
   assert(A5: range_perm_keep m1 m').
     red; intros. apply H5; auto. red; intros ? C.
     apply H10 in C. eapply Mem.perm_storebytes_2; eauto.
   assert(A4: mem_mapping m1 m' (Mem.nextblock m1) l').
     rewrite A3. eapply storebytes_mem_mapping_cons_inv; eauto.
     apply Mem.loadbytes_storebytes_same in A2.
     rewrite <-A in *. rewrite A2; auto.
     red; intros ? C. apply B1 in A1; auto. apply A1 in C; try omega.
     eapply Mem.perm_implies; eauto. constructor.
   assert(A6: blocks_incl bl l' bs' (Mem.nextblock m1)).
     rewrite A3. red; intros. apply H3; auto. simpl; auto.
   assert(A7: range_perm_keep_inv m' m1).
     red; intros. apply B1; auto. apply H6; auto. congruence.
   assert(A8: locrets_match e1 teC m1 bl /\  locvars_match te1 eC m1 bs' bl).
     destruct H23 as [mv1 [C [C1 C2]]]. simpl in *.
     rewrite C in H9. inv H9.
     eapply locenv_setvaddr_same_locrets_match; eauto.
   destruct A8 as [A8 A9].
   eapply IHlocenv_setvaddrs; eauto.
   congruence.
Qed.

Lemma locenv_setvaddrs_match:
  forall ta te e lhs dl,
  eval_vaddrs gcL ta te e lhs dl ->
  forall  vrets te' e' m m' bs' bl' bl'' eC leC teC ef' rets vl,
  locenv_setvaddrs te e dl vrets te' e' ->
  eval_exprs geC eC leC teC m (map mkaddr (map trans_expr lhs)) (map (fun x => Vptr (fst x) (fst (snd x))) bl'') ->
  globconsts_match m' ->
  locenv_getvars ef' rets vrets ->
  retvals_match ef' m' rets bl'' ->
  mem_mapping m m' (Mem.nextblock m) bl'' ->
  blocks_incl bl' bl'' bs' (Mem.nextblock m) ->
  blocks_range bl' bo bs' ->
  range_perm_keep m m' ->
  range_perm_keep_inv m' m ->
  map Lustre.typeof lhs = map (snd (B:=type)) rets ->
  locenv_getmvls gcL ta te e lhs vl ->
  block_ofs_ty_list_norepet bl'' ->
  lvalue_list_norepet (LsemC.eval_lvalue gcL ta te e) lhs ->
  locvars_match te eC m bs' bl' ->
  env_match ta te e eC leC teC m bs' bl' ->
  env_diff_id_diff_b eC ->
  ret_env_diff_id_disjoint teC ->
  Ple bs' (Mem.nextblock m) ->
  env_match ta te' e' eC leC teC m' bs' bl'.
Proof.
  intros. generalize H15; intros A.
  destruct A as [A [A1 [A2 [A3 A4]]]].
  assert(B: map (fun x => snd (snd x)) bl'' = map (snd (B:=type)) rets).
    eapply retvals_match_type_map; eauto.
  assert(B1: vaddr_matchs eC teC dl bl'').
    eapply locenv_setvaddrs_vaddr_matchs; eauto. congruence.
  assert(B2: vaddr_list_norepet dl).
    eapply eval_vaddrs_list_norepet; eauto.
  eapply locenv_setvaddrs_locrets_match in A1; eauto. destruct A1.
  repeat (split; auto).
  +eapply mem_mapping_locargs_match; eauto.
  +eapply locenv_setvaddrs_vars_none; eauto.
  +erewrite <-eval_vaddrs_type_map; eauto.
Qed.

Lemma trans_node_all_correct:
  forall eL eL' fd vinL' voutL,
  eval_node progL gcL eL eL' fd vinL' voutL ->
  forall m vinL vinC voutC vinC' bs bl bl',
  globconsts_match m ->
  vals_match m (map snd (nd_args (snd fd))) vinL vinC ->
  Lsem.eval_casts vinL (map snd (nd_args (snd fd))) vinL' ->
  eval_casts vinC (map snd (map trans_para (nd_args (snd fd)))) vinC' ->
  blockof_vptrs voutC (map (fun x => snd x) (nd_rets (snd fd))) bl' ->
  retvals_match eL m (nd_rets (snd fd)) bl' ->
  Plt bo bs /\ Ple bs (Mem.nextblock m)  ->
  locenv_rets_match eL (nd_rets (snd fd)) ->
  blocks_incl bl bl' bs (Mem.nextblock m) ->
  blocks_range bl bo bs ->
  args_blocks_range (Mem.nextblock m) bl' vinC' (map snd (nd_args (snd fd)))->
  block_ofs_ty_list_norepet bl' ->
  has_types vinL (map snd (nd_args (snd fd))) ->
  exists m', eval_funcall geC m (trans_body (snd fd)) vinC' voutC E0 m' Vundef
     /\ globconsts_match m'
     /\ retvals_match eL' m' (nd_rets (snd fd)) bl'
     /\ mem_mapping m m' (Mem.nextblock m) bl'.
Proof.
  induction 1 using eval_node_ind2 with
  (P0 := fun ta te eL te' eL' s =>
      forall eC leC teC m bs bs' be bl bl',
      env_match ta te eL eC leC teC m bs' bl' ->
      env_diff_id_diff_b eC ->
      le_env eC bs' ->
      Plt bo bs /\ Ple bs bs' ->
      Ple bs' be  ->
      env_mem_prop eC m be ->
      blocks_incl bl bl' bs bs' ->
      blocks_range bl bo bs ->
      ret_env_diff_id_disjoint teC ->
      exists m', exec_stmt geC eC leC teC m (trans_stmt s) E0 m' Out_normal
        /\ env_match ta te' eL' eC leC teC m' bs' bl'
        /\ env_mem_prop eC m' be
        /\ mem_mapping m m' bs' bl');
  simpl; intros.
 +(*exec_node *)
  unfold trans_body.
  destruct c_alloc_variables_empty with (nd_vars f) m
    as [eC [m1 [A [A1 [A2 [A3 A4]]]]]]; auto.
  destruct bind_parameter_temps_exists with (trans_paras f) (vinC') empty_temp
    as [leC A6].
    erewrite <-trans_paras_length_eq; eauto.
  destruct bind_parameter_temps_exists with (trans_rets f) voutC empty_temp
    as [teC A7].
    erewrite <-trans_rets_length_eq; eauto.
  generalize H3; intros A8.
  rewrite map_app in A8. apply list_norepet_app in A8.
  destruct A8 as [A8 [A9 A10]].
  destruct IHeval_node with eC leC teC m1 bs (Mem.nextblock m) (Mem.nextblock m1) bl bl' as [m2 [B [B1 [B2 B3]]]]; auto.
    eapply alloc_variables_match; eauto. unfold Plt, Ple in *. omega.
    apply Ple_trans with (Mem.nextblock m); auto. apply Ple_refl.
    eapply c_alloc_variables_nextblock_le; eauto.
    eapply bind_parameter_temps_diff_id_disjoint; eauto.
  destruct c_free_list_exists with eC m2
    as [m3 B6]; auto.
    apply env_perm_m_infer; auto.
    destruct B2 as [? [? ?]]; auto.
  exists m3. repeat (split; auto).
  -apply eval_funcall_internal with leC teC eC m1 m2 Out_normal; simpl; auto.
   apply trans_paras_rets_norepet; auto.
  -destruct B1 as [B1 ?].
   eapply free_list_globconsts_match; eauto. unfold Plt, Ple in *. omega.
  -eapply free_list_disjoint_retvals_match; eauto.
   *destruct B1 as [C [C1 [C2 [C3 C4]]]].
    eapply locenv_getvars_retvals_match; eauto.
    eapply bind_parameter_temps_getvars_match; eauto.
    apply incl_refl.
   *eapply retvals_match_le_env_block_disjoint; eauto. unfold Plt, Ple in *. omega.
  -eapply free_list_mem_mapping; eauto.
   *apply Ple_trans with (Mem.nextblock m1).
    eapply c_alloc_variables_nextblock_le; eauto.
    eapply exec_stmt_funcall_m_nextblock_zle in B; eauto.
   *eapply mem_mapping_trans; eauto.
    eapply alloc_variables_mem_mapping; eauto. unfold Plt, Ple in *. omega.
 +(*eval_Sassign *)
  eapply eval_eqf_match in H; eauto.
 +(*eval_Scall *)
  destruct H as [A [A1 [A2 [A3 A4]]]].
  assert (B: fst fd = callid cdef).
    eapply find_funct_fid; eauto.
  destruct fd as [fid f]. simpl in *. rewrite <-B in *.
  destruct globfuncs_match with fid f as [loc [B1 B2]]; auto.
  assert(B4: list_norepet (map fst (nd_rets f))).
    clear TRANS. inv H4. rewrite map_app in H26.
    apply list_norepet_app in H26. intuition.
  generalize H0 H2 H0 H0; intros B5 B6 B7 B8.
  apply eval_sexps_has_types in B5.
  eapply trans_args_exists in H0; eauto. destruct H0 as [vinC [C C1]].
  eapply eval_sexps_casts_exists in B7; eauto. destruct B7 as [vinC' C1'].
  eapply trans_rets_correct in H2; eauto.
  destruct H2 as [voutC [bl'' [C2 [C3 [C4 [C5 [C7 C7']]]]]]].
  generalize C4; intros C4'. rewrite H7 in C4'; auto.
  assert(C8: retvals_match ef m (nd_rets f) bl'').
    eapply locenv_setmvls_retvals_match; eauto. congruence.
  generalize H12; intros C9.
  destruct C9 as [C9 [C10 [C11 [C12 C13]]]].
  assert(C14: blocks_range bl' bo bs').
    eapply blocks_incl_range; eauto.
  destruct IHeval_node with m vargs vinC voutC vinC' bs' bl' bl'' as [m' [D1 [D2 [D3 D4]]]]; auto.
    congruence.
    congruence.
    erewrite trans_paras_typeof; eauto.
    destruct H17 as [? [? ?]]. unfold Plt, Ple in *. omega.
    eapply locenv_setmvls_locenv_rets_match; eauto.
    rewrite <-H8. eapply eval_casts_args_blocks_range; eauto.
    apply assign_list_disjoint_args_blocks_range with ta te e eC leC teC bs bs' bl bl' lhs voutC vargs vl; auto.
    rewrite <-H8. auto.
  exists m'. split;[| split; [| split]]; auto.
  -apply exec_Scall
      with (to_typelist (map trans_ptype (argtys cdef)))
           (to_typelist (map (fun a => snd (trans_ret a))
           (rettys cdef))) cc_default (Vptr loc Int.zero) vinC' voutC (trans_body f); auto.
   *rewrite <-to_typelist_app; auto.
   *apply eval_Elvalue with loc Int.zero; auto.
    constructor 2; auto.
    rewrite <-trans_fundef_type with cdef f; auto.
    constructor 2; auto.
   *apply eval_exprlist_inv with vinC; auto.
    rewrite A2. erewrite <-trans_paras_typeof; eauto.
    repeat rewrite map_map. f_equal. apply map_ext.
    intros. rewrite trans_para_ptype; auto.
   *apply eval_exprlist_inv with voutC; auto.
    rewrite A3. erewrite trans_rets_typeof_eq; eauto.
    apply blockof_vptrs_eval_casts with bl''; eauto.
   *rewrite <-to_typelist_app; auto. apply trans_fundef_type; auto.
  -eapply locenv_setvaddrs_match; eauto.
   *erewrite <-blockof_vptrs_inv; eauto.
   *clear TRANS. inv H4; auto.
   *eapply eval_stmt_funcall_mem_range_perm; eauto.
   *eapply eval_stmt_funcall_mem_range_perm_inv; eauto.
   *destruct H17 as [? [? ?]]. unfold Plt, Ple in *. omega.
  -eapply eval_funcall_env_mem_prop; eauto.
  -eapply mem_mapping_incl; eauto.
   destruct H17 as [? [? ?]]; auto.
 +(*eval_Sfor_start *)
  eapply eval_eqf_match in H; eauto.
  destruct H as [m1 [? [? [? ?]]]].
  destruct IHeval_node with eC leC teC m1 bs bs' be bl bl' as [m' [? [? [? ?]]]]; auto.
  exists m'. split;[| split; [| split]]; auto.
  -replace E0 with (E0 ** E0); auto.
   apply exec_Sfor_start with m1; auto.
   unfold trans_eqf, assign_check, make_memcpy.
   destruct (is_arystr _); try congruence.
  -eapply mem_mapping_trans; eauto.
 +(*eval_Sfor_false *)
  exists m. split;[| split; [| split]]; auto.
  -generalize H. intros A.
   eapply eval_expr_match in H; eauto. destruct H as [vc [? ?]].
   apply eval_sexp_has_type in A.
   apply exec_Sfor_false with vc; auto.
   rewrite trans_expr_typeof.
   eapply eval_bool_val_match; eauto.
   eapply has_type_bool_val; eauto.
  -red; intros; auto.
 +(*eval_Sfor_loop *)
  generalize H; intros A.
  eapply eval_expr_match in H; eauto.
  destruct H as [vc [ ? ?]].
  destruct IHeval_node with eC leC teC m bs bs' be bl bl' as [m1 [? [? [? ?]]]]; auto.
  eapply eval_eqf_match in H1; eauto.
  destruct H1 as [m2 [? [? [? ?]]]]; auto.
  destruct IHeval_node0 with eC leC teC m2 bs bs' be bl bl' as [m' [? [? [? ?]]]]; auto.
  exists m'. split;[| split; [| split]]; auto.
  -replace E0 with (E0 ** E0 ** E0); auto.
   eapply exec_Sfor_loop; eauto.
   rewrite trans_expr_typeof.
    apply eval_sexp_has_type in A.
    eapply eval_bool_val_match; eauto.
    clear TRANS. destruct (Lustre.typeof a2); inv A; simpl;auto.
  -apply mem_mapping_trans with m2; auto.
   eapply mem_mapping_trans; eauto.
 +(*eval_Sskip *)
  exists m. split;[| split; [| split]]; auto.
  constructor. red; intros; auto.
 +(*eval_Sseq *)
  destruct IHeval_node with eC leC teC m bs bs' be bl bl' as [m1 [? [? [? ?]]]]; auto.
  destruct IHeval_node0 with eC leC teC m1 bs bs' be bl bl' as [m' [? [? [? ?]]]]; auto.
  exists m'. split;[| split; [| split]]; auto.
  -change E0 with (E0 ** E0). eapply exec_Sseq_1;eauto.
  -eapply mem_mapping_trans; eauto.
 +(*eval_Sif *)
  destruct IHeval_node with eC leC teC m bs bs' be bl bl' as [m' [? [? [? ?]]]]; auto.
  exists m'. split;[| split; [| split]]; auto.
  eapply eval_expr_match in H; eauto. destruct H as [vc [? ?]].
  apply exec_Sifthenelse with vc b; auto.
  -rewrite trans_expr_typeof.
   eapply eval_bool_val_match; eauto.
  -destruct b; auto.
 +(*eval_Scase *)
  clear TRANS.
  generalize H; intros A.
  apply eval_sexp_has_type in A.
  eapply eval_expr_match in H; eauto.
  destruct H as [vc [? ?]]. inv H11. inv H1.
  eapply eval_eqf_match in H17; eauto.
  destruct H17 as [m' [? [? [? ?]]]].
  exists m'. split;[| split; [| split]]; auto.
  remember (trans_cases _ _) as sl.
  assert (A3: exec_stmt geC eC leC teC m (select_switch2 i sl) E0 m' Out_break).
    subst sl. rewrite case_atom_select_switch2_eq with _ _ a _; auto.
    replace E0 with (E0 ** E0); auto.
    apply exec_Sseq_1 with m'; auto. constructor.
  eapply exec_stmt_select_switch_simpl in A3; eauto.
  change Out_normal with (outcome_switch Out_break).
  apply exec_Sswitch with i; auto.
  rewrite trans_expr_typeof.
  destruct (Lustre.typeof ca); simpl in *; try tauto.
Qed.

End NODE_CORRECT.

Section PROGRAM_CORRECT.

Lemma trans_mainid_eq:
  progL.(node_main) = progC.(prog_main).
Proof.
  inversion TRANS. auto.
Qed.

Lemma locenv_getvars_retvals_match_loadbytes:
  forall e rets mv b ty m,
  locenv_getvars e rets (Vmvl mv :: nil) ->
  retvals_match e m rets ((b, (Int.zero, ty)) :: nil) ->
  Mem.loadbytes m b 0 (Z.of_nat (length mv)) = Some mv.
Proof.
  clear TRANS.
  intros. inv H. inv H5. inv H0. inv H3.
  destruct H4 as [? [? [? ?]]]. inv H1.
  apply load_vmvl_false in H4. tauto.
  rewrite Int.unsigned_zero in *. simpl in *.
  rewrite H in H2. inv H2. rewrite H0 in *.
  rewrite loadbytes_full in H8; auto. inv H8; auto.
  split; auto. omega.
Qed.

Lemma storebytes_retval_match:
  forall e m ret bot b o mv m1,
  retval_match e m ret bot ->
  Mem.storebytes m b o mv = Some m1 ->
  b <> fst bot ->
  retval_match e m1 ret bot.
Proof.
  induction 1. intros.
  generalize (sizeof_pos ty); intros.
  constructor 1 with mv0; auto.
  rewrite <-H1. erewrite <-cloadbytes_length2; eauto.
  eapply Mem.loadbytes_storebytes_other; eauto. omega.
  eapply cstorebytes_range_perm_keep; eauto. omega.
Qed.

Lemma storebytes_retvals_match:
  forall e m rets bl b o mv m1,
  retvals_match e m rets bl ->
  Mem.storebytes m b o mv = Some m1 ->
  ~ In b (map (@fst block (int*type)) bl) ->
  retvals_match e m1 rets bl.
Proof.
  induction 1; simpl; intros.
  constructor.
  constructor 2;auto.
  eapply storebytes_retval_match; eauto.
  eapply IHForall2; eauto.
Qed.

Inductive classify_args: list (ident*type) -> type -> bool -> Prop :=
  | classify_args_nil:
      classify_args nil Tvoid false
  | classify_args_cons: forall arg,
      0 < sizeof (snd arg) <= Int.max_signed ->
      classify_args (arg::nil) (snd arg) true.

Lemma args_prop_classify_args:
  forall l, args_prop l ->
  exists ity b, classify_args l ity b.
Proof.
  clear TRANS.
  unfold args_prop. intros. destruct H.
  destruct l; simpl in *.
  +exists Tvoid, false. constructor 1; auto.
  +destruct l; simpl in *; try omega.
   inv H. destruct H3 as [? ?].
   exists (snd p), true. constructor 2; auto.
Qed.

Theorem trans_program_correct_general:
  forall gcL main e n maxn vass vrss,
  LsemD.exec_prog progL gcL eval_node main e n maxn vass vrss ->
  forall bi bo m b1 b2 ity oty,
  Plt bi bo /\ Plt bo (Mem.nextblock m) ->
  globconsts_match gcL bi m ->
  locenv_rets_match e (nd_rets (snd main)) ->
  classify_args (nd_args (snd main)) ity b1 ->
  Mem.range_perm m bi 0 (sizeof ity) Cur Writable ->
  classify_args (nd_rets (snd main)) oty b2 ->
  retvals_match e m (nd_rets (snd main)) (if b2 then (bo, (Int.zero, oty)) :: nil else nil) ->
  exec_prog progC bi bo (trans_body (snd main)) m n maxn vass vrss.
Proof.
  clear TRANS.
  induction 1; intros.
  constructor 1; auto.

  assert (A: exists mv1, classify_mvls (Streams.hd vass) mv1 b1).
    inv H6. rewrite <-H11 in *; simpl in *.
    exists nil. destruct (Streams.hd vass); inv H0. constructor.
    rewrite <-H10 in *. destruct (Streams.hd vass); inv H0.
    destruct l; inv H16. exists m0. constructor.
  assert (A1: exists mv2, classify_mvls (Streams.hd vrss) mv2 b2).
    inv H1. inv H8. rewrite <-H17 in *.
    exists nil. destruct (Streams.hd vrss); inv H16. constructor.
    rewrite <-H1 in *. destruct (Streams.hd vrss); inv H16.
    destruct l; inv H22. exists m0. constructor.
  destruct A as [mv1 A]. destruct A1 as [mv2 A1].

  destruct Mem.range_perm_storebytes with m bi 0 mv1 as [m1 A2].
    inv A. simpl. red. intros. omega.
    inv H6. rewrite <-H11, <-H10 in *.
    destruct has_type_mvl_inv with (snd arg) mv1 as [? ?]; auto.
      inv H0; auto.
      apply mvl_type_length in H6. rewrite H6; eauto.
  assert(A3: Mem.nextblock m1 = Mem.nextblock m).
    eapply Mem.nextblock_storebytes; eauto.
  assert(A4: globconsts_match gcL bi m1).
    eapply storebytes_globconsts_match; eauto. unfold Plt, Ple in *. omega.
  assert(A7: vals_match m1 (map snd (nd_args (snd main))) (List.map Vmvl (Streams.hd vass)) (if b1 then Vptr bi Int.zero :: nil else nil)
              /\ Lsem.eval_casts (List.map Vmvl (Streams.hd vass)) (map snd (nd_args (snd main))) (List.map Vmvl (Streams.hd vass))
              /\ eval_casts (if b1 then Vptr bi Int.zero :: nil else nil) (map snd (map trans_para (nd_args (snd main)))) (if b1 then Vptr bi Int.zero :: nil else nil)
              /\ args_blocks_range (Mem.nextblock m1) (if b2 then (bo, (Int.zero, oty)) :: nil else nil) (if b1 then Vptr bi Int.zero :: nil else nil)
                (map snd (nd_args (snd main)))).
    inv A; inv H6. repeat (econstructor; eauto).
    rewrite <-H11, <-H10 in *.
    destruct has_type_mvl_inv with (snd arg) mv1 as [? ?]; auto.
      inv H0; auto.
     generalize H6; intros A5. apply mvl_type_length in A5.
     repeat split; econstructor; eauto; try (constructor; fail).
     constructor; rewrite Int.unsigned_zero.
      eapply Mem.loadbytes_storebytes_same; eauto.
      omega. exists 0. omega.
     constructor 2; auto. eapply is_arystr_true_access_mode; eauto.
     unfold trans_para. rewrite H13. simpl. auto.
     rewrite A3. red; simpl. split. unfold Plt, Ple in *. omega.
      destruct b2; red; simpl; intros ? B; try tauto.
       destruct B; try tauto; subst. left. simpl. red; intros; subst.
       unfold Plt, Ple in *. omega.
  destruct A7 as [A7 [A8 [A9 A10]]].
  assert(A11: retvals_match e m1 (nd_rets (snd main)) (if b2 then (bo, (Int.zero, oty)) :: nil else nil)
             /\ blocks_incl (if b2 then (bo, (Int.zero, oty)) :: nil else nil) (if b2 then (bo, (Int.zero, oty)) :: nil else nil) (Mem.nextblock m1) (Mem.nextblock m1)
             /\ blocks_range (if b2 then (bo, (Int.zero, oty)) :: nil else nil) bo (Mem.nextblock m1)).
    inv H8; inv A1.
    split; [| split]; constructor; red; simpl; intros; tauto.
    rewrite <-H12, <-H10 in *. split; [| split].
    eapply storebytes_retvals_match; eauto.
     simpl. red. intros B. destruct B; try tauto; subst. unfold Plt, Ple in *. omega.
    red; intros. left. apply block_ofs_ty_incl_in_in; auto.
    red; simpl; intros ? B. destruct B; try tauto; subst. simpl. rewrite A3.
     unfold Plt, Ple in *. omega.
  destruct A11 as [A11 [A12 A13]].
  assert(B: exists m', eval_funcall geC m1 (trans_body (snd main)) (if b1 then Vptr bi Int.zero :: nil else nil) (if b2 then Vptr bo Int.zero :: nil else nil) E0 m' Vundef
              /\ globconsts_match gcL bi m'
              /\ retvals_match e' m' (nd_rets (snd main)) (if b2 then (bo, (Int.zero,oty)) :: nil else nil)
              /\ mem_mapping m1 m' (Mem.nextblock m1) (if b2 then (bo, (Int.zero, oty)) :: nil else nil)).
    apply trans_node_all_correct with bo e (List.map Vmvl (Streams.hd vass)) (List.map Vmvl (Streams.hd vrss)) (List.map Vmvl (Streams.hd vass))
       (if b1 then Vptr bi Int.zero::nil else nil) (Mem.nextblock m1) (if b2 then (bo, (Int.zero, oty))::nil else nil); auto.
    unfold Plt, Ple in *. omega.
    inv H8; inv A1; constructor; auto. constructor.
    rewrite A3. unfold Plt, Ple in *. omega.
    inv H8; constructor; auto. red; intros; tauto. constructor.
  destruct B as [m' [B [B1 [B2 B3]]]].
  assert(B6: Ple (Mem.nextblock m1) (Mem.nextblock m')).
    eapply exec_stmt_funcall_m_nextblock_zle; eauto.
  rewrite A3 in *.
  constructor 2 with b1 b2 m1 mv1 mv2 m'; auto.
  inv H1. inv A1. simpl. apply Mem.loadbytes_empty; omega.
   eapply locenv_getvars_retvals_match_loadbytes; eauto.
   rewrite <-H17 in *; auto.
  eapply IHexec_prog; eauto.
  unfold Plt, Ple in *. omega.
  inv H1. eapply eval_stmt_locenv_rets_match; eauto.
  destruct (zlt 0 (sizeof ity)).
  eapply eval_stmt_funcall_mem_range_perm; eauto; try omega.
   eapply cstorebytes_range_perm_keep; eauto; try omega.
  red; intros; omega.
Qed.

Theorem loadbytes_firstn_skipn:
  forall mv o n mv1,
  loadbytes mv o n = Some mv1 ->
  firstn (nat_of_Z n) (skipn (nat_of_Z o) mv) = mv1.
Proof.
  intros. erewrite loadbytes_contents; eauto.
  unfold getN,getn. auto.
Qed.

Lemma load_store_init_data_loadbytes:
  forall l mv o m b,
  Lenv.loadbytes_store_init_data mv o l ->
  loadbytes_store_init_data m b o l ->
  Genv.init_data_list_size l + o = Z_of_nat (length mv) ->
  0 <= o ->
  Mem.loadbytes m b o (Genv.init_data_list_size l) = Some (skipn (nat_of_Z o) mv).
Proof.
  clear TRANS.
  induction l; intros.
  +simpl in *. subst. rewrite nat_of_Z_of_nat.
   rewrite skipn_bign; auto.
   rewrite Mem.loadbytes_empty; auto. omega.
  +simpl in *.
   generalize (Genv.init_data_size_pos a) (init_data_list_size_pos l); intros.
   remember (Genv.init_data_size a) as n.
   assert(A: skipn (nat_of_Z o) mv = firstn (nat_of_Z n) (skipn (nat_of_Z o) mv) ++ skipn (nat_of_Z (o+n)) mv).
     rewrite nat_of_Z_plus; try omega. rewrite skipn_add.
     rewrite firstn_skipn; auto.
   rewrite A.
   apply Mem.loadbytes_concat; auto; destruct a; destruct H, H0; subst;
   try erewrite loadbytes_firstn_skipn; eauto;
   apply IHl; auto; try omega.
Qed.

Lemma alloc_global_genv_alloc:
  forall a gc gc' m,
  alloc_global gc a = Some gc' ->
  exists m', Genv.alloc_global geC m (trans_gvar a) = Some m'.
Proof.
  clear TRANS.
  unfold alloc_global, trans_gvar, Genv.alloc_global.
  destruct a. destruct g. simpl. intros.
  destruct (store_zeros _ _) eqn:?; try congruence.
  destruct (store_init_datas _ _ _) eqn:?; try congruence.
  destruct (Mem.alloc _ _ _) eqn:?. inv H.
  generalize (init_data_list_size_pos gvar_init). intros.
  assert(A: Mem.range_perm m2 b 0 (Genv.init_data_list_size gvar_init) Cur Freeable).
    eapply alloc_range_perm; eauto.
  generalize (init_data_list_size_pos gvar_init); intros A0.
  destruct range_perm_store_zeros with b m2 0 (Genv.init_data_list_size gvar_init) as [m3 B]; auto.
    eauto with mem.
    omega.
  rewrite B.
  assert(A1: Mem.range_perm m3 b 0 (Genv.init_data_list_size gvar_init) Cur Freeable).
    red; intros. apply ->Genv.store_zeros_perm; eauto.
  destruct range_perm_store_init_data_list with geC b gvar_init 0 m3 m0 m1 as [m4 B1]; auto.
    eauto with mem.
  rewrite B1.
  destruct Mem.range_perm_drop_2 with m4 b 0 (Genv.init_data_list_size gvar_init) Readable as [m' B2]; auto.
    red; intros. eapply Genv.store_init_data_list_perm in B1; eauto.
    apply B1; auto.
  exists m'. unfold Genv.perm_globvar. simpl. auto.
Qed.

Lemma alloc_globals_genv_allocs:
  forall l gc gc' m,
  alloc_globals gc l = Some gc' ->
  exists m', Genv.alloc_globals geC m (map trans_gvar l) = Some m'.
Proof.
  clear TRANS.
  induction l; intros.
  +exists m. inv H. auto.
  +simpl in H. destruct (alloc_global _ _) eqn:?; try congruence.
   simpl map. remember (trans_gvar a). simpl.
   destruct alloc_global_genv_alloc with a gc l0 m as [m1 ?]; auto.
   destruct IHl with l0 gc' m1 as [m' ?]; auto.
   exists m'. subst. rewrite H0. auto.
Qed.

Lemma alloc_app_nextblock_order:
  forall m m0 m1 s1 s2 bi bo,
  Mem.alloc m 0 s1 = (m0, bi) ->
  Mem.alloc m0 0 s2 = (m1, bo) ->
  Plt bi bo /\ Plt bo (Mem.nextblock m1).
Proof.
  clear TRANS.
  intros. generalize H H0; intros.
  apply Mem.nextblock_alloc in H. apply Mem.nextblock_alloc in H0.
  apply Mem.alloc_result in H1. apply Mem.alloc_result in H2.
  subst. rewrite H0, H.
  unfold Plt, Ple in *. repeat rewrite Psucc_Zsucc. omega.
Qed.

Lemma alloc_globconsts_match:
  forall gcL m n m1 bo bi,
  Mem.alloc m 0 n = (m1, bo) ->
  globconsts_match gcL bi m ->
  globconsts_match gcL bi m1.
Proof.
  intros. red; intros.
  destruct H0 with id mv ty as [l [? [? ?]]]; auto.
  exists l. repeat (split; auto).
  rewrite <-H4.
  destruct (zle (Z.of_nat (length mv)) 0).
  repeat rewrite Mem.loadbytes_empty; auto.
  apply loadbytes_alloc_unchanged with 0%Z n bo; auto.
  eapply loadbytes_valid_block; eauto. omega.
Qed.

Lemma alloc_retvals_match:
  forall e ret m m1 bo,
  Lsem.alloc_variables empty_locenv (ret :: nil) e ->
  Mem.alloc m 0 (sizeof (snd ret)) = (m1, bo) ->
  0 < sizeof (snd ret) <= Int.max_signed ->
  retvals_match e m1 (ret :: nil) ((bo, (Int.zero, snd ret)) :: nil).
Proof.
  clear TRANS.
  intros.
  inv H. inv H6. simpl in *.
  constructor 2; auto.
  constructor 1 with (alloc (sizeof ty)); auto.
  +rewrite PTree.gss; auto.
  +rewrite Int.unsigned_zero. simpl. unfold alloc.
   rewrite length_list_repeat. generalize (sizeof_pos ty).
   intros. rewrite nat_of_Z_eq; try omega.
  +rewrite Int.unsigned_zero. eapply alloc_loadbytes_same; eauto.
  +eapply alloc_range_perm; eauto.
  +rewrite Int.unsigned_zero. exists 0. auto.
  +omega.
Qed.

Lemma alloc_globals_in_exists:
  forall l gc gc' id mv ty,
  alloc_globals gc l = Some gc' ->
  gc ! id = None ->
  gc' ! id = Some (mv, ty) ->
  list_norepet (map fst l) ->
  exists init b1 b2, In (id, mkglobvar ty init b1 b2) l
    /\ Lenv.loadbytes_store_init_data mv 0 init
    /\ Z_of_nat (length mv) = Genv.init_data_list_size init.
Proof.
  clear TRANS.
  induction l; simpl; intros.
  +inv H. congruence.
  +destruct (alloc_global gc a) eqn:?; try congruence.
   inv H2. destruct a. destruct g. simpl in Heqo.
   destruct (store_zeros _ _) eqn:?; try congruence.
   destruct (store_init_datas _ _ _) eqn:?; inv Heqo.
   compare id i; intros; subst.
   -erewrite alloc_globals_notin_eq in H1; eauto.
    rewrite PTree.gss in H1. inv H1.
    exists gvar_init, gvar_readonly, gvar_volatile.
    repeat (split; auto).
    *eapply store_init_datas_bytes; eauto.
    *erewrite store_init_datas_length; eauto.
     erewrite store_zeros_length; eauto.
     unfold alloc. rewrite length_list_repeat.
     rewrite nat_of_Z_eq; try omega.
     apply init_data_list_size_pos.
   -destruct IHl with (PTree.set i (m0, gvar_info) gc) gc' id mv  ty as [init [b1 [b2 [? [? ?]]]]]; auto.
    rewrite PTree.gso; auto.
    exists init, b1, b2.
    repeat (split; auto).
Qed.

Lemma init_genvc_in_exists:
  forall gcL id mv ty,
  init_genvc (const_block progL) = Some gcL ->
  gcL ! id = Some (mv, ty) ->
  exists init b1 b2, In (id, mkglobvar ty init b1 b2) (const_block progL)
    /\ Lenv.loadbytes_store_init_data mv 0 init
    /\ Z_of_nat (length mv) = Genv.init_data_list_size init.
Proof.
  unfold init_genvc. intros.
  eapply alloc_globals_in_exists; eauto.
  rewrite PTree.gempty; auto.
  apply const_block_names_norepet.
Qed.

Lemma init_genvc_init_mem_match:
  forall gcL, init_genvc (const_block progL) = Some gcL ->
  exists m_init, Genv.init_mem progC = Some m_init
    /\ globconsts_match gcL (Mem.nextblock m_init) m_init.
Proof.
  unfold init_genvc, Genv.init_mem. intros.
  destruct alloc_globals_genv_allocs with (const_block progL) empty_locenv gcL Mem.empty as [m1 ?]; eauto.
  destruct alloc_globals_genv_alloc_funcs with geC (map trans_node (progL.(node_block))) m1 as [m2 ?]; auto.
  +simpl. intros. eapply trans_nodes_gfun; eauto.
  +exists m2. split.
   -subst geC. inv TRANS. simpl.
    rewrite <-Genv.alloc_globals_app with (m1:=m1); auto.
   -intros. red. intros.
    destruct init_genvc_in_exists with gcL id mv ty as [init [b1 [b2 [A [A1 A2]]]]]; auto.
    destruct Genv.find_var_exists with fundef type progC id (mkglobvar ty init true false) as [l [? ?]]; auto.
     rewrite func_block_names_eq; auto.
     subst geC. inv TRANS. simpl. apply in_or_app.
     apply in_map with (f:=trans_gvar) in A. auto.
    exists l. split; auto.
    apply list_norepet_app in GLOBAL_IDS_NOREPET.
    destruct GLOBAL_IDS_NOREPET as [B [B1 B2]].
    subst geC. unfold Genv.globalenv in *. inv TRANS.
    simpl prog_defs in *. rewrite Genv.add_globals_app in *.
    remember (Genv.add_globals (Genv.empty_genv fundef type) _) as g.
    rewrite add_global_funs_find_var_info in H4.
    rewrite find_symbol_add_globals_new in H3.
    rewrite alloc_globals_vars_idem with (g2:=g) in H0.
    cut (Mem.valid_block m1 l). intros A6.
    apply alloc_globals_bytes with (g:=Genv.empty_genv fundef type) (id:=id) (ty:=ty) (init:=init) in H0; auto.
    destruct H0 as [b' [A3 [A4 A5]]].
    repeat (split; auto).
    *apply Genv.alloc_globals_nextblock in H1; auto.
     rewrite H1. red in A6. clear -A6.
     apply Plt_le_trans with (Mem.nextblock m1); auto.
     apply Genv.advance_next_le.
    *rewrite A2. apply load_store_init_data_loadbytes with (m:=m2) (b:=l) in A1; eauto; try omega.
     apply loadbytes_store_init_data_invariant with m1; auto.
     intros. eapply loadbytes_alloc_globals; eauto.
     subst g. rewrite H3 in A3. inv A3.
     rewrite H4 in A4. inv A4. auto.
    *rewrite map_map. simpl. auto.
    *apply in_map with (f:=trans_gvar) in A. auto.
    *intros. eapply trans_gvars_in; eauto.
    *apply Genv.genv_vars_range in H4.
     red. apply Genv.alloc_globals_nextblock in H0; auto.
     subst g. rewrite Genv.genv_next_add_globals in H4; auto.
     rewrite H0. rewrite Mem.nextblock_empty.
     simpl Genv.genv_next in H4. auto.
    *intros. generalize H5; intros A3.
     apply trans_gvars_in in H5. destruct H5.
     exists x. split; auto. destruct a; simpl in *. subst.
     apply in_map_iff in A3. destruct A3 as [? [A3 A4]].
     destruct x0; inv A3. simpl.
     eapply alloc_globals_init_datas_types in H; eauto.
     auto.
    *apply in_map with (f:=fst) in A.
     simpl. rewrite map_map. simpl.
     red. intros. apply B2 with (x:=id) (y:=id); auto.
    *simpl; intros. eapply trans_nodes_gfun; eauto.
Qed.

Lemma args_prop_is_arystr:
  forall arg, args_prop (arg :: nil) ->
  is_arystr (snd arg) = true.
Proof.
  clear TRANS.
  intros. destruct H. inv H.
  destruct H3; auto.
Qed.

Lemma initial_states_match:
  forall gcL main e,
  LsemD.initial_state progL gcL eval_node main e ->
  exists bi bo m ity oty b1 b2, initial_state progC bi bo (trans_body (snd main)) m
     /\ (bi < bo < Mem.nextblock m)%positive
     /\ globconsts_match gcL bi m
     /\ locenv_rets_match e (nd_rets (snd main))
     /\ classify_args (nd_args (snd main)) ity b1
     /\ Mem.range_perm m bi 0 (sizeof ity) Cur Writable
     /\ classify_args (nd_rets (snd main)) oty b2
     /\ retvals_match e m (nd_rets (snd main)) (if b2 then (bo, (Int.zero, oty)) :: nil else nil).
Proof.
 induction 1; intros.
  destruct init_genvc_init_mem_match with gcL as [m_init [A A1]]; auto.
  assert (fst fi = reset_id (node_main progL)).
    eapply find_funct_fid; eauto.
  assert (fst main = node_main progL).
    eapply find_funct_fid; eauto.
  destruct fi as [fid fi]. destruct main as [nid f]. simpl in *. subst fid nid.
  destruct globfuncs_match with (reset_id (node_main progL)) fi as [loc1 [A2 A3]]; auto.
  destruct globfuncs_match with (node_main progL) f as [loc2 [A6 A7]]; auto.
  destruct args_prop_classify_args with (nd_args f) as [ity [b1 ?]]; auto.
  destruct args_prop_classify_args with (nd_rets f) as [oty [b2 ?]]; auto.
  remember (Mem.alloc m_init 0 (sizeof ity)). destruct p as [m0 bi]. symmetry in Heqp.
  remember (Mem.alloc m0 0 (sizeof oty)). destruct p as [m1 bo]. symmetry in Heqp0.
  remember (reset_id (node_main progL), fi)as fd.
  assert(A5: nd_args fi = nil).
    clear TRANS. inv H6. inv H13. auto.
  assert(A9: Plt bi bo /\ Plt bo (Mem.nextblock m1)).
    eapply alloc_app_nextblock_order; eauto.
  destruct A9 as [A9 A9'].
  assert(B: exists m', eval_funcall geC m1 (trans_body (snd fd)) nil (if b2 then Vptr bo Int.zero :: nil else nil) E0 m' Vundef
              /\ globconsts_match gcL bi m'
              /\ retvals_match e1 m' (nd_rets (snd fd)) (if b2 then (bo, (Int.zero, oty)) :: nil else nil)
              /\ mem_mapping m1 m' (Mem.nextblock m1) (if b2 then (bo, (Int.zero, oty)) :: nil else nil)).
    clear TRANS.
    apply trans_node_all_correct with bo e nil vr nil nil (Mem.nextblock m1) (if b2 then (bo, (Int.zero, oty))::nil else nil); subst; simpl; auto.
    eapply alloc_globconsts_match; eauto.
     eapply alloc_globconsts_match; eauto. erewrite <-Mem.alloc_result in A1; eauto.
    rewrite A5. constructor.
    rewrite A5; constructor.
    rewrite A5; constructor.
    rewrite H2. inv H8. constructor. constructor 2; auto. constructor.
    rewrite H2. inv H8. constructor. eapply alloc_retvals_match; eauto. congruence.
    unfold Plt, Ple in *. omega.
    rewrite H2; auto.
    eapply alloc_variables_locenv_sets_match; eauto. inv H8; repeat constructor; auto.
    red; intros. left. apply block_ofs_ty_incl_in_in; auto.
    destruct b2; red; simpl; intros ? B; try tauto. destruct B; try tauto; subst. simpl.
     unfold Plt, Ple in *. omega.
    rewrite A5. simpl. constructor.
    destruct b2. split; auto. red; intros. tauto. constructor. constructor.
    rewrite A5; constructor.
  destruct B as [m2 [B [B1 [B2 B3]]]].
  exists bi, bo, m2, ity,oty,b1,b2.
  repeat (split; auto).
  -constructor 1 with loc1 loc2 (trans_body fi) m_init m0 m1 ity oty b2; auto.
   *rewrite <-trans_mainid_eq; auto.
   *rewrite <-trans_mainid_eq; auto.
   *simpl. unfold trans_rets, trans_paras,type_of_function; simpl.
    unfold trans_para.
    rewrite A5, H2.
    clear TRANS. inv H7; inv H8; simpl; try rewrite args_prop_is_arystr;
    try congruence; try econstructor; eauto.
   *clear TRANS. inv H7; auto.
  -apply exec_stmt_funcall_m_nextblock_zle in B.
   apply Plt_le_trans with (Mem.nextblock m1); auto.
  -clear TRANS. inv H6. eapply eval_stmt_locenv_rets_match; eauto.
   eapply alloc_variables_locenv_sets_match; eauto. inv H8; repeat constructor; auto.
  -destruct (zlt 0 (sizeof ity)).
   eapply eval_stmt_funcall_mem_range_perm; eauto; try omega.
   change (sizeof ity) with (0+sizeof ity).
   eapply range_perm_alloc_other2; eauto; try omega.
   eapply alloc_range_perm; eauto.
   red; intros; omega.
  -clear TRANS. inv H8; auto. constructor. simpl in *. congruence.
Qed.

Theorem trans_program_correct:
  forall gcL main e vass vrss n maxn,
  LsemD.initial_state progL gcL eval_node main e ->
  LsemD.exec_prog progL gcL eval_node main e n maxn vass vrss ->
  exists mainC bi bo m, Ctemp.initial_state progC bi bo mainC m
    /\ Ctemp.exec_prog progC bi bo mainC m n maxn vass vrss.
Proof.
  intros.
  destruct initial_states_match with gcL main e as
    [bi [bo [m [ity [oty [b1 [b2 [A [A1 [A2 [A3 [A4 [A5 [A6 A7]]]]]]]]]]]]]]; auto.
  exists (trans_body (snd main)), bi, bo, m. split; auto.
  eapply trans_program_correct_general; eauto.
Qed.

End PROGRAM_CORRECT.

End CORRECTNESS.
