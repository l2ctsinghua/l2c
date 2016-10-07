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

Require Import List.
Require Import Maps.
Require Import Coqlib.
Require Import AST.
Require Import Errors.
Require Import Integers.
Require Import Floats.
Require Import Lident.
Require Import Lint.
Require Import Ltypes.
Require Import Lop.
Require Import Lustre.
Require Import Lvalues.
Require Import Lenv.
Require Import Lsem.
Require Import Cop.
Require Import Clop.
Require Import Values.
Require Import Events.
Require Import Memory.
Require Import Globalenvs.
Require Import Ctypes.
Require Import Cltypes.
Require Import Clight.
Require Import ClightBigstep.
Require Import Ctemp.
Require Import ExtraList.
Require Import CtempGen.
Require Import MemProof.

Section CPROOF.

Fixpoint select_switch2 (n: int) (sl: labeled_statements): statement :=
  match sl with
  | LSdefault s => s
  | LScase c s sl' => if Int.eq c n then s else select_switch2 n sl'
  end.

Definition tempenv_getvar(teC: temp_env)(var: ident*type)(v:val) :=
  teC ! (fst var) = Some (v,snd var).

Definition tempenv_getvars(teC: temp_env)(vars: list (ident*type))(vl: list val) :=
  Forall2 (tempenv_getvar teC) vars vl.

Definition eval_lvalue_disjoint(b1 b2: block)(o1 o2: int)(t1 t2: type): Prop :=
   b2 <> b1 \/ Int.unsigned o2 + sizeof t2 <= Int.unsigned o1 \/
       Int.unsigned o1 + sizeof t1 <= Int.unsigned o2.

Definition block_ofs_ty_disjoint(bot1 bot2: block*(int*type)): Prop :=
   eval_lvalue_disjoint (fst bot1) (fst bot2) (fst (snd bot1)) (fst (snd bot2)) (snd (snd bot1)) (snd (snd bot2)).

Definition block_ofs_ty_disjoints(bl: list (block*(int*type)))(bot: block*(int*type)): Prop :=
   forall bot1, In bot1 bl -> block_ofs_ty_disjoint bot bot1.

Fixpoint block_ofs_ty_list_norepet(bl: list (block*(int*type))): Prop :=
  match bl with
  | nil => True
  | cons hd tl => block_ofs_ty_disjoints tl hd /\ block_ofs_ty_list_norepet tl
  end.

Definition eval_lvalue_incl(b1 b2: block)(o1 o2: int)(t1 t2: type): Prop :=
   b2 = b1 /\ Int.unsigned o2 <= Int.unsigned o1 /\
       Int.unsigned o1 + sizeof t1 <= Int.unsigned o2 + sizeof t2.

Definition block_ofs_ty_incl(bot1 bot2: block*(int*type)): Prop :=
  eval_lvalue_incl (fst bot1) (fst bot2) (fst (snd bot1)) (fst (snd bot2)) (snd (snd bot1)) (snd (snd bot2)).

Definition block_ofs_ty_incl_in(bl: list (block*(int*type)))(bot: block*(int*type)): Prop :=
   exists bot1, In bot1 bl /\ block_ofs_ty_incl bot bot1.

Definition blocks_range(bl: list (block*(int*type)))(bs be: block):=
  forall bot, In bot bl -> (Ple bs (fst bot) /\ Plt (fst bot) be).

Definition blocks_incl(bl bl': list (block*(int*type)))(bs bs': block):=
  forall bot, In bot bl' ->
  block_ofs_ty_incl_in bl bot \/ (Ple bs (fst bot) /\ Plt (fst bot) bs').

Definition arg_blocks_range(bs: block)(bl: list (block*(int*type)))(v: val)(ty:type): Prop :=
  match v with
  | Vptr b o => Plt b bs /\ block_ofs_ty_disjoints bl (b,(o,ty))
  | _ => True
  end.

Definition args_blocks_range(bs: block)(bl: list (block*(int*type)))(vl: list val)(tyl: list type): Prop :=
  Forall2 (arg_blocks_range bs bl) vl tyl.

Definition ret_env_diff_id_disjoint (e: temp_env):  Prop :=
  forall b1 b2 id1 id2 o1 o2 t1 t2,
  e ! id1 = Some (Vptr b1 o1, Tpointer t1) ->
  e ! id2 = Some (Vptr b2 o2, Tpointer t2) ->
  id1 <> id2  ->
  eval_lvalue_disjoint b1 b2 o1 o2 t1 t2.

Definition block_range_perm(m: mem)(p: block*(int*type)) :=
  Mem.range_perm m (fst p) (Int.unsigned (fst (snd p))) (Int.unsigned (fst (snd p)) + sizeof (snd (snd p))) Cur Writable
  /\ (alignof (snd (snd p)) | Int.unsigned (fst (snd p))).

Definition blocks_range_perm(m: mem)(bl: list (block*(int*type))) :=
  Forall (block_range_perm m) bl.

Definition block_ofs_ty_disjoints_z(b: block)(o n: Z)(bl: list (block*(int*type))): Prop :=
   forall bot, In bot bl ->
   fst bot <> b \/ Int.unsigned (fst (snd bot)) + sizeof (snd (snd bot)) <= o \/ o + n <= Int.unsigned (fst (snd bot)).

Definition mem_mapping (m m': mem)(be: block)(bl: list (block*(int*type))): Prop :=
  forall b o n,
  Plt b be /\ block_ofs_ty_disjoints_z b o n bl ->
  Mem.loadbytes m' b o n = Mem.loadbytes m b o n.

Lemma block_ofs_ty_incl_in_in:
  forall bot bl, In bot bl ->
  block_ofs_ty_incl_in bl bot.
Proof.
  intros. red; intros. exists bot; split; auto.
  red; red; intros. intuition.
Qed.

Lemma blocks_incl_bot_range_lt:
  forall bo bs bs' bl bl' l l' o',
  Ple bs bs' /\ Ple bs' l ->
  blocks_incl bl bl' bs bs' ->
  blocks_range bl bo bs ->
  In (l', o') bl' ->
  Plt l' l.
Proof.
  intros.
  apply H0 in H2. destruct H2; simpl in *.
  +destruct H2 as [bot [? ?]].
   destruct H3 as [? [? ?]]. simpl in *. subst.
   red in H1. apply H1 in H2.
   unfold Plt, Ple in *. omega.
  +unfold Plt, Ple in *. omega.
Qed.

Lemma args_blocks_range_trans:
  forall bs1 bl vl tyl,
  args_blocks_range bs1 bl vl tyl ->
  forall bs2, Ple bs1 bs2->
  args_blocks_range bs2 bl vl tyl.
Proof.
  induction 1; intros.
  constructor.
  constructor 2; auto.
  destruct x; simpl in *; auto.
  destruct H. split; auto.
  unfold Plt, Ple in *. omega.
  apply IHForall2; auto.
Qed.

Lemma mem_mapping_trans:
  forall m m1 m2 be l,
  mem_mapping m m1 be l ->
  mem_mapping m1 m2 be l ->
  mem_mapping m m2 be l.
Proof.
  intros. red; intros.
  rewrite H0; auto.
Qed.

Lemma blocks_incl_ofs_ty_disjoints_z:
  forall bl bl' bs be b o n,
  blocks_incl bl bl' bs be ->
  Plt b bs ->
  block_ofs_ty_disjoints_z b o n bl ->
  block_ofs_ty_disjoints_z b o n bl'.
Proof.
  intros. red; intros.
  apply H in H2. destruct bot as [b1 [o1 ty1]].
  simpl in *. destruct H2.
  +destruct H2 as [bot [? ?]]. apply H1 in H2.
   destruct H3 as [? [? ?]]. destruct bot as [? [? ?]]. simpl in *.
   subst. destruct H2; auto. right. omega.
  +left. red; intros. subst.
   unfold Ple, Plt in *. omega.
Qed.

Lemma mem_mapping_incl:
  forall m m' bl' bl'' bs' be,
  mem_mapping m m' (Mem.nextblock m) bl'' ->
  blocks_incl bl' bl'' bs' (Mem.nextblock m) ->
  Ple bs' be ->
  Ple be (Mem.nextblock m) ->
  mem_mapping m m' bs' bl'.
Proof.
  intros. red; intros.
  apply H; auto. destruct H3.
  assert (Plt b (Mem.nextblock m)).
    unfold Plt, Ple in *. omega.
  split; auto.
  eapply blocks_incl_ofs_ty_disjoints_z; eauto.
Qed.

Lemma case_atom_select_switch2_eq:
  forall l i ac lexpr,
  select_case i l = Some ac ->
  select_switch2 i (trans_cases lexpr l) = Ssequence (assign_check lexpr ac) Sbreak.
Proof.
  induction l; simpl; intros.
  inv H.

  destruct a.
  destruct p; simpl in *; try congruence;
  remember (Int.eq _ _) as q;
  destruct q; simpl in *; try congruence; auto;
  destruct b; simpl in *; rewrite <-Heqq in H;
  try congruence; auto.
Qed.

Lemma exec_stmt_select_switch_simpl:
  forall geC l lh sl i eC leC teC m m' t out,
  sl = trans_cases (trans_expr lh) l ->
  exec_stmt geC eC leC teC m (select_switch2 i sl) t m' out ->
  exec_stmt geC eC leC teC m (seq_of_labeled_statement (select_switch i sl)) t m' out.
Proof.
  induction l; intros; subst; simpl in *; auto.
  destruct a. remember (trans_expr lh) as lexpr.
  destruct p; simpl in *; auto;
  remember (Int.eq _ _) as q;
  destruct q; simpl in *;
  try (apply exec_Sseq_2; auto);
  try (inv H0; auto; inv H10; congruence; fail);
  subst; apply IHl with lh; auto.
Qed.

Lemma sizeof_chunk_eq:
  forall t chunk,
  access_mode t = By_value chunk ->
  size_chunk chunk = sizeof t.
Proof.
  destruct t; intros; inv H; simpl; auto.
  destruct i; destruct s; inv H1; auto.
  destruct f; inv H1; auto.
Qed.

Lemma deref_loc_determ:
  forall ty m b o v1,
  deref_loc ty m b o v1 ->
  forall v2,
  deref_loc ty m b o v2 ->
  v1 = v2.
Proof.
  induction 1; induction 1; intros; congruence.
Qed.

Lemma load_load_bytes:
  forall m b o mv m1,
  Mem.loadbytes m b (Int.unsigned o) (Z.of_nat (length mv)) = Some mv ->
  loadbytes mv (Int.unsigned Int.zero) (Z_of_nat (length m1)) = Some m1 ->
  Mem.loadbytes m b (Int.unsigned o) (Z.of_nat (length m1)) = Some m1.
Proof.
  intros.
  assert (A: Z_of_nat (length m1) <= Z_of_nat (length mv)).
    apply loadbytes_length_le in H0.
    omega.
  assert (A1: Z.of_nat (length mv) = Z.of_nat (length m1) + (Z.of_nat (length mv) - Z.of_nat (length m1))).
    omega.
  rewrite A1 in H.
  apply Mem.loadbytes_split in H; try omega.
  destruct H as [bytes1 [bytes2 [A2 [A3 A4]]]].
  subst. rewrite A2. f_equal.
  apply Mem.loadbytes_length in A2.
  rewrite nat_of_Z_of_nat in A2. rewrite <- A2 in *.
  rewrite Int.unsigned_zero in H0.
  apply loadbytes_first in H0; auto.
Qed.

Lemma loadbytes_simpl:
  forall m o t bytes,
  loadbytes m o (sizeof t) = Some bytes ->
  loadbytes m o (Z.of_nat (length bytes)) = Some bytes.
Proof.
  intros. erewrite <-loadbytes_length2; eauto.
Qed.

Lemma cloadbytes_length2:
  forall m b o t bytes,
  Mem.loadbytes m b o (sizeof t) = Some bytes ->
  Z_of_nat (length bytes) = sizeof t.
Proof.
  intros. erewrite Mem.loadbytes_length; eauto.
  generalize (sizeof_pos t); intros.
  rewrite nat_of_Z_eq; auto.
Qed.

Lemma cloadbytes_simpl:
  forall m b o n bytes,
  Mem.loadbytes m b o n = Some bytes ->
  Mem.loadbytes m b o (Z.of_nat (length bytes)) = Some bytes.
Proof.
  intros.
  destruct (zle n 0).
  rewrite Mem.loadbytes_empty in H; auto.
  inv H. simpl. rewrite Mem.loadbytes_empty; auto. omega.
  erewrite Mem.loadbytes_length; eauto.
  rewrite nat_of_Z_eq; auto. omega.
Qed.

Lemma load_skip:
  forall l1 l2 chunk v o,
  load chunk (l1 ++ l2) (Int.unsigned o) = Some v ->
  length l1 = nat_of_Z (Int.unsigned o) ->
  load chunk l2 0 = Some v.
Proof.
  unfold load. intros.
  destruct (valid_access_dec (l1 ++ l2) chunk (Int.unsigned o)); inv H.
  rewrite pred_dec_true; auto.
  +rewrite <-H0. simpl.
   replace (length l1) with (0 + length l1)%nat by omega.
   rewrite getN_app_skipn; auto.
   rewrite skipn_length_app; try omega.
   replace (length l1 - length l1)%nat with 0%nat by omega.
   simpl. auto.
  +destruct v0 as [[? ?] ?].
   rewrite app_length, Nat2Z.inj_add in H1.
   rewrite H0 in H1. rewrite nat_of_Z_eq in H1; try omega.
   repeat split; try omega.
   exists 0. auto.
Qed.

Lemma load_first:
  forall l1 l2 chunk v,
  load chunk (l1 ++ l2) 0 = Some v ->
  size_chunk chunk <= Z_of_nat (length l1) ->
  load chunk l1 0 = Some v.
Proof.
  unfold load. intros.
  destruct (valid_access_dec (l1 ++ l2) chunk 0); inv H.
  rewrite pred_dec_true; auto.
  +unfold size_chunk_nat. simpl.
   unfold getN, getn. simpl.
   rewrite firstn_length_app1; auto.
   apply Nat2Z.inj_le.
   generalize (size_chunk_pos chunk); intros.
   rewrite nat_of_Z_eq; try omega.
  +destruct v0 as [[? ?] ?].
   rewrite app_length, Nat2Z.inj_add in H1.
   repeat split; try omega.
   exists 0. auto.
Qed.

Lemma load_load_match:
  forall m b o mv v chunk ty,
  Mem.loadbytes m b (Int.unsigned o) (Z_of_nat (length mv)) = Some mv ->
  load chunk mv (Int.unsigned Int.zero) = Some v ->
  (align_chunk chunk | Int.unsigned o) ->
  exists vc, Mem.load chunk m b (Int.unsigned o) = Some vc
    /\ val_match m ty v vc.
Proof.
  intros. generalize H H0; intros A A1.
  apply load_valid_access in A1. destruct A1 as [[? ?] ?].
  apply Mem.loadbytes_length in A.
  assert (A2: Z.of_nat (length mv) = size_chunk chunk + (Z.of_nat (length mv) - size_chunk chunk)).
    omega.
  rewrite A2 in H.
  apply Mem.loadbytes_split in H; try omega.
  destruct H as [bytes1 [bytes2 [A3 [A4 A5]]]].
  subst. generalize A3; intros A5.
  apply Mem.loadbytes_length in A5.
  apply load_first in H0.
  apply Mem.loadbytes_load in A3; auto.
  exists (Memdata.decode_val chunk bytes1).
  split; auto.
  apply load_decode_match; auto.
  rewrite A5. rewrite nat_of_Z_eq; try omega.
Qed.

Lemma loadbytes_load_match:
  forall m b o1 o2 mv v chunk ty,
  Mem.loadbytes m b (Int.unsigned o1) (Z_of_nat (length mv)) = Some mv ->
  load chunk mv (Int.unsigned o2) = Some v ->
  Int.unsigned o1 + Int.unsigned o2 <= Int.max_signed ->
  (align_chunk chunk | Int.unsigned o1) ->
  exists vc, Mem.load chunk m b (Int.unsigned (Int.add o1 o2)) = Some vc
    /\ val_match m ty v vc.
Proof.
  intros.
  generalize H0 (Int.unsigned_range o1) (Int.unsigned_range o2). intros.
  apply load_valid_access in H3. destruct H3 as [[? ?] ?].
  assert (A2: Z.of_nat (length mv) = Int.unsigned o2 + (Z.of_nat (length mv) - Int.unsigned o2)).
    omega.
  rewrite A2 in H.
  generalize Int.max_signed_unsigned. intros.
  apply Mem.loadbytes_split in H; try omega.
  destruct H as [bytes1 [bytes2 [A3 [A4 A5]]]].
  subst.
  apply Mem.loadbytes_length in A3.
  apply cloadbytes_simpl in A4.
  apply load_skip in H0; auto.
  apply load_load_match with bytes2; auto;
  unfold Int.add; rewrite Int.unsigned_repr; try omega; auto.
  apply Zdivide_plus_r; auto.
Qed.

Lemma loadbytes_loadbytes_match:
  forall m b o1 o2 mv m1,
  Mem.loadbytes m b (Int.unsigned o1) (Z.of_nat (length mv)) = Some mv ->
  loadbytes mv (Int.unsigned o2) (Z_of_nat (length m1)) = Some m1 ->
  Int.unsigned o1 + Int.unsigned o2 <= Int.max_signed ->
  Mem.loadbytes m b (Int.unsigned (Int.add o1 o2)) (Z.of_nat (length m1)) = Some m1.
Proof.
  intros.
  generalize H0 (Int.unsigned_range o2); intros.
  apply loadbytes_range_perm in H2. red in H2.
  assert (A2: Z.of_nat (length mv) = Int.unsigned o2 + (Z.of_nat (length mv) - Int.unsigned o2)).
    omega.
  rewrite A2 in H.
  generalize (Int.unsigned_range o1) (Int.unsigned_range o2); intros.
  generalize Int.max_signed_unsigned. intros.
  apply Mem.loadbytes_split in H; try omega.
  destruct H as [bytes1 [bytes2 [A3 [A4 A5]]]].
  subst. apply Mem.loadbytes_length in A3.
  apply cloadbytes_simpl in A4.
  change (Int.unsigned o2) with (0 + Int.unsigned o2) in H0.
  eapply loadbytes_offset_add_skipn in H0; eauto; try omega.
  rewrite <-A3, skipn_length_app in H0; try omega.
  rewrite minus_diag in H0. simpl in H0.
  apply load_load_bytes with bytes2; auto.
  unfold Int.add. rewrite Int.unsigned_repr; try omega. auto.
Qed.

Lemma loadbytes_loadbytes_match_simpl:
  forall m l mv mv1 ofs,
  Mem.loadbytes m l 0 (Z.of_nat (length mv)) = Some mv ->
  loadbytes mv (Int.unsigned ofs) (Z.of_nat (length mv1)) = Some mv1 ->
  Mem.loadbytes m l (Int.unsigned ofs) (Z.of_nat (length mv1)) = Some mv1.
Proof.
  intros.
  apply loadbytes_loadbytes_match with (o1:= Int.zero) (b:=l) (m:=m) in H0; simpl; auto.
  +rewrite Int.add_zero_l in H0; auto.
  +apply loadbytes_range_perm in H0.
   red in H0. rewrite Int.unsigned_zero. simpl.
   generalize Int.max_signed_unsigned. intros. omega.
Qed.

Lemma load_mvl_loadbytes_deref_loc_exists_rec:
  forall ty mv o v m l o',
  load_mvl ty mv o v ->
  Mem.loadbytes m l (Int.unsigned o') (Z_of_nat (length mv)) = Some mv ->
  Int.unsigned o' + Z.of_nat (length mv) <= Int.max_signed ->
  (alignof ty | Int.unsigned o') ->
  exists vc, deref_loc ty m l (Int.add o' o) vc
    /\ val_match m ty v vc.
Proof.
  intros. generalize H; intros A.
  apply load_mvl_range_perm in A. red in A.
  generalize (Int.unsigned_range o') Int.max_signed_unsigned.
  intros A1 A2.
  inv H.
  +destruct loadbytes_load_match with m l o' o mv v chunk ty as [vc [? ?]]; auto.
   omega.
   erewrite <-alignof_chunk_eq; eauto.
   rewrite access_mode_eq in *; eauto.
   exists vc. split; auto.
   constructor 1 with chunk; auto.
  +exists (Vptr l (Int.add o' o)).
   rewrite access_mode_eq in *; eauto.
   split. destruct H3.
   -constructor 3; auto.
   -constructor 2; auto.
   -assert(Int.unsigned o' + Int.unsigned o + Z_of_nat (length m1) <= Int.max_signed).
      apply loadbytes_length in H4.
      rewrite <-H4. rewrite nat_of_Z_eq; try omega.
    constructor 4; auto.
    apply loadbytes_loadbytes_match with mv; auto; try omega.
    erewrite <-loadbytes_length; eauto;
    rewrite nat_of_Z_eq; try omega. auto.
    unfold Int.add. rewrite Int.unsigned_repr; try omega.
    apply Zdivides_plus_int; auto.
    apply alignof_1248.
Qed.

Lemma load_mvl_loadbytes_deref_loc_exists:
  forall ty mv o v m l,
  load_mvl ty mv o v ->
  Mem.loadbytes m l 0 (Z_of_nat (length mv)) = Some mv ->
  exists vc, deref_loc ty m l o vc
    /\ val_match m ty v vc.
Proof.
  intros.
  destruct load_mvl_loadbytes_deref_loc_exists_rec with ty mv o v m l Int.zero as [vc [? ?]]; auto.
  rewrite Int.unsigned_zero. simpl.
  apply load_mvl_range_perm in H. red in H. omega.
  rewrite Int.unsigned_zero. exists 0. auto.
  exists vc. split; auto.
  rewrite Int.add_zero_l in H1; auto.
Qed.

Lemma val_match_encode_val:
  forall chunk m v vc ty,
  val_match m ty v vc ->
  has_type v ty ->
  Ltypes.access_mode ty = By_value chunk ->
  Lvalues.encode_val chunk v = Memdata.encode_val chunk vc.
Proof.
  induction 1; destruct ty; simpl; try tauto; intros; try congruence.
  destruct i0,s; inv H0; auto.
  destruct f0; inv H0; auto.
  destruct f0; inv H0; auto.
Qed.

Lemma storebytes_same_loadbytes:
  forall m l o ofs bytes m' mv mv' n,
  Mem.storebytes m l (o + ofs) bytes = Some m' ->
  storebytes mv ofs bytes = Some mv' ->
  Mem.loadbytes m l o n = Some mv ->
  Mem.loadbytes m' l o n = Some mv'.
Proof.
  intros.
  generalize H0 H0 H1; intros A A1 A2.
  apply storebytes_length in A.
  apply storebytes_range_perm in A1. red in A1.
  apply Mem.loadbytes_length in A2.
  rewrite <- A in *.
  assert(A3: n <= 0 \/ 0 < n). omega. destruct A3 as [A3 | A3].
  +rewrite Mem.loadbytes_empty in *; auto. inv H1.
   destruct mv'; auto. inv A.
  +rewrite <-Nat2Z.id with (length mv) in A2.
   apply Z2Nat.inj in A2; try omega. subst.
   replace (Z.of_nat (length mv)) with (ofs + (Z.of_nat (length mv)-ofs)) in *; try omega.
   apply Mem.loadbytes_split in H1; try omega.
   destruct H1 as [mv1 [mv2 [? [? ?]]]]. subst.
   generalize H1; intros A4.
   apply Mem.loadbytes_length in A4.
   rewrite <-Nat2Z.id with (length mv1) in A4.
   apply Z2Nat.inj in A4; try omega. subst.
   apply storebytes_split_right in H0. destruct H0 as [mv2' [? ?]].
   subst. apply Mem.loadbytes_concat; auto; try omega.
   -rewrite <-H1. eapply Mem.loadbytes_storebytes_other; eauto; try omega.
    right. left. omega.
   -repeat rewrite app_length in *.
    rewrite Nat2Z.inj_add in *.
    replace (Z.of_nat (length mv1) + Z.of_nat (length mv2) - Z.of_nat (length mv1))
      with (Z.of_nat (length mv2')) in *; try omega.
    destruct storebytes_split_left with mv2 bytes mv2' as [l1 [l2 [? ?]]]; auto.
    subst. repeat rewrite app_length in *. rewrite Nat2Z.inj_add in *.
    eapply Mem.loadbytes_concat; eauto; try omega.
    *eapply Mem.loadbytes_storebytes_same; eauto.
    *apply Mem.loadbytes_split in H2; try omega.
     destruct H2 as [mv21 [mv22 [? [? ?]]]]. subst.
     generalize H3; intros A4.
     apply Mem.loadbytes_length in A4. rewrite nat_of_Z_of_nat in A4.
     eapply app_length_equal_inv in H4; eauto. destruct H4; subst.
     rewrite <-H3. eapply Mem.loadbytes_storebytes_other; eauto; try omega.
     right. right. omega.
Qed.

Lemma store_same_loadbytes:
  forall m chunk l o ofs v vc m' mv mv' n ty,
  Mem.store chunk m l (o + ofs) vc = Some m' ->
  store chunk mv ofs v = Some mv' ->
  val_match m ty v vc ->
  has_type v ty ->
  Ltypes.access_mode ty = By_value chunk ->
  Mem.loadbytes m l o n = Some mv ->
  Mem.loadbytes m' l o n = Some mv'.
Proof.
  intros.
  generalize H0 H0 H4; intros A A1 A2.
  apply store_length in A.
  apply store_valid_access in A1. destruct A1 as [A1 B]. red in A1.
  apply Mem.loadbytes_length in A2.
  rewrite <- A in *.
  assert(A3: n <= 0 \/ 0 < n). omega. destruct A3 as [A3 | A3].
  +rewrite Mem.loadbytes_empty in *; auto. inv H4.
   destruct mv'; auto. inv A.
  +rewrite <-Nat2Z.id with (length mv) in A2.
   apply Z2Nat.inj in A2; try omega. subst.
   replace (Z.of_nat (length mv)) with (ofs + (Z.of_nat (length mv)-ofs)) in *; try omega.
   apply Mem.loadbytes_split in H4; try omega.
   destruct H4 as [mv1 [mv2 [? [? ?]]]]. subst.
   generalize H4; intros A4.
   apply Mem.loadbytes_length in A4.
   rewrite <-Nat2Z.id with (length mv1) in A4.
   apply Z2Nat.inj in A4; try omega. subst.
   apply store_split_right in H0. destruct H0 as [mv2' [? ?]].
   subst. apply Mem.loadbytes_concat; auto; try omega.
   -rewrite <-H4. eapply Mem.loadbytes_store_other; eauto; try omega.
    right. right. left. omega.
   -repeat rewrite app_length in *.
    rewrite Nat2Z.inj_add in *.
    replace (Z.of_nat (length mv1) + Z.of_nat (length mv2) - Z.of_nat (length mv1))
      with (Z.of_nat (length mv2')) in *; try omega.
    destruct store_split_left with chunk mv2 mv2' v as [l1 [l2 [? [? [? ?]]]]]; auto.
    subst. rewrite app_length in *. rewrite Nat2Z.inj_add in *.
    apply Mem.loadbytes_split in H5; try omega.
    destruct H5 as [mv21 [mv22 [? [? ?]]]]. subst.
    generalize H7; intros A4.
    apply Mem.loadbytes_length in A4. rewrite nat_of_Z_of_nat in A4.
    eapply app_length_equal_inv in H8; eauto. destruct H8; subst.
    apply Mem.loadbytes_concat; auto; try omega.
    *rewrite Lvalues.encode_val_length. unfold size_chunk_nat.
     rewrite nat_of_Z_eq; try omega.
     erewrite val_match_encode_val; eauto.
     eapply Mem.loadbytes_store_same; eauto.
    *rewrite <-H7. eapply Mem.loadbytes_store_other; eauto; try omega.
     right. right. right.
     apply store_length in H6. omega.
Qed.

Lemma assign_loc_value_exits:
  forall ty loc ofs v vc m,
  is_arystr ty = false ->
  has_type v ty ->
  (alignof ty | Int.unsigned ofs) ->
  Mem.range_perm m loc (Int.unsigned ofs) (Int.unsigned ofs + sizeof ty) Cur Writable ->
  exists m', assign_loc ty m loc ofs vc m'.
Proof.
  unfold is_arystr. intros.
  destruct has_type_access_mode with v ty as [ [chunk ?] | [? | ?]]; auto;
  generalize H3; intros A; rewrite access_mode_eq in A; eauto.
  +destruct Mem.valid_access_store with m chunk loc (Int.unsigned ofs) vc as [m1 ?]; auto.
   red. split. erewrite sizeof_chunk_eq; eauto.
   erewrite <-alignof_chunk_eq; eauto.
   exists m1. constructor 1 with chunk; auto.
  +destruct ty; inv H; inv H3.
   destruct i, s; congruence.
   destruct f; congruence.
  +destruct ty; inv H; inv H3.
   destruct i, s; congruence.
   destruct f; congruence.
Qed.

Lemma assign_loc_nextblock_eq:
  forall ty m loc ofs v m',
  assign_loc ty m loc ofs v m' ->
  Mem.nextblock m' = Mem.nextblock m.
Proof.
  induction 1; simpl in *; intros.
  destruct (access_mode ty); try congruence.
  apply Mem.nextblock_store in H0; auto.
  apply Mem.nextblock_storebytes in H4; auto.
Qed.

Lemma assign_loc_loadbytes_other:
  forall ty1 b1 o1 v1 m m',
  assign_loc ty1 m b1 o1 v1 m' ->
  forall b o n,
  b <> b1 \/ o + n <= Int.unsigned o1 \/ Int.unsigned o1 + sizeof ty1 <= o->
  Mem.loadbytes m' b o n =
  Mem.loadbytes m b o n.
Proof.
  intros. inv H; simpl in *.
  +apply Mem.loadbytes_store_other with chunk b1 (Int.unsigned o1) v1; auto.
   erewrite sizeof_chunk_eq; eauto. destruct H0; auto.
  +generalize (sizeof_pos ty1); intros.
   assert(n <= 0 \/ 0 < n). omega.
   destruct H7. repeat rewrite Mem.loadbytes_empty; auto.
   apply Mem.loadbytes_storebytes_other with b1 (Int.unsigned o1) bytes; auto.
   omega. erewrite Mem.loadbytes_length; eauto.
   rewrite nat_of_Z_eq; try omega; auto.
Qed.

Lemma block_ofs_ty_disjoints_incl_in_trans_or_uneq:
  forall b1 b2 o1 o2 ty1 n2 bs bl,
  Ple bs b1 \/ block_ofs_ty_incl_in bl (b1, (o1, ty1)) ->
  Plt b2 bs ->
  block_ofs_ty_disjoints_z b2 o2 n2 bl ->
  b2 <> b1 \/ o2 + n2 <= Int.unsigned o1 \/
    Int.unsigned o1 + sizeof ty1 <= o2.
Proof.
  intros. destruct H;[left |].
  +red; intros; subst. unfold Ple, Plt in *. omega.
  +destruct H as [bot [? ?]]. apply H1 in H.
   destruct H2 as [? [? ?]]. destruct bot as [? [? ?]]. simpl in *.
   subst. destruct H; auto. right. omega.
Qed.

Lemma assign_loc_mem_mapping:
  forall ty m b o v m' bs bl,
  assign_loc ty m b o v m' ->
  Ple bs b \/ block_ofs_ty_incl_in bl (b,(o,ty)) ->
  mem_mapping m m' bs bl.
Proof.
  intros. red; intros. destruct H1.
  eapply assign_loc_loadbytes_other; eauto.
  eapply block_ofs_ty_disjoints_incl_in_trans_or_uneq; eauto.
Qed.

Lemma storebytes_mem_mapping:
  forall m l ofs bytes m' ty bs bl,
  Mem.storebytes m l (Int.unsigned ofs) bytes = Some m' ->
  sizeof ty = Z_of_nat (length bytes) ->
  Ple bs l \/ block_ofs_ty_incl_in bl (l,(ofs,ty)) ->
  mem_mapping m m' bs bl.
Proof.
  intros. red; intros. destruct H2.
  destruct (zle n 0).
  +repeat rewrite Mem.loadbytes_empty; auto.
  +eapply Mem.loadbytes_storebytes_other; eauto.
   omega. rewrite <-H0.
   eapply block_ofs_ty_disjoints_incl_in_trans_or_uneq; eauto.
Qed.

Lemma assign_loc_range_perm:
  forall ty m b ofs v m1,
  assign_loc ty m b ofs v m1 ->
  forall b lo hi p,
  Mem.range_perm m b lo hi Cur p ->
  Mem.range_perm m1 b lo hi Cur p.
Proof.
  unfold Mem.range_perm.
  induction 1; simpl in *; intros.
  apply H1 in H2.
  apply Mem.perm_store_1 with chunk m b (Int.unsigned ofs) v; auto.
  apply Mem.perm_storebytes_1 with m b (Int.unsigned ofs) bytes; auto.
Qed.

Lemma assign_loc_range_perm_inv:
  forall ty m b ofs v m1,
  assign_loc ty m b ofs v m1 ->
  forall b lo hi p,
  Plt b (Mem.nextblock m) ->
  Mem.range_perm m1 b lo hi Cur p ->
  Mem.range_perm m b lo hi Cur p.
Proof.
  unfold Mem.range_perm.
  induction 1; simpl in *; intros.
  apply H2 in H3.
  apply Mem.perm_store_2 with chunk b (Int.unsigned ofs) v m'; auto.
  apply Mem.perm_storebytes_2 with b (Int.unsigned ofs) bytes m'; auto.
Qed.

Lemma c_alloc_variables_exists:
  forall args m eC,
  exists eC1 m1, alloc_variables eC m args eC1 m1.
Proof.
  induction args; intros.
  exists eC; exists m. constructor.
  destruct a. remember (Mem.alloc m 0 (sizeof t)) as mt.
  destruct mt as [m1 b1].
  destruct IHargs with m1 (PTree.set i (b1, t) eC) as [eC1 [m2 A1]].
  exists eC1; exists m2. constructor 2 with m1 b1;auto.
Qed.

Lemma c_alloc_variables_range_perm:
  forall eC m args eC' m',
  alloc_variables eC m args eC' m' ->
  forall b o n p,
  Mem.range_perm m b o n Cur p ->
  Mem.range_perm m' b o n Cur p.
Proof.
  induction 1; intros; auto.
  apply IHalloc_variables.
  unfold Mem.range_perm in *; intros.
  apply H1 in H2.
  apply Mem.perm_alloc_1 with m 0 (sizeof ty) b1; auto.
Qed.

Lemma c_alloc_variables_range_perm_inv:
  forall eC m args eC' m',
  alloc_variables eC m args eC' m' ->
  forall b o n p,
  Mem.range_perm m' b o n Cur p ->
  Plt b (Mem.nextblock m) ->
  Mem.range_perm m b o n Cur p.
Proof.
  induction 1; intros; auto.
  generalize H H; intros.
  apply Mem.nextblock_alloc in H3.
  apply Mem.alloc_result in H4.
  apply IHalloc_variables in H1; auto.
  unfold Mem.range_perm in *; intros.
  apply H1 in H5. eapply Mem.perm_alloc_inv in H5; eauto.
  rewrite peq_false in H5; auto.
  subst. red; intros; subst.
  unfold Ple, Plt in *. omega.
  rewrite H3. apply Plt_trans with (Mem.nextblock m); auto.
  apply Plt_succ.
Qed.

Lemma c_alloc_variables_loadbytes_eq:
  forall argsc eC eC1 m m1,
  alloc_variables eC m argsc eC1 m1 ->
  forall i ofs n,
  Plt i (Mem.nextblock m) ->
  Mem.loadbytes m1 i ofs n = Mem.loadbytes m i ofs n.
Proof.
  induction 1; intros; auto.
  rewrite IHalloc_variables.
  apply loadbytes_alloc_unchanged with 0%Z (sizeof ty) b1; auto.
  apply Mem.nextblock_alloc in H.
  rewrite H. apply Plt_trans with (Mem.nextblock m); auto.
  apply Plt_succ.
Qed.

Lemma c_alloc_variables_loadbytes:
  forall argsc eC eC1 m m1,
  alloc_variables eC m argsc eC1 m1 ->
  forall i ofs n mv,
  Mem.loadbytes m i ofs n = Some mv ->
  Mem.loadbytes m1 i ofs n = Some mv.
Proof.
  induction 1; intros; auto.
  eapply IHalloc_variables; eauto.
  eapply loadbytes_alloc_other; eauto.
Qed.

Lemma alloc_variables_val_match:
  forall m ty v vc eC al eC1 m1,
  val_match m ty v vc ->
  alloc_variables eC m al eC1 m1 ->
  val_match m1 ty v vc.
Proof.
  induction 1; intros; try constructor; auto.
  erewrite c_alloc_variables_loadbytes; eauto.
Qed.

Lemma c_alloc_variables_nextblock_le:
  forall eC m args eC1 m1,
  alloc_variables eC m args eC1 m1 ->
  Ple (Mem.nextblock m) (Mem.nextblock m1).
Proof.
  induction 1; intros.
  unfold Ple. omega.
  apply Mem.nextblock_alloc in H.
  rewrite H in *.
  apply Ple_trans with (Pos.succ (Mem.nextblock m)); auto.
  apply Plt_Ple. apply Plt_succ.
Qed.

Lemma alloc_variables_mem_mapping:
  forall m al eC m1 be l,
  alloc_variables empty_env m al eC m1 ->
  Ple be (Mem.nextblock m) ->
  mem_mapping m m1 be l.
Proof.
  intros. red; intros.
  eapply c_alloc_variables_loadbytes_eq; eauto.
  unfold Plt, Ple in *. omega.
Qed.

Lemma bind_parameter_temps_exists:
  forall args vargs leC,
  length args = length vargs ->
  exists leC', bind_parameter_temps args vargs leC = Some leC'.
Proof.
  induction args, vargs; simpl; intros; try congruence.
  +exists leC. auto.
  +destruct a. auto.
Qed.

Lemma bind_parameter_temps_length:
  forall al vl leC leC',
  bind_parameter_temps al vl leC = Some leC' ->
  length al = length vl.
Proof.
  induction al, vl; simpl; intros; try congruence.
  destruct a; congruence.
  destruct a. f_equal. eapply IHal; eauto.
Qed.

Lemma bind_parameter_temps_notin_eq:
  forall al vl leC leC' id,
  bind_parameter_temps al vl leC = Some leC' ->
  ~ In id (map fst al) ->
  leC' ! id = leC ! id.
Proof.
  induction al,vl; simpl; intros; try congruence.
  +destruct a. congruence.
  +destruct a. apply IHal with (id:=id) in H; auto.
   rewrite H. rewrite PTree.gso; auto.
Qed.

Lemma bind_parameter_temps_app_inv:
  forall l1 l2 vl leC leC',
  bind_parameter_temps (l1++l2) vl leC = Some leC' ->
  exists vl1 vl2 leC1, bind_parameter_temps l1 vl1 leC = Some leC1
    /\ bind_parameter_temps l2 vl2 leC1 = Some leC'
    /\ vl = vl1 ++ vl2.
Proof.
  induction l1; simpl; intros.
  +exists nil, vl, leC. split; auto.
  +destruct a. destruct vl; try congruence.
   apply IHl1 in H. destruct H as [vl1 [vl2 [leC1 [? [? ?]]]]].
   subst. exists (v::vl1), vl2, leC1.
   split; auto.
Qed.

Lemma bind_parameter_temps_getvars_match:
  forall l vl leC leC',
  bind_parameter_temps (map trans_ret l) vl leC = Some leC' ->
  list_norepet (map fst l) ->
  tempenv_getvars leC' (map trans_ret l) vl.
Proof.
  induction l, vl; simpl; intros; try congruence.
  +constructor.
  +inv H0. constructor 2; auto.
   -red. apply bind_parameter_temps_notin_eq with (id:=fst a) in H; auto.
    rewrite PTree.gss in H. auto.
    rewrite map_map. rewrite map_ext with (g:=fst); auto.
   -eapply IHl; eauto.
Qed.

Combined Scheme exec_stmt_funcall_ind2 from
   exec_stmt_ind2, eval_funcall_ind2.

Lemma exec_stmt_funcall_m_nextblock_zle:
  forall geC,
  (
     forall eC leC teC m s t m1 c,
     exec_stmt geC eC leC teC m s t m1 c ->
     Ple (Mem.nextblock m) (Mem.nextblock m1)
  )/\
  (
     forall m mainC args rets t m' c,
     eval_funcall geC m mainC args rets t m' c ->
     Ple (Mem.nextblock m) (Mem.nextblock m')
  ).
Proof.
  intros geC.
  apply exec_stmt_funcall_ind2; intros;
  unfold Plt, Ple in *; try (omega); auto.
  +apply assign_loc_nextblock_eq in H2.
    rewrite H2; omega.
  +inv H2. apply Mem.nextblock_storebytes in H18.
   rewrite H18. omega.
  +apply c_alloc_variables_nextblock_le in H1.
    apply free_list_nextblock_eq in H7.
    rewrite H7. unfold Ple in *. omega.
Qed.

Definition env_perm_m (e: env)(m: mem) : Prop :=
  forall id b ty p,
  e ! id = Some (b, ty) ->
  Mem.range_perm m b 0 (sizeof ty) Cur p.

Definition env_elements_perm_m (e: env)(m: mem) : Prop :=
  forall id b ty p,
  In (id, (b, ty)) (PTree.elements e) ->
  Mem.range_perm m b 0 (sizeof ty) Cur p.

Definition env_lt_m (e: env)(m: mem) : Prop :=
  forall id b ty,
  e ! id = Some (b, ty) ->
  Plt b (Mem.nextblock m).

Definition le_env (e: env)(be: block) : Prop :=
  forall id b ty,
  e ! id = Some (b, ty) ->
  Ple be b.

Definition le_env_elements (e: env)(be: block) : Prop :=
  forall id b ty,
  In (id, (b, ty)) (PTree.elements e) ->
  Ple be b.

Definition env_mem_prop(e: env)(m: mem)(be: block): Prop :=
  env_lt_m e m
  /\ env_perm_m e m
  /\ Ple be (Mem.nextblock m).

Definition env_diff_id_diff_b (e: env):  Prop :=
  forall b1 b2 id1 id2 ty1 ty2,
  e ! id1 = Some (b1, ty1) ->
  e ! id2 = Some (b2, ty2) ->
  id1 <> id2  ->
  b1 <> b2.

Lemma env_lt_m_empty_env:
  forall m , env_lt_m empty_env m.
Proof.
  unfold env_lt_m, empty_env. intros.
  rewrite PTree.gempty in H. congruence.
Qed.

Lemma le_env_empty_env:
  forall m,
  le_env empty_env (Mem.nextblock m).
Proof.
  unfold le_env, empty_env. intros.
  rewrite PTree.gempty in H. congruence.
Qed.

Lemma env_perm_m_empty_env:
  forall m, env_perm_m empty_env m.
Proof.
  unfold env_perm_m; intros.
  rewrite PTree.gempty in H. congruence.
Qed.

Lemma le_env_infer:
  forall e b,
  le_env e b <-> le_env_elements e b.
Proof.
  unfold le_env_elements, le_env.
  split; intros; apply H with id ty.
  apply PTree.elements_complete; auto.
  apply PTree.elements_correct; auto.
Qed.

Lemma env_perm_m_infer:
  forall e m,
  env_perm_m e m <-> env_elements_perm_m e m.
Proof.
  unfold env_elements_perm_m, env_perm_m.
  split; intros; apply H with id.
  apply PTree.elements_complete; auto.
  apply PTree.elements_correct; auto.
Qed.

Lemma storebytes_env_mem_prop:
  forall eC m be l ofs bytes m',
  env_mem_prop eC m be ->
  Mem.storebytes m l ofs bytes = Some m' ->
  env_mem_prop eC m' be.
Proof.
  unfold env_mem_prop. intros.
  cut (Ple (Mem.nextblock m) (Mem.nextblock m')); intros.
  intuition.
  +red; intros. apply H2 in H3.
   unfold Plt,Ple in *. omega.
  +red; intros. red in H. apply H with (p:=p) in H3.
   red; intros. eauto with mem.
  +eapply Mem.nextblock_storebytes in H0; eauto.
   unfold Plt,Ple in *. omega.
  +eapply Mem.nextblock_storebytes in H0; eauto.
   rewrite H0. unfold Plt,Ple in *. omega.
Qed.

Lemma le_env_lt_notin:
  forall eC be l,
  le_env eC be ->
  Plt l be ->
  ~ In l (map (fun x : block * Z * Z => fst (fst x)) (blocks_of_env eC)).
Proof.
  intros. apply le_env_infer in H.
  red in H. unfold blocks_of_env. rewrite map_map.
  red; intros.
  cut (Ple be l). intros. unfold Plt,Ple in *. omega.
  apply in_map_iff in H1. destruct H1 as [x [? ?]].
  destruct x. destruct p. simpl in *.
  subst. eapply H; eauto.
Qed.

Lemma ptree_set_env_diff_id_diff_b :
  forall e m b1 ty id,
  env_lt_m e m ->
  b1 = (Mem.nextblock m) ->
  env_diff_id_diff_b e ->
  env_diff_id_diff_b (PTree.set id (b1, ty) e).
Proof.
  unfold env_diff_id_diff_b, env_lt_m. intros.
  compare id id1; intros A.
  +subst. rewrite PTree.gss in H2. inv H2.
   rewrite PTree.gso in H3; auto.
   red; intros. subst. apply H in H3.
   unfold Plt,Ple in *. omega.
  +rewrite PTree.gso in H2; auto.
   compare id id2; intros A1.
   -subst. rewrite PTree.gss in H3. inv H3.
    red; intros. subst. apply H in H2.
    unfold Plt,Ple in *. omega.
   -rewrite PTree.gso in H3; auto.
    eapply H1; eauto.
Qed.

Lemma c_alloc_variables_diff_id_diff_b:
  forall args m eC eC1 m1,
  alloc_variables eC m args eC1 m1 ->
  env_lt_m eC m ->
  env_diff_id_diff_b eC ->
  env_lt_m eC1 m1 /\ env_diff_id_diff_b eC1.
Proof.
  induction 1; intros; auto.
  apply IHalloc_variables.

  unfold env_lt_m in *. intros.
  rewrite Mem.nextblock_alloc with m 0 (sizeof ty) _ b1; auto.
  compare id id0; intros; subst.
  rewrite PTree.gss in H3. inv H3; auto.
  rewrite Mem.alloc_result with m 0 (sizeof ty0) m1 _; auto.
  apply Plt_succ.
  rewrite PTree.gso in H3; auto.
  apply H1 in H3. apply Plt_trans with (Mem.nextblock m); auto.
  apply Plt_succ.

  apply ptree_set_env_diff_id_diff_b with m; auto.
  apply Mem.alloc_result with 0 (sizeof ty) m1; auto.
Qed.

Lemma c_alloc_variables_perm_true:
  forall args m m1 eC eC1,
  env_perm_m eC m ->
  alloc_variables eC m args eC1 m1 ->
  env_lt_m eC m ->
  env_perm_m eC1 m1.
Proof.
  induction args; simpl; intros.
  inv H0; auto.

  inv H0. apply IHargs in H9; auto.
  unfold env_perm_m in *. intros.
  compare id id0; intros; subst.
    rewrite PTree.gss in H0;auto.
    inv H0. unfold Mem.range_perm. apply alloc_range_perm with m; auto.

    rewrite PTree.gso in H0; auto.
    generalize H0; intros.
    apply H with _ _ _ p in H0.
    unfold Mem.range_perm in *. intros. apply H0 in H3.
    apply Mem.perm_alloc_1 with m 0 (sizeof ty) b1; auto.

    unfold env_lt_m in *. intros.
    generalize H6; intros.
    apply Mem.alloc_result in H6.
    apply Mem.nextblock_alloc in H2. rewrite H2.
    compare id id0; intros; subst.
      rewrite PTree.gss in H0;auto. inv H0. apply Plt_succ.
      rewrite PTree.gso in H0;auto. apply H1 in H0.
       apply Plt_trans with (Mem.nextblock m); auto.
       apply Plt_succ.
Qed.

Lemma c_alloc_variables_le_env:
  forall eC m args eC1 m1,
  alloc_variables eC m args eC1 m1 ->
  forall be,
  Ple be (Mem.nextblock m) ->
  le_env eC be ->
  le_env eC1 be.
Proof.
  induction 1; intros; auto.

  unfold le_env in *. intros.
  assert (A: Ple be (Mem.nextblock m1)).
    apply Mem.nextblock_alloc in H. rewrite H.
    apply Ple_trans with (Mem.nextblock m); auto.
    apply Plt_Ple. apply Plt_succ.
  apply IHalloc_variables with _ id0 b ty0 in A; auto.
  intros. compare id id1; intros; subst.
    rewrite PTree.gss in H4. inv H4.
    apply Mem.alloc_result in H. subst. auto.

    rewrite PTree.gso in H4; auto. apply H2 with id1 ty1; auto.
Qed.

Lemma c_alloc_variables_empty:
  forall args m,
  exists eC m1, alloc_variables empty_env m args eC m1
    /\ env_lt_m eC m1
    /\ env_diff_id_diff_b eC
    /\ le_env eC (Mem.nextblock m)
    /\ env_mem_prop eC m1 (Mem.nextblock m1).
Proof.
  intros.
  destruct c_alloc_variables_exists with args m empty_env
    as [eC [m1 ?]].
  exists eC, m1. unfold env_mem_prop.
  generalize H H H; intros.
  apply c_alloc_variables_diff_id_diff_b in H.
  apply c_alloc_variables_le_env with (be:=Mem.nextblock m) in H0.
  apply c_alloc_variables_perm_true in H1; auto.
  intuition.
  apply env_perm_m_empty_env; auto.
  apply env_lt_m_empty_env; auto.
  unfold Ple. omega.
  apply le_env_empty_env.
  apply env_lt_m_empty_env; auto.
  red; intros. rewrite PTree.gempty in *. congruence.
Qed.

Lemma c_free_list_exists:
  forall eC,
  env_diff_id_diff_b eC ->
  forall m, env_elements_perm_m eC m ->
  exists m', Mem.free_list m (blocks_of_env eC) = Some m'.
Proof.
  unfold env_diff_id_diff_b, env_elements_perm_m.
  unfold blocks_of_env.
  intros until 1. generalize (PTree.elements_keys_norepet eC).
  remember (PTree.elements eC).
  cut (forall b1 b2 id1 id2 ty1 ty2,
       In (id1, (b1, ty1)) l ->
       In (id2, (b2, ty2)) l ->
       id1 <> id2 ->
       b1 <> b2).
  clear.

  +induction l; simpl; intros.
   -exists m; auto.
   -inv H0. destruct a as [id [b ty]]. simpl in *.
    destruct Mem.range_perm_free with m b 0 (sizeof ty) as [m1 A]; eauto.
    destruct IHl with m1 as [m' A1]; auto.
    *intros. eapply H; eauto.
    *intros.
     assert (A1: Mem.range_perm m b0 0 (sizeof ty0) Cur p).
      apply H1 with id0; auto.
     unfold Mem.range_perm in *. intros.
     apply A1 in H2.
     apply Mem.perm_free_1 with m b 0 (sizeof ty); eauto.
     left. eapply H; eauto.
     apply in_map with (f:=fst) in H0. red; intros; subst. auto.
    *exists m'. rewrite A; auto.
  +intros. subst.
   apply H with id1 id2 ty1 ty2; auto;
   apply PTree.elements_complete; auto.
Qed.

Lemma free_list_mem_mapping:
  forall m m2 eC m3 be l,
  Mem.free_list m2 (blocks_of_env eC) = Some m3 ->
  Ple be (Mem.nextblock m2) ->
  le_env eC be ->
  mem_mapping m m2 be l ->
  mem_mapping m m3 be l.
Proof.
  intros. red; intros.
  rewrite <-H2; auto.
  eapply free_list_loadbytes_eq; eauto.
  apply le_env_infer in H1. red; intros.
  unfold blocks_of_env in H4. rewrite map_map in *.
  apply in_map_iff in H4. destruct H4 as [x [? ?]].
  destruct x. destruct p. simpl in *. subst.
  apply H1 in H5. unfold Ple, Plt in *. omega.
Qed.

Definition range_perm_keep(m m': mem) :=
  forall b lo hi p,
  Mem.range_perm m b lo hi Cur p ->
  lo < hi ->
  Mem.range_perm m' b lo hi Cur p.

Lemma cstorebytes_range_perm_keep:
  forall m l o mv m1,
  Mem.storebytes m l o mv = Some m1 ->
  range_perm_keep m m1.
Proof.
  intros. red; intros. red; intros.
  apply H0 in H2. eapply Mem.perm_storebytes_1; eauto.
Qed.

Lemma eval_stmt_funcall_mem_range_perm:
  forall geC,
  (
     forall eC leC teC m stmts t m' c,
     exec_stmt geC eC leC teC m stmts t m' c ->
     range_perm_keep m m'
  )/\
  (
     forall m mainC args rets t m' c,
     eval_funcall geC m mainC args rets t m' c ->
     range_perm_keep m m'
  ).
Proof.
  intros geC.
  apply exec_stmt_funcall_ind2; intros; red; intros; auto.
  +eapply assign_loc_range_perm; eauto.
  +inv H2. red; intros. eapply Mem.perm_storebytes_1; eauto.
  +eapply free_list_range_perm; eauto.
   -apply le_env_lt_notin with (Mem.nextblock m); eauto.
    *eapply c_alloc_variables_le_env; eauto.
     apply Ple_refl.
     apply le_env_empty_env.
    *eapply range_perm_valid_block2; eauto.
     eauto with mem.
   -apply H5; auto.
    eapply c_alloc_variables_range_perm; eauto.
Qed.


Definition range_perm_keep_inv(m' m: mem) :=
  forall b lo hi p,
  Mem.range_perm m' b lo hi Cur p ->
  lo < hi ->
  Plt b (Mem.nextblock m) ->
  Mem.range_perm m b lo hi Cur p.

Lemma eval_stmt_funcall_mem_range_perm_inv:
  forall geC,
  (
     forall eC leC teC m stmts t m' c,
     exec_stmt geC eC leC teC m stmts t m' c ->
     range_perm_keep_inv m' m
  )/\
  (
     forall m mainC args rets t m' c,
     eval_funcall geC m mainC args rets t m' c ->
     range_perm_keep_inv m' m
  ).
Proof.
  intros geC.
  apply exec_stmt_funcall_ind2; intros; red; intros; auto.
  +eapply assign_loc_range_perm_inv; eauto.
  +inv H2. red; intros. eapply Mem.perm_storebytes_2; eauto.
  +apply H0; auto. apply H2; auto.
   apply exec_stmt_funcall_m_nextblock_zle in H.
   unfold Plt,Ple in *. omega.
  +apply H1; auto. apply H3; auto.
   apply exec_stmt_funcall_m_nextblock_zle in H0.
   unfold Plt,Ple in *. omega.
  +apply exec_stmt_funcall_m_nextblock_zle in H3.
   apply exec_stmt_funcall_m_nextblock_zle in H1.
   apply H2; auto. unfold Plt,Ple in *.
   apply H4; auto. apply H6; auto.
   unfold Plt. omega. unfold Plt. omega.
  +eapply c_alloc_variables_range_perm_inv; eauto.
   apply H5; auto. eapply free_list_range_perm_inv; eauto.
   apply c_alloc_variables_nextblock_le in H1.
   unfold Plt,Ple in *. omega.
Qed.

Lemma loadbytes_eq_app:
  forall m1 m2 b ofs n1 n2,
  Mem.loadbytes m2 b ofs (n1 + n2) = Mem.loadbytes m1 b ofs (n1 + n2) ->
  0 <= n1 -> 0 <= n2 -> 0 < n1 + n2 ->
  Mem.range_perm m1 b ofs (ofs + (n1 + n2)) Cur Readable ->
  range_perm_keep m1 m2 ->
  Mem.loadbytes m2 b ofs n1 = Mem.loadbytes m1 b ofs n1
    /\ Mem.loadbytes m2 b (ofs+n1) n2 = Mem.loadbytes m1 b (ofs+n1) n2.
Proof.
  intros.
  destruct Mem.range_perm_loadbytes with m1 b ofs (n1+n2) as [mv ?]; auto.
  destruct Mem.range_perm_loadbytes with m2 b ofs (n1+n2) as [mv1 ?]; auto.
  apply H4; auto. omega. rewrite H5, H6 in H. inv H.
  apply Mem.loadbytes_split in H5; try omega. destruct H5 as [? [? [? [? ?]]]].
  apply Mem.loadbytes_split in H6; try omega. destruct H6 as [? [? [? [? ?]]]].
  subst. apply app_length_equal_inv in H9. destruct H9. subst.
  rewrite H, H8,H5,H6. split; auto.
  left. repeat erewrite Mem.loadbytes_length; eauto.
Qed.

Lemma cloadbytes_incl_eq:
  forall m1 b o1 n1 m2 o2 n2,
  Mem.loadbytes m2 b o1 n1 = Mem.loadbytes m1 b o1 n1 ->
  o1 <= o2 /\ o2 + n2 <= o1 + n1 ->
  Mem.range_perm m1 b o1 (o1 + n1) Cur Readable ->
  range_perm_keep m1 m2 ->
  Mem.loadbytes m2 b o2 n2 = Mem.loadbytes m1 b o2 n2.
Proof.
  intros.
  destruct (zle n2 0).
  +repeat rewrite Mem.loadbytes_empty; auto.
  +replace n1 with ((o2-o1)+(n1-(o2-o1))) in H; try omega.
   apply loadbytes_eq_app in H; try omega; auto. destruct H.
   replace (o1 + (o2 - o1)) with o2 in H3; try omega.
   replace (n1 - (o2 - o1)) with (n2+(n1 - (o2 - o1)-n2)) in H3; try omega.
   apply loadbytes_eq_app in H3; try omega; auto. destruct H3; auto.
   red; intros. apply H1; omega.
   red; intros. apply H1; omega.
Qed.

Lemma storebytes_mem_mapping_cons_inv:
  forall m m' b o ty bl m1,
  mem_mapping m m' (Mem.nextblock m) ((b, (o, ty)) :: bl) ->
  block_ofs_ty_disjoints bl (b, (o, ty)) ->
  mem_mapping m m1 (Mem.nextblock m) ((b, (o, ty)) :: nil) ->
  Mem.loadbytes m' b (Int.unsigned o) (sizeof ty) = Mem.loadbytes m1 b (Int.unsigned o) (sizeof ty) ->
  range_perm_keep m1 m' ->
  Mem.range_perm m1 b (Int.unsigned o) (Int.unsigned o + sizeof ty) Cur Readable ->
  mem_mapping m1 m' (Mem.nextblock m) bl.
Proof.
  intros. red; intros. destruct H5.
  generalize (sizeof_pos ty); intros.
  assert(A: (b0 <> b \/ o0 + n <= Int.unsigned o \/ Int.unsigned o + sizeof ty <= o0)
            \/ (b0 = b /\ Int.unsigned o < o0 + n /\ o0 < Int.unsigned o + sizeof ty)).
    destruct (peq b0 b), (zle (o0+n) (Int.unsigned o)), (zle ( Int.unsigned o + sizeof ty) o0); auto.
    subst. right. split; auto. omega.
  destruct A as [A | A].
  +rewrite H; auto.
   -rewrite H1; auto. split; auto. red; simpl; intros ? A1.
    destruct A1; subst; try tauto. simpl. destruct A; [left | right]; auto. omega.
   -split; auto. red; simpl; intros. destruct H8; subst; auto.
    simpl. destruct A; [left | right]; auto. omega.
  +destruct A as [? [A A1]]. subst.
   assert(A4: (Int.unsigned o <= o0 /\ o0 + n <= Int.unsigned o + sizeof ty)
               \/ (o0 < Int.unsigned o) \/ Int.unsigned o + sizeof ty < o0 + n).
     omega.
   destruct A4 as [A4 | A4].
   assert(A5: n <= 0 \/ 0 < n). omega.
   destruct A5 as [A5 | A5]. repeat rewrite Mem.loadbytes_empty; auto.
   eapply cloadbytes_incl_eq; eauto; try omega.
   assert(A6: (o0 <= Int.unsigned o /\ Int.unsigned o + sizeof ty <= o0 + n)
               \/ (Int.unsigned o < o0) \/ o0 + n < Int.unsigned o + sizeof ty).
     omega.
   destruct A6 as [A6 | A6]; [| destruct A4 as [A4 | A4]; destruct A6 as [A6 | A6]; try omega].
   -assert(B: n = (Int.unsigned o - o0) + (o0 + n - Int.unsigned o)).
      omega.
    rewrite B. apply loadbytes_eq_app_inv; try omega.
    *rewrite H, H1; auto; try omega; split; auto; red; simpl; intros ? B1.
     destruct B1 as [B1 | B1]; try tauto. rewrite <-B1 in *.
     simpl in *. right. omega.
     destruct B1 as [B1 | B1]. rewrite <-B1 in *. simpl in *. right. omega.
     apply H6 in B1. destruct B1; auto. right. omega.
    *replace (o0 + (Int.unsigned o - o0)) with (Int.unsigned o); try omega.
     replace (o0 + n - Int.unsigned o) with (sizeof ty +  (o0 + n - (Int.unsigned o+sizeof ty))); try omega.
     apply loadbytes_eq_app_inv; try omega; auto.
     rewrite H, H1; auto; try omega; split; auto; red; simpl; intros ? B1.
     destruct B1 as [B1 | B1]; try tauto. rewrite <-B1 in *.
     simpl in *. right. omega.
     destruct B1 as [B1 | B1]. rewrite <-B1 in *. simpl in *. right. omega.
     apply H6 in B1. destruct B1; auto. right. omega.
   -assert(B: n = (Int.unsigned o - o0) + (o0 + n - Int.unsigned o)).
      omega.
    rewrite B. apply loadbytes_eq_app_inv; try omega.
    *rewrite H, H1; auto; try omega; split; auto; red; simpl; intros ? B1.
     destruct B1 as [B1 | B1]; try tauto. rewrite <-B1 in *.
     simpl in *. right. omega.
     destruct B1 as [B1 | B1]. rewrite <-B1 in *. simpl in *. right. omega.
     apply H6 in B1. destruct B1; auto. right. omega.
    *replace (o0 + (Int.unsigned o - o0)) with (Int.unsigned o); try omega.
     eapply cloadbytes_incl_eq; eauto; try omega.
   -assert(B: n = (Int.unsigned o + sizeof ty - o0) + (n - (Int.unsigned o + sizeof ty - o0))).
      omega.
    rewrite B. apply loadbytes_eq_app_inv; try omega.
    *eapply cloadbytes_incl_eq; eauto; try omega.
    *rewrite H, H1; auto; try omega; split; auto; red; simpl; intros ? B1.
     destruct B1 as [B1 | B1]; try tauto. rewrite <-B1 in *.
     simpl in *. right. omega.
     destruct B1 as [B1 | B1]. rewrite <-B1 in *. simpl in *. right. omega.
     apply H6 in B1. destruct B1; auto. right. omega.
Qed.

Lemma assign_loc_env_mem_prop:
  forall eC m be ty l ofs v m',
  env_mem_prop eC m be ->
  assign_loc ty m l ofs v m' ->
  env_mem_prop eC m' be.
Proof.
  unfold env_mem_prop. intros.
  cut (Ple (Mem.nextblock m) (Mem.nextblock m')); intros.
  intuition.
  +red; intros. apply H2 in H3.
   unfold Ple, Plt in *. omega.
  +red; intros. eapply assign_loc_range_perm; eauto.
  +eapply assign_loc_nextblock_eq in H0; eauto.
   unfold Ple, Plt in *. omega.
  +eapply assign_loc_nextblock_eq in H0; eauto.
   unfold Ple, Plt in *. rewrite H0. omega.
Qed.

Lemma eval_funcall_env_mem_prop:
  forall geC eC m be m' f  vargs rets,
  env_mem_prop eC m be ->
  eval_funcall geC m f vargs rets E0 m' Vundef ->
  env_mem_prop eC m' be.
Proof.
  unfold env_mem_prop. intros.
  cut (Ple (Mem.nextblock m) (Mem.nextblock m')); intros.
  intuition.
  +red; intros. apply H2 in H3.
   unfold Ple, Plt in *. omega.
  +red; intros. destruct (zlt 0 (sizeof ty)).
   eapply eval_stmt_funcall_mem_range_perm; eauto.
   red; intros. omega.
  +eapply exec_stmt_funcall_m_nextblock_zle in H0; eauto.
   unfold Ple, Plt in *. omega.
  +eapply exec_stmt_funcall_m_nextblock_zle in H0; eauto.
Qed.

Lemma is_arystr_deref_loc_vtpr_eq:
  forall t m loc ofs l o,
  is_arystr t = true ->
  deref_loc t m loc ofs (Vptr l o) ->
  l = loc /\ o = ofs.
Proof.
  intros.
  destruct t; inv H; inv H0; simpl in *; try congruence; auto.
Qed.

Lemma has_type_is_arystr_vptr:
  forall v t m vc,
  has_type v t ->
  is_arystr t = true ->
  val_match m t v vc ->
  exists l o, vc = Vptr l o.
Proof.
  unfold is_arystr, has_type.
  destruct v, t; simpl; intros; try inv H; simpl in *;
  try congruence; inv H1; eauto.
Qed.

Lemma load_mvl_is_arystr_vptr:
  forall t mv ofs v m vc,
  load_mvl t mv ofs v ->
  is_arystr t = true ->
  val_match m t v vc ->
  exists l o, vc = Vptr l o.
Proof.
  unfold is_arystr.
  destruct t; simpl; intros; inv H; simpl in *;
  try congruence; inv H1; eauto.
Qed.

Lemma eval_sem_cast_correct:
  forall v1 t1 t2 v vc1 m,
  Lop.sem_cast v1 t1 t2 = Some v ->
  val_match m t1 v1 vc1 ->
  sem_cast vc1 t1 t2 = Some (valof v).
Proof.
  unfold Lop.sem_cast, sem_cast.
  destruct t1, t2; simpl; intros; try congruence;
  try (destruct f; congruence; fail);
  try (destruct i; congruence; fail).
  +destruct i0, v1; inv H; inv H0; auto.
  +destruct f, v1; inv H; inv H0; auto.
  +destruct i, f; try congruence; destruct v1; try congruence; inv H0;
   try (destruct (cast_single_int _ _); inv H; auto);
   destruct (cast_float_int _ _); inv H; auto.
  +destruct f, f0,  v1; inv H; inv H0; auto.
  +destruct i0, v1; inv H; inv H0; auto.
  +destruct i0, v1; inv H; inv H0; auto.
  +destruct f0, v1; inv H; inv H0; auto.
Qed.

Lemma sem_cast_correct:
  forall v1 t ty v,
  Lop.sem_cast v1 t ty = Some v ->
  sem_cast (valof v1) t ty = Some (valof v).
Proof.
  intros.
  apply eval_sem_cast_correct with v1 Mem.empty; auto.
  destruct v1; try econstructor; eauto.
  unfold Lop.sem_cast in *.
  destruct (Lop.classify_cast _ _); try congruence.
Qed.

Lemma sem_add_ptr_eq:
  forall l ofs aid ty z i i0 s,
  sem_add (Vptr l ofs) (Tarray aid ty z) (Vint i) (Tint i0 s) = Some (Vptr l (Int.add ofs (array_ofs i ty))).
Proof.
  unfold array_ofs,sem_add. simpl. intros.
  unfold classify_add. simpl.
  destruct i0, s; try rewrite <-sizeof_eq; auto.
Qed.

Lemma eval_bool_val_match:
  forall v t b m vc,
  Lop.bool_val v t = Some b ->
  val_match m t v vc ->
  bool_val vc t = Some b.
Proof.
  destruct v, t; intros; inv H; inv H0;simpl; auto.
  destruct i0, s; auto.
Qed.

Lemma has_type_bool_val:
  forall t,
  has_type Lvalues.Vfalse t ->
  Lop.bool_val Lvalues.Vfalse t = Some false.
Proof.
  destruct t; intros; inv H; simpl;auto.
Qed.

Lemma is_arystr_true_access_mode:
  forall t, is_arystr t = true ->
  Ltypes.access_mode t = By_copy \/ Ltypes.access_mode t = By_reference.
Proof.
  unfold is_arystr in *. destruct t; simpl in *; auto; congruence.
Qed.

Lemma eval_expr_determ:
forall geC eC leC teC m,
(
  forall a v1,
  eval_expr geC eC leC teC m a v1 ->
  forall v2,
  eval_expr geC eC leC teC m a v2 ->
  v1 = v2
)
/\
(
  forall a l1 o1,
  eval_lvalue geC eC leC teC m a l1 o1 ->
  forall l2 o2,
  eval_lvalue geC eC leC teC m a l2 o2 ->
  l1 = l2 /\ o1 = o2
).
Proof.
  intros until m. apply eval_expr_lvalue_ind; intros.
  +inv H; auto. inv H0.
  +inv H; auto. inv H0.
  +inv H; auto. inv H0.
  +inv H0; auto. congruence. inv H1.
  +inv H0; auto. congruence. inv H1.
  +inv H1; auto. apply H0 in H5; auto.
   destruct H5; congruence. inv H2.
  +inv H2. apply H0 in H7. subst. congruence. inv H3.
  +inv H4. apply H0 in H10. apply H2 in H11.
   congruence. inv H5.
  +inv H2. apply H0 in H5. congruence. inv H3.
  +inv H; auto. inv H0.
  +inv H; auto. inv H0.
  +inv H2; try (inv H; fail). apply H0 in H3; auto.
   destruct H3. subst.
   apply deref_loc_determ with (v1:=v) in H4; auto.
  +inv H0. split;congruence. congruence.
  +inv H1; split; congruence.
  +inv H1. apply H0 in H6. split; congruence.
  +inv H3. apply H0 in H7. split; congruence.
Qed.

Lemma trans_unop_correct:
  forall geC eC leC teC m a1 v v1 vc1 u ty t,
  eval_expr geC eC leC teC m a1 vc1 ->
  val_match m (typeof a1) v1 vc1 ->
  Lop.sem_unary_operation u v1 ty = Some v ->
  ty = typeof a1 ->
  exists vc, eval_expr geC eC leC teC m (Eunop u a1 t) vc
               /\ val_match m t v vc.
Proof.
  clear. intros.
  destruct u,ty, v1; simpl in *; inv H1; auto; inv H0.
  +destruct i; try congruence. inv H4.
   exists (Val.of_bool (Int.eq i0 Int.zero)).
   unfold Val.of_bool, of_bool. split.
   apply eval_Eunop with (Vint i0); auto.
   rewrite <-H2. simpl. unfold sem_notbool, classify_bool, typeconv; auto.
   destruct (Int.eq i0 Int.zero); constructor.
  +exists (Vint (Int.neg i0)). split.
   apply eval_Eunop with (Vint i0); auto.
   rewrite <-H2. simpl. unfold sem_neg. simpl.
     destruct i; auto. destruct s; auto. constructor.
  +destruct f; inv H4.
   exists (Vfloat (Floats.Float.neg f0)). split.
   apply eval_Eunop with (Vfloat f0); auto. simpl.
   unfold sem_neg. rewrite <- H2. simpl. auto.
   constructor.
  +destruct f; inv H4.
   exists (Vsingle (Floats.Float32.neg f0)). split.
   apply eval_Eunop with (Vsingle f0); auto. simpl.
   unfold sem_neg. rewrite <- H2. simpl. auto.
   constructor.
Qed.

Lemma of_bool_eq:
  forall b, valof (of_bool b) = Val.of_bool b.
Proof.
  destruct b; auto.
Qed.

Lemma sem_binary_operation_correct:
  forall m b v1 v2 t t1 t2 vc1 vc2 ty v,
  val_match m t1 v1 vc1 ->
  val_match m t2 v2 vc2 ->
  Lop.sem_binary_operation b v1 v2 t ty = Some v ->
  classify_binop t b = binop_case_normal ->
  sem_binary_operation (trans_binary_operator b) vc1 t vc2 t m = Some (valof v).
Proof.
  intros.
  destruct b; simpl in *.
  +inv H; inv H0; destruct t; inv H1.
   destruct i1, s; auto.
   destruct f1; inv H0; auto.
   destruct f1; inv H0; auto.
  +inv H; inv H0; destruct t; inv H1.
   destruct i1, s; auto.
   destruct f1; inv H0; auto.
   destruct f1; inv H0; auto.
  +inv H; inv H0; destruct t; inv H1.
   destruct i1, s; auto.
   destruct f1; inv H0; auto.
   destruct f1; inv H0; auto.
  +destruct t; try congruence.
   inv H; inv H0; destruct f; inv H1; auto.
  +destruct t; try congruence. destruct i, s; try congruence.
   unfold sem_div_operation, sem_div, sem_binarith in *.
   inv H; inv H0; simpl in *; inv H1; auto.
   destruct (_ ||_); inv H0; simpl; auto.
  +inv H; inv H0; destruct t; simpl in *; try congruence.
   unfold sem_mod, sem_binarith. simpl.
   destruct i1, s; inv H1; simpl;
   try destruct (_ || _); inv H0; auto.
   destruct (Int.eq _ _); inv H1; auto.
  +inv H; inv H0; destruct t; inv H1. destruct i1,s; auto.
  +inv H; inv H0; destruct t; inv H1. destruct i1,s; auto.
  +inv H; inv H0; destruct t; inv H1. destruct i1,s; auto.
  +inv H; inv H0; destruct t; inv H1;
   [destruct i1,s | destruct f1; inv H0 | destruct f1; inv H0];
   rewrite of_bool_eq; auto.
  +inv H; inv H0; destruct t; inv H1;
   [destruct i1,s | destruct f1; inv H0 | destruct f1; inv H0];
   rewrite of_bool_eq; auto.
  +inv H; inv H0; destruct t; inv H1;
   [destruct i1,s | destruct f1; inv H0 | destruct f1; inv H0];
   rewrite of_bool_eq; auto.
  +inv H; inv H0; destruct t; inv H1;
   [destruct i1,s | destruct f1; inv H0 | destruct f1; inv H0];
   rewrite of_bool_eq; auto.
  +inv H; inv H0; destruct t; inv H1;
   [destruct i1,s | destruct f1; inv H0 | destruct f1; inv H0];
   rewrite of_bool_eq; auto.
  +inv H; inv H0; destruct t; inv H1;
   [destruct i1,s | destruct f1; inv H0 | destruct f1; inv H0];
   rewrite of_bool_eq; auto.
Qed.

Lemma trans_binop_correct:
  forall geC eC leC teC m a1 a2 v1 v2 v vc1 vc2 b ty t,
  eval_expr geC eC leC teC m a1 vc1->
  eval_expr geC eC leC teC m a2 vc2 ->
  val_match m t v1 vc1 ->
  val_match m t v2 vc2 ->
  Lop.sem_binary_operation b v1 v2 t ty = Some v ->
  typeof a2 = typeof a1 ->
  typeof a1 = t ->
  exists vc, eval_expr geC eC leC teC m (trans_binop_expr b a1 a2 ty) vc
    /\ val_match m ty v vc.
Proof.
  intros. exists (valof v). split.
  +unfold trans_binop_expr.
   destruct (classify_binop _ _) eqn:?.
   -apply eval_Ebinop with vc1 vc2; auto.
    rewrite H4,H5 in *.
    eapply sem_binary_operation_correct; eauto.
   -rewrite H5 in *.
    unfold Lop.sem_binary_operation,sem_div_operation in *.
    destruct b; simpl in *; try congruence; rewrite Heqc in *.
    destruct t; try congruence.
    destruct (Lop.sem_div _ _ _) eqn:?; try congruence.
    apply eval_Ecast with (valof v0); auto.
    econstructor; eauto. simpl.
    *rewrite H4,H5.
     destruct t; try congruence;
     destruct v1, v2; inv Heqo; inv H1; inv H2; unfold sem_div.
     destruct i,s; simpl in *; inv H3; auto;
      unfold sem_binarith; simpl;
      try (destruct (_ || _); inv H7; auto).
      destruct (Int.eq _ _); inv H7; auto.
     destruct f; simpl in *; inv H3; inv H7; auto.
     destruct f; simpl in *; inv H3; inv H7; auto.
    *simpl. eapply sem_cast_correct; eauto.
   -rewrite H5 in *.
    unfold Lop.sem_binary_operation,sem_div_operation in *.
    destruct b; simpl in *; try congruence; rewrite Heqc in *.
    *destruct (Lop.sem_cast v1 _ _) eqn:?; try congruence.
     destruct (Lop.sem_cast v2 _ _) eqn:?; try congruence.
     apply eval_Ebinop with (valof v0) (valof v3); auto.
     apply eval_Ecast with vc1; auto. rewrite H5.
     eapply sem_cast_correct in Heqo; eauto.
     unfold sem_cast. destruct v1, t; inv Heqo; inv H1; simpl; auto.
     destruct f; auto.
     apply eval_Ecast with vc2; auto. rewrite H4.
     eapply sem_cast_correct in Heqo0; eauto.
     unfold sem_cast. destruct v2, t; inv Heqo0; inv H2; simpl; auto.
     simpl. destruct v0,v3; inv H3; simpl; auto.
     destruct f; auto.
     simpl. destruct v0,v3; inv H3; simpl; auto.
    *destruct t; try congruence. destruct i,s; congruence.
  +destruct v; simpl; try constructor.
   apply sem_binary_operation_not_mvl in H3. tauto.
Qed.

Definition eval_exprs(ge: genv)(e: env)(le te: temp_env)(m: mem)(al: list expr)(vl: list val): Prop :=
  Forall2 (eval_expr ge e le te m) al vl.

Inductive eval_casts: list val -> list type -> list val -> Prop :=
  | eval_casts_nil:
      eval_casts nil nil nil
  | eval_casts_cons:  forall  ty tyl v1 v2 vl1 vl2,
      sem_cast v1 ty ty = Some v2 ->
      eval_casts vl1 tyl vl2 ->
      eval_casts (v1 :: vl1) (ty :: tyl) (v2 :: vl2).

Lemma eval_casts_app:
  forall vl1 tyl1 vl1',
  eval_casts vl1 tyl1 vl1' ->
  forall vl2 tyl2 vl2',
  eval_casts vl2 tyl2 vl2' ->
  eval_casts (vl1++vl2) (tyl1++tyl2) (vl1'++vl2').
Proof.
  induction 1; simpl; intros; auto.
  constructor 2; auto.
Qed.

Lemma eval_casts_app_inv_l:
  forall vl tyl1 tyl2 vl1' vl2',
  eval_casts vl (tyl1++tyl2) (vl1'++vl2') ->
  length tyl1 = length vl1' ->
  exists vl1 vl2, eval_casts vl1 tyl1 vl1'
    /\ eval_casts vl2 tyl2 vl2'
    /\ vl = vl1 ++ vl2.
Proof.
  induction vl; simpl; intros; inv H; auto.
  +exists nil, nil. symmetry in H1. symmetry in H2.
   apply app_eq_nil in H1. apply app_eq_nil in H2.
   destruct H1. destruct H2. subst.
   repeat (split; auto); constructor.
  +destruct tyl1, vl1'; simpl in *; try (inv H0; fail).
   -subst. exists nil, (a :: vl). repeat (split; auto).
    constructor. constructor 2; auto.
   -inv H3. inv H4.
    destruct IHvl with tyl1 tyl2 vl1' vl2' as [vl1 [vl2 [? [? ?]]]]; auto.
    subst. exists (a::vl1), vl2. repeat (split; auto).
    constructor 2; auto.
Qed.

Lemma eval_exprlist_inv:
  forall geC eC leC teC m al vl1,
  eval_exprs geC eC leC teC m al vl1 ->
  forall vl2 tyl,
  tyl = to_typelist (map typeof al) ->
  eval_casts vl1 (map typeof al) vl2 ->
  eval_exprlist geC eC leC teC m al tyl vl2.
Proof.
  induction 1; simpl; intros.
  +inv H0. constructor.
  +inv H2. simpl. constructor 2 with y; auto.
Qed.

Lemma eval_casts_length:
  forall vl1 tyl vl2,
  eval_casts vl1 tyl vl2 ->
  length vl1 = length vl2 /\ length vl1 = length tyl.
Proof.
  induction 1; simpl; intros; omega.
Qed.

Lemma sem_cast_decode_encode_val:
  forall ty chunk v v',
  Ltypes.access_mode ty = By_value chunk ->
  Lop.sem_cast v ty ty = Some v' ->
  has_type v ty ->
  Lvalues.decode_val chunk (Lvalues.encode_val chunk v') = Some v'.
Proof.
  intros.
  unfold Lop.sem_cast, Lvalues.decode_val, Lvalues.encode_val.
  destruct ty; simpl in *; intros; try congruence.
  +destruct v; inv H1. unfold Lop.sem_cast in *.
   destruct i, s; simpl in *; inv H; inv H0; simpl;
   rewrite Memdata.proj_inj_bytes.
   -rewrite decode_encode_int_1, Int.sign_ext_zero_ext, Int.sign_ext_idem; auto; omega.
   -rewrite decode_encode_int_1, Int.zero_ext_idem, Int.zero_ext_idem; auto; omega.
   -rewrite decode_encode_int_2, Int.sign_ext_zero_ext, Int.sign_ext_idem; auto; omega.
   -rewrite decode_encode_int_2, Int.zero_ext_idem, Int.zero_ext_idem; auto; omega.
   -rewrite decode_encode_int_4. auto.
   -rewrite decode_encode_int_4. auto.
   -rewrite decode_encode_int_1, Int.zero_ext_idem; auto.
    destruct (Int.eq _ _); auto. omega.
   -rewrite decode_encode_int_1, Int.zero_ext_idem; auto.
    destruct (Int.eq _ _); auto. omega.
  +destruct f, v; inv H; inv H1; inv H0;
   rewrite Memdata.proj_inj_bytes.
   -rewrite decode_encode_int_4, Float32.of_to_bits; auto.
   -rewrite decode_encode_int_8, Float.of_to_bits; auto.
Qed.

Lemma store_eval_cast_load:
  forall chunk mv o v v' mv' ty,
  store chunk mv o v' = Some mv' ->
  has_type v ty ->
  Ltypes.access_mode ty = By_value chunk ->
  Lop.sem_cast v ty ty = Some v' ->
  load chunk mv' o = Some v'.
Proof.
  intros. generalize H H; intros.
  apply store_valid_access in H3.
  unfold load in *. rewrite pred_dec_true; auto.
  apply store_mem_contents in H.
  apply store_length in H4.
  destruct H3. red in H3. rewrite <-H4 in *. subst.
  cut (size_chunk_nat chunk=length (Lvalues.encode_val chunk v')). intros.
  +rewrite H. rewrite getN_setN_same; auto.
   eapply sem_cast_decode_encode_val; eauto.
   rewrite <-H.
   unfold size_chunk_nat. rewrite <-Z2Nat.inj_add; try omega.
   apply Nat2Z.inj_le. rewrite nat_of_Z_eq; try omega.
  +rewrite Lvalues.encode_val_length; auto.
Qed.

Lemma store_mvl_eval_cast_load:
  forall ty mv ofs v v' mv',
  store_mvl ty mv ofs v' mv' ->
  eval_cast v ty v' ->
  has_type v ty ->
  load_mvl ty mv' ofs v'.
Proof.
  intros. inv H; inv H0.
  +rewrite H in H2. inv H2.
   constructor 1 with chunk; auto.
   eapply store_eval_cast_load; eauto.
  +destruct H; congruence.
  +destruct H2; congruence.
  +constructor 2; auto.
   rewrite H4.
   eapply loadbytes_storebytes_same; eauto.
Qed.

Lemma eval_cast_val_match:
  forall ty v v' m vc vc',
  val_match m ty v vc ->
  eval_cast v ty v' ->
  sem_cast vc (trans_ptype ty) (trans_ptype ty) = Some vc' ->
  has_type v ty ->
  val_match m ty v' vc'.
Proof.
  intros. inv H0.
  +unfold Lop.sem_cast, sem_cast in *.
   destruct v, ty; simpl in *; try inv H2; inv H3; inv H.
   -destruct i0, s; inv H4; inv H1; constructor; auto.
   -destruct f0; try tauto. inv H1. inv H4. constructor 2; auto.
   -destruct f0; try tauto. inv H1. inv H4. constructor 3; auto.
  +destruct has_type_access_mode_mvl with v' ty as [mv [? ?]]; auto.
   subst. inv H. unfold trans_ptype in *.
   destruct ty; inv H2; simpl in *; inv H1; constructor 4; auto.
Qed.

Lemma has_type_casts_val_exist:
  forall v ty m vc,
  val_match m ty v vc ->
  has_type v ty ->
  is_arystr ty = false ->
  exists vc', sem_cast vc ty ty = Some vc'.
Proof.
  unfold is_arystr, sem_cast.
  induction 1; destruct ty; simpl; intros; try tauto; try congruence.
  +destruct i0, s; simpl; eauto.
  +destruct f0; try tauto; simpl; eauto.
  +destruct f0; try tauto; simpl; eauto.
Qed.

Lemma has_type_casts_exist:
  forall a v m vc,
  has_type v (Lustre.typeof a) ->
  val_match m (Lustre.typeof a) v vc ->
  exists vc', sem_cast vc (typeof (trans_arg a)) (typeof (trans_arg a)) = Some vc'.
Proof.
  intros.
  destruct (is_arystr (Lustre.typeof a)) eqn: ?.
  +rewrite trans_arg_typeoftr; auto.
   unfold is_arystr in *. exists vc.
   inv H0; destruct (Lustre.typeof a); try inv H; simpl in *; try congruence; auto.
  +rewrite trans_arg_typeof_val; auto.
   eapply has_type_casts_val_exist; eauto.
Qed.

Inductive blockof_vptrs: list val -> list type -> list (block*(int*type)) -> Prop :=
  | blockof_vptrs_nil:
     blockof_vptrs nil nil nil
  | blockof_vptrs_cons: forall b o vl t tl bl,
     blockof_vptrs vl tl bl ->
     blockof_vptrs (Vptr b o::vl) (t::tl) ((b,(o,t))::bl).

Lemma blockof_vptrs_length1:
  forall vl tys bl,
  blockof_vptrs vl tys bl ->
  length vl = length bl.
Proof.
  induction 1; simpl; auto.
Qed.

Lemma blockof_vptrs_length2:
  forall vl tys bl,
  blockof_vptrs vl tys bl ->
  length vl = length tys.
Proof.
  induction 1; simpl; auto.
Qed.

Lemma blockof_vptrs_app_inv_left:
  forall vl tyl bl1 bl2,
  blockof_vptrs vl tyl (bl1++bl2) ->
  exists vl1 vl2 tyl1 tyl2, vl = vl1 ++ vl2
    /\ tyl = tyl1 ++ tyl2
    /\ blockof_vptrs vl1 tyl1 bl1
    /\ blockof_vptrs vl2 tyl2 bl2.
Proof.
  induction vl; intros.
  +inv H. destruct bl1; simpl in *; inv H0.
   exists nil, nil, nil,nil. repeat (split; auto); constructor.
  +inv H. destruct bl1; simpl in *; inv H4.
   -exists nil, (Vptr b o::vl), nil, (t::tl). repeat (split; auto); constructor; auto.
   -destruct IHvl with tl bl1 bl2 as [vl1 [vl2 [tyl1 [tyl2 [? [? [? ?]]]]]]]; auto.
    subst. exists (Vptr b o::vl1), vl2,(t::tyl1),tyl2.
    repeat (split; auto); constructor; auto.
Qed.

Lemma blockof_vptrs_inv:
  forall vl tyl bl,
  blockof_vptrs vl tyl bl ->
  vl = map (fun x => Vptr (fst x) (fst (snd x))) bl.
Proof.
  induction 1; simpl; intros; auto.
  f_equal. auto.
Qed.

Lemma blockof_vptrs_eval_casts:
  forall vl bl al,
  blockof_vptrs vl (map (fun x => Lustre.typeof x) al) bl ->
  eval_casts vl (map typeof (map mkaddr (map trans_expr al))) vl.
Proof.
  induction vl; simpl; intros.
  +inv H. destruct al; inv H0. constructor.
  +inv H. destruct al; inv H3.
   constructor 2; eauto.
Qed.

Lemma blockof_vptrs_nth_error:
  forall vl tyl bl,
  blockof_vptrs vl tyl bl ->
  forall n b o t,
  nth_error tyl n = value t ->
  nth_error vl n = value (Vptr b o) ->
  nth_error bl n = value (b, (o,t)).
Proof.
  induction 1; simpl; intros.
  +destruct n; simpl in *; inv H.
  +destruct n; simpl in *; eauto.
   inv H0. inv H1. auto.
Qed.

Lemma bind_parameter_temps_new_nth_error_exists:
  forall al vl leC leC1,
  bind_parameter_temps al vl leC = Some leC1 ->
  forall id v t,
  leC ! id = None ->
  leC1 ! id = Some (v, t) ->
  list_norepet (map fst al) ->
  exists n, nth_error al n = value (id,t)
    /\ nth_error vl n = value v.
Proof.
  induction al; simpl; intros.
  +destruct vl; try congruence.
  +destruct a, vl; try congruence. inv H2.
   compare i id; intros; subst.
   -exists O. erewrite bind_parameter_temps_notin_eq in H1; eauto.
    rewrite PTree.gss in H1. inv H1. simpl. auto.
   -destruct IHal with vl (PTree.set i (v0, t0) leC) leC1 id v t as [n1 [? ?]]; auto.
    rewrite PTree.gso; auto.
    exists (S n1). simpl. split; auto.
Qed.

Lemma list_norepet_nth_error_inv:
  forall al n1 id1 t1 n2 id2 t2,
  list_norepet (map (@fst ident type) al) ->
  nth_error al n1 = value (id1, t1) ->
  nth_error al n2 = value (id2, t2) ->
  id1 <> id2 ->
  n1 <> n2.
Proof.
  induction al; simpl; intros.
  +destruct n1; inv H0.
  +destruct n1,n2; inv H0; inv H1; try omega. congruence.
   inv H. eapply IHal in H4; eauto.
Qed.

Lemma nth_error_trans_type_pointer_inv:
  forall rets n t,
  nth_error (map (fun x: ident*type => Tpointer (snd x)) rets) n = Some (Tpointer t) ->
  nth_error (map (fun x: ident*type => snd x) rets) n = Some t.
Proof.
  induction rets; intros.
  +destruct n; inv H.
  +destruct n; simpl in *; inv H; eauto.
Qed.

Lemma block_ofs_ty_list_norepet_nth_error_diff:
  forall bl n1 n2 bot1 bot2,
  block_ofs_ty_list_norepet bl ->
  nth_error bl n1 = value bot1 ->
  nth_error bl n2 = value bot2 ->
  n1 <> n2 ->
  block_ofs_ty_disjoint bot1 bot2.
Proof.
  induction bl; simpl; intros.
  +destruct n1; inv H0.
  +destruct H. destruct n1, n2; inv H0; inv H1; try omega.
   -apply H. apply nth_error_in with n2; auto.
   -apply nth_error_in in H5. apply H in H5.
    destruct H5; [left | right]; auto. omega.
   -apply IHbl with n1 n2; auto.
Qed.

Lemma bind_parameter_temps_diff_id_disjoint:
  forall rets vl leC bl,
  bind_parameter_temps (map trans_ret rets) vl empty_temp = Some leC ->
  blockof_vptrs vl (map (fun x => snd x) rets) bl ->
  block_ofs_ty_list_norepet bl ->
  list_norepet (map fst rets) ->
  ret_env_diff_id_disjoint leC.
Proof.
  intros. red; intros.
  assert(A: list_norepet (map fst (map trans_ret rets))).
    rewrite map_map. simpl. auto.
  destruct bind_parameter_temps_new_nth_error_exists
    with (map trans_ret rets) vl empty_temp leC id1 (Vptr b1 o1) (Tpointer t1)
    as [n1 [? ?]]; auto.
    rewrite PTree.gempty; auto.
  destruct bind_parameter_temps_new_nth_error_exists
    with (map trans_ret rets) vl empty_temp leC id2 (Vptr b2 o2) (Tpointer t2)
    as [n2 [? ?]]; auto.
    rewrite PTree.gempty; auto.
  assert(A1: n1 <> n2).
    eapply list_norepet_nth_error_inv; eauto.
  apply map_nth_error with (f:=snd) in H6.
  apply map_nth_error with (f:=snd) in H8.
  rewrite map_map in *. simpl in *.
  apply nth_error_trans_type_pointer_inv in H6.
  apply nth_error_trans_type_pointer_inv in H8.
  eapply blockof_vptrs_nth_error in H6; eauto.
  eapply blockof_vptrs_nth_error in H8; eauto.
  eapply block_ofs_ty_list_norepet_nth_error_diff with (n1:=n1) (n2:=n2) in H1; eauto.
  red in H1; auto.
Qed.

End CPROOF.
