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

Require Import Axioms.
Require Import Coqlib.
Require Import AST.
Require Import Integers.
Require Import Floats.
Require Import Lvalues.
Require Import Values.
Require Export Memdata.
Require Export Memtype.
Require Import Memory.
Require Import Maps.
Require Import Lenv.
Require Import Globalenvs.
Require Import Cltypes.
Require Import Ctemp.
Require Import ExtraList.

Section MEMORY.

Transparent Mem.alloc Mem.free Mem.store Mem.load Mem.storebytes Mem.loadbytes.

Theorem range_perm_valid_block2:
  forall m b lo hi,
  Mem.range_perm m b lo hi Cur Nonempty ->
  lo < hi ->
  Mem.valid_block m b.
Proof.
  intros.
  assert (Mem.perm m b lo Cur Nonempty).
    apply H. omega.
  eauto with mem.
Qed.

Theorem range_perm_alloc_other2:
  forall m1 lo hi m2 b,
  Mem.alloc m1 lo hi = (m2, b) ->
  forall b' ofs n p,
  0 < n ->
  Mem.range_perm m1 b' ofs (ofs + n) Cur p ->
  Mem.range_perm m2 b' ofs (ofs + n) Cur p.
Proof.
  intros. red; intros. apply H1 in H2.
  eapply Mem.perm_alloc_1; eauto.
Qed.

Theorem range_perm_alloc_inv2:
  forall m1 lo hi m2 b,
  Mem.alloc m1 lo hi = (m2, b) ->
  forall b' ofs n p,
  Mem.range_perm m2 b' ofs (ofs + n) Cur p ->
  0 < n ->
  if eq_block b' b
  then lo <= ofs /\ ofs + n <= hi
  else Mem.range_perm m1 b' ofs (ofs + n) Cur p.
Proof.
  intros.
  unfold eq_block. destruct (peq b' b). subst b'.
  assert (Mem.perm m2 b ofs Cur p). apply H0. omega.
  assert (Mem.perm m2 b (ofs + n - 1) Cur p). apply H0. omega.
  exploit Mem.perm_alloc_inv. apply H. eexact H2. rewrite peq_true. intro.
  exploit Mem.perm_alloc_inv. apply H. eexact H3. rewrite peq_true. intro.
  intuition omega.
  red; intros.
  exploit Mem.perm_alloc_inv. apply H. apply H0. eauto. rewrite peq_false; auto.
Qed.

Lemma getN_repeat_undef:
  forall n lo, Mem.getN n lo (ZMap.init Undef) = list_repeat n Undef.
Proof.
  induction n; simpl; intros; auto.
  f_equal; auto. unfold ZMap.init, PMap.init,ZMap.get,PMap.get.
  simpl. rewrite PTree.gempty. auto.
Qed.

Theorem loadbytes_alloc_same:
  forall m1 lo hi m2 b,
  Mem.alloc m1 lo hi = (m2, b) ->
  Mem.loadbytes m2 b lo (hi-lo) = Some (list_repeat (nat_of_Z (hi-lo)) Undef ).
Proof.
  intros. unfold Mem.loadbytes.
  injection H; intros. rewrite <-H1.
  rewrite pred_dec_true; simpl.
  rewrite H0. rewrite PMap.gss; auto.
  rewrite getN_repeat_undef; auto.

  red. unfold Mem.perm. simpl. rewrite H0.
  rewrite PMap.gss. intros.
  replace (lo + (hi - lo)) with hi in H2; try omega.
  destruct (zle lo ofs); try omega.
  destruct (zlt ofs hi); try omega.
  simpl. constructor.
Qed.

Theorem loadbytes_alloc_unchanged:
  forall m1 m2 lo hi b b' ofs n,
  Mem.alloc m1 lo hi = (m2, b) ->
  Mem.valid_block m1 b' ->
  Mem.loadbytes m2 b' ofs n = Mem.loadbytes m1 b' ofs n.
Proof.
  intros.
  assert(n <= 0 \/ 0 < n). omega.
  destruct H1.
  repeat rewrite Mem.loadbytes_empty; auto.

  unfold Mem.loadbytes.
  destruct (Mem.range_perm_dec m2 b' ofs (ofs + n) Cur Readable).
  exploit range_perm_alloc_inv2; eauto. destruct (eq_block b' b); intros.
  +subst b'. elimtype False.
   apply Mem.alloc_result in H. red in H0. subst.
   apply Plt_strict in H0. auto.
  +rewrite pred_dec_true; auto.
   injection H; intros. rewrite <- H4; simpl.
   rewrite H3. rewrite PMap.gso; auto.
  +rewrite pred_dec_false. auto.
   red; intros. red in n0. apply n0.
   eapply range_perm_alloc_other2; eauto.
Qed.

Theorem loadbytes_alloc_other:
  forall m1 m2 lo hi b b' ofs n bytes,
  Mem.alloc m1 lo hi = (m2, b) ->
  Mem.loadbytes m1 b' ofs n = Some bytes ->
  Mem.loadbytes m2 b' ofs n = Some bytes.
Proof.
  intros.
  assert(n <= 0 \/ 0 < n). omega.
  destruct H1.
  rewrite Mem.loadbytes_empty in *; auto.

  rewrite <- H0.
  eapply loadbytes_alloc_unchanged; eauto.
  apply Mem.loadbytes_range_perm in H0.
  apply range_perm_valid_block2 with ofs (ofs+n); try omega.
  eauto with mem.
Qed.

Theorem range_perm_free_3:
  forall m1 bf lo hi m2,
  Mem.free m1 bf lo hi = Some m2 ->
  forall b ofs n p,
  Mem.range_perm m1 b ofs (ofs + n) Cur p ->
  b <> bf \/ lo >= hi \/ ofs + n <= lo \/ hi <= ofs ->
  Mem.range_perm m2 b ofs (ofs + n) Cur p.
Proof.
  intros.
  red; intros. eapply Mem.perm_free_1; eauto.
  destruct (zlt lo hi). intuition. right. omega.
Qed.

Theorem range_perm_free_inv_3:
  forall m1 bf lo hi m2 b ofs p n,
  Mem.free m1 bf lo hi = Some m2 ->
  Mem.range_perm m2 b ofs (ofs + n) Cur p  ->
  Mem.range_perm m1 b ofs (ofs + n) Cur p .
Proof.
  intros. generalize H; intros A.
  apply Mem.free_result in H. subst.
  red; intros. generalize (H0 ofs0 H).

  unfold Mem.perm, Mem.unchecked_free; simpl.
  assert(b = bf \/ b <> bf). tauto. destruct H1.
  subst b. rewrite PMap.gss in *.
  destruct (zle lo ofs0); simpl in *.
  destruct (zlt ofs0 hi); simpl in *. tauto.
  congruence. auto.
  rewrite PMap.gso in *; auto.
Qed.

Theorem loadbytes_free:
  forall m1 bf lo hi m2 b ofs n,
  Mem.free m1 bf lo hi = Some m2 ->
  b <> bf ->
  Mem.loadbytes m2 b ofs n = Mem.loadbytes m1 b ofs n.
Proof.
  intros.
  assert(n <= 0 \/ 0 < n). omega.
  destruct H1.
  repeat rewrite Mem.loadbytes_empty; auto.

  unfold Mem.loadbytes.
  destruct (Mem.range_perm_dec m2 b ofs (ofs + n) Cur Readable).
  rewrite pred_dec_true.
  generalize H; intros A.
  apply Mem.free_result in A. rewrite A.
  simpl. auto.

  eapply range_perm_free_inv_3; eauto.
  rewrite pred_dec_false; auto.
  red; intro; elim n0.
  eapply range_perm_free_3; eauto.
Qed.

Theorem range_perm_drop_5:
  forall m b lo hi p m' n b' ofs p',
  Mem.drop_perm m b lo hi p = Some m' ->
  b' <> b \/ ofs + n <= lo \/ hi <= ofs \/ perm_order p p' ->
  0 <= n ->
  Mem.range_perm m b' ofs (ofs + n) Cur p'  ->
  Mem.range_perm m' b' ofs (ofs + n) Cur p' .
Proof.
  intros.
  red; intros.
  destruct (peq b' b). subst b'.
  destruct (zlt ofs0 lo). eapply Mem.perm_drop_3; eauto.
  destruct (zle hi ofs0). eapply Mem.perm_drop_3; eauto.
  apply Mem.perm_implies with p. eapply Mem.perm_drop_1; eauto. omega.
  intuition.
  eapply Mem.perm_drop_3; eauto.
Qed.

Theorem range_perm_drop_6:
  forall m b lo hi p m' n b' ofs p',
  Mem.drop_perm m b lo hi p = Some m' ->
  Mem.range_perm m' b' ofs (ofs + n) Cur p' ->
  Mem.range_perm m b' ofs (ofs + n) Cur p'.
Proof.
  intros. red; intros. eapply Mem.perm_drop_4; eauto.
Qed.

Theorem loadbytes_drop:
  forall m b lo hi p m' n b' ofs,
  Mem.drop_perm m b lo hi p = Some m' ->
  b' <> b \/ ofs + n <= lo \/ hi <= ofs \/ perm_order p Readable ->
  Mem.loadbytes m' b' ofs n = Mem.loadbytes m b' ofs n.
Proof.
  intros.
  destruct (zle n 0).
  repeat rewrite Mem.loadbytes_empty; auto.
  unfold Mem.loadbytes.
  destruct (Mem.range_perm_dec m b' ofs (ofs + n) Cur Readable).
  rewrite pred_dec_true.
  unfold Mem.drop_perm in H. destruct (Mem.range_perm_dec m b lo hi Cur Freeable); inv H.
  simpl. auto.
  eapply range_perm_drop_5; eauto. omega.
  rewrite pred_dec_false. auto.
  red; intros; elim n0. eapply range_perm_drop_6; eauto.
Qed.

Lemma alloc_range_perm:
  forall m1 m2 hi i p,
  Mem.alloc m1 0 hi = (m2, i) ->
  Mem.range_perm m2 i 0 hi Cur p.
Proof.
  unfold Mem.range_perm. simpl; intros.
  apply Mem.perm_alloc_2 with _ _ _ _ _ ofs Cur in H; auto.
  unfold Mem.perm in *. unfold Mem.perm_order' in *.
  destruct (PMap.get i (Mem.mem_access m2) ofs Cur) eqn:?; try congruence.
  inv H; constructor.
Qed.

Lemma range_perm_sube:
  forall m l o1 n1 o2 n2 p,
  Mem.range_perm m l o1 n1 Cur p ->
  o1 <= o2 /\ n2 <= n1 ->
  Mem.range_perm m l o2 n2 Cur p.
Proof.
  intros. red. intros. apply H. omega.
Qed.

Lemma loadbytes_valid_block:
  forall m b o n mv,
  Mem.loadbytes m b o n = Some mv ->
  0 < n ->
  Plt b (Mem.nextblock m).
Proof.
  intros. apply Mem.loadbytes_range_perm in H.
  apply range_perm_valid_block2 with o (o+n); try omega.
  eauto with mem.
Qed.

Lemma alloc_loadbytes_same:
  forall m t m1 b1,
  Mem.alloc m 0 (sizeof t) = (m1, b1) ->
  Mem.loadbytes m1 b1 0 (sizeof t) = Some (alloc (sizeof t)).
Proof.
  intros. apply loadbytes_alloc_same in H.
  rewrite Z.sub_0_r in H; auto.
Qed.

Lemma free_list_nextblock_eq:
  forall l m m1,
  Mem.free_list m l = Some m1 ->
  Mem.nextblock m1 = Mem.nextblock m.
Proof.
  induction l; intros; inv H; auto.
  destruct a. destruct p.
  destruct (Mem.free _ _ _ _) eqn:?; try congruence.
  rewrite IHl with m0 _; auto.
  apply Mem.nextblock_free in Heqo; auto.
Qed.

Lemma free_list_loadbytes_eq:
  forall bl m m',
  Mem.free_list m bl = Some m' ->
  forall b o n, ~ In b (map (fun x => fst (fst x)) bl) ->
  Mem.loadbytes m' b o n = Mem.loadbytes m b o n.
Proof.
  induction bl; simpl; intros.
  +inv H; auto.
  +destruct a. destruct p.
   destruct (Mem.free _ _ _ _) eqn:?; try congruence.
   erewrite IHbl with (m:=m0); eauto.
   erewrite loadbytes_free; eauto.
Qed.

Lemma free_list_range_perm:
  forall bl m m',
  Mem.free_list m bl = Some m' ->
  forall b o n p ,
  ~ In b (map (fun x => fst (fst x)) bl) ->
  Mem.range_perm m b o n Cur p ->
  Mem.range_perm m' b o n Cur p.
Proof.
  induction bl; simpl; intros.
  +inv H; auto.
  +destruct a. destruct p0.
   destruct (Mem.free _ _ _ _) eqn:?; try congruence.
   apply IHbl with m0; auto.
   red; intros. eapply Mem.perm_free_1; eauto.
Qed.

Lemma free_list_range_perm_inv:
  forall bl m m',
  Mem.free_list m bl = Some m' ->
  forall b o n p ,
  Mem.range_perm m' b o n Cur p ->
  Mem.range_perm m b o n Cur p.
Proof.
  induction bl; simpl; intros.
  +inv H; auto.
  +destruct a. destruct p0.
   destruct (Mem.free _ _ _ _) eqn:?; try congruence.
   apply IHbl with (m:=m0) in H0; eauto.
   red; intros. eapply Mem.perm_free_3; eauto.
Qed.

End MEMORY.

Section GLOBALENVS.

Variable ge: Genv.t fundef type.

Fixpoint loadbytes_store_init_data (m: mem) (b: block) (p: Z) (il: list init_data) {struct il} : Prop :=
  match il with
  | nil => True
  | Init_int8 n :: il' =>
      Mem.loadbytes m b p 1 = Some (encode_val Mint8unsigned (Vint n))
      /\ loadbytes_store_init_data m b (p + 1) il'
  | Init_int16 n :: il' =>
      Mem.loadbytes m b p 2 = Some (encode_val Mint16unsigned (Vint n))
      /\ loadbytes_store_init_data m b (p + 2) il'
  | Init_int32 n :: il' =>
      Mem.loadbytes m b p 4 = Some (encode_val Mint32 (Vint n))
      /\ loadbytes_store_init_data m b (p + 4) il'
  | Init_int64 n :: il' =>
      Mem.loadbytes m b p 8 = Some (encode_val Mint64 (Vlong n))
      /\ loadbytes_store_init_data m b (p + 8) il'
  | Init_float32 n :: il' =>
      Mem.loadbytes m b p 4 = Some (encode_val Mfloat32 (Vsingle n))
      /\ loadbytes_store_init_data m b (p + 4) il'
  | Init_float64 n :: il' =>
      Mem.loadbytes m b p 8 = Some (encode_val Mfloat64 (Vfloat n))
      /\ loadbytes_store_init_data m b (p + 8) il'
  | Init_addrof symb ofs :: il' =>
      loadbytes_store_init_data m b (p + 4) il'
  | Init_space n :: il' =>
      loadbytes_store_init_data m b (p + Zmax n 0) il'
  end.

Lemma store_init_data_list_outside_bytes:
  forall  b il m p m',
  Genv.store_init_data_list ge m b p il = Some m' ->
  forall n b' q,
  b' <> b \/ q + n <= p ->
  Mem.loadbytes m' b' q n = Mem.loadbytes m b' q n.
Proof.
  induction il; simpl.
  intros; congruence.
  intros until m'. caseEq (Genv.store_init_data ge m b p a); try congruence.
  intros m1 A B n b' q C. transitivity (Mem.loadbytes m1 b' q n).
  eapply IHil; eauto. generalize (Genv.init_data_size_pos a). intuition omega.
  destruct a; simpl in A;
  try (eapply Mem.loadbytes_store_other; eauto; intuition; fail).
  congruence.
  destruct (Genv.find_symbol ge i); try congruence.
  eapply Mem.loadbytes_store_other; eauto; intuition.
Qed.

Lemma store_init_data_list_bytes:
  forall b il m p m',
  Genv.store_init_data_list ge m b p il = Some m' ->
  loadbytes_store_init_data m' b p il.
Proof.
  assert (A: forall chunk v m b p m1 il m',
    Mem.store chunk m b p v = Some m1 ->
    Genv.store_init_data_list ge m1 b (p + size_chunk chunk) il = Some m' ->
    Mem.loadbytes m' b p (size_chunk chunk) = Some (Memdata.encode_val chunk v)).
  intros. transitivity (Mem.loadbytes m1 b p (size_chunk chunk)).
  eapply store_init_data_list_outside_bytes; eauto. right. omega.
  eapply Mem.loadbytes_store_same; eauto.

  induction il; simpl.
  auto.
  intros until m'. caseEq (Genv.store_init_data ge m b p a); try congruence.
  intros m1 B C.
  exploit IHil; eauto. intro D.
  destruct a; simpl in B; intuition.
  eapply (A Mint8unsigned (Vint i)); eauto.
  eapply (A Mint16unsigned (Vint i)); eauto.
  eapply (A Mint32 (Vint i)); eauto.
  eapply (A Mint64 (Vlong i)); eauto.
  eapply (A Mfloat32 (Vsingle f)); eauto.
  eapply (A Mfloat64 (Vfloat f)); eauto.
Qed.

Lemma loadbytes_store_init_data_invariant:
  forall m m' b,
  (forall ofs n, Mem.loadbytes m' b ofs n = Mem.loadbytes m b ofs n) ->
  forall il p,
  loadbytes_store_init_data m b p il -> loadbytes_store_init_data m' b p il.
Proof.
  induction il; intro p; simpl.
  auto.
  repeat rewrite H. destruct a; intuition.
Qed.

Lemma store_zeros_outside_bytes:
  forall m b z n m',
  Globalenvs.store_zeros m b z n = Some m' ->
  forall n b' p,
  b' <> b -> Mem.loadbytes m' b' p n = Mem.loadbytes m b' p n.
Proof.
  intros until n. functional induction (Globalenvs.store_zeros m b z n); intros.
  inv H; auto.
  rewrite IHo; auto. eapply Mem.loadbytes_store_other; eauto.
  inv H.
Qed.

Lemma init_data_list_size_pos:
  forall l, Genv.init_data_list_size l >= 0.
Proof.
  induction l; simpl; auto.
  omega.
  generalize (Genv.init_data_size_pos a); intros. omega.
Qed.

Lemma alloc_globals_genv_alloc_funcs:
  forall l m,
  (forall a, In a l -> exists f, snd a = Gfun f) ->
  exists m', Genv.alloc_globals ge m l = Some m'.
Proof.
  induction l; simpl; intros.
  +exists m. auto.
  +destruct H with a; auto. destruct a. simpl in *. subst.
   destruct (Mem.alloc m 0 1) eqn:?.
   destruct Mem.range_perm_drop_2 with m0 b 0 1 Nonempty; auto.
   red; intros. eapply Mem.perm_alloc_2; eauto.
   rewrite e. eauto.
Qed.

Lemma store_init_data_perm:
  forall prm b' q a b m p m',
  Genv.store_init_data ge m b p a = Some m' ->
  Mem.perm m b' q Cur prm -> Mem.perm m' b' q Cur prm.
Proof.
  intros.
  destruct a; simpl in H; eauto with mem.
  congruence.
  destruct (Genv.find_symbol ge i); try congruence. eauto with mem.
Qed.

Lemma range_perm_store_zeros:
  forall b m p n,
  Mem.range_perm m b p (p+n) Cur Writable ->
  0 <= n ->
  exists m', Globalenvs.store_zeros m b p n = Some m'.
Proof.
  intros until n. functional induction (Globalenvs.store_zeros m b p n); intros.
  +eauto.
  +apply IHo; try omega. red; intros.
   eapply Mem.perm_store_1; eauto.
   apply H; auto. omega.
  +destruct Mem.valid_access_store with m Mint8unsigned b p Vzero as [m' ?]; auto.
   red. split.
   red; intros. apply H. simpl in *. omega.
   simpl. red. exists p. omega.
   congruence.
Qed.

Lemma loadbytes_alloc_globals:
  forall n b p vl m m',
  Genv.alloc_globals ge m vl = Some m' ->
  Mem.valid_block m b ->
  Mem.loadbytes m' b p n = Mem.loadbytes m b p n.
Proof.
  induction vl; simpl; intros until m'.
  congruence.
  unfold Genv.alloc_global. destruct a. destruct g.
  +intros. destruct (Mem.alloc m 0 1) eqn:?.
   destruct (Mem.drop_perm m0 b0 0 1 Nonempty) eqn:?; try congruence.
   rewrite IHvl with m1 m'; auto.
   transitivity (Mem.loadbytes m0 b p n).
   -eapply loadbytes_drop; eauto.
    left. apply Mem.alloc_result in Heqp0. red in H0. subst.
    red; intros. subst. apply Plt_strict in H0. auto.
   -eapply loadbytes_alloc_unchanged; eauto.
   -apply Mem.nextblock_drop in Heqo. apply Mem.nextblock_alloc in Heqp0.
    unfold Mem.valid_block in *. rewrite Heqo,Heqp0.
    apply Plt_trans with (Mem.nextblock m); auto.
    apply Plt_succ.
  +set (init := gvar_init v).
   set (sz := Genv.init_data_list_size init).
   caseEq (Mem.alloc m 0 sz). intros m1 b1 ALLOC.
   caseEq (store_zeros m1 b1 0 sz); try congruence. intros m2 STZ.
   caseEq (Genv.store_init_data_list ge m2 b1 0 init); try congruence. intros m3 STORE.
   caseEq (Mem.drop_perm m3 b1 0 sz (Genv.perm_globvar v)); try congruence. intros m4 DROP REC VALID.
   assert (b <> b1). apply Mem.valid_not_valid_diff with m; eauto with mem.
   transitivity (Mem.loadbytes m4 b p n).
   apply IHvl; auto. red.
   rewrite (Mem.nextblock_drop _ _ _ _ _ _ DROP).
   rewrite (Genv.store_init_data_list_nextblock _ _ _ _ _ STORE).
   rewrite (Genv.store_zeros_nextblock _ _ _ _ STZ).
   change (Mem.valid_block m1 b). eauto with mem.
   transitivity (Mem.loadbytes m3 b p n).
   eapply loadbytes_drop; eauto.
   transitivity (Mem.loadbytes m2 b p n).
   eapply store_init_data_list_outside_bytes; eauto.
   transitivity (Mem.loadbytes m1 b p n).
   eapply store_zeros_outside_bytes; eauto.
  eapply loadbytes_alloc_unchanged; eauto.
Qed.

Lemma add_global_funs_find_var_info:
  forall b l (g:Genv.t fundef type),
  (forall a, In a l -> exists f, snd a = Gfun f) ->
  Genv.find_var_info (Genv.add_globals g l) b = Genv.find_var_info g b.
Proof.
  induction l; simpl; intros; auto.
  rewrite IHl; auto.
  destruct H with a as [f ?]; auto.
  destruct a; simpl in *. subst.
  unfold Genv.add_global, Genv.find_var_info. simpl. auto.
Qed.

Lemma store_init_data_list_var_idem:
  forall (g1 g2:Genv.t fundef type) l m o b,
  init_data_types l ->
  Genv.store_init_data_list g1 m b o l = Genv.store_init_data_list g2 m b o l.
Proof.
  induction l; simpl; intros; auto.
  inv H.
  destruct a; simpl in *; auto; try destruct (Mem.store _ _ _ _ _); auto.
  tauto.
Qed.

Lemma range_perm_store_init_data:
  forall b a ofs m,
  Mem.range_perm m b ofs (ofs+ Genv.init_data_size a) Cur Writable ->
  forall mv mv1, store_init_data mv ofs a = Some mv1 ->
  exists m', Genv.store_init_data ge m b ofs a = Some m'.
Proof.
  intros. generalize H0. intros.
  destruct a; simpl in *; try (eapply store_valid_access in H1; eauto; destruct H1).
  destruct Mem.valid_access_store with m Mint8unsigned b ofs (Vint i) as [m' ?]; eauto.
   split; auto.
  destruct Mem.valid_access_store with m Mint16unsigned b ofs (Vint i) as [m' ?]; eauto.
   split; auto.
  destruct Mem.valid_access_store with m Mint32 b ofs (Vint i) as [m' ?]; eauto.
   split; auto.
  congruence.
  destruct Mem.valid_access_store with m Mfloat32 b ofs (Vsingle f) as [m' ?]; eauto.
   split; auto.
  destruct Mem.valid_access_store with m Mfloat64 b ofs (Vfloat f) as [m' ?]; eauto.
   split; auto.
  eauto.
  congruence.
Qed.

Lemma range_perm_store_init_data_list:
  forall b l ofs m,
  Mem.range_perm m b ofs (ofs+(Genv.init_data_list_size l)) Cur Writable ->
  forall mv mv1, store_init_datas mv ofs l = Some mv1 ->
  exists m', Genv.store_init_data_list ge m b ofs l = Some m'.
Proof.
  induction l; simpl; intros; eauto.
  destruct (store_init_data _ _ _) eqn:?; try congruence.
  generalize (Genv.init_data_size_pos a) (init_data_list_size_pos l); intros.
  destruct range_perm_store_init_data with b a ofs m mv m0 as [m1 ?]; auto.
  red; intros. apply H. omega.
  rewrite H3. destruct IHl with (ofs + Genv.init_data_size a) m1 m0 mv1 as [m' ?]; eauto.
  red; intros. eapply store_init_data_perm; eauto.
  apply H. omega.
Qed.

Lemma alloc_global_var_idem:
  forall i v m (g1 g2:Genv.t fundef type),
  init_data_types (gvar_init v) ->
  Genv.alloc_global g1 m (i, Gvar v) = Genv.alloc_global g2 m (i, Gvar v).
Proof.
  simpl. intros.
  destruct (Mem.alloc _ _ _).
  destruct (Globalenvs.store_zeros _ _ _ _); auto.
  rewrite store_init_data_list_var_idem with (g2:=g2); auto.
Qed.

Lemma alloc_globals_vars_idem:
  forall l m (g1 g2:Genv.t fundef type),
  (forall a, In a l -> exists v, snd a = Gvar v /\ init_data_types (gvar_init v)) ->
  Genv.alloc_globals g1 m l = Genv.alloc_globals g2 m l.
Proof.
  induction l; simpl; intros; auto.
  destruct H with a as [v [? ?]]; auto.
  destruct a; simpl in H0; subst.
  rewrite alloc_global_var_idem with (g2:=g2); auto.
  destruct (Genv.alloc_global _ _ _);auto.
Qed.

Lemma find_symbol_add_globals_new:
  forall id l (g:Genv.t fundef type),  ~ In id (map fst l) ->
  Genv.find_symbol (Genv.add_globals g l) id = Genv.find_symbol g id.
Proof.
  induction l; simpl; intros; auto.
  rewrite IHl; auto.
  unfold Genv.find_symbol, Genv.add_global.
  simpl. rewrite PTree.gso; auto.
Qed.

Lemma find_var_info_add_globals_new:
  forall i l (g:Genv.t fundef type),
  Plt i (Genv.genv_next g) ->
  Genv.find_var_info (Genv.add_globals g l) i = Genv.find_var_info g i.
Proof.
  induction l; simpl; intros; auto.
  rewrite IHl; auto.
  unfold Genv.find_var_info, Genv.add_global.
  +simpl. destruct a. destruct g0; simpl; auto.
   rewrite PTree.gso; auto. red; intros; subst.
   apply Plt_strict in H; auto.
  +destruct a. apply Plt_trans with (Genv.genv_next g); auto.
   destruct g0; simpl; apply Plt_succ; auto.
Qed.

Lemma alloc_globals_bytes:
  forall id ty init vl (g:Genv.t fundef type) m m',
  Genv.genv_next g = Mem.nextblock m ->
  Genv.alloc_globals ge m vl = Some m' ->
  list_norepet (map fst vl) ->
  In (id, Gvar (mkglobvar ty init true false)) vl ->
  (forall a, In a vl -> exists v, snd a = Gvar v) ->
  exists b, Genv.find_symbol (Genv.add_globals g vl) id = Some b
         /\ Genv.find_var_info (Genv.add_globals g vl) b = Some (mkglobvar ty init true false)
         /\ loadbytes_store_init_data m' b 0 init.
Proof.
  induction vl; simpl; intros.
  contradiction.
  inv H1. destruct H3 with a as [? A]; auto.
  destruct a; simpl in *. subst.
  destruct (Mem.alloc _ _ _) eqn:?.
  destruct (Globalenvs.store_zeros _ _ _ _) eqn:?; try congruence.
  destruct (Genv.store_init_data_list _ _ _ _ _) eqn:?; try congruence.
  destruct (Mem.drop_perm _ _ _ _ _) eqn:?; try congruence.
  exploit Mem.alloc_result; eauto. intro A1.
  exploit Mem.nextblock_alloc; eauto. intros A2.
  cut ( Pos.succ (Genv.genv_next g) = Mem.nextblock m3). intros A3.
  destruct H2.
  +inv H1. exists (Mem.nextblock m); repeat split.
   -rewrite find_symbol_add_globals_new; auto.
    unfold Genv.find_symbol,Genv.add_global.
    simpl; rewrite PTree.gss; auto. congruence.
   -rewrite <-H. rewrite find_var_info_add_globals_new; auto.
    unfold Genv.find_var_info, Genv.add_global; simpl.
    rewrite PTree.gss; auto. simpl.
    apply Plt_succ.
   -apply loadbytes_store_init_data_invariant with m2.
    intros. transitivity (Mem.loadbytes m3 (Mem.nextblock m) ofs n).
    *eapply loadbytes_alloc_globals; eauto.
     red. rewrite <-A3, H. apply Plt_succ.
    *eapply loadbytes_drop; eauto. repeat right. constructor.
    *eapply store_init_data_list_bytes; eauto.
  +eapply IHvl; eauto.
  +rewrite (Mem.nextblock_drop _ _ _ _ _ _ Heqo1).
   rewrite (Genv.store_init_data_list_nextblock _ _ _ _ _ Heqo0).
   rewrite (Genv.store_zeros_nextblock _ _ _ _ Heqo).
   rewrite A2, H. auto.
Qed.

End GLOBALENVS.
