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

Require Import Bool.
Require Import List.
Require Import Omega.
Require Import Permutation.

Set Implicit Arguments.

Open Scope list_scope.

Section ListExtra.

Variable A B C: Type.

Lemma app_length_equal_inv: forall (l1 l3 l2 l4:list A),
  l1 ++ l2 = l3 ++ l4 ->
  length l1 = length l3 \/ length l2 = length l4 ->
  l1 = l3 /\ l2 = l4.
Proof.
  induction l1, l3; simpl; intros; destruct H0; auto; try (omega; fail).
  subst. simpl in *. rewrite app_length in H0. omega.
  subst. simpl in *. rewrite app_length in H0. omega.
  simpl in *. inversion H. apply IHl1 in H3; auto. destruct H3; split; f_equal; auto.
  simpl in *. inversion H. apply IHl1 in H3; auto. destruct H3; split; f_equal; auto.
Qed.

Lemma not_in_app: forall (l1 l2: list A)(a: A),
  ~ In a (l1 ++ l2) -> ~ In a l1 /\ ~ In a l2.
Proof.
  intuition.
Qed.

Lemma not_in_app_inv: forall (l1 l2: list A)(a: A),
  ~ In a l1 -> ~ In a l2 -> ~ In a (l1 ++ l2).
Proof.
  induction l1; simpl; intros; auto.
  intuition. apply IHl1 with l2 a0; auto.
Qed.

Lemma seq_map_equal : forall (l: list A),
  l = map (fun x => x) l.
Proof.
  induction l; simpl; trivial.
  rewrite <- IHl; trivial.
Qed.

Lemma seq_nth_equal : forall (l: list A)(d: A),
  l = (map (fun id => nth id l d) (seq O (length l))).
Proof.
  induction l; simpl; intros; trivial.
  rewrite <- seq_shift. rewrite map_map.
  rewrite <- IHl with d; trivial.
Qed.

Lemma seq_nth_fun_equal : forall (f: A -> B) (l: list A)(d: A),
  map f l = (map (fun id => f (nth id l d)) (seq O (length l))).
Proof.
  intros. rewrite <- map_map with _ _ _ (fun id => nth id l d) f _.
  rewrite <- seq_nth_equal. trivial.
Qed.

Lemma seq_nth_perm : forall (l: list A)(ids: list nat)(d: A),
  Permutation (seq O (length l)) ids ->
  Permutation l (map (fun id => nth id l d) ids).
Proof.
  intros.
  apply Permutation_trans with (map (fun id => nth id l d) (seq O (length l))).
  rewrite <- seq_nth_equal; apply Permutation_refl.
  apply Permutation_map; trivial.
Qed.

Lemma nth_In_exists : forall (l:list A) (a d:A),
  In a l -> exists n, n < length l /\ a = (nth n l d).
Proof.
  intros. induction l; simpl in *. contradict H.
  destruct H. rewrite H. exists 0; split; trivial. omega.
  apply IHl in H. destruct H as [n []].
  exists (S n). split. omega. auto.
Qed.

Lemma map_incl: forall (f:A-> B)(l1 l2: list A),
  incl l1 l2 ->
  incl (map f l1) (map f l2).
Proof.
  unfold incl. intros.
  apply in_map_iff in H0. destruct H0 as [x [H0 H1]].
  subst a. apply in_map; auto.
Qed.

Lemma  permutation_nodup: forall (l1 l2: list A),
  NoDup l1 ->
  Permutation l1 l2 ->
  NoDup l2.
Proof.
  intros l1. elim l1. intros. apply Permutation_nil in H0. rewrite H0. constructor.
  intros.
  assert (Hin: In a l2).
    apply (Permutation_in a)  in H1. trivial. apply in_eq.
  apply In_split in Hin. inversion_clear Hin as [x1 Hin0].
  destruct Hin0 as [x2 Hin].
  assert (Hp: Permutation l (x1 ++ x2)).
    rewrite Hin in H1. apply Permutation_cons_app_inv with a; trivial.
  assert (Hnd: NoDup (x1 ++ x2)).
    inversion H0. apply H;  trivial.
  assert (Hnin: ~ In a (x1 ++ x2)).
    unfold not. inversion H0. intros Hin0. apply Permutation_sym in Hp.
    apply (Permutation_in a) in Hp. contradict Hp. trivial. trivial.
  rewrite Hin. clear - a x1 x2 Hnd Hnin.
  induction x1; simpl in *; constructor; trivial. inversion Hnd.
  assert (HA: ~ (a0 = a \/ In a (x1 ++ x2)) -> ~ (a0 = a \/ In a x1 \/ In a x2)).
    intuition.
  assert (HB: ~ (In a0 (x1 ++ x2)) -> ~ (In a0 x1 \/ In a0 x2)).
    intros. unfold not. intros. apply in_or_app in H4. contradict H4. trivial.
  assert (HC: ~ (In a0 x1 \/ In a0 (a :: x2)) -> ~ (In a0 (x1 ++ a :: x2))).
    intros. unfold not. intros. apply in_app_or in H4. contradict H4. trivial.
  apply HA in Hnin. subst. red; intros. apply in_app_or in H. simpl in H.
  destruct H as [? | [? | ?]]; auto;
  red in H1; apply H1; apply in_or_app; auto.
  apply IHx1. inversion Hnd. trivial. simpl in Hnin.
  intuition.
Qed.

Lemma map_nodup_find_eq: forall (l: list A)(a b: A)(f: A -> B),
  NoDup (map f l) ->
  In a l ->
  In b l ->
  f a = f b ->
  a = b.
Proof.
  induction l; simpl; intros.
  +destruct H0.
  +inversion_clear H. destruct H0; destruct H1;subst;eauto.
   -apply in_map with (B:=B) (f:=f) in H0.
    rewrite H2 in *. congruence.
   -apply in_map with (B:=B) (f:=f) in H.
    rewrite H2 in *. congruence.
Qed.

Lemma flat_map_app: forall (f:A->list B)(l1 l2: list A),
  flat_map f (l1 ++ l2) = (flat_map f l1) ++ (flat_map f l2).
Proof.
  intros. induction l1; simpl. trivial.
  rewrite IHl1. apply ass_app.
Qed.

Lemma flat_map_permutation: forall (f:A->list B)(l1 l2: list A),
  Permutation l1 l2->
  Permutation (flat_map f l1) (flat_map f l2).
Proof.
  induction 1; simpl. constructor.
  apply Permutation_app_head; trivial.
  repeat rewrite <- app_ass; apply Permutation_app_tail; apply Permutation_app_swap.
  apply Permutation_trans with (flat_map f l'); trivial.
Qed.

Lemma flat_map_incl: forall (f:A->list B) (l1 l2: list A),
  incl l1 l2 ->
  incl (flat_map f l1) (flat_map f l2).
Proof.
  unfold incl. intros. generalize (in_flat_map f l2 a).
  intros Hfml. inversion_clear Hfml as [Hfml1 Hfml2]. apply Hfml2.
  generalize (in_flat_map f l1 a).
  intros Hfml'. inversion_clear Hfml' as [Hfml1' Hfml2']. apply Hfml1' in H0.
  clear Hfml1 Hfml2 Hfml1' Hfml2'.
  inversion_clear H0. inversion_clear H1. apply H in H0. eauto.
Qed.

Lemma flat_map_in: forall (l: list A)(f:A->list B) (a:A),
  In a l ->
  incl (f a) (flat_map f l).
Proof.
  unfold incl.
  induction l; simpl; intros; auto.
  apply in_or_app.
  destruct H; subst;auto.
  right. apply IHl with a0; auto.
Qed.

Lemma flat_map_map: forall (f:A-> B)(g:B->list C) l,
  flat_map g (map f l) = flat_map (fun x => g (f x)) l.
Proof.
  induction l; simpl; intros. trivial.
  rewrite IHl. trivial.
Qed.

Lemma flat_map_simpl: forall (f:A-> B)(l: list A),
  flat_map (fun x=> f x :: nil) l = map f l.
Proof.
  induction l; simpl; intros; auto.
Qed.

Lemma map_ext2 : forall (f g:A->B)(l: list A),
  (forall a, In a l -> f a = g a) -> map f l = map g l.
Proof.
  induction l; simpl; auto. intros.
  rewrite H. rewrite IHl; auto. auto.
Qed.

Lemma map_ext3 : forall (f:A->B)(l1 l2: list A)(d: A),
  length l1 = length l2 ->
  (forall i, i < length l1 -> f (nth i l1 d) = f (nth i l2 d)) ->
  map f l1 = map f l2.
Proof.
  induction l1; induction l2; auto; intros;
  try (contradict H; simpl; omega).
  assert (0 < length (a :: l1)). simpl. omega.
  apply H0 in H1. simpl in H1. simpl.
  rewrite H1, IHl1 with l2 d; auto. intros.
  assert (S i < length (a :: l1)). simpl. omega.
  apply H0 in H3. simpl in H3. trivial.
Qed.

Lemma existsb_false_inv: forall (f :A->bool)(l: list A),
  existsb f l = false ->
  (forall (a: A),In a l -> f a = false ).
Proof.
  intros Hf l Hex. induction l; simpl; intros. contradict H.
  simpl in Hex. apply orb_false_elim in Hex. inversion_clear Hex.
  elim H; intros. rewrite <- H2; trivial.
  apply IHl; trivial.
Qed.

Lemma existsb_false: forall  (f :A->bool) (l: list A),
  (forall a,In a l -> f a = false ) ->
  existsb f l = false.
Proof.
  induction l; simpl; trivial.
  intros; rewrite orb_false_intro; trivial.
  apply (H a). auto.
  apply IHl. intros. apply (H a0). right. trivial.
Qed.

Lemma existsb_incl: forall (f :A->bool)(l1 l2: list A),
  incl l1 l2 ->
  existsb f l2 = false ->
  existsb f l1 = false.
Proof.
  intros Hf l1 l2 Hincl Hex. induction l1;simpl. trivial.
  apply orb_false_intro.
  apply (existsb_false_inv Hf l2 ) with a in Hex; auto.
  apply Hincl; simpl; auto.
  apply IHl1. apply incl_tran with (a :: l1).
  apply incl_tl. apply incl_refl. trivial.
Qed.

Lemma existsb_app: forall (f :A->bool)(l1 l2: list A),
  existsb f (l1 ++ l2) = existsb f l1 || existsb f l2.
Proof.
  intros. induction l1; simpl. trivial.
  rewrite IHl1. rewrite orb_assoc. trivial.
Qed.

Lemma existsb_equal: forall (f g:A->bool)(l: list A),
  (forall a, f a = g a) ->
  existsb f l = existsb g l.
Proof.
  induction l; simpl; intros; trivial.
  rewrite H with a. rewrite IHl;trivial.
Qed.

Lemma existsb_equal_app: forall (f g h:A->bool)(l: list A),
  (forall a, f a = g a || h a) ->
  existsb f l = existsb g l || existsb h l.
Proof.
  induction l; simpl; intros; trivial.
  rewrite H with a. rewrite IHl;trivial.
  destruct (h a);
  try (repeat (rewrite orb_true_r || rewrite orb_true_l)). trivial.
  try (repeat (rewrite orb_false_r || rewrite orb_false_l)).
  rewrite orb_assoc; trivial.
Qed.

Lemma existsb_perm: forall (f :A->bool)(l1 l2: list A),
  Permutation l1 l2->
  existsb f l1 = existsb f l2.
Proof.
  induction 1; simpl; trivial.
  rewrite IHPermutation; trivial.
  repeat rewrite orb_assoc.
  replace (f y || f x) with ( f x || f y).
  trivial. apply orb_comm.
  transitivity (existsb f l'); trivial.
Qed.

Lemma find_some_true: forall (f: A->bool)(l:list A)(x: A),
  find f l = Some x -> f x = true.
Proof.
  induction l; simpl; intros. congruence.
  destruct (f a) eqn:?; auto. congruence.
Qed.

Lemma find_some_in: forall (f: A->bool)(l:list A)(x: A),
  find f l = Some x -> In x l.
Proof.
  induction l; simpl; intros. congruence.
  destruct (f a) eqn:?; auto. left. congruence.
Qed.

Lemma find_some_app: forall (f: A->bool)(l1 l2:list A)(x: A),
  find f l1 = Some x -> find f (l1 ++ l2) = Some x.
Proof.
  induction l1; simpl; intros. inversion H.
  destruct (f a); auto.
Qed.

Lemma firstn_nil: forall (n : nat),
  firstn n (@nil A)  = (@nil A).
Proof.
  induction n; simpl; trivial.
Qed.

Lemma skipn_nil: forall (n : nat),
  skipn n (@nil A)  = (@nil A).
Proof.
  induction n; simpl; trivial.
Qed.

Lemma firstn_length_app1: forall (n: nat)(l1 l2: list A),
  n <= length l1 ->
  firstn n (l1 ++ l2)  = firstn n l1.
Proof.
  induction n; trivial.
  induction l1; simpl; intros.
  inversion H.
  f_equal. apply IHn; omega.
Qed.

Lemma firstn_length_app2: forall (n: nat)(l1 l2: list A),
  length l1 <= n ->
  firstn n (l1 ++ l2)  = l1 ++ firstn (n - length l1) l2.
Proof.
  induction n; induction l1; simpl; intros; auto.
  inversion H.
  f_equal. apply IHn; omega.
Qed.

Lemma firstn_firstn: forall (m n: nat)(l: list A),
  firstn m (firstn n l) = firstn (min m n) l.
Proof.
  induction m. simpl. auto.
  induction n. simpl. auto.
  induction l; simpl; auto. rewrite IHm. auto.
Qed.

Lemma skipn_firstn_nil: forall (l: list A)(m n: nat),
  n <= m ->
  skipn m (firstn n l) = nil.
Proof.
  induction l;simpl; intros.
  rewrite firstn_nil, skipn_nil; auto.
  destruct n; simpl. rewrite skipn_nil; auto.
  destruct m; simpl. inversion H.
  apply IHl; omega.
Qed.

Lemma skipn_firstn: forall (n: nat)(l: list A),
  skipn n (firstn n l) = nil.
Proof.
  intros. apply skipn_firstn_nil; auto.
Qed.

Lemma skipn_bign: forall (n: nat)(l: list A),
  length l <= n  -> skipn n l = nil.
Proof.
  induction n.
  simpl; auto. intros. destruct l; simpl in *; auto; omega.
  induction l; simpl; intros. trivial.
  apply IHn. omega.
Qed.

Lemma skipn_length_app: forall (n: nat)(l l': list A) ,
  length l <= n  -> skipn n (l++l') = skipn (n-length l) l'.
Proof.
  induction n; induction l; simpl; intros; try (inversion H; fail); auto.
  apply IHn; try omega.
Qed.

Lemma skipn_length_app2: forall (n: nat)(l l': list A),
  n <= length l -> skipn n (l++l') = skipn n l ++ l'.
Proof.
  induction n. simpl; auto.
  induction l; intros.
  inversion H.
  simpl in *. apply IHn; omega.
Qed.

Lemma firstn_skipn_swap: forall (m n: nat)(l: list A),
  skipn m (firstn (m + n) l) = firstn n (skipn m l).
Proof.
  induction m. simpl. auto.
  induction n; induction l; simpl; trivial.
  replace (m + 0) with m; try omega.
  rewrite skipn_bign; trivial.
  rewrite firstn_length. apply Min.le_min_l.
  rewrite IHm. destruct (skipn m l); simpl; trivial.
Qed.

Lemma firstn_app: forall (m n: nat)(l: list A),
  firstn (m + n) l = firstn m l ++ firstn n (skipn m l).
Proof.
  intros. rewrite <- firstn_skipn with _ m (firstn (m + n) l).
  rewrite firstn_firstn. replace (min m (m + n)) with m.
  rewrite firstn_skipn_swap; auto.
  rewrite min_l; omega.
Qed.

Lemma skipn_add: forall (m n : nat)(l: list A),
  skipn (m + n) l = skipn n (skipn m l).
Proof.
  induction m. simpl. trivial.
  induction l. repeat rewrite skipn_nil. trivial.
  simpl. auto.
Qed.

Lemma skipn_app: forall (m n: nat)(l: list A),
  skipn m l = firstn n (skipn m l) ++ skipn (m + n) l.
Proof.
  intros. rewrite skipn_add. rewrite firstn_skipn. trivial.
Qed.

Lemma firstn_sube: forall (m n: nat)(l1 l2: list A),
  m <= n ->
  firstn n l1 = firstn n l2 ->
  firstn m l1 = firstn m l2.
Proof.
  induction m; induction n; induction l1; induction l2;
  intros; auto; try (inversion H; fail).
  rewrite firstn_nil in H0; simpl in H0; inversion H0.
  rewrite firstn_nil in H0; simpl in H0; inversion H0.
  simpl in *. inversion H0. f_equal.
  apply IHm with n; auto; omega.
Qed.

Lemma skipn_sube: forall (m n: nat)(l1 l2: list A),
  n <= m ->
  skipn n l1 = skipn n l2 ->
  skipn m l1 = skipn m l2.
Proof.
  intros. replace m with (n+(m-n)); try omega.
  repeat rewrite skipn_add. rewrite H0; auto.
Qed.

Lemma nth_error_value_lt: forall (l: list A),
  forall n x, nth_error l n = value x ->
  n < length l.
Proof.
  induction l; induction n; simpl; intros; auto.
  inversion H. inversion H. omega.
  apply IHl in H. try omega.
Qed.

Lemma nth_error_app1: forall (l1 l2: list A),
  forall n, n < length l1 ->
  nth_error (l1++l2) n = nth_error l1 n.
Proof.
  induction l1; induction n; simpl; intros; auto.
  inversion H. inversion H.
  apply IHl1; try omega.
Qed.

Lemma nth_error_app2: forall (l1 l2: list A),
  forall n, length l1 <= n ->
  nth_error (l1++l2) n = nth_error l2 (n- length l1).
Proof.
  induction l1; induction n; simpl; intros; auto.
  inversion H.
  apply IHl1; try omega.
Qed.


Lemma firstn_bign: forall (n: nat)(l: list A),
  length l <= n -> l = firstn n l.
Proof.
  induction n.
  simpl; auto. intros. destruct l; simpl in *; auto; omega.
  induction l; simpl; intros. trivial.
  f_equal. apply IHn. omega.
Qed.

Lemma skipn_nth: forall (l: list A)(d: A),
  0 < length l ->
  l = nth 0 l d :: skipn 1 l.
Proof.
  induction l; simpl; intros; [contradict H; omega | trivial].
Qed.

Lemma skipn_length : forall (n: nat) (l: list A),
  length (skipn n l) = (length l) - (min n (length l)).
Proof.
  intros.
  assert (length ((firstn n l) ++ (skipn n l)) = length l).
    rewrite firstn_skipn. trivial.
  rewrite app_length in H. rewrite firstn_length in H. omega.
Qed.

Lemma skipn_nth_app: forall (n: nat)(d: A)(l: list A),
  n < length l ->
  skipn n l=  (nth n l d) :: skipn (n + 1) l.
Proof.
  induction n.
  simpl; intros. destruct  l; simpl; trivial.
  contradict H. simpl. omega.
  destruct l;simpl; intros. contradict H. omega.
  rewrite (IHn d l). trivial. omega.
Qed.

Lemma map_firstn: forall (f: A -> B)(l: list A)(n: nat),
  map f (firstn n l) = firstn n (map f l).
Proof.
  induction l; simpl; induction n; simpl;auto.
  rewrite IHl. trivial.
Qed.

Lemma map_skipn: forall (f: A -> B)(l: list A)(n: nat),
  map f (skipn n l) = skipn n (map f l).
Proof.
  induction l; simpl; induction n; simpl;auto.
Qed.

Lemma map_app_inv: forall (f: A -> B)(l: list A)(bl1 bl2: list B),
  map f l = bl1 ++ bl2 ->
  exists l1 l2, map f l1 = bl1
    /\ map f l2 = bl2
    /\ l = l1 ++ l2.
Proof.
  induction l; simpl; intros.
  +symmetry in H. apply app_eq_nil in H.
   destruct H. subst. exists nil,nil; split ;auto.
  +destruct bl1; simpl in *.
   -subst. exists nil, (a::l).
    split; auto.
   -inversion H. destruct IHl with bl1 bl2 as [l1 [l2 [? [? ?]]]]; auto.
    subst. exists (a::l1), l2. split; auto.
Qed.

Lemma map_nth2 : forall (f: A -> B)(l: list A) (d1: B)(d2: A),
  forall n, n < length l ->
  nth n (map f l) d1 = f (nth n l d2).
Proof.
  intros. rewrite nth_indep with _ _ _ _ (f d2).
  apply map_nth. rewrite map_length; auto.
Qed.

Lemma firstn_app_nth: forall (n: nat)(d: A)(l: list A),
  n  < length l ->
  firstn (n + 1) l= firstn n l ++ (nth n l d :: nil).
Proof.
  induction n.
  simpl; intros. destruct  l; simpl; trivial.
  contradict H. simpl. omega.
  destruct l;simpl; intros. contradict H. omega.
  rewrite (IHn d l). trivial. omega.
Qed.

Lemma nth_firstn: forall (m n:nat)(d: A)(l: list A),
  m < n -> nth m (firstn n l) d = nth m l d.
Proof.
  induction m; induction l; try (rewrite firstn_nil; auto);
  induction n; intros; try (contradict H; omega); simpl.
  trivial. apply IHm. omega.
Qed.

Lemma nth_skipn: forall (m n: nat)(d: A)(l: list A),
  nth m (skipn n l) d = nth (m + n) l d.
Proof.
  induction m; induction n; induction l; simpl; auto.
  rewrite plus_0_r in *. trivial.
  replace (m + S n) with (S m + n). apply IHn. omega.
Qed.

Lemma nth_list_eq: forall (l1 l2: list A)(d: A),
  length l1 = length l2 ->
  (forall n, nth n l1 d = nth n l2 d) ->
  l1 = l2.
Proof.
  induction l1; induction l2; simpl; intros; auto.
  inversion H.
  inversion H.
  rewrite H0 with 0. f_equal.
  apply IHl1 with d; auto.
  intros. generalize (H0 (S n)); simpl; intros; auto.
Qed.


Lemma partition_permutation: forall (f : A -> bool)(l l1 l2: list A),
  (l1,l2) = partition f l ->
  Permutation l (l1 ++ l2).
Proof.
  induction l; simpl; intros.
  injection H; intros; rewrite H0, H1.
  simpl; apply Permutation_refl.
  destruct (partition f l); destruct (f a);
  injection H; intros; rewrite H0, H1; simpl;
  [constructor |  apply Permutation_cons_app];
  apply IHl; trivial.
Qed.

Lemma filter_app:
  forall (f: A -> bool) l1 l2, filter f (l1++l2) = filter f l1 ++ filter f l2.
Proof.
  induction l1; simpl; intros; auto.
  destruct (f a); simpl; auto. f_equal; auto.
Qed.

Lemma fold_left_swap_sup : forall (f: A -> B -> A)(g: A -> C -> A)(l:list C)(i:A)(a: B),
  (forall x y j, g (f j x) y = f (g j y) x) ->
  fold_left g l (f i a) = f (fold_left g l i) a.
Proof.
  induction l; intros; simpl in *. trivial.
  rewrite <- IHl with (g i a) a0; trivial.
  rewrite H; trivial.
Qed.

Lemma fold_left_swap : forall (f: A -> B -> A)(g: A -> C -> A)(l1:list B)(l2:list C)(i:A),
  (forall x y j, g (f j x) y = f (g j y) x) ->
  fold_left g l2 (fold_left f l1 i) = fold_left f l1 (fold_left g l2 i).
Proof.
  induction l1; intros; simpl in *. trivial.
  rewrite IHl1 with l2 (f i a); trivial.
  rewrite fold_left_swap_sup; trivial.
Qed.

Lemma fold_left_equal : forall (f g: A -> B -> A)(l:list B)(i:A),
  (forall x j, f j x =  g j x) ->
  fold_left g l i = fold_left f l i.
Proof.
  induction l; intros; simpl in *. trivial.
  rewrite H, IHl; trivial.
Qed.

Lemma incl_splitl : forall (l1 l2 l: list A),
  incl (l1 ++ l2) l -> incl l1 l.
Proof.
  intros. apply incl_tran with (l1 ++ l2); auto.
  apply incl_appl. apply incl_refl.
Qed.

Lemma incl_splitr : forall (l1 l2 l: list A),
  incl (l1 ++ l2) l -> incl l2 l.
Proof.
  intros. apply incl_tran with (l1 ++ l2); auto.
  apply incl_appr. apply incl_refl.
Qed.

Lemma incl_split : forall (l1 l2 l: list A),
  incl (l1 ++ l2) l -> incl l1 l /\ incl l2 l.
Proof.
  intros. split.
  apply incl_splitl with l2; auto.
  apply incl_splitr with l1; auto.
Qed.

End ListExtra.

Lemma flat_map_seq_nth_fun_equal : forall (A B: Type) (f:A->list B) (l: list A)(d: A),
  flat_map f l = (flat_map (fun id => f (nth id l d)) (seq O (length l))).
Proof.
  intros. rewrite <- flat_map_map with _ _ _ (fun id => nth id l d) f _.
  rewrite <- seq_nth_equal. trivial.
Qed.

Lemma seq_forall_lt: forall (A: Type)(l: list A)(n: nat),
  forall x, In x (seq (S n) (length l)) -> n < x.
Proof.
  induction l; simpl; intros; destruct H.
  subst. omega.
  apply lt_trans with (S n); auto.
Qed.

Lemma seq_forall_range: forall (A: Type)(l: list A)(n: nat),
  forall x i, In x (seq i n) -> (x < i + n)%nat.
Proof.
  induction n; simpl; intros; destruct H.
  subst. omega.
  replace (i+ S n)%nat with (S i + n)%nat; try omega.
  apply IHn; auto.
Qed.

Lemma seq_nodup: forall (A: Type)(l: list A)(n: nat),
  NoDup (seq n (length l)).
Proof.
  induction l; simpl; constructor; auto.
  red; intros.
  apply seq_forall_lt in H; omega.
Qed.

Section ListUtils.

Variable A B: Type.
Variable f: A -> option B.

Definition slice (l: list A)(i j: nat) : list A :=
  skipn i (firstn j l).

Definition replace_nth (l: list A) (n: nat) (a: A) : list A :=
  (firstn n l) ++ (a :: (skipn (S n) l)).

Definition replace_map (l l1: list A)(n: nat): list A :=
  (firstn n l) ++ l1 ++ (skipn (n+length l1) l).

Definition getn (n p: nat)(l: list A) : list A :=
  firstn n (skipn p l).

Fixpoint omap (l: list A): option (list B) :=
  match l with
  | nil => Some nil
  | hd :: tl =>
    match (f hd), (omap tl) with
    | Some hd', Some tl' => Some (hd' :: tl')
    | _, _ => None
    end
  end.

Lemma replace_nth_shift:
  forall eh et ord ef,
  replace_nth (eh :: et) (S ord) ef = eh :: (replace_nth et ord ef).
Proof.
  unfold replace_nth. intros. simpl firstn.
  rewrite <-app_comm_cons; auto.
Qed.

Lemma replace_nth_error_self:
  forall l i a,
  nth_error l i = value a ->
  replace_nth l i a = l.
Proof.
  induction l,i; simpl; intros; try (inversion H; fail).
  inversion H; eauto.
  rewrite replace_nth_shift, IHl; auto.
Qed.

Lemma replace_nth_nil:
  forall ord a,
  replace_nth nil ord a = a::nil.
Proof.
  unfold replace_nth. simpl. intros.
  rewrite firstn_nil. auto.
Qed.

Lemma replace_nth_length_eq:
  forall l ord a,
  ord < length l ->
  length (replace_nth l ord a) = length l.
Proof.
  unfold replace_nth. intros.
  rewrite app_length, firstn_length.
  replace (S ord) with (ord+1); try omega.
  simpl. rewrite Min.min_l; try omega.
  rewrite skipn_length. rewrite Min.min_l; try omega.
Qed.

Lemma replace_map_length_eq:
  forall l l1 ord,
  ord <= length l ->
  length (replace_map l l1 ord) = max (ord + length l1) (length l).
Proof.
  unfold replace_map. intros.
  rewrite app_length, firstn_length, app_length.
  rewrite skipn_length. rewrite Min.min_l; try omega.
  assert (ord+length l1 < length l \/ length l <= ord + length l1).
    omega.
  destruct H0.
  rewrite Min.min_l; try omega.
  rewrite Max.max_r; try omega.

  rewrite Max.max_l; try omega.
  rewrite Min.min_r; try omega.
Qed.

Lemma replace_map_all_eq:
  forall l l1 l2,
  length l1 = length l2 -> length l1 <= length l ->
  replace_map l1 l 0 = replace_map l2 l 0.
Proof.
  unfold replace_map. simpl; intros.
  f_equal. repeat rewrite skipn_bign; try omega.
  auto.
Qed.

Lemma Forall_nth_error:
  forall l i a (P: A-> Prop),
  nth_error l i = value a ->
  Forall P l ->
  P a.
Proof.
  induction l; induction i; simpl; intros.
  inversion H.
  inversion H.
  inversion H. subst. inversion_clear H0; auto.
  inversion_clear H0. apply IHl with i; auto.
Qed.


Lemma replace_map_length:
  forall se se1 ord,
  length se <= length (replace_map se se1 ord).
Proof.
  unfold  replace_map. intros.
  generalize (firstn_skipn ord se). intros.
  rewrite <-H at 1.
  repeat (rewrite app_length).
  rewrite skipn_length, skipn_length.
  assert (ord <= length se \/ length se < ord). omega.
  assert (ord + length se1 <= length se \/ length se < ord + length se1). omega.
  destruct H0;destruct H1.
  rewrite Min.min_l; auto. rewrite Min.min_l;auto. omega.
  rewrite Min.min_l; auto. rewrite Min.min_r; try omega.
  rewrite Min.min_r; try omega.
  rewrite Min.min_r; try omega.
Qed.

Remark omap_inversion:
  forall (l: list A) (l': list B),
  omap l = Some l' ->
  Forall2 (fun x y => f x = Some y) l l'.
Proof.
  induction l; induction l'; simpl; intros; try congruence.
  constructor.
  remember (f a) as p. destruct p; try congruence.
  remember (omap l) as q. destruct q; try congruence.
  remember (f a) as p. destruct p; try congruence.
  remember (omap l) as q. destruct q; try congruence.
  inversion H. subst. constructor; auto.
Qed.

Lemma getn_length:
  forall l p n,
  0 <= p -> p + n <= length l ->
  length (getn n p l) = n.
Proof.
  unfold getn. intros.
  rewrite firstn_length, skipn_length.
  rewrite Min.min_l; auto.
  rewrite Min.min_l; omega.
Qed.

End ListUtils.

Lemma Forall_app:
  forall (A: Type)(P: A -> Prop) l1 l2,
  Forall P (l1++l2) <-> Forall P l1 /\ Forall P l2.
Proof.
  induction l1; simpl; intros; auto.
  split; intros; auto. destruct H; auto.
  split; intros.
  inversion_clear H. apply IHl1 in H1.
  destruct H1. split; auto.
  destruct H. inversion_clear H.
  constructor; auto. apply IHl1; auto.
Qed.

Lemma Forall_permut:
  forall (A: Type)(P: A -> Prop) l1 l2,
  Forall P l1 ->
  Permutation l1 l2 ->
  Forall P l2.
Proof.
  intros. apply Forall_forall.
  intros. apply Permutation_sym in H0.
  apply Permutation_in with _ _ _ x in H0; auto.
  apply ->Forall_forall; eauto.
Qed.

Theorem Forall_firstn:
  forall A (P:A->Prop) l,
  Forall P l ->
  forall n,
  Forall P (firstn n l).
Proof.
  induction 1; simpl; intros.
  repeat rewrite firstn_nil. constructor.
  destruct n; simpl; constructor; auto.
Qed.

Theorem Forall_skipn:
  forall A (P:A->Prop) l,
  Forall P l ->
  forall n,
  Forall P (skipn n l).
Proof.
  induction 1; simpl; intros.
  repeat rewrite skipn_nil. constructor.
  destruct n; simpl; auto.
Qed.

Lemma Forall_replace:
  forall (A: Type)(P: A -> Prop) l a i,
  Forall P l ->
  P a ->
  Forall P (replace_nth l i a).
Proof.
  unfold replace_nth. intros.
  apply Forall_forall; intros.
  apply in_app_or in H1. destruct H1 as [? | [? | ?]]; subst; auto.
  eapply Forall_forall; eauto. rewrite <-firstn_skipn with _ i _.
   apply in_or_app; auto.
  eapply Forall_forall; eauto. rewrite <-firstn_skipn with _ (S i) _.
   apply in_or_app; auto.
Qed.

Lemma Forall_nth:
  forall (A: Type)(P: A -> Prop) l,
  Forall P l ->
  forall i d,
  P d ->
  P (nth i l d).
Proof.
  induction 1; simpl; intros; destruct i; try omega; auto.
Qed.

Lemma Forall2_length:
  forall (A B: Type)(P: A -> B -> Prop) l1 l2,
  Forall2 P l1 l2 ->
  length l1 = length l2.
Proof.
  induction 1; simpl; auto.
Qed.

Lemma Forall2_ext:
  forall (A B: Type)(P1 P2: A -> B -> Prop) l1 l2,
  Forall2 P1 l1 l2 ->
  (forall a b, P1 a b -> P2 a b) ->
  Forall2 P2 l1 l2.
Proof.
  induction 1; simpl; auto.
Qed.

Lemma Forall2_nth:
  forall (A B: Type)(P: A -> B -> Prop) l1 l2,
  Forall2 P l1 l2 ->
  forall i d1 d2,
  P d1 d2 ->
  P (nth i l1 d1) (nth i l2 d2).
Proof.
  induction 1; simpl; intros; destruct i; auto.
Qed.

Lemma Forall2_nth_in:
  forall (A B: Type)(P: A -> B -> Prop) l1 l2,
  Forall2 P l1 l2 ->
  forall i d1 d2,
  i < length l1 ->
  P (nth i l1 d1) (nth i l2 d2).
Proof.
  induction 1; simpl; intros; destruct i; try omega; auto.
  apply IHForall2; auto. omega.
Qed.

Lemma Forall2_nth_error_exists:
  forall (A B: Type) i l1 l2 x (P: A -> B -> Prop),
  Forall2 P l1 l2 ->
  nth_error l1 i = value x ->
  exists y, nth_error l2 i = value y
    /\ P x y.
Proof.
  induction i; induction 1; simpl; intros; eauto; try inversion H.
  inversion H1. subst. exists y. split; auto.
Qed.

Lemma Forall2_replace:
  forall (A B: Type)(P: A -> B -> Prop) l1 l2,
  Forall2 P l1 l2 ->
  forall i a b,
  P a b ->
  Forall2 P (replace_nth l1 i a) (replace_nth l2 i b).
Proof.
  induction 1; simpl; intros.
  unfold replace_nth, replace_nth.
  repeat rewrite firstn_nil; simpl.
  constructor; auto.

  destruct i; unfold replace_nth, replace_nth in *.
  simpl. constructor; auto.
  simpl firstn. repeat rewrite <- app_comm_cons. constructor; auto.
  apply IHForall2 with i _ _ in H1; auto.
Qed.

Theorem Forall2_firstn:
  forall A B (R:A->B->Prop) l1 l2,
  Forall2 R l1 l2 ->
  forall n,
  Forall2 R (firstn n l1) (firstn n l2).
Proof.
  induction 1; simpl; intros.
  repeat rewrite firstn_nil. constructor.
  destruct n; simpl; constructor; auto.
Qed.

Theorem Forall2_skipn:
  forall A B (R:A->B->Prop) l1 l2,
  Forall2 R l1 l2 ->
  forall n,
  Forall2 R (skipn n l1) (skipn n l2).
Proof.
  induction 1; simpl; intros.
  repeat rewrite skipn_nil. constructor.
  destruct n; simpl; auto.
Qed.

Theorem Forall2_app_inv:
  forall A B (R:A->B->Prop) l1 l2 l3 l4,
  Forall2 R (l1++l2) (l3++l4) ->
  length l1 = length l3 ->
  Forall2 R l1 l3 /\ Forall2 R l2 l4.
Proof.
  induction l1; simpl; intros.
  +destruct l3; simpl in *; try omega. split; auto.
  +destruct l3; simpl in *; try omega. inversion H.
   subst. destruct IHl1 with l2 l3 l4; auto.
Qed.
