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
Require Import List.
Require Import ExtraList.
Require Import Permutation.
Require Import Cltypes.
Require Import Ltypes.

Set Implicit Arguments.

Definition ACG_DEST     :=  7%positive.   (**r dest address of input parameters in memcpy function：acg_dest*)
Definition ACG_SRC      :=  8%positive.   (**r src address of input parameters in memcpy function：acg_src*)
Definition ACG_SIZE     :=  9%positive.   (**r copy size of input parameters in memcpy function：acg_size*)
Definition ACG_D        :=  10%positive.  (**r dest address of local variables in memcpy function：acg_d*)
Definition ACG_S        :=  11%positive.  (**r src address of local variables in memcpy function：acg_s*)

Definition ACG_MEMCPY   :=  12%positive.  (**r name of memcpy function: acg_memcpy*)

Definition OUTSTRUCT    :=  13%positive.  (**r name of output struct in main node: outC*)
Definition ACG_J        :=  14%positive.  (**r loop variable for fbyn initiation： acg_j*)
Definition ACG_INIT     :=  15%positive.  (**r flag variable for first cycle of tempo expr: acg_init*)
Definition FBYIDX       :=  16%positive.  (**r loop counter for fbyn: idx*)
Definition FBYITEM      :=  17%positive.  (**r array name for fbyn: item*)

Definition INSTRUCT     :=  18%positive.  (**r name of input struct in main node: inC*)
Definition ACG_I        :=  19%positive.  (**r loop variable for high order stmtement： acg_i*)
Definition ACG_B        :=  20%positive.  (**r flag variable for mapw stmtement： acg_b*)

Definition ACG_LOCAL    :=  21%positive.  (**r local variable in acgcmp function：acg_local*)
Definition ACG_C1       :=  22%positive.  (**r first input parameter in acgcmp function：acg_c1*)
Definition ACG_C2       :=  23%positive.  (**r second input parameter in acgcmp function：acg_c2*)
Definition ACG_EQU      :=  24%positive.  (**r output parameter in acgcmp function：acg_equ*)

Definition in_struct_type(nid: ident) := Pplus nid 1.    (**r NID + 1 inC_<operator>*)
Definition out_struct_type(nid: ident) := Pplus nid 2. (**r NID + 2  outC_<operator>*)
Definition reset_id (nid: ident) := Pplus nid 3.       (**r NID + 3 acg_<node>_reset*)
Definition comp_funcs_id (tid: ident) := Pplus tid 1.  (**r TID + 1 comp_funcs__<operator>*)

Definition Plt (x y: positive): Prop := Zlt (Zpos x) (Zpos y).
Definition Ple (p q: positive) := Zle (Zpos p) (Zpos q).

Remark Psucc_Zsucc:
  forall (x: positive), Zpos (Psucc x) = Zsucc (Zpos x).
Proof.
  intros. rewrite Pplus_one_succ_r.
  reflexivity.
Qed.

Definition ids_plt(pid: ident)(l: list ident) :=
  forall id, In id l -> Plt pid id.

Lemma ids_plt_le_notin:
  forall id pid l, Ple id pid -> ids_plt pid l ->
  ~ In id l.
Proof.
  unfold ids_plt. intros.
  red; intros. apply H0 in H1.
   unfold Ple, Plt in *. omega.
Qed.

Lemma ids_plt_trans:
  forall id1 id2 l,
  ids_plt id1 l ->
  Ple id2 id1 ->
  ids_plt id2 l.
Proof.
  unfold ids_plt; intros.
  apply H in H1.
  unfold Plt, Ple in *. omega.
Qed.

Section ID_FIND.

Definition identeq : ident -> ident -> bool := Pos.eqb.

Definition in_list(id: ident)(idl: list ident): bool :=
  existsb (fun id' => identeq id' id) idl.

Definition list_in_list (lx ly: list ident): bool :=
  existsb (fun id => in_list id ly) lx.

Lemma in_list_true_in:
  forall id vids,
  in_list id vids = true <-> In id vids.
Proof.
  unfold in_list. intuition.
  apply existsb_exists in H.
  destruct H as [x []].
  apply Peqb_eq in H0. subst. auto.
  apply existsb_exists.
  exists id; intuition. apply Peqb_eq. auto.
Qed.

Lemma in_list_false_notin:
  forall id vids,
  in_list id vids = false <-> ~ In id vids.
Proof.
  induction vids; simpl; split; intros; auto.
  apply orb_false_elim in H.
  destruct H. unfold not.
  intros. destruct H1.
  apply IHvids in H0.
  subst. rewrite Peqb_refl in H. congruence.
  apply IHvids in H0; auto.

  destruct IHvids. rewrite H1; auto.
  apply orb_false_intro; auto.
  apply Pos.eqb_neq. intuition.
Qed.

Lemma in_list_app: forall (x:ident)(l1 l2: list ident),
  in_list x (l1 ++ l2) = in_list x l1 || in_list x l2.
Proof.
  intros. apply existsb_app.
Qed.

Lemma in_list_perm: forall (x:ident)(l1 l2: list ident),
  Permutation l1 l2 ->
  in_list x l1 = in_list x l2.
Proof.
  intros.
  apply existsb_perm; auto.
Qed.

Lemma field_offset_in_list_false:
  forall al id msg,
  field_offset id (fieldlist_of al) = Error msg ->
  in_list id (map fst al) = false.
Proof.
  intros. apply fieldlist_list_notin in H.
  apply existsb_false. intros.
  apply Pos.eqb_neq; eauto.
  red; intros. subst; auto.
Qed.

Lemma field_offset_in_list_true:
  forall al id delta,
  field_offset id (fieldlist_of al) = OK delta ->
  in_list id (map fst al) = true.
Proof.
  intros. apply in_list_true_in; auto.
  destruct field_offset_type_exists with (fieldlist_of al) id delta
    as [ty ?]; auto.
  eapply fieldlist_list_in in H0; eauto.
  change id with (fst (id,ty)).
  eapply in_map; eauto.
Qed.

Lemma in_list_field_offset_exists:
  forall al id,
  in_list id (map fst al) = true ->
  exists delta, field_offset id (fieldlist_of al) = OK delta.
Proof.
  intros. apply in_list_true_in in H; auto.
  eapply fieldlist_list_in_offset_exists; eauto.
Qed.

Lemma list_in_list_swap:
  forall l1 l2,
  list_in_list l1 l2 = list_in_list l2 l1.
Proof.
  unfold list_in_list.
  induction l1; induction l2; simpl; auto.
  generalize (IHl1 nil); auto.
  generalize Pos.eqb_sym. intros.
  repeat rewrite <-orb_assoc. f_equal; auto.
  rewrite existsb_equal_app with _ _ (Peqb a0) (fun id => in_list id l2) l1; auto.
  rewrite existsb_equal_app with _ _ (Peqb a) (fun id => in_list id l1) l2; auto.
  rewrite IHl1, orb_assoc, orb_assoc. f_equal.
  unfold in_list. rewrite orb_comm.
  rewrite existsb_equal with _ _ (fun id => Peqb id a0) l1; auto.
  rewrite existsb_equal with _ _ (Peqb a) l2; auto.
Qed.

Lemma list_in_list_perm1:
  forall l l1 l2,
  Permutation l1 l2 ->
  list_in_list l l1 = list_in_list l l2.
Proof.
  induction l; simpl; intros; auto.
  rewrite IHl with l1 l2; auto.
  rewrite in_list_perm with a l1 l2; auto.
Qed.

Lemma list_in_list_perm2:
  forall l l1 l2,
  Permutation l1 l2 ->
  list_in_list l1 l = list_in_list l2 l.
Proof.
  intros.
  rewrite list_in_list_swap. symmetry.
  rewrite list_in_list_swap. symmetry.
  apply list_in_list_perm1; auto.
Qed.

Lemma list_in_list_disjoint:
  forall l1 l2,
  list_in_list l1 l2 = false <->
  list_disjoint l1 l2.
Proof.
  unfold list_disjoint.
  induction l1; simpl; intros;
  split; intros; auto.

  apply orb_false_elim in H. destruct H.
  destruct H0; subst.
  apply in_list_false_notin in H.
  red; intros; subst; auto.
  eapply IHl1; eauto.

  apply orb_false_intro; auto.
  apply <-in_list_false_notin.
  red; intros. eapply H; eauto.
  apply <-IHl1; auto.
Qed.

Lemma list_in_list_right_app:
  forall l l1 l2,
  list_in_list l (l1 ++ l2) = list_in_list l l1 || list_in_list l l2.
Proof.
  intros. rewrite list_in_list_swap.
  rewrite list_in_list_swap with l l1.
  rewrite list_in_list_swap with l l2.
  apply existsb_app.
Qed.

Lemma list_in_list_left_app:
  forall l l1 l2,
  list_in_list (l1 ++ l2) l = list_in_list l1 l || list_in_list l2 l.
Proof.
  intros. apply existsb_app.
Qed.

Variable A B: Type.

Lemma list_disjoint_app_left:
  forall (l1: list A) l2 l3,
  list_disjoint (l1++l2) l3 <->
  list_disjoint l1 l3 /\ list_disjoint l2 l3.
Proof.
  unfold list_disjoint. split; intros.
  split; intros; apply H; auto; apply in_or_app; auto.
  destruct H. apply in_app_or in H0. destruct H0; auto.
Qed.

Lemma list_disjoint_app_right:
  forall (l: list A) l1 l2,
  list_disjoint l (l1++l2) <->
  list_disjoint l l1 /\ list_disjoint l l2.
Proof.
  unfold list_disjoint. split; intros.
  split; intros; apply H; auto; apply in_or_app; auto.
  destruct H. apply in_app_or in H1. destruct H1; auto.
Qed.

Lemma list_disjoint_appa_left:
  forall (a: A) l1 l2,
  list_disjoint (a::l1) l2 ->
  ~ In a l2 /\ list_disjoint l1 l2.
Proof.
  unfold list_disjoint; intuition; subst;
  eapply H; eauto; simpl; auto.
Qed.

Lemma list_disjoint_appa_right:
  forall (a: A) l1 l2,
  list_disjoint l1 (a::l2) <->
  ~ In a l1 /\ list_disjoint l1 l2.
Proof.
  unfold list_disjoint; intuition; subst;
  try (eapply H; eauto; simpl; auto).
  simpl in *. destruct H2; subst; auto.
  eapply H1; eauto.
Qed.

Lemma list_disjoint_incl_left:
  forall (l: list A) l1 l2,
  list_disjoint l2 l ->
  incl l1 l2 ->
  list_disjoint l1 l.
Proof.
  unfold list_disjoint, incl. intros.
  apply H; auto.
Qed.

Lemma list_disjoint_incl_right:
  forall (l: list A) l1 l2,
  list_disjoint l l2 ->
  incl l1 l2 ->
  list_disjoint l l1.
Proof.
  unfold list_disjoint, incl. intros.
  apply H; auto.
Qed.

Lemma list_disjoint_incl:
  forall (l1: list A) l2 l1' l2',
  list_disjoint l1 l2 ->
  incl l1' l1 ->
  incl l2' l2 ->
  list_disjoint l1' l2'.
Proof.
  unfold list_disjoint, incl. intros.
  apply H; auto.
Qed.

Lemma list_norepet_nodup:
  forall (l: list A),
  list_norepet l <-> NoDup l.
Proof.
  induction l;intros.
  split; constructor.
  split; intros; inv H; constructor; auto.
  apply IHl; auto. apply <-IHl; auto.
Qed.

Lemma list_norepet_permut:
  forall (l1: list A) l2,
  list_norepet l1 ->
  Permutation l1 l2 ->
  list_norepet l2.
Proof.
  intros.
  apply list_norepet_nodup.
  apply list_norepet_nodup in H.
  eapply permutation_nodup; eauto.
Qed.

Lemma list_disjoint_permut:
  forall (l: list A) l1 l2,
  list_disjoint l l1 ->
  Permutation l1 l2 ->
  list_disjoint l l2.
Proof.
  unfold list_disjoint. intros.
  apply H; auto.
  apply Permutation_in with l2; eauto.
  apply Permutation_sym; auto.
Qed.

Lemma list_repeat_add_one:
  forall i (a: A),
  list_repeat (i + 1) a =  list_repeat i a ++ a :: nil.
Proof.
  induction i; simpl; intros; f_equal; auto.
Qed.

Lemma Forall_list_repeat:
  forall n a (P: A -> Prop),
  P a ->
  Forall P (list_repeat n a).
Proof.
  induction n; intros; simpl; intros.
  constructor.
  constructor 2; auto.
Qed.

Lemma Forall2_list_repeat:
  forall n a b (P: A -> B -> Prop),
  P a b ->
  Forall2 P (list_repeat n a) (list_repeat n b).
Proof.
  induction n; intros; simpl; intros.
  constructor.
  constructor 2; auto.
Qed.

Lemma list_forall2_infer:
  forall (A B: Type)(R: A->B->Prop) a1 b1,
  list_forall2 R a1 b1 <-> Forall2 R a1 b1.
Proof.
  split; induction 1; intros; constructor; auto.
Qed.

Definition find_funct(ge: list (ident*A))(id: ident): option (ident*A) :=
  find (fun x => identeq (fst x) id) ge.

Lemma identeq_shift:
  forall i j k,
  identeq (i+k)%positive (j+k)%positive = identeq i j.
Proof.
  intros. remember (identeq i j).
  destruct b; symmetry in Heqb.
  +apply Pos.eqb_eq in Heqb. subst.
   rewrite Pos.eqb_refl. auto.
  +apply Pos.eqb_neq in Heqb.
   rewrite Pos.eqb_neq. red. intros.
   red in Heqb. apply Heqb.
   apply Pos.add_reg_r with k; auto.
Qed.

Lemma identeq_succ:
  forall i j,
  identeq (Psucc i) (Psucc j) = identeq i j.
Proof.
  intros. repeat rewrite <-Pos.add_1_r.
  apply identeq_shift; auto.
Qed.

Lemma list_in_shift:
  forall l (j k: positive),
  In (Pplus j k) (map (fun i => Pplus i k) l) ->
  In j l.
Proof.
  induction l; simpl; intros.
  tauto.
  destruct H; [left | right].
  apply Pos.add_reg_r with k; auto.
  apply IHl with k; auto.
Qed.

Lemma list_norepet_shift:
  forall l (k: positive),
  list_norepet l ->
  list_norepet (map (fun i => Pplus i k) l).
Proof.
  induction l;  intros.
  simpl. constructor.
  inv H. simpl. constructor; auto.
  red. intros. apply H2.
  eapply list_in_shift; eauto.
Qed.

Lemma find_funct_fid:
  forall l fid fd,
  find_funct l fid = Some fd ->
  fst fd = fid.
Proof.
  unfold find_funct. intros.
  apply find_some_true in H.
  apply Peqb_eq in H; auto.
Qed.

Lemma find_funct_eq:
  forall l fid fd,
  find_funct l fid = Some fd ->
  find_funct l (fst fd) = Some fd.
Proof.
  intros.
  cut (fst fd = fid); intros.
  rewrite H0; auto.
  apply find_funct_fid in H; auto.
Qed.

Lemma find_funct_in1:
  forall l x,
  In x l ->
  list_norepet (map (@fst ident A) l) ->
  find_funct l (fst x) = Some x.
Proof.
  induction l; simpl; intros; destruct H.
  subst. rewrite Peqb_refl; auto.

  inversion_clear H0.
  assert (fst a <> fst x).
    red; intros. apply H1. rewrite H0.
    apply in_map; trivial.
  rewrite IHl; auto.
  remember (identeq (fst a) (fst x)).
  destruct b; auto.
  symmetry in Heqb. apply Peqb_eq in Heqb.
  contradict H0; auto.
Qed.

Lemma find_funct_in2:
  forall l x fid,
  find_funct l fid = Some x ->
  In x l.
Proof.
  unfold find_funct. intros.
  apply find_some_in in H ; auto.
Qed.

Lemma find_funct_fid_in:
  forall l fid fd,
  find_funct l fid = Some fd ->
  In fid (map (fst (B:=A)) l).
Proof.
  intros. generalize H; intros.
  apply find_funct_in2 in H.
  apply find_funct_fid in H0.
  subst. eapply in_map; eauto.
Qed.

Lemma find_funct_app_notin:
  forall ge1 ge2 fid fd,
  find_funct (ge1++ge2) fid = Some fd ->
  ~ In fid (map (@fst ident A) ge2) ->
  find_funct ge1 fid = Some fd.
Proof.
  induction ge1; simpl; intros.
  apply find_funct_fid_in in H.
  congruence.

  destruct (identeq (fst a) fid); eauto.
Qed.

Lemma find_funct_notin_app:
  forall l fid fd,
  find_funct l fid = Some fd ->
  exists l1 l2, l = l1 ++ fd :: l2
    /\ ~ In fid (map (@fst ident A) l1).
Proof.
  induction l; simpl; intros.
  +congruence.
  +compare (fst a) fid; intros; subst.
   -rewrite Pos.eqb_refl in H.
    inv H. exists nil, l; split; auto.
   -generalize n; intros.
    unfold identeq in H. apply Pos.eqb_neq in n.
    rewrite n in H; auto.
    destruct IHl with fid fd as [l1 [l2 [? ?]]]; auto.
    subst. exists (a::l1), l2; split; simpl; auto.
    red. intros. destruct H0.
    *red in n0; auto.
    *red in H1; auto.
Qed.

Lemma find_funct_app_notin_right:
  forall l1 l2 fid,
  ~ In fid (map (@fst ident A) l1) ->
  find_funct (l1++l2) fid = find_funct l2 fid.
Proof.
  induction l1; simpl; intros; auto.
  assert(fst a <> fid). auto.
  apply Pos.eqb_neq in H0; auto.
  unfold identeq. rewrite H0; auto.
Qed.

Lemma find_funct_app:
  forall ge1 ge2 fid fd,
  find_funct ge1 fid = Some fd ->
  find_funct (ge1++ge2) fid = Some fd.
Proof.
  unfold find_funct. intros.
  apply find_some_app; auto.
Qed.

Definition get_nt_byid(nid :ident)(l: list (ident*A)): res (ident*A) :=
  match find_funct l nid with
  | Some fd => OK fd
  | None => Error (msg "!!")
  end.

Lemma find_funct_get_nt_byid:
  forall l cid nt,
  find_funct l cid = Some nt <->
  get_nt_byid cid l = OK nt.
Proof.
  unfold get_nt_byid. split; intros.
  rewrite H; auto.
  remember (find_funct l cid).
  destruct o; inv H. auto.
Qed.

Lemma getntbyid_ntl_app_any:
  forall l1 i x l2,
  get_nt_byid i l1 = OK x ->
  get_nt_byid i (l1 ++ l2) = OK x.
Proof.
  intros.
  apply find_funct_get_nt_byid.
  apply find_funct_get_nt_byid in H.
  apply find_funct_app; auto.
Qed.

End ID_FIND.

Lemma trans_funcs_find:
  forall A B ge (f: ident*A->ident*B) id fd,
  find_funct ge id = Some fd ->
  (forall x, fst x = fst (f x)) ->
  find_funct (map f ge) id = Some (f fd).
Proof.
  induction ge; simpl; intros.
  congruence.
  rewrite <-H0.
  destruct (identeq (fst a) id); auto.
  congruence.
Qed.

Lemma find_funcs_monad_exits:
  forall A B l1 l2 (f: ident*A-> res (ident*B)) id fd1,
  find_funct l1 id = Some fd1 ->
  mmap f l1 = OK l2 ->
  (forall x x1, f x = OK x1 -> fst x = fst x1) ->
  exists fd2, f fd1 = OK fd2 /\ find_funct l2 id = Some fd2.
Proof.
  induction l1; simpl; intros.
  congruence.
  monadInv H0. destruct (identeq (fst a) id) eqn:?; auto.
  inv H. exists x; split; auto. simpl.
  apply H1 in EQ. rewrite <-EQ, Heqb; auto.
  destruct IHl1 with x0 f id fd1 as [fd2 [? ?]]; auto.
  exists fd2; split; simpl; auto.
  apply H1 in EQ. rewrite <-EQ, Heqb; auto.
Qed.

Lemma find_funct_permut:
  forall A fid l1 l2,
  Permutation l1 l2 ->
  list_norepet (map (@fst ident A) l1) ->
  find_funct l1 fid = find_funct l2 fid.
Proof.
  induction 1; intros; simpl; trivial.
  inv H0. destruct (identeq (fst x) fid);auto.
  inv H. simpl in *. apply Decidable.not_or in H2. destruct H2.
  caseEq (identeq (fst x) fid);caseEq (identeq (fst y) fid);auto.
  intros. apply Peqb_eq  in H1. apply Peqb_eq in H2. congruence.
  rewrite IHPermutation1, IHPermutation2; auto.
  eapply list_norepet_permut; eauto.
  apply Permutation_map; trivial.
Qed.

Lemma trans_nodes_fids_eq:
  forall A B l1 l2 (f: ident*A-> res (ident*B)),
  mmap f l1 = OK l2 ->
  (forall x x1, f x = OK x1 -> fst x = fst x1) ->
  map (@fst ident A) l1 = map (@fst ident B) l2.
Proof.
  induction l1; simpl; intros.
  inv H. auto.

  monadInv H. simpl. f_equal; auto.
  eapply IHl1; eauto.
Qed.

Lemma mmap_app:
  forall A B l1 l2 l1' l2' (f: A-> res B),
  mmap f l1 = OK l1' ->
  mmap f l2 = OK l2' ->
  mmap f (l1++l2) = OK (l1'++l2').
Proof.
  induction l1; simpl; intros.
  inv H. simpl; auto.
  monadInv H. rewrite EQ. simpl.
  rewrite IHl1 with l2 x0 l2' f; auto.
Qed.

Lemma mmap_ext:
  forall A B l l' (f: A-> res A)(g: A -> B),
  mmap f l = OK l' ->
  (forall a b, f a = OK b -> g a = g b) ->
  map g l = map g l'.
Proof.
  induction l; simpl; intros.
  +monadInv H; simpl in *. auto.
  +monadInv H. simpl.
   f_equal; eauto.
Qed.

Lemma in_mmap_iff :
  forall A B l1 l2 y (f: A-> res B),
  mmap f l1 = OK l2 ->
  In y l2 ->
  exists x, f x = OK y /\ In x l1.
Proof.
  intros.
  apply mmap_inversion in H.
  apply list_forall2_infer in H.
  apply in_split in H0. destruct H0 as [l3 [l4 ?]].
  subst. apply Forall2_app_inv_r in H.
  destruct H as [l5 [l6 [? [? ?]]]]. subst.
  inv H0. exists x. split; auto.
  apply in_or_app; simpl; auto.
Qed.

Section DEPEND.

Inductive depend : Type := mkdepend {
  lidl: list ident;
  ridl: list ident;
  seqn: nat
}.

Definition depnil := mkdepend nil nil O.

Definition dependon (x y: depend): bool :=
  list_in_list (ridl x) (lidl y) .

Definition dependonlist (x: depend)(l: list depend): bool :=
  list_in_list (ridl x) (flat_map lidl l).

Definition listdependonlist (l1 l2: list depend): bool :=
  list_in_list (flat_map ridl l1) (flat_map lidl l2).

Fixpoint topo_sorted (l: list depend) : Prop :=
  match l with
  | nil => True
  | cons hd tl => (dependonlist hd l = false) /\ topo_sorted tl
  end.

Lemma dependonlist_permutation: forall (a:depend)(l1 l2: list depend),
  Permutation l1 l2->
  dependonlist a l1 = dependonlist a l2.
Proof.
  intros. unfold dependonlist. apply list_in_list_perm1; auto.
  apply flat_map_permutation; trivial.
Qed.

Lemma dependonlist_app: forall (a:depend)(l1 l2: list depend),
  dependonlist a (l1 ++ l2) = dependonlist a l1 || dependonlist a l2.
Proof.
  unfold dependonlist. intros. rewrite flat_map_app.
  apply list_in_list_right_app.
Qed.

Lemma dependonlist_appa: forall (x y:depend)(l: list depend),
  dependonlist x (y :: l) = dependon x y || dependonlist x l.
Proof.
  intros. change (y :: l) with ((y :: nil) ++ l).
  rewrite dependonlist_app.
  unfold dependonlist, dependon.
  simpl. rewrite <-app_nil_end; trivial.
Qed.

Lemma dependonlist_incl:
  forall a l1 l2,
  dependonlist a l1 = false ->
  incl l2 l1 ->
  dependonlist a l2 = false.
Proof.
  unfold dependonlist. intros.
  rewrite list_in_list_swap in *.
  eapply existsb_incl; simpl; eauto.
  eapply flat_map_incl; eauto.
Qed.

Lemma listdependonlist_permutation: forall (l l1 l2: list depend),
  Permutation l1 l2->
  listdependonlist l l1 = listdependonlist l l2.
Proof.
  intros. apply list_in_list_perm1.
  apply flat_map_permutation; auto.
Qed.

Lemma listdependonlist_app: forall (l l1 l2: list depend),
  listdependonlist l (l1 ++ l2) = listdependonlist l l1 || listdependonlist l l2.
Proof.
  unfold listdependonlist. intros. rewrite flat_map_app.
  apply list_in_list_right_app.
Qed.

Lemma toposort_app: forall (l1 l2: list depend),
  topo_sorted l1 /\
  topo_sorted l2 /\
  listdependonlist l1 l2 = false <->
  topo_sorted (l1 ++ l2).
Proof.
  unfold listdependonlist.
  induction l1; simpl; unfold dependonlist in *;
  simpl; intros; split; intuition; auto;
  try (apply IHl1 in H1; intuition; fail).
  +rewrite list_in_list_left_app in H3.
   apply orb_false_elim in H3. destruct H3.
   rewrite flat_map_app, <-app_ass, list_in_list_right_app, H; auto.
  +rewrite list_in_list_left_app in H3.
   apply orb_false_elim in H3. destruct H3.
   destruct IHl1 with l2 as [A1 A2]. apply A1; eauto.
  +rewrite flat_map_app, <-app_ass in H0.
   rewrite list_in_list_right_app in H0.
   apply orb_false_elim in H0. destruct H0; auto.
  +rewrite flat_map_app, <-app_ass in H0.
   rewrite list_in_list_right_app in H0.
   apply orb_false_elim in H0. destruct H0.
   destruct IHl1 with l2 as [A1 A2]. apply A2 in H1.
   intuition. rewrite list_in_list_left_app. rewrite H0; auto.
Qed.

Lemma topo_sorted_perm:
  forall a lx ly l,
  Permutation (a :: l) (lx ++ a :: ly) ->
  topo_sorted (a :: l) ->
  topo_sorted (lx ++ a :: ly) ->
  topo_sorted (a :: lx ++ ly).
Proof.
  simpl; intros. apply toposort_app in H1. destruct H1 as [A [A1 A2]].
  change (a :: ly) with ((a :: nil) ++ ly) in A2.
  rewrite listdependonlist_app in A2. apply orb_false_elim in A2.
  simpl in A1. rewrite dependonlist_appa in *. apply Permutation_cons_app_inv in H.
  apply Permutation_sym in H. rewrite dependonlist_permutation with _ _ l; auto.
  intuition. apply ->toposort_app; auto.
Qed.

Lemma depend_toposorted: forall (l1 l2: list depend),
  map (fun d: depend => mkdepend (lidl d) (ridl d) O) l1 =
  map (fun d: depend => mkdepend (lidl d) (ridl d) O) l2 ->
  topo_sorted l1 ->
  topo_sorted l2.
Proof.
  set (Hf := (fun d: depend => mkdepend (lidl d) (ridl d) O)).
  induction l1; induction l2; simpl;intros; auto.
  contradict H. apply nil_cons.
  destruct H0; inversion H. unfold dependonlist in *.
  simpl in *. rewrite <- H3, <-H4.
  split; auto. rewrite <-H0; f_equal. f_equal.
  transitivity (flat_map lidl (map Hf l1));[rewrite H5 | idtac];
  rewrite flat_map_map; simpl; auto.
Qed.

End DEPEND.
