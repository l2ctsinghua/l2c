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
Require Import Integers.
Require Import Floats.
Require Import Zwf.
Require Import Maps.
Require Import Memory.
Require Import Globalenvs.
Require Import Ctypes.
Require Import Cltypes.
Require Import ExtraList.
Require Import Streams.
Require Import Peano.
Require Import Lident.
Require Import Ltypes.
Require Import Lvalues.
Require Import Lustre.

Set Implicit Arguments.

Section PTREE.

Variable A: Type.

Lemma ptree_set_swap:
  forall e id1 id2 (a1 a2: A), id1 <> id2 ->
  PTree.set id2 a2 (PTree.set id1 a1 e) = PTree.set id1 a1 (PTree.set id2 a2 e).
Proof.
  induction e; induction id1; induction id2;
  simpl; intros; auto; try congruence.
  f_equal. apply IHid1. congruence.
  f_equal. apply IHid1. congruence.
  f_equal. apply IHe2. congruence.
  f_equal. apply IHe1. congruence.
Qed.

Lemma ptree_set_repeat_leaf:
  forall id (v: A) v1,
  PTree.set id v (PTree.set id v1 PTree.Leaf) = PTree.set id v PTree.Leaf.
Proof.
  induction id; simpl; intros; f_equal; auto.
Qed.

Lemma ptree_set_repeat:
  forall e id (v: A) v1,
  PTree.set id v (PTree.set id v1 e) = PTree.set id v e.
Proof.
  induction e, id; simpl; intros; f_equal; auto;
  apply ptree_set_repeat_leaf.
Qed.

Lemma ptree_set_same:
  forall e id (v: A),
  e ! id = Some v ->
  PTree.set id v e = e.
Proof.
  induction e, id; simpl; intros; try congruence; f_equal; auto.
Qed.

End PTREE.

Section ENV.


(** The local environment maps local variables to mvl and types. *)

Definition locenv:= PTree.t (mvl*type).

(** The tempo environment maps tempo variables to tree of locenv. *)

Inductive env: Type := mkenv {
  le: locenv;  (**r local tempo environment. *)
  sube: PTree.t (list env)  (**r subset tempo environment of the node call. *)
}.

(** subset tempo environment of the node call。*)

Definition subenv := PTree.t (list env).

Definition empty_locenv := PTree.empty (mvl*type).
Definition empty_subenv := PTree.empty (list env).
Definition empty_env := mkenv empty_locenv empty_subenv.

Definition nat_of_int(i: int):= nat_of_Z (Int.unsigned i).

(** the chage of env state after the node call executed. *)

Inductive callnd_env(c: calldef)(i: int): subenv -> subenv -> env -> env -> Prop :=
  | callnd_env_: forall se1 se2 e1 e2 efs,
     se1 ! (instid c) = Some efs ->
     nth_error efs (nat_of_int i) = value e1 ->
     se2 = PTree.set (instid c) (replace_nth efs (nat_of_int i) e2) se1 ->
     Z_of_nat (length efs) = Int.unsigned (intof_opti (callnum c)) ->
     callnd_env c i se1 se2 e1 e2.

(** the chage of env state after the node or function call executed. *)

Inductive call_env(c: calldef)(i: int): subenv -> subenv -> env -> env -> Prop :=
  | call_env_: forall se1 se2 e1 e2,
     cakind c = true ->
     callnd_env c i se1 se2 e1 e2 ->
     call_env c i se1 se2 e1 e2
  | call_env_func_: forall se,
     cakind c = false ->
     call_env c i se se empty_env empty_env.

(** the property of variable in locenv after allocation. *)

Definition locenv_range_perm_var(eh: locenv)(id: ident)(ty: type) :=
  exists m, eh ! id = Some (m,ty)
    /\ Z_of_nat (length m) = sizeof ty
    /\ range_perm m 0 (sizeof ty).

(** the property of variables in locenv after allocation. *)

Definition locenv_range_perm_vars(eh: locenv)(al: list (ident*type)) :=
  forall id ty, In (id,ty) al -> locenv_range_perm_var eh id ty.

Inductive callnd_inst_env(c: calldef)(i: int)(se: subenv): env -> Prop :=
  | callnd_inst_env_node: forall efs ef,
     se ! (instid c) = Some efs ->
     nth_error efs (nat_of_int i) = value ef ->
     Z_of_nat (length efs) = Int.unsigned (intof_opti (callnum c)) ->
     callnd_inst_env c i se ef.

Lemma callnd_env_range_i:
  forall cdef i se se' ef ef',
  callnd_env cdef i se se' ef ef' ->
  (0 <= Int.unsigned i < Int.unsigned (intof_opti (callnum cdef)))%Z.
Proof.
  intros. inv H. rewrite <-H3. apply nth_error_value_lt in H1.
  apply Nat2Z.inj_lt in H1. unfold nat_of_int in H1.
  generalize (Int.unsigned_range i); intros.
  rewrite nat_of_Z_eq in H1; try omega.
Qed.

Lemma callnd_inst_env_eq:
  forall cdef i se se' ef ef',
  callnd_env cdef i se se' ef ef' ->
  callnd_inst_env cdef i se ef.
Proof.
  induction 1. constructor 1 with efs; auto.
Qed.

Lemma call_env_determ1:
  forall cdef i se se1 se2 ef1 ef2 ef1' ef2',
  call_env cdef i se se1 ef1 ef1' ->
  call_env cdef i se se2 ef2 ef2' ->
  ef1 = ef2.
Proof.
  intros. inv H; inv H0; try congruence.
  inv H2; inv H3. rewrite H2 in H0. inv H0.
  rewrite H4 in H5. inv H5; auto.
Qed.

Lemma call_env_determ2:
  forall cdef i se se1 se2 ef ef',
  call_env cdef i se se1 ef ef' ->
  call_env cdef i se se2 ef ef' ->
  se1 = se2.
Proof.
  intros. inv H; inv H0; try congruence.
  inv H2; inv H3. congruence.
Qed.

End ENV.

Section GLOBAL_ENV.

(** global environment. *)

Definition store_init_data(m: mvl)(p: Z)(id: init_data): option mvl:=
  match id with
  | Init_int8 n => store Mint8unsigned m p (Vint n)
  | Init_int16 n => store Mint16unsigned m p (Vint n)
  | Init_int32 n => store Mint32 m p (Vint n)
  | Init_float32 n => store Mfloat32 m p (Vsingle n)
  | Init_float64 n => store Mfloat64 m p (Vfloat n)
  | _ => None
  end.

Fixpoint store_init_datas(m: mvl)(p: Z)(idl: init_datas): option mvl :=
  match idl with
  | nil => Some m
  | id :: idl' =>
      match store_init_data m p id with
      | None => None
      | Some m' => store_init_datas m' (p + Genv.init_data_size id) idl'
      end
  end.

Definition init_data_type(init: init_data): Prop :=
  match init with
  | Init_space _ => False
  | Init_addrof _ _ => False
  | _ => True
  end.

Definition init_data_types(inits: list init_data): Prop :=
  Forall init_data_type inits.

Lemma store_init_data_length:
  forall a o mv mv',
  store_init_data mv o a = Some mv' ->
  length mv' = length mv.
Proof.
  destruct a; simpl; intros; try congruence;
  apply store_length in H; auto.
Qed.

Lemma store_init_datas_length:
  forall il o mv mv',
  store_init_datas mv o il = Some mv' ->
  length mv' = length mv.
Proof.
  induction il; simpl; intros.
  +inv H. auto.
  +destruct (store_init_data mv o a) eqn:?; try congruence.
   apply store_init_data_length in Heqo0. rewrite <-Heqo0.
   eapply IHil; eauto.
Qed.

Lemma store_init_datas_types:
  forall il o mv mv',
  store_init_datas mv o il = Some mv' ->
  init_data_types il.
Proof.
  induction il; simpl; intros.
  constructor.
  destruct (store_init_data _ _ _) eqn:?; try congruence.
  constructor 2.
  destruct a; simpl in *; auto; try congruence.
  eapply IHil; eauto.
Qed.

Fixpoint loadbytes_store_init_data (m: mvl)(p: Z) (il: list init_data) {struct il} : Prop :=
  match il with
  | nil => True
  | Init_int8 n :: il' =>
      loadbytes m p 1 = Some (Lvalues.encode_val Mint8unsigned (Lvalues.Vint n))
      /\ loadbytes_store_init_data m (p + 1) il'
  | Init_int16 n :: il' =>
      loadbytes m p 2 = Some (Lvalues.encode_val Mint16unsigned (Lvalues.Vint n))
      /\ loadbytes_store_init_data m (p + 2) il'
  | Init_int32 n :: il' =>
      loadbytes m p 4 = Some (Lvalues.encode_val Mint32 (Lvalues.Vint n))
      /\ loadbytes_store_init_data m (p + 4) il'
  | Init_float32 n :: il' =>
      loadbytes m p 4 = Some (Lvalues.encode_val Mfloat32 (Lvalues.Vsingle n))
      /\ loadbytes_store_init_data m (p + 4) il'
  | Init_float64 n :: il' =>
      loadbytes m p 8 = Some (Lvalues.encode_val Mfloat64 (Lvalues.Vfloat n))
      /\ loadbytes_store_init_data m (p + 8) il'
  | _ :: il' => False
  end.

Lemma store_init_datas_outside_bytes:
  forall il m p m',
  store_init_datas m p il = Some m' ->
  forall n q,
  (q + n <= p)%Z ->
  loadbytes m' q n = loadbytes m q n.
Proof.
  induction il; simpl.
  intros; congruence.
  intros until m'. caseEq (store_init_data m p a); try congruence.
  intros m1 A B n q C. transitivity (loadbytes m1 q n).
  eapply IHil; eauto.
  generalize (Genv.init_data_size_pos a). intros. omega.
  destruct a; simpl in A; try congruence;
  eapply loadbytes_store_other; eauto.
Qed.

Lemma store_init_datas_loadbytes_app:
  forall chunk v m p m1 il m',
  store chunk m p v = Some m1 ->
  store_init_datas m1 (p + size_chunk chunk) il = Some m' ->
  loadbytes m' p (size_chunk chunk) = Some (encode_val chunk v).
Proof.
  intros. transitivity (loadbytes m1 p (size_chunk chunk)).
  eapply store_init_datas_outside_bytes; eauto. omega.
  generalize H; intros. apply store_length in H.
  unfold store in *. destruct (valid_access_dec _ _ _); try congruence.
  destruct v0.
  unfold loadbytes. rewrite pred_dec_true; auto.
  inv H1.
  assert(nat_of_Z (size_chunk chunk) = length (encode_val chunk v)).
    rewrite encode_val_length; auto.
  rewrite H1. rewrite getN_setN_same; auto.
   rewrite encode_val_length.
  red in H2. unfold size_chunk_nat. rewrite <-Z2Nat.inj_add; try omega.
  apply Nat2Z.inj_le. rewrite nat_of_Z_eq; try omega.
  red. rewrite <-H. auto.
Qed.

Lemma store_init_datas_bytes:
  forall il m p m',
  store_init_datas m p il = Some m' ->
  loadbytes_store_init_data m' p il.
Proof.
  induction il; simpl.
  auto.
  intros until m'. caseEq (store_init_data m p a); try congruence.
  intros m1 B C.
  exploit IHil; eauto. intro D.
  destruct a; simpl in B; intuition; try congruence.
  +change 1%Z with (size_chunk Mint8unsigned).
   erewrite store_init_datas_loadbytes_app; eauto. auto.
  +change 2%Z with (size_chunk Mint16unsigned).
   erewrite store_init_datas_loadbytes_app; eauto. auto.
  +change 4%Z with (size_chunk Mint32).
   erewrite store_init_datas_loadbytes_app; eauto. auto.
  +change 4%Z with (size_chunk Mfloat32).
   erewrite store_init_datas_loadbytes_app; eauto. auto.
  +change 8%Z with (size_chunk Mfloat64).
   erewrite store_init_datas_loadbytes_app; eauto. auto.
Qed.

Function store_zeros (m: mvl)(n: Z){wf (Zwf 0) n}: option mvl :=
  if zle n 0 then Some m else
    let n' := (n - 1)%Z in
    match store Mint8unsigned m n' Vzero with
    | Some m' => store_zeros m' n'
    | None => None
    end.
Proof.
  intros. red. omega.
  apply Zwf_well_founded.
Qed.

Definition alloc_global(gc:locenv)(idl: (ident * globvar type)): option locenv :=
  match idl with
  | (id, (mkglobvar ty init _ _)) =>
    let sz := Genv.init_data_list_size init in
    match store_zeros (alloc sz) sz with
    | None => None
    | Some m1 =>
      match store_init_datas m1 0 init with
      | None => None
      | Some m2 => Some (PTree.set id (m2,ty) gc)
      end
    end
  end.

Fixpoint alloc_globals(gc: locenv)(gl: list (ident * globvar type)): option locenv :=
  match gl with
  | nil => Some gc
  | idl :: gl' =>
      match alloc_global gc idl with
      | None => None
      | Some gc' => alloc_globals gc' gl'
      end
  end.

Definition init_genvc(gl: list (ident * globvar type)): option locenv :=
  alloc_globals empty_locenv gl.


Lemma store_zeros_zero:
  forall m n, (n = 0)%Z ->
  store_zeros m n = Some m.
Proof.
  intros m n.
  functional induction (store_zeros m n); intros; auto.
  subst. omega.
  subst. omega.
Qed.

Lemma store_zeros_length:
  forall m n m',
  store_zeros m n = Some m' ->
  length m' = length m.
Proof.
  intros until n.
  functional induction (store_zeros m n); intros.
  +inv H. auto.
  +rewrite IHo; auto; try omega.
   eapply store_length in e0; eauto.
  +congruence.
Qed.

Lemma alloc_globals_app:
  forall l1 l2 gc gc1 gc2,
  alloc_globals gc l1 = Some gc1 ->
  alloc_globals gc1 l2 = Some gc2 ->
  alloc_globals gc (l1++l2) = Some gc2.
Proof.
  induction l1; simpl; intros.
  congruence.
  destruct (alloc_global gc a) eqn:?; try congruence.
  eapply IHl1; eauto.
Qed.

Lemma alloc_globals_notin_eq:
  forall id l gc gc',
  alloc_globals gc l = Some gc'->
  ~ In id (List.map (@fst ident (globvar type)) l) ->
  gc' ! id =gc ! id.
Proof.
  induction l; simpl; intros.
  +inv H. auto.
  +remember (alloc_global gc a).
   destruct o; try congruence.
   rewrite IHl with l0 gc'; eauto.
   unfold alloc_global in Heqo. destruct a.
   destruct g. destruct (store_zeros _ _) eqn:?; try congruence.
   destruct (store_init_datas _ _ _) eqn:?; inv Heqo.
   rewrite PTree.gso; auto.
Qed.

Lemma init_genvc_notin_none:
  forall id l gc,
  init_genvc l = Some gc ->
  ~ In id (List.map (@fst ident (globvar type)) l) ->
  gc ! id = None.
Proof.
  unfold init_genvc. intros.
  erewrite alloc_globals_notin_eq; eauto.
  rewrite PTree.gempty; auto.
Qed.

Lemma alloc_globals_init_datas_types:
  forall l gc gc',
  alloc_globals gc l = Some gc'->
  (forall a, In a l -> init_data_types (gvar_init (snd a))).
Proof.
  induction l; simpl; intros.
  tauto.
  destruct (alloc_global _ _) eqn:?; try congruence.
  destruct H0; subst; eauto.
  destruct a0; simpl in *. destruct g.
  destruct (store_zeros _ _); try congruence.
  destruct (store_init_datas _ _ _) eqn:?; try congruence.
  simpl. eapply store_init_datas_types; eauto.
Qed.

Inductive load_argv(ty: type)(m: mvl)(ofs: int): val -> Prop :=
  | load_argv_value: forall chunk v,
      access_mode ty = By_value chunk ->
      loadbytes m (Int.unsigned ofs) (sizeof ty) = Some (encode_val chunk v) ->
      load_argv ty m ofs v
  | load_argv_copy: forall m1,
      access_mode ty = By_copy \/ access_mode ty = By_reference ->
      loadbytes m (Int.unsigned ofs) (sizeof ty) = Some m1 ->
      (alignof ty | Int.unsigned ofs) ->
      load_argv ty m ofs (Vmvl m1).

Inductive load_mvl(ty: type)(m: mvl)(ofs: int): val -> Prop :=
  | load_mvl_value: forall chunk v,
      access_mode ty = By_value chunk ->
      load chunk m (Int.unsigned ofs) = Some v ->
      load_mvl ty m ofs v
  | load_mvl_copy: forall m1,
      access_mode ty = By_copy \/ access_mode ty = By_reference ->
      loadbytes m (Int.unsigned ofs) (sizeof ty) = Some m1 ->
      (alignof ty | Int.unsigned ofs) ->
      load_mvl ty m ofs (Vmvl m1).

Inductive vargs_match(m: mvl)(delta: Z): list (ident*type) -> list val -> Prop :=
  | vargs_match_nil:
      vargs_match m delta nil nil
  | vargs_match_cons: forall id ty al v vl,
      load_argv ty m (Int.repr (align delta (alignof ty))) v ->
      vargs_match m (align delta (alignof ty) + sizeof ty) al vl ->
      vargs_match m delta ((id,ty)::al) (v::vl).

CoInductive vargs_matchss_rec(al: list (ident*type))(vass: Stream (list val)) (mass: Stream (list mvl)) : Prop :=
    vargs_matchss_rec_ : forall m,
      vargs_match m 0 al (Streams.hd vass) ->
      Streams.hd mass = m :: nil ->
      mvl_type true m (Tstruct xH (fieldlist_of al)) ->
      vargs_matchss_rec al (Streams.tl vass) (Streams.tl mass) ->
      vargs_matchss_rec al vass mass.

CoInductive vargs_matchss_nil_rec(vass: Stream (list val)) (mass: Stream (list mvl)) : Prop :=
    vargs_matchss_nil_rec_ :
      Streams.hd mass = nil ->
      Streams.hd vass = nil ->
      vargs_matchss_nil_rec (Streams.tl vass) (Streams.tl mass) ->
      vargs_matchss_nil_rec vass mass.

Inductive vargs_matchss(al: list (ident*type))(vass: Stream (list val)) (mass: Stream (list mvl)) : Prop :=
  | vargs_matchss_cons :
      0 < length al ->
      vargs_matchss_rec al vass mass ->
      vargs_matchss al vass mass
  | vargs_matchss_nil:
      al = nil ->
      vargs_matchss_nil_rec vass mass ->
      vargs_matchss al vass mass.

Inductive vrets_match(m: mvl)(delta: Z): list (ident*type) -> list val -> Prop :=
  | vrets_match_nil:
      vrets_match m delta nil nil
  | vrets_match_cons: forall id ty al v vl,
      load_mvl ty m (Int.repr (align delta (alignof ty))) v ->
      vrets_match m (align delta (alignof ty) + sizeof ty) al vl ->
      vrets_match m delta ((id,ty)::al) (v::vl).

CoInductive vrets_matchss_rec(al: list (ident*type))(vrss: Stream (list val)) (mrss: Stream (list mvl)) : Prop :=
    vrets_matchss_ : forall m,
      vrets_match m 0 al (Streams.hd vrss) ->
      Streams.hd mrss = m :: nil ->
      vrets_matchss_rec al (Streams.tl vrss) (Streams.tl mrss) ->
      vrets_matchss_rec al vrss mrss.

Inductive vrets_matchss(al: list (ident*type))(vrss: Stream (list val)) (mrss: Stream (list mvl)) : Prop :=
  | vrets_matchss_cons :
      0 < length al ->
      vrets_matchss_rec al vrss mrss ->
      vrets_matchss al vrss mrss
  | vrets_matchss_nil:
      al = nil ->
      vrets_matchss al vrss mrss.

Variable S: Type.

Variable p: general_program (general_node S).
Variable gc: locenv.


Variable alloc_node: general_program (general_node S) -> env -> ident*general_node S -> Prop.

Inductive initial_state(main: ident*general_node S): env -> Prop :=
  | initial_state_node: forall e,
      init_genvc (const_block p) = Some gc ->
      find_funct (node_block p) p.(node_main) = Some main ->
      alloc_node p e main ->
      initial_state main e.

Definition arg_prop(a: ident*type): Prop :=
  (0 < sizeof (snd a) <= Int.max_signed)%Z
    /\ is_arystr (snd a) = true.

Definition args_prop(l: list (ident*type)): Prop :=
  Forall arg_prop l /\ length l <= 1.

Inductive initial_state1(main: ident*general_node S): env -> Prop :=
  | initial_state1_node: forall e,
      init_genvc (const_block p) = Some gc ->
      find_funct (node_block p) p.(node_main) = Some main ->
      args_prop (nd_args (snd main)) ->
      alloc_node p e main ->
      initial_state1 main e.

Variable eval_node: general_program (general_node S) -> locenv -> env -> env -> ident*general_node S -> list val -> list val -> Prop.

Inductive exec_prog(main: ident*general_node S)(e: env)(n maxn: nat)(vass vrss: Stream (list val)) : Prop :=
  | exec_prog_term: forall mrss,
      n > maxn ->
      vrets_matchss (nd_rets (snd main)) vrss mrss ->
      exec_prog main e n maxn vass vrss
  | exec_prog_cons: forall e',
      n <= maxn ->
      eval_node p gc e e' main (hd vass) (hd vrss) ->
      exec_prog main e' (n+1) maxn (tl vass) (tl vrss) ->
      exec_prog main e n maxn vass vrss.

Inductive exec_prog1(main: ident*general_node S)(e: env)(n maxn: nat)(mass: Stream (list mvl))(vrss: Stream (list val)) : Prop :=
  | exec_prog1_term: forall mrss,
      n > maxn ->
      vrets_matchss (nd_rets (snd main)) vrss mrss ->
      exec_prog1 main e n maxn mass vrss
  | exec_prog1_cons: forall e',
      n <= maxn ->
      has_types (List.map Vmvl (Streams.hd mass)) (List.map snd (nd_args (snd main))) ->
      eval_node p gc e e' main (List.map Vmvl (Streams.hd mass)) (hd vrss) ->
      exec_prog1 main e' (n+1) maxn (tl mass) (tl vrss) ->
      exec_prog1 main e n maxn mass vrss.

End GLOBAL_ENV.
