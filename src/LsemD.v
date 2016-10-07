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
Require Import List.
Require Import Maps.
Require Import Streams.
Require Import Cltypes.
Require Import Lvalues.
Require Import Lident.
Require Import Lop.
Require Import Ltypes.
Require Import Lustre.
Require Import LustreF.
Require Import Lenv.
Require Import Lsem.
Require Import LsemF.

Section SEMANTICS.

Variable p: program.
Variable gc: locenv.

Inductive locenv_getmvl(te e: locenv)(lh: sexp)(mv: mvl): Prop :=
  | locenv_getmvl_: forall id ofs k m t,
      eval_lvalue gc te e lh id ofs k ->
      k = Lid \/ k = Sid ->
      (case_env gc te e k) ! id = Some (m,t) ->
      loadbytes m (Int.unsigned ofs) (sizeof (typeof lh)) = Some mv ->
      locenv_getmvl te e lh mv.

Definition locenv_getmvls(te e: locenv)(l: list sexp)(vl: list mvl): Prop :=
  Forall2 (locenv_getmvl te e) l vl.


Inductive locenv_setmvl: locenv -> ident*type -> mvl-> locenv -> Prop :=
  | locenv_setmvl_: forall e id ty mv,
      sizeof ty = Z_of_nat (length mv) ->
      0 < Z_of_nat (length mv) <= Int.max_signed ->
      locenv_setmvl e (id, ty) mv (PTree.set id (mv,ty) e).

Inductive locenv_setmvls: locenv -> list (ident*type) -> list mvl-> locenv -> Prop :=
  | locenv_setmvls_nil: forall e,
      locenv_setmvls e nil nil e
  | locenv_setmvls_cons_id: forall e e1 e' a al mv vl,
      locenv_setmvl e a mv e1 ->
      locenv_setmvls e1 al vl e' ->
      locenv_setmvls e (a :: al) (mv :: vl) e'.

Lemma locenv_getmvls_set_mvls_exists:
  forall te e l vl,
  locenv_getmvls te e l vl ->
  forall ef rets,
  List.map typeof l = List.map (snd (B:=type)) rets ->
  exists ef' : locenv, locenv_setmvls ef rets vl ef'.
Proof.
  induction 1; simpl; intros.
  +destruct rets; inv H. exists ef. constructor.
  +destruct rets; inv H1. destruct p0. simpl in *. subst.
   destruct IHForall2 with (PTree.set i (y,typeof x) ef) rets as [ef' ?]; auto.
   exists ef'. econstructor 2; eauto.
   generalize (sizeof_pos (typeof x)); intros.
   inv H. generalize H7; intros.
   apply loadbytes_length in H7.
   apply loadbytes_range_perm in H8. red in H8.
   constructor 1; rewrite <-H7; rewrite nat_of_Z_eq; try omega.
Qed.

Lemma locenv_setmvls_notin_eq:
  forall e al vl e',
  locenv_setmvls e al vl e' ->
  forall id, ~ In id (List.map fst al) ->
  e' ! id = e ! id.
Proof.
  induction 1; simpl; intros; auto.
  rewrite IHlocenv_setmvls; auto.
  inv H. rewrite PTree.gso; auto.
Qed.

Lemma locenv_setmvls_locenv_rets_match_rec:
  forall rets vl e e',
  locenv_setmvls e rets vl e' ->
  forall id mv t, e ! id = None ->
  e' ! id = Some (mv, t) ->
  list_norepet (List.map fst rets) ->
  In (id, t) rets.
Proof.
  induction 1; simpl; intros.
  +congruence.
  +inv H3. inv H.
   compare id id0; intros; subst.
   -erewrite locenv_setmvls_notin_eq in H2; eauto.
    rewrite PTree.gss in H2. inv H2; auto.
   -right. eapply IHlocenv_setmvls; eauto.
    rewrite PTree.gso; auto.
Qed.

Inductive eval_node: locenv -> locenv -> ident*func -> list val -> list val -> Prop :=
  | exec_node: forall te te1 te2 e e1 vrs vas nid f,
      alloc_variables empty_locenv (lvarsof f) te ->
      locenv_setvars te f.(nd_args) vas te1 ->
      ids_norepet f ->
      eval_stmt nid te1 e te2 e1 f.(nd_stmt) ->
      locenv_getvars e1 f.(nd_rets) vrs ->
      eval_node e e1 (nid,f) vas vrs

with eval_stmt: ident -> locenv -> locenv -> locenv -> locenv -> stmt  -> Prop :=
  | eval_Sassign: forall nid te te' e e' lh a,
      eval_eqf gc te e te' e' (lh,a) ->
      eval_stmt nid te e te' e' (Sassign lh a)
  | eval_Scall: forall nid te te' e e' ef ef' vl oid cdef fd args lhs vargs vargs' vrets,
      call_func (node_block p) cdef fd ->
      eval_sexps gc te e args vargs ->
      eval_casts vargs (List.map typeof args) vargs' ->
      locenv_getmvls te e lhs vl ->
      locenv_setmvls empty_locenv (nd_rets (snd fd)) vl ef ->
      eval_node ef ef' fd vargs' vrets ->
      locenv_setvarfs gc te e lhs vrets te' e' ->
      Forall (lid_disjoint) lhs ->
      List.map typeof lhs = List.map snd (nd_rets (snd fd)) ->
      List.map typeof args = List.map snd (nd_args (snd fd)) ->
      lvalue_list_norepet (eval_lvalue gc te e) lhs ->
      assign_list_disjoint (eval_lvalue gc te e) lhs args ->
      te ! (callid cdef) = None ->
      eval_stmt nid te e te' e' (Scall oid lhs cdef args)
  | eval_Sfor_start: forall nid te te1 te2 e e1 e2 a1 a2 a3 s,
      eval_eqf gc te e te1 e1 a1 ->
      eval_stmt nid te1 e1 te2 e2 (Sfor None a2 a3 s) ->
      eval_stmt nid te e te2 e2 (Sfor (Some a1) a2 a3 s)
  | eval_Sfor_false: forall nid te e a2 a3 s,
      eval_sexp gc te e a2 Vfalse ->
      eval_stmt nid te e te e (Sfor None a2 a3 s)
  | eval_Sfor_loop: forall nid te te1 te2 te3 e e1 e2 e3 a2 a3 s,
      eval_sexp gc te e a2 Vtrue ->
      eval_stmt nid te e te1 e1 s ->
      eval_eqf gc te1 e1 te2 e2 a3 ->
      eval_stmt nid te2 e2 te3 e3 (Sfor None a2 a3 s) ->
      eval_stmt nid te e te3 e3 (Sfor None a2 a3 s)
  | eval_Sskip: forall nid te e ,
      eval_stmt nid te e te e Sskip
  | eval_Sseq: forall nid te te1 te2 e e1 e2 s1 s2,
      eval_stmt nid te e te1 e1 s1 ->
      eval_stmt nid te1 e1 te2 e2 s2 ->
      eval_stmt nid te e te2 e2 (Sseq s1 s2)
  | eval_Sif: forall nid te te1 e e1 a s1 s2 v b,
      eval_sexp gc te e a v ->
      bool_val v (typeof a) = Some b ->
      eval_stmt nid te e te1 e1 (if b then s1 else s2)  ->
      eval_stmt nid te e te1 e1 (Sif a s1 s2)
  | eval_Scase: forall nid te te1 e e1 lh ca pl i a,
      eval_sexp gc te e ca (Vint i) ->
      select_case i pl = Some a ->
      eval_stmt nid te e te1 e1 (Sassign lh a) ->
      eval_stmt nid te e te1 e1 (Scase lh ca pl).

Scheme eval_node_ind2 := Minimality for eval_node Sort Prop
  with eval_stmt_ind2 := Minimality for eval_stmt Sort Prop.
Combined Scheme eval_node_stmt_ind2 from eval_node_ind2, eval_stmt_ind2.

End SEMANTICS.

Section GLOBAL_ENV.

Variable p: program.
Variable gc: locenv.

Variable eval_node: program -> locenv -> locenv -> locenv -> ident*func-> list val -> list val -> Prop.

Inductive initial_state(fd: ident*func):  locenv -> Prop :=
  | initial_state_: forall e e1 fi vr,
      init_genvc (const_block p) = Some gc ->
      find_funct (node_block p) (reset_id p.(node_main)) = Some fi ->
      find_funct (node_block p) p.(node_main) = Some fd ->
      nd_rets (snd fi) = nd_rets (snd fd) ->
      args_prop (nd_args (snd fd)) ->
      args_prop (nd_rets (snd fd)) ->
      alloc_variables empty_locenv (nd_rets (snd fd)) e ->
      eval_node p gc e e1 fi nil vr ->
      initial_state fd e1.


Definition vret_from_struct(fld: fieldlist)(m: mvl)(o: int)(a: ident*type)(v: val): Prop :=
  exists delta, field_offset (fst a) fld = OK delta
    /\ field_type (fst a) fld = OK (snd a)
    /\ has_type v (snd a)
    /\ load_mvl (snd a) m (Int.add o (Int.repr delta)) v.


Definition vrets_match(fld: fieldlist)(m: mvl)(o: int)(al: list (ident*type))(vl: list val): Prop :=
  Forall2 (vret_from_struct fld m o) al vl.

Inductive vrets_fld_match(fld: fieldlist)(al: list (ident*type))(vl: list val)(m: mvl)(o: int): Prop :=
  | vrets_fld_match_:
      vrets_match fld m o al vl ->
      Z_of_nat (length m) = sizeof_fld fld ->
      vrets_fld_match fld al vl m o.

Inductive exec_prog(main: ident*func)(e: locenv)(n maxn: nat)(vass vrss: Stream (list mvl)) : Prop :=
  | exec_prog_term:
      (n > maxn)%nat ->
      exec_prog main e n maxn vass vrss
  | exec_prog_cons: forall e',
      (n <= maxn)%nat ->
      has_types (List.map Vmvl (Streams.hd vass)) (List.map snd (nd_args (snd main))) ->
      eval_node p gc e e' main (List.map Vmvl (Streams.hd vass)) (List.map Vmvl (Streams.hd vrss)) ->
      exec_prog main e' (n+1) maxn (Streams.tl vass) (Streams.tl vrss) ->
      exec_prog main e n maxn vass vrss.

End GLOBAL_ENV.
