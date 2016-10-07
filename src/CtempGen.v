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

(** Translation from LustreF to Ctemp.*)

Require Import Coqlib.
Require Import AST.
Require Import Integers.
Require Import Ltypes.
Require Import Lident.
Require Import Lustre.
Require Import LustreF.
Require Import Ctypes.
Require Import Cltypes.
Require Import Lop.
Require Import Cop.
Require Import Clight.
Require Import Ctemp.
Require Import ExtraList.

(** translate const expr. *)

Definition trans_const(c: const)(ty: type): expr :=
  match c with
  | Cint i => Econst_int i ty
  | Cfloat f => Econst_float f ty
  | Csingle f => Econst_single f ty
  | Cbool b => Econst_int (trans_bool b) ty
  end.

(** make deref expr for input parameters of struct or array type： (unary [*]) *)

Definition mkderef(id: ident)(ty: type):= Ederef (Etempvar id (Tpointer ty)) ty.

(** make deref expr for output parameters： (unary [*]) *)

Definition mkret(id: ident)(ty: type):= Ederef (Etempret id (Tpointer ty)) ty.

(** make addrof expr： ([&]) *)

Definition mkaddr(p: expr):= Eaddrof p (Tpointer (typeof p)).

(** translate input parameters. *)

Definition trans_v(id: ident)(ty:type): expr:=
  if is_arystr ty then mkderef id ty else Etempvar id ty.

Definition Eindex(r1 r2: expr) (ty: type) :=
  Ederef (Ebinop Oadd r1 r2 (Tpointer ty)) ty.

Fixpoint trans_binary_operator (op: binary_operationL): Cop.binary_operation :=
  match op with
  | Lop.Oadd => Cop.Oadd
  | Lop.Osub => Cop.Osub
  | Lop.Omul => Cop.Omul
  | Lop.Odivreal => Cop.Odiv
  | Lop.Odivint => Cop.Odiv
  | Lop.Omod => Cop.Omod
  | Lop.Oand => Cop.Oand
  | Lop.Oor => Cop.Oor
  | Lop.Oxor => Cop.Oxor
  | Lop.Oeq => Cop.Oeq
  | Lop.One => Cop.One
  | Lop.Olt => Cop.Olt
  | Lop.Ogt => Cop.Ogt
  | Lop.Ole => Cop.Ole
  | Lop.Oge => Cop.Oge
  end.

Definition trans_binop_expr (op : binary_operationL) (a1 a2 : expr)(ty : type): expr :=
  match classify_binop (typeof a1) op with
  | binop_case_normal => Ebinop (trans_binary_operator op) a1 a2 ty
  | binop_case_divint => Ecast (Ebinop Odiv a1 a2 (typeof a1)) ty
  | binop_case_divreal => Ebinop Odiv (Ecast a1 (Cltypes.Tfloat F64)) (Ecast a2 (Cltypes.Tfloat F64)) ty
  end.

Fixpoint trans_expr(e: sexp): expr :=
  match e with
  | Sconst c ty => trans_const c ty  (**r translate const expr. *)
  | Svar id ty  => Evar id ty        (**r translate local variables expr. *)
  | Savar id ty  => trans_v id ty    (**r translate input parameters expr. *)
  | Scvar id ty  => Evar id ty       (**r translate global const expr. *)
  | Ssvar id ty  => mkret id ty      (**r translate output parameters expr. *)
  | Saryacc a1 a2 ty => Eindex (trans_expr a1) (trans_expr a2) ty
  | Sfield a id ty => Efield (trans_expr a) id ty
  | Scast a ty => Ecast (trans_expr a) ty
  | Sunop op a ty => Eunop op (trans_expr a) ty
  | Sbinop op a1 a2 ty => trans_binop_expr op (trans_expr a1) (trans_expr a2) ty
  end.

Definition to_typelist(tl: list type): typelist :=
  fold_right Tcons Tnil tl.

(** translate lvalue expr of assign statement. *)

Definition trans_assign_lhs(lh: expr): expr :=
  match lh with
  | Ederef (Etempret lhsid t) _ => Etempret lhsid t
  | _ =>  mkaddr lh
  end.

(** translate right expr of assign statement. *)

Definition trans_assign_expr(a: sexp): expr :=
  match a with
  | Savar id ty => Etempvar id (Tpointer ty)  (**r translate input parameters expr into Etempvar expr. *)
  | Scvar id ty => Ecast (Eaddrof (Evar id ty) (Tpointer ty)) (Tpointer ty)  (**r translate global const expr. *)
  | Ssvar id ty => Etempret id (Tpointer ty)  (**r translate output parameters expr into Etempret expr. *)
  | _ => mkaddr (trans_expr a)
  end.

(** make the call of memcpy. *)

Definition make_memcpy (dst: expr)(src: sexp)(ty: type) :=
  let dst := trans_assign_lhs dst in
  let src := trans_assign_expr src in
  Smemcpy ty (Tcons type_pvoid (Tcons type_pvoid Tnil)) (dst :: src :: nil).

(** translate assign statement. *)

Definition assign_check(lh: expr)(rv: sexp): statement :=
  let t := typeof lh in
  if is_arystr t then make_memcpy lh rv t else Sassign lh (trans_expr rv).

(** translate switch statement. *)

Fixpoint trans_cases(lh: expr)(pel: list (patn*sexp)): labeled_statements :=
  match pel with
  | nil => LSdefault Sskip
  | (p, e) :: petl =>
    let cs := Ssequence (assign_check lh e) Sbreak in
    let rs := trans_cases lh petl in
    match p with
    | Pany => LSdefault cs
    | Pachar c => LScase c cs rs
    | Paint i => LScase i cs rs
    | Pabool b => LScase (trans_bool b) cs rs
    end
  end.

(** translate input parameter expr of function call. *)

Definition trans_arg(p: sexp): expr :=
  let a := trans_expr p in
  if is_arystr (typeof a) then
    mkaddr a
  else a.

(** translate equtation. *)

Definition trans_eqf(s: eqf): statement :=
  assign_check (trans_expr (fst s)) (snd s).

Definition trans_opteqf(os: option eqf): statement :=
  match os with
  | Some s => trans_eqf s
  | None => Sskip
  end.

(** translate output parameter in function. *)

Definition trans_ret(p: ident*type): ident*type :=
  (fst p, Tpointer (snd p)).

Definition trans_ptype(t: type): type :=
  if is_arystr t then Tpointer t else t.

Definition trans_ptypes(c: calldef) :=
  to_typelist (map trans_ptype (argtys c) ++ map (fun a => snd (trans_ret a)) (rettys c)).

(** translate statement. *)

Fixpoint trans_stmt(s: stmt): statement :=
  match s with
  | LustreF.Scall oid lh cdef vals =>
     let args := map trans_arg vals in
     let rets := map mkaddr (map trans_expr lh) in
     let cty := Tfunction (trans_ptypes cdef) Tvoid cc_default in
     (Scall None (Evar (callid cdef) cty) args rets)
  | LustreF.Sfor a1 a2 a3 s1 =>
     Sfor (trans_opteqf a1) (trans_expr a2) (trans_eqf a3) (trans_stmt s1)
  | LustreF.Sseq s1 s2 => Ssequence (trans_stmt s1) (trans_stmt s2)
  | LustreF.Sskip => Sskip
  | LustreF.Sassign lh a => assign_check (trans_expr lh) a
  | LustreF.Sif a s1 s2 =>
     Sifthenelse (trans_expr a) (trans_stmt s1) (trans_stmt s2)
  | LustreF.Scase lh swt cases =>
    let lv := trans_expr lh in
    Sswitch (trans_expr swt) (trans_cases lv cases)
  end.

(** translate input parameter in function *)

Definition trans_para(p: ident*type): ident*type :=
  let t := snd p in
  if is_arystr t then (fst p, Tpointer t) else (fst p, t).

(** translate input parameters in function *)

Definition trans_paras(b: func) :=
  map trans_para b.(nd_args).

(** translate output parameters in function *)

Definition trans_rets(b: func) :=
  map trans_ret (nd_rets b).

(** translate body of function. *)

Definition trans_body(b: func): fundef :=
  let s := trans_stmt b.(nd_stmt) in
  Internal (mkfunction Tvoid cc_default (trans_paras b) (nd_vars b) (trans_rets b) s).

Definition trans_node(fd: ident*func): ident* globdef fundef type :=
  (fst fd, Gfun (trans_body (snd fd))).

Definition trans_gvar (tc: ident*globvar type): ident*globdef fundef type :=
  (fst tc, Gvar (mkglobvar (gvar_info (snd tc)) (gvar_init (snd tc)) true false)).

Definition trans_program(p: LustreF.program): program :=
  let func := map trans_node (p.(node_block)) in
  let global := map trans_gvar (const_block p)  in
  AST.mkprogram (global++func) p.(node_main).

Lemma trans_v_typeof:
  forall i t, typeof (trans_v i t) = t.
Proof.
  unfold trans_v. intros.
  destruct (is_arystr t); auto.
Qed.

Lemma typepf_tran_binop_expr:
  forall b a1 a2 t,
  typeof (trans_binop_expr b a1 a2 t) = t.
Proof.
  unfold trans_binop_expr. intros.
  destruct (classify_binop _ _); auto.
Qed.

Lemma trans_expr_typeof:
  forall a, typeof (trans_expr a) =  Lustre.typeof a.
Proof.
  induction a; simpl; intros; auto.
  +destruct c; auto.
  +rewrite trans_v_typeof; auto.
  +apply typepf_tran_binop_expr; auto.
Qed.

Lemma trans_arg_typeoftr:
  forall a, is_arystr (Lustre.typeof a) = true ->
  typeof (trans_arg a) = Tpointer (Lustre.typeof a).
Proof.
  unfold trans_arg,mkaddr. intros. rewrite trans_expr_typeof; auto.
  rewrite H; auto.
Qed.

Lemma trans_arg_typeof_val:
  forall a, is_arystr (Lustre.typeof a) = false ->
  typeof (trans_arg a) = Lustre.typeof a.
Proof.
  unfold trans_arg,mkaddr. intros. rewrite trans_expr_typeof; auto.
  rewrite H; auto. rewrite trans_expr_typeof; auto.
Qed.

Lemma trans_para_ptype:
  forall a, snd (trans_para a) = trans_ptype (snd a).
Proof.
  unfold trans_para, trans_ptype. intros.
  destruct (is_arystr _); auto.
Qed.

Lemma trans_para_eq:
  forall a, trans_para a = (fst a, trans_ptype (snd a)).
Proof.
  unfold trans_para, trans_ptype. intros.
  destruct (is_arystr _); auto.
Qed.

Lemma paras_type_match:
  forall l,
  type_of_params l = to_typelist (map snd l).
Proof.
  unfold type_of_params.
  induction l; simpl; intros; auto.
  destruct a. simpl. rewrite IHl; auto.
Qed.

Lemma trans_paras_typeof:
  forall l args,
  map Lustre.typeof args = map (snd (B:=type)) l ->
  map (snd (B:=type)) (map trans_para l) = map typeof (map trans_arg args).
Proof.
  induction l, args; simpl; intros; auto.
  inv H. inv H. inv H.
  f_equal; eauto.
  unfold trans_para, trans_arg, mkaddr.
  rewrite trans_expr_typeof, H1.
  destruct (is_arystr _); auto.
  rewrite trans_expr_typeof, H1; auto.
Qed.

Lemma trans_rets_typeof_eq:
  forall lhs rets,
  map Lustre.typeof lhs = map (snd (B:=type)) rets ->
  map (fun a => snd (trans_ret a)) rets =  map typeof (map mkaddr (map trans_expr lhs)).
Proof.
  induction lhs,rets; simpl; intros; inv H; auto.
  f_equal; auto.
  rewrite trans_expr_typeof; auto.
Qed.

Lemma to_typelist_app:
  forall l1 l2,
  to_typelist (l1 ++ l2) = typelist_app (to_typelist l1) (to_typelist l2).
Proof.
  induction l1; simpl; intros; auto.
  rewrite IHl1; auto.
Qed.

Lemma trans_fundef_type:
  forall c f,
  argtys c = map (snd (B:=type)) (nd_args f) ->
  rettys c = nd_rets f ->
  type_of_fundef (trans_body f) = Tfunction (trans_ptypes c) Tvoid cc_default.
Proof.
  unfold type_of_fundef, type_of_function.
  unfold trans_body, trans_paras, trans_rets, trans_ptypes.
  simpl. intros.
  rewrite H, H0. rewrite paras_type_match.
  rewrite map_app. repeat rewrite map_map.
  f_equal. f_equal. f_equal.
  apply map_ext. intros. apply trans_para_ptype.
Qed.

Lemma trans_paras_rets_norepet:
  forall f, list_norepet (map fst (nd_args f++nd_rets f)) ->
  list_norepet (var_names (trans_paras f++trans_rets f)).
Proof.
  intros.
  unfold trans_paras, trans_rets, var_names.
  rewrite map_app in *. repeat rewrite map_map.
  rewrite map_ext with _ _ _ fst _; auto.
  intros. unfold trans_para.
  destruct (is_arystr _); auto.
Qed.

Lemma trans_nodes_gfun:
  forall l a, In a (map trans_node l) -> exists f, snd a = Gfun f.
Proof.
  induction l; simpl; intros; try tauto.
  destruct H; subst; simpl; eauto.
Qed.

Lemma trans_gvars_in:
  forall l a, In a (map trans_gvar l) -> exists v, snd a = Gvar v.
Proof.
  induction l; simpl; intros; try tauto.
  destruct H; subst; simpl; eauto.
Qed.
