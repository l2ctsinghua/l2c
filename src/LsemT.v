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
Require Import Inclusion.
Require Import Integers.
Require Import Maps.
Require Import Cop.
Require Import Cltypes.
Require Import List.
Require Import ExtraList.
Require Import Permutation.
Require Import Lvalues.
Require Import Peano.
Require Import Lident.
Require Import Ltypes.
Require Import Lop.
Require Import Lustre.
Require Import LustreS.
Require Import Lenv.
Require Import Lsem.
Require Import Lenvmatch.

Section SEMANTICS.

Variable semkind: bool.

Variable p: program.
Variable gc: locenv.

Section EVAL_EXPR.

Variable tyl: list (ident*type).

Inductive eval_expr: locenv -> expr -> type -> val -> Prop :=
  | eval_Expr: forall eh a v ty,
      eval_sexp gc eh a v ->
      ty = typeof a ->
      eval_expr eh (Expr a) ty v
  | eval_Earyprj_in: forall eh ty a is d m vi vl delta v,
      eval_sexp gc eh a (Vmvl m)->
      Forall2 (eval_sexp gc eh) is (vi::vl) ->
      (forall t, In t (map typeof is) -> t = type_int32s) ->
      ary_prjs (typeof a) vi vl = OK (Some delta,ty) ->
      load_mvl ty m delta v ->
      eval_expr eh (Earyprj a is d) ty v
  | eval_Earyprj_out: forall eh a ty is d vi vl v3,
      Forall2 (eval_sexp gc eh) is (vi::vl) ->
      eval_sexp gc eh d v3 ->
      typeof d = ty ->
      (forall t, In t (map typeof is) -> t = type_int32s) ->
      ary_prjs (typeof a) vi vl = OK (None, ty) ->
      eval_expr eh (Earyprj a is d) ty v3
  | eval_Ecase: forall eh ca pl i a v ty,
      eval_sexp gc eh ca (Vint i) ->
      select_case i pl = Some a ->
      eval_sexp gc eh a v ->
      ty = typeof a ->
      eval_expr eh (Ecase ca pl) ty v
  | eval_Eif: forall eh ty a a1 a2 v v1 b,
      eval_sexp gc eh a v ->
      typeof a = type_bool ->
      bool_val v type_bool = Some b ->
      typeof a1 = typeof a2  ->
      ty = typeof a1 ->
      eval_sexp gc eh (if b then a1 else a2) v1->
      eval_expr eh (Eif a a1 a2) ty v1
  | eval_Eprefix: forall eh op al vl v v1 ty,
      Forall2 (eval_sexp gc eh) al (v::vl) ->
      (forall t, In t (map typeof al) -> t = ty) ->
      sem_fold_operation op ty v vl = Some v1 ->
      has_type v1 ty ->
      eval_expr eh (Eprefix op al) ty v1
  | eval_Etypecmp: forall eh a1 a2 k b,
      eval_typecmp gc tyl eh a1 a2 b ->
      eval_expr eh (Etypecmp k a1 a2) type_bool (if (if k then b else negb b) then Vtrue else Vfalse).

End EVAL_EXPR.

Inductive store_loop(ty: type)(e: locenv)(b: ident): val -> locenv -> Prop :=
  | store_loop_intro: forall m' v v',
      eval_cast v ty v' ->
      store_mvl ty (alloc (sizeof ty)) Int.zero v' m'->
      store_loop ty e b v (PTree.set b (m',ty) e).

Definition stmts_topo_match (l1 l2: list stmt) : Prop :=
   Permutation l1 l2 /\
   topo_sorted (deps_of_stmts l2) /\
   nodup_lids (deps_of_stmts_simpl l2).

Inductive eval_node: env -> env -> ident*node -> list val -> list val -> Prop :=
   | exec_node: forall te te1 te2 eh eh1 eh3 se se1 vrs vas nid f ss,
      alloc_variables empty_locenv (allvarsof f) te ->
      ids_norepet f ->
      locenv_setvars te f.(nd_args) vas te1 ->
      (if semkind then stmts_topo_match f.(nd_stmt) ss else ss = f.(nd_stmt)) ->
      eval_stmts (nd_kind f) te1 (mkenv eh se) te2 (mkenv eh1 se1) ss ->
      eval_poststmt gc te2 eh1 (fbyeqsof ss) eh3 ->
      locenv_getvars te2 f.(nd_rets) vrs ->
      has_types vrs (map snd (nd_rets f)) ->
      eval_node (mkenv eh se) (mkenv eh3 se1) (nid,f) vas vrs

with eval_stmts: bool -> locenv -> env -> locenv -> env -> list stmt -> Prop :=
  | eval_stmts_nil: forall nk te e,
      eval_stmts nk te e te e nil
  | eval_stmts_cons: forall nk te te1 te2 e e1 e2 ta s ss,
      eval_stmt nk te e te1 e1 s empty_locenv ta->
      eval_stmts nk te1 e1 te2 e2 ss ->
      eval_stmts nk te e te2 e2 (s :: ss)

with eval_stmt: bool -> locenv -> env -> locenv -> env -> stmt -> locenv -> locenv -> Prop :=
  | eval_Sassign: forall nk te te' e ta lh a v v',
      eval_expr (type_block p) te a (snd lh) v ->
      ~ In (fst lh) (lids_of_e a) ->
      eval_cast v (snd lh) v' ->
      locenv_setlvar gc te (lvarof lh) v' te' ->
      eval_stmt nk te e te' e (Sassign lh a) ta ta
  | eval_Scall: forall nk te te' eh se se' ta args vargs vrets cdef lhs,
      eval_sexps gc te args vargs ->
      eval_apply nk te se se' args (map typeof args) vargs Int.zero cdef (map fst lhs) (map snd lhs) vrets ->
      locenv_setvars te lhs vrets te' ->
      eval_stmt nk te (mkenv eh se) te' (mkenv eh se') (Scall lhs cdef args) ta ta
  | eval_Sfor_start: forall nk te te1 te2 e e1 ta ta1 ta2 s j,
      eval_stmts nk te e te1 e (initstmtsof1 s) ->
      store_loop type_int32s ta ACG_I (Vint Int.zero) ta1 ->
      eval_stmt nk te1 e te2 e1 (Sfor false s j) ta1 ta2 ->
      eval_stmt nk te e te2 e1 (Sfor true s j) ta ta2
  | eval_Sfor_false: forall nk te e ta s j,
      eval_sexp gc ta (loop_cond j) Vfalse ->
      eval_stmt nk te e te e (Sfor false s j) ta ta
  | eval_Sfor_loop: forall nk te te1 te2 e e1 e2 ta ta1 ta2 ta3 s j,
      eval_sexp gc ta (loop_cond j) Vtrue ->
      eval_hstmt nk te e te1 e1 s ta ta1 ->
      eval_eqf gc ta1 ta2 loop_add ->
      eval_stmt nk te1 e1 te2 e2 (Sfor false s j) ta2 ta3 ->
      eval_stmt nk te e te2 e2 (Sfor false s j) ta ta3
  | eval_Sarydif_nil: forall nk te e ta lh i,
      eval_stmt nk te e te e (Sarydif lh i nil) ta ta
  | eval_Sarydif_cons: forall nk te te1 te2 e ta lid aid ty num i a al v v',
      eval_sexp gc te a v ->
      ~ (In lid (get_expids a)) ->
      typeof a = ty ->
      eval_cast v ty v' ->
      locenv_setlvar gc te (Saryacc (Svar lid (Tarray aid ty num)) (Sconst (Cint i) type_int32s) ty) v' te1 ->
      eval_stmt nk te1 e te2 e (Sarydif (lid,Tarray aid ty num) (Int.add i Int.one) al) ta ta ->
      eval_stmt nk te e te2 e (Sarydif (lid,Tarray aid ty num) i (a :: al)) ta ta
  | eval_Smix: forall nk te te1 te2 e lid ty a1 lis a3 o v3 v ta,
      eval_lindexs gc te (typeof a3) ty lis Int.zero o ->
      eval_sexp gc te a3 v3 ->
      eval_stmt nk te e te1 e (Sassign (lid,ty) (Expr a1)) ta ta->
      eval_cast v3 (typeof a3) v ->
      store_env (typeof a3) te1 lid o v te2 ->
      ~ In lid (get_lindexids lis++get_expids a3) ->
      eval_stmt nk te e te2 e (Smix (lid,ty) a1 lis a3) ta ta
  | eval_Sstruct_nil: forall nk te e lh ta,
      eval_stmt nk te e te e (Sstruct lh Fnil nil) ta ta
  | eval_Sstruct_cons: forall nk te te1 te2 e lid ty i t ftl a al v v' ta,
      eval_sexp gc te a v ->
      eval_cast v t v' ->
      locenv_setlvar gc te (Sfield (Svar lid ty) i t) v' te1 ->
      ~ (In lid (get_expids a)) ->
      typeof a = t ->
      eval_stmt nk te1 e te2 e (Sstruct (lid,ty) ftl al) ta ta ->
      eval_stmt nk te e te2 e (Sstruct (lid,ty) (Fcons i t ftl) (a::al)) ta ta
  | eval_Sskip: forall nk te e ta,
      eval_stmt nk te e te e Sskip ta ta
  | eval_Sfby_cycle_1: forall te te1 eh se ta lh id a1 a2 v2 v,
      eval_sexp empty_locenv eh (Svar ACG_INIT type_bool) Vtrue ->
      eval_sexp gc te a2 v2 ->
      snd lh = typeof a2 ->
      ~ In (fst lh) (get_lids a2) ->
      eval_cast v2 (snd lh) v ->
      locenv_setlvar gc te (lvarof lh) v te1 ->
      eval_stmt true te (mkenv eh se) te1 (mkenv eh se) (Sfby lh id a1 a2) ta ta
  | eval_Sfby_cycle_n: forall te te1 eh se ta lh id a1 a2 v1 v,
      eval_sexp empty_locenv eh (Svar ACG_INIT type_bool) Vfalse ->
      eval_sexp empty_locenv eh (Svar id (typeof a1)) v1 ->
      snd lh = typeof a1 ->
      eval_cast v1 (snd lh) v ->
      locenv_setlvar gc te (lvarof lh) v te1 ->
      id <> fst lh ->
      eval_stmt true te (mkenv eh se) te1 (mkenv eh se) (Sfby lh id a1 a2) ta ta
  | eval_Sfbyn_cycle_1: forall te te1 eh eh1 eh2 se ta lh id1 id2 aid sa aty i a1 a2 v1 v2 v,
      Tarray aid (typeof a1) (Int.unsigned i) = aty ->
      Svar id1 (make_fbyn_type id2 aty) = sa ->
      eval_sexp empty_locenv eh (Svar ACG_INIT type_bool) Vtrue->
      eval_sexp gc te a2 v2 ->
      eval_fbyn_init gc id1 id2 aid (typeof a2) Int.zero i v2 eh eh1 ->
      eval_eqf gc eh1 eh2 (Sfield sa FBYIDX type_int32s, Sconst (Cint Int.zero) type_int32s) ->
      eval_sexp empty_locenv eh2 (fbyn_aryacc sa (typeof a1) aty) v1 ->
      snd lh = typeof a2 ->
      snd lh = typeof a1 ->
      eval_cast v1 (snd lh) v ->
      locenv_setlvar gc te (lvarof lh) v te1 ->
      ~ In id1 (get_lids a2++fst lh :: nil) ->
      eval_stmt true te (mkenv eh se) te1 (mkenv eh2 se) (Sfbyn lh (id1,id2,aid) i a1 a2) ta ta
  | eval_Sfbyn_cycle_n: forall te te1 eh se ta lh id1 id2 aid sa aty i a1 a2 v1 v,
      Tarray aid (typeof a1) (Int.unsigned i) = aty ->
      Svar id1 (make_fbyn_type id2 aty) = sa ->
      eval_sexp empty_locenv eh (Svar ACG_INIT type_bool) Vfalse->
      eval_sexp empty_locenv eh (fbyn_aryacc sa (typeof a1) aty) v1 ->
      snd lh = typeof a2 ->
      snd lh = typeof a1 ->
      eval_cast v1 (snd lh) v ->
      locenv_setlvar gc te (lvarof lh) v te1 ->
      id1 <> fst lh ->
      eval_stmt true te (mkenv eh se) te1 (mkenv eh se) (Sfbyn lh (id1,id2,aid) i a1 a2) ta ta
  | eval_Sarrow: forall te te1 eh se ta lh a1 a2 v b,
      eval_sexp empty_locenv eh (Svar ACG_INIT type_bool) v ->
      bool_val v type_bool = Some b ->
      eval_stmt true te (mkenv eh se) te1 (mkenv eh se) (Sassign lh (Expr (if b then a1 else a2))) ta ta ->
      eval_stmt true te (mkenv eh se) te1 (mkenv eh se) (Sarrow lh a1 a2) ta ta

with eval_hstmt: bool -> locenv -> env -> locenv -> env -> hstmt -> locenv -> locenv -> Prop :=
  | eval_Hmaptyeq: forall nk te te1 e ta lid aid aid1 t num a1 a2 (k: bool) b i,
      eval_sexp gc ta (Svar ACG_I type_int32s) (Vint i) ->
      typeof a1 = Tarray aid1 t num ->
      eval_typecmp gc (type_block p) te (Saryacc a1 (Sconst (Cint i) type_int32s) t) (Saryacc a2 (Sconst (Cint i) type_int32s) t) b ->
      locenv_setlvar gc te (Saryacc (Svar lid (Tarray aid type_bool num)) (Sconst (Cint i) type_int32s) type_bool) (if (if k then b else negb b) then Vtrue else Vfalse) te1 ->
      eval_hstmt nk te e te1 e (Hmaptycmp (lid, (Tarray aid type_bool num)) k a1 a2) ta ta
  | eval_Hmapary: forall nk te te1 e ta lid aid t num op a1 a2 v v' i,
      eval_sexp gc ta (Svar ACG_I type_int32s) (Vint i) ->
      eval_sexp gc te (Sbinop op (Saryacc a1 (Sconst (Cint i) type_int32s) t) (Saryacc a2 (Sconst (Cint i) type_int32s) t) t) v ->
      eval_cast v t v' ->
      locenv_setlvar gc te (Saryacc (Svar lid (Tarray aid t num)) (Sconst (Cint i) type_int32s) t) v' te1 ->
      eval_hstmt nk te e te1 e (Hmapary (lid, (Tarray aid t num)) op a1 a2) ta ta
  | eval_Hmapunary: forall nk te te1 e ta lid aid t1 t2 num op a1 v v' i,
      eval_sexp gc ta (Svar ACG_I type_int32s) (Vint i) ->
      typeof a1 = Tarray aid t1 num ->
      ~ In lid (get_lids a1) ->
      prefix_unary_type op t1 t2 ->
      eval_sexp gc te (trans_prefix_unary_expr op (Saryacc a1 (Sconst (Cint i) type_int32s) t1) t2) v ->
      eval_cast v t2 v' ->
      locenv_setlvar gc te (Saryacc (Svar lid (Tarray aid t2 num)) (Sconst (Cint i) type_int32s) t2) v' te1 ->
      eval_hstmt nk te e te1 e (Hmapunary (lid, (Tarray aid t2 num)) op a1) ta ta
  | eval_Hflodary: forall nk te te1 e ta lid t op a1 a2 i,
      eval_sexp gc ta (Svar ACG_I type_int32s) (Vint i) ->
      eval_eqf gc te te1 (Svar lid t, Sbinop op (Svar lid t) (Saryacc a2 (Sconst (Cint i) type_int32s) t) t) ->
      eval_hstmt nk te e te1 e (Hfoldary (lid, t) op a1 a2) ta ta
  | eval_Hflodunary: forall nk te te1 e ta lid t op a1,
      eval_eqf gc te te1 (Svar lid t, Sunop op (Svar lid t) t) ->
      eval_hstmt nk te e te1 e (Hfoldunary (lid, t) op a1) ta ta
  | eval_Hflodcast: forall nk te te1 e ta lid t a1,
      eval_eqf gc te te1 (Svar lid t, Scast (Svar lid t) t) ->
      eval_hstmt nk te e te1 e (Hfoldcast (lid, t) a1 t) ta ta
  | eval_Harydef: forall nk te te1 e ta lid aid t num a v v' i,
      eval_sexp gc ta (Svar ACG_I type_int32s) (Vint i) ->
      eval_sexp gc te a v ->
      ~ In lid (get_expids a) ->
      typeof a = t ->
      eval_cast v t v' ->
      locenv_setlvar gc te (Saryacc (Svar lid (Tarray aid t num)) (Sconst (Cint i) type_int32s) t) v' te1 ->
      eval_hstmt nk te e te1 e (Harydef (lid,Tarray aid t num) a) ta ta
  | eval_Haryslc: forall nk te te1 e ta lid aid t num a j v v' i,
      eval_sexp gc ta (Svar ACG_I type_int32s) (Vint i) ->
      ~ In lid (get_expids a) ->
      eval_sexp gc te (Saryacc a (Sbinop Oadd (Sconst (Cint j) type_int32s) (Sconst (Cint i) type_int32s) type_int32s) t) v ->
      eval_cast v t v' ->
      locenv_setlvar gc te (Saryacc (Svar lid (Tarray aid t num)) (Sconst (Cint i) type_int32s) t) v' te1 ->
      eval_hstmt nk te e te1 e (Haryslc (lid, Tarray aid t num) a j) ta ta
  | eval_Hboolred_true: forall nk te te1 e lid a ta i,
      eval_sexp gc ta (Svar ACG_I type_int32s) (Vint i) ->
      eval_sexp gc te (Saryacc a (Sconst (Cint i) type_int32s) type_bool) Vtrue ->
      eval_eqf gc te te1 (Svar lid type_int32s, self_add lid) ->
      eval_hstmt nk te e te1 e (Hboolred (lid, type_int32s) a) ta ta
  | eval_Hboolred_false: forall nk te e lid a ta i,
      eval_sexp gc ta (Svar ACG_I type_int32s) (Vint i) ->
      eval_sexp gc te (Saryacc a (Sconst (Cint i) type_int32s) type_bool) Vfalse ->
      eval_hstmt nk te e te e (Hboolred (lid, type_int32s) a) ta ta
  | eval_Hmapcall: forall nk te te1 eh se se1 ta lhs cdef args atys rtys i vl vas vrs,
      eval_sexp gc ta (Svar ACG_I type_int32s) (Vint i) ->
      eval_sexps gc te args vl ->
      locenv_getarys i (map typeof args) atys vl vas ->
      eval_apply nk te se se1 args atys vas i cdef (map fst lhs) rtys vrs ->
      locenv_setarys gc (Sconst (Cint i) type_int32s) te lhs rtys vrs te1 ->
      eval_hstmt nk te (mkenv eh se) te1 (mkenv eh se1) (Hmapcall lhs cdef args) ta ta
  | eval_Hmapfoldcall: forall nk te te1 te2 te3 eh se se1 ta lid tid ty lhs cdef args i v atys vl init vargs vret vrs tys,
      eval_sexp gc ta (Svar ACG_I type_int32s) (Vint i) ->
      eval_stmt nk te (mkenv eh se) te1 (mkenv eh se) (Sassign (tid,ty) (Expr (Svar lid ty))) ta ta->
      eval_sexp gc te1 (Svar tid ty) v ->
      eval_sexps gc te1 args vl ->
      locenv_getarys i (map typeof args) atys vl vargs ->
      eval_apply nk te1 se se1 (Svar tid ty::args) (ty::atys) (v::vargs) i cdef (lid::map fst lhs) (ty::tys) (vret::vrs) ->
      locenv_setlvar gc te1 (Svar lid ty) vret te2 ->
      locenv_setarys gc (Sconst (Cint i) type_int32s) te2 lhs tys vrs te3 ->
      eval_hstmt nk te (mkenv eh se) te3 (mkenv eh se1) (Hmapfoldcall (lid,ty) (tid,ty) lhs cdef init args) ta ta

with eval_apply: bool -> locenv -> subenv -> subenv -> list sexp -> list type -> list val-> int-> calldef -> list ident -> list type -> list val -> Prop :=
  | eval_Apply: forall nk fd ef ef' te se se1 cdef i l args atys rtys vargs vargs' vrets,
      callorder nk (nd_kind (snd fd)) = true ->
      call_func (node_block p) cdef fd ->
      map snd (nd_args (snd fd)) = atys ->
      map snd (nd_rets (snd fd)) = rtys ->
      eval_casts vargs atys vargs' ->
      call_env cdef i se se1 ef ef' ->
      eval_node ef ef' fd vargs' vrets ->
      list_norepet (ACG_I::l) ->
      list_disjoint l (flat_map get_lids (arystr_sexps args)) ->
      te ! (callid cdef) = None ->
      eval_apply nk te se se1 args atys vargs i cdef l rtys vrets
.

Scheme eval_node_ind2 := Minimality for eval_node Sort Prop
  with eval_stmts_ind2 := Minimality for eval_stmts Sort Prop
  with eval_stmt_ind2 := Minimality for eval_stmt Sort Prop
  with eval_hstmt_ind2 := Minimality for eval_hstmt Sort Prop
  with eval_apply_ind2 := Minimality for eval_apply Sort Prop.


Inductive init_node: env -> ident*node -> Prop :=
  | init_node_: forall eh1 se nid f,
      ids_norepet f ->
      eval_init (length (fbyeqsof (nd_stmt f))) empty_locenv ((ACG_INIT,type_bool) :: fbyvarsof f.(nd_stmt)) eh1 ->
      (forall ty, In ty (map snd (nd_rets f ++ fbyvarsof f.(nd_stmt))) -> 0 < sizeof ty)%Z ->
      init_stmt (nd_kind f) (mkenv eh1 empty_subenv) (mkenv eh1 se) (instidof f.(nd_stmt)) ->
      init_node (mkenv eh1 se) (nid,f)

with init_stmt:  bool -> env -> env -> list calldef ->  Prop :=
  | init_call_nil: forall nk e,
      init_stmt nk e e nil
  | init_call_node_cons: forall nk le se se1 se2 fd ef c l,
      callorder nk (nd_kind (snd fd)) = true ->
      call_func (node_block p) c fd ->
      init_node ef fd ->
      se1 = PTree.set (instid c) (list_repeat (nat_of_int (intof_opti (callnum c))) ef) se ->
      init_stmt nk (mkenv le se1) (mkenv le se2) l ->
      init_stmt nk (mkenv le se) (mkenv le se2) (c::l).

Scheme init_node_ind2 := Minimality for init_node Sort Prop
  with init_stmt_ind2 := Minimality for init_stmt Sort Prop.
Combined Scheme init_node_stmt_ind2 from init_node_ind2, init_stmt_ind2.

Lemma eval_sexps_ptree_ids_match:
  forall e1 al vl,
  eval_sexps gc e1 al vl ->
  forall e2, ptree_ids_match (get_expsids al) e1 e2 ->
  eval_sexps gc e2 al vl.
Proof.
  induction 1; simpl; intros.
  constructor.
  apply ptree_ids_match_app in H1. destruct H1.
  constructor 2; auto.
  apply eval_sexp_ptree_ids_match with e1; auto.
  apply IHForall2; auto.
Qed.

Lemma eval_lindexs_ptree_ids_match:
  forall eh1 t ty lis i o,
  eval_lindexs gc eh1 t ty lis i o ->
  forall eh2 l, ptree_ids_match l eh1 eh2 ->
  incl (get_lindexids lis) l ->
  eval_lindexs gc eh2 t ty lis i o.
Proof.
  induction 1; simpl; intros.
  +constructor 1.
  +constructor 2 with delta ty; eauto.
   eapply IHeval_lindexs; eauto. red; intros. apply H4; simpl; auto.
  +constructor 3 with i; auto.
   eapply eval_sexp_ptree_ids_match; eauto.
    red; intros. apply H4; auto. apply H5; auto. apply in_or_app; auto.
   eapply IHeval_lindexs; eauto. red; intros. apply H5.
    apply in_or_app; auto.
Qed.

Lemma eval_typecmp_match:
  forall e1 l a1 a2 b,
  eval_typecmp gc l e1 a1 a2 b ->
  forall e2, ptree_ids_match (get_expids a1 ++ get_expids a2) e1 e2 ->
  ptree_some_match e1 e2 ->
  eval_typecmp gc l e2 a1 a2 b.
Proof.
  intros until l.
  induction 1 using eval_typecmp_ind2 with
  ( P0 := fun a1 a2 num aty i b =>
      forall e2, ptree_ids_match (get_expids a1 ++ get_expids a2) e1 e2 ->
      ptree_some_match e1 e2 ->
      eval_arycmp gc l e2 a1 a2 num aty i b)
  ( P1 := fun a1 a2 fld ftl b =>
      forall e2, ptree_ids_match (get_expids a1 ++ get_expids a2) e1 e2 ->
      ptree_some_match e1 e2 ->
      eval_strcmp gc l e2 a1 a2 fld ftl b);
  intros; try (econstructor; eauto; fail).
 +eapply eval_typecmp_chunk with chunk v; eauto.
  eapply eval_sexp_ptree_ids_match; simpl; eauto.
 +eapply eval_typecmp_array; eauto;
  try (eapply eval_sexp_ptree_ids_match; simpl; eauto).
  red; intros; apply H6; apply in_or_app;auto.
  red; intros; apply H6; apply in_or_app;auto.
  destruct (e2 ! (comp_funcs_id aid)) eqn:?; auto.
  destruct H7 with (comp_funcs_id aid) p0 as [? ?]; auto.
  congruence.
 +eapply eval_typecmp_struct; eauto;
  try eapply eval_sexp_ptree_ids_match; simpl; eauto.
  red; intros; apply H6; apply in_or_app;auto.
  red; intros; apply H6; apply in_or_app;auto.
  destruct (e2 ! (comp_funcs_id sid)) eqn:?; auto.
  destruct H7 with (comp_funcs_id sid) p0 as [? ?]; auto.
  congruence.
 +apply eval_arycmp_loop; eauto.
  eapply IHeval_typecmp; simpl; eauto.
  repeat rewrite <-app_nil_end; auto.
Qed.

Lemma eval_expr_ptree_ids_match:
  forall l a e1 ty v,
  eval_expr l e1 a ty v ->
  forall e2, ptree_ids_match (ridl_of_e a) e1 e2 ->
  ptree_some_match e1 e2 ->
  eval_expr l e2 a ty v.
Proof.
  induction 1; simpl; intros.
  +eapply eval_Expr; eauto. eapply eval_sexp_ptree_ids_match; eauto.
  +eapply eval_Earyprj_in; eauto.
   -eapply eval_sexp_ptree_ids_match; eauto.
    red; intros. apply H4. in_tac.
   -eapply eval_sexps_ptree_ids_match; eauto.
    red; intros. apply H4. in_tac.
  +eapply eval_Earyprj_out; eauto.
   -eapply eval_sexps_ptree_ids_match; eauto.
    red; intros. apply H4. in_tac.
   -eapply eval_sexp_ptree_ids_match; eauto.
    red; intros. apply H4. in_tac.
  +eapply eval_Ecase; eauto; eapply eval_sexp_ptree_ids_match; eauto.
   red. intros. apply H3. in_tac.
   apply select_case_in in H0. red; intros. apply H3.
   rewrite <- flat_map_map. apply flat_map_in with (f:=get_expids) in H0.
   apply H0 in H5. in_tac.
  +eapply eval_Eif; eauto; eapply eval_sexp_ptree_ids_match; eauto.
   red; intros. apply H5. in_tac.
   red; intros. apply H5. destruct b; in_tac.
  +eapply eval_Eprefix; eauto. eapply eval_sexps_ptree_ids_match; eauto.
  +eapply eval_Etypecmp; eauto.
   eapply eval_typecmp_match; eauto.
Qed.

Lemma eval_fbyeqs_ptree_ids_match:
  forall te e e' s,
  eval_fbyeqs gc te e e' (fbyeqof s) ->
  (forall l1, list_disjoint (map fst (fbyvarsof_s s)) l1 ->
   ptree_ids_match l1 e e').
Proof.
  destruct s; simpl; intros;
  try (inv H; econstructor).
  +inv H. inv H6. inv H5.
   eapply locenv_setlvar_ptree_ids_match; eauto.
  +destruct p1. destruct p1.
   inv H. inv H6. inv H7. inv H5. inv H4.
   apply ptree_ids_match_trans with e1; auto.
   eapply locenv_setlvar_ptree_ids_match; eauto.
   inv H7. eapply locenv_setlvar_ptree_ids_match; eauto.
  +inv H. inv H5. inv H6. red; auto.
Qed.

Lemma eval_fbyeqs_swap_first:
  forall te e1 e1' s,
  eval_fbyeqs gc te e1 e1' (fbyeqof s) ->
  forall e2,
  ptree_ids_match (map fst (fbyvarsof_s s)) e1 e2 ->
  exists e2', eval_fbyeqs gc te e2 e2' (fbyeqof s)
    /\ ptree_ids_match (map fst (fbyvarsof_s s)) e1' e2'
    /\ locenv_stmt_sets (map fst (fbyvarsof_s s))  e1 e1' e2 e2'.
Proof.
  destruct s; simpl; intros; inv H;
  try (exists e2; repeat (split; auto);
    [constructor | apply locenv_stmt_sets_refl]; fail).
  +inv H6. inv H5.
   eapply ptree_ids_match_locenv_setlvar_exists in H4; eauto.
   destruct H4 as [e2' [? [? [? [? ?]]]]].
   exists e2'. repeat (split; auto).
   -constructor 2 with e2'; auto.
    constructor 1 with v v'; auto. constructor.
   -econstructor; eauto. red; auto.
   -simpl; auto. red; auto.
  +destruct p1. destruct p1.
   inv H1. inv H5. inv H7. inv H2. inv H6. inv H7.
   eapply ptree_ids_match_locenv_setlvar_exists in H5; eauto.
   destruct H5 as [e21 [? [? [? [? ?]]]]].
   eapply ptree_ids_match_locenv_setlvar_exists in H13; eauto.
   destruct H13 as [e2' [? [? [? [? ?]]]]].
   exists e2'. repeat (split; auto).
   -constructor 2 with e21; auto.
    *constructor 1 with v v'; auto.
    *constructor 2 with e2'; auto.
     constructor 2. constructor 1 with v0 v'0; auto.
     eapply eval_sexp_ptree_ids_match; eauto.
     constructor 1 with Mint32; auto.
     constructor.
   -apply locenv_stmt_sets_trans with e0 e21; auto.
    econstructor; eauto. simpl. red; auto.
    econstructor; eauto. simpl. red; auto.
   -simpl. red; auto.
   -simpl. red; simpl; intros.
    destruct H as [ | [|]]; subst; tauto.
  +inv H5. inv H6. exists e2. repeat split; auto.
   constructor 2 with e2; constructor. apply locenv_stmt_sets_refl.
Qed.

Lemma eval_fbyeqs_swap:
  forall te e e' x y,
  eval_fbyeqs gc te e e' (fbyeqof y ++ fbyeqof x) ->
  list_norepet (map fst (fbyvarsof_s y ++ fbyvarsof_s x)) ->
  eval_fbyeqs gc te e e' (fbyeqof x ++ fbyeqof y).
Proof.
  intros. apply eval_fbyeqs_app_inv in H.
  destruct H as [e0 [? ?]].
  rewrite map_app in H0. apply list_norepet_app in H0.
  destruct H0 as [? [? ?]].
  assert (A: ptree_ids_match (map fst (fbyvarsof_s x)) e e0).
    apply eval_fbyeqs_ptree_ids_match with te y; auto.
  assert (A1: ptree_ids_match (map fst (fbyvarsof_s y)) e0 e').
    eapply eval_fbyeqs_ptree_ids_match; eauto.
    apply list_disjoint_sym; auto.
  generalize H; intros.
  destruct eval_fbyeqs_swap_first with te e0 e' x e as [e21 [? [B B1]]]; eauto.
    eapply ptree_ids_match_swap; eauto.
  apply eval_fbyeqs_app with e21; auto.
  assert(A2: ptree_ids_match (map fst (fbyvarsof_s y)) e e21).
    eapply eval_fbyeqs_ptree_ids_match; eauto.
    apply list_disjoint_sym; auto.
  destruct eval_fbyeqs_swap_first with te e e0 y e21 as [e2' [? [B2 B3]]]; auto.
  assert (A7: e' = e2').
    inv B1. inv B3.
    eapply ptree_sets_determ; eauto.
    eapply ptree_sets_swap; eauto.
    apply list_disjoint_incl with (map fst (fbyvarsof_s x)) (map fst (fbyvarsof_s y)); eauto.
    apply list_disjoint_sym; auto.
  subst. auto.
Qed.

Lemma eval_fbyeqs_permut:
  forall te l1 l2,
  Permutation l1 l2 ->
  forall eh eh',
  list_norepet (map fst (fbyvarsof l1)) ->
  eval_fbyeqs gc te eh eh' (fbyeqsof l1) ->
  eval_fbyeqs gc te eh eh' (fbyeqsof l2).
Proof.
  induction 1; simpl; intros; auto.
  +apply eval_fbyeqs_app_inv in H1.
   destruct H1 as [e1 [? ?]].
   rewrite map_app in H0. apply list_norepet_app in H0.
   destruct H0 as [? [? ?]].
   apply eval_fbyeqs_app with e1; auto.
  +rewrite <-app_ass in *.
   rewrite map_app in H. apply list_norepet_app in H.
   destruct H as [? [? ?]].
   apply eval_fbyeqs_app_inv in H0.
   destruct H0 as [e1 [? ?]].
   apply eval_fbyeqs_app with e1; auto.
   eapply eval_fbyeqs_swap; eauto.
  +eapply IHPermutation2; eauto.
   eapply list_norepet_permut; eauto.
   apply Permutation_map. apply flat_map_permutation; auto.
Qed.

Lemma eval_poststmt_permut:
  forall te eh eh' l1 l2,
  Permutation l1 l2 ->
  list_norepet (map fst (fbyvarsof l1)) ->
  eval_poststmt gc te eh (fbyeqsof l1) eh' ->
  eval_poststmt gc te eh (fbyeqsof l2) eh'.
Proof.
  intros. inv H1. constructor 1 with eh1.
  eapply eval_fbyeqs_permut; eauto.
  erewrite <-Permutation_length; eauto.
  apply flat_map_permutation; auto.
Qed.

Lemma eval_stmts_split:
  forall nk eql1 eql2 te1 e1 te3 e3,
  eval_stmts nk te1 e1 te3 e3 (eql1 ++ eql2) ->
  exists te2 e2, eval_stmts nk te1 e1 te2 e2 eql1
    /\ eval_stmts nk te2 e2 te3 e3 eql2.
Proof.
  induction eql1; simpl; intros.
  exists te1, e1; split; trivial. constructor.
  inversion_clear H.
  destruct IHeql1 with eql2 te0 e0 te3 e3 as [te2 [e2 []]];trivial.
  exists te2, e2; split; trivial.
  econstructor 2; eauto.
Qed.

Lemma eval_stmts_app:
  forall nk eql1 eql2 te1 e1 te2 e2 te3 e3,
  eval_stmts nk te1 e1 te2 e2 eql1 ->
  eval_stmts nk te2 e2 te3 e3 eql2 ->
  eval_stmts nk te1 e1 te3 e3 (eql1 ++ eql2).
Proof.
  induction eql1; simpl; intros; inversion_clear H; trivial.
  econstructor 2; eauto.
Qed.

Lemma eval_sassign_env_ids_match:
  forall nk e e1 p a l l1 te te1 ta1 ta2,
  eval_stmt nk te e te1 e1 (Sassign p a) ta1 ta2 ->
  list_disjoint l l1 ->
  In (fst p) l ->
  ptree_ids_match l1 te te1.
Proof.
  intros. inv H.
  eapply locenv_setlvar_ptree_ids_match; eauto.
  red; simpl; intros. destruct H; subst; try tauto.
  eapply H0; eauto.
Qed.

Lemma eval_initstmt_ptree_ids_match:
  forall l nk te te' e e',
  eval_stmts nk te e te' e' l ->
  forall l1, list_disjoint (flat_map lidl_of_s l) l1 ->
  Forall is_assign l ->
  ptree_ids_match l1 te te'.
Proof.
  induction 1; simpl; intros.
  +red; auto.
  +inv H2. destruct s; try tauto.
   apply ptree_ids_match_trans with te1.
   eapply eval_sassign_env_ids_match; eauto. simpl. auto.
   apply IHeval_stmts; auto.
   red; intros. apply H1; auto. simpl. auto.
Qed.

Lemma locenv_setarys_ptree_ids_match:
  forall i e l tys vl e' l1,
  locenv_setarys gc i e l tys vl e' ->
  list_disjoint (map fst l) l1 ->
  ptree_ids_match l1 e e'.
Proof.
  induction 1; simpl; intros.
  red; auto.
  apply ptree_ids_match_trans with e1; auto.
  eapply locenv_setlvar_ptree_ids_match; eauto.
  red; simpl; intros. apply H1; auto.
   destruct H2; subst; simpl; auto. tauto.
  eapply IHlocenv_setarys; eauto.
   red; intros. apply H1; auto. simpl; auto.
Qed.

Lemma eval_apply_ptree_ids_match:
  forall nk te se se' al atys vas i cdef lhs rtys vrs l,
  eval_apply nk te se se' al atys vas i cdef lhs rtys vrs ->
  list_disjoint (map instid (cons_inst cdef)) l ->
  ptree_ids_match l se se'.
Proof.
  unfold cons_inst. intros. inv H.
  eapply call_env_ptree_ids_match; eauto.
Qed.

Lemma ptree_ids_match_setarys_exists:
  forall i e1 l tys vl e1',
  locenv_setarys gc (Sconst (Cint i) type_int32s) e1 l tys vl e1' ->
  forall l1 e2, ptree_ids_match (l1++map fst l) e1 e2 ->
  exists e2' ml, locenv_setarys gc (Sconst (Cint i) type_int32s) e2 l tys vl e2'
    /\ ptree_ids_match (l1++map fst l) e1' e2'
    /\ ptree_sets e1 (map fst l) ml e1'
    /\ ptree_sets e2 (map fst l) ml e2'.
Proof.
  induction 1; simpl; intros.
  exists e2; exists nil; repeat split; auto; constructor.

  eapply ptree_ids_match_locenv_setlvar_exists in H; simpl; eauto.
  destruct H as [e21 [m' [? [? [? ?]]]]]; simpl; auto.
  destruct IHlocenv_setarys with l1 e21 as [e2' [ml [? [? [? ?]]]]]; auto.
    subst. red. intros. apply H2. in_tac.
  simpl in *. change (id :: map fst dl) with ((id :: nil) ++ map fst dl).
  exists e2', (m'++ml). repeat (split; auto).
  +constructor 2 with e21; auto.
  +red; simpl; intros. eapply ptree_sets_match; eauto.
  +eapply ptree_sets_trans; eauto.
  +eapply ptree_sets_trans; eauto.
  +incl_tac.
Qed.

Lemma eval_hstmt_env_ids_match:
  forall nk te1 e1 te2 e2 s ta1 ta2,
  eval_hstmt nk te1 e1 te2 e2 s ta1 ta2 ->
  forall l l1 l2 j,
  list_disjoint (lidl_of_fs s) l ->
  list_disjoint (map instid (instidof_s (Sfor false s j))) l2 ->
  ptree_ids_match l te1 te2
    /\ env_ids_match l1 l2 e1 e2.
Proof.
  induction 1; simpl; intros; split;
  try (apply env_ids_match_refl); try constructor;
  try (red; auto; fail);
  try (eapply eval_apply_ptree_ids_match; eauto; fail);
  try (eapply locenv_setlvar_ptree_ids_match; eauto; fail).
  +inv H0. eapply locenv_setlvar_ptree_ids_match; eauto.
  +inv H. eapply locenv_setlvar_ptree_ids_match; eauto.
  +inv H. eapply locenv_setlvar_ptree_ids_match; eauto.
  +inv H1. eapply locenv_setlvar_ptree_ids_match; eauto.
  +eapply locenv_setarys_ptree_ids_match; eauto.
  +eapply ptree_ids_match_trans; eauto.
   eapply eval_sassign_env_ids_match; eauto. simpl; auto.
   eapply ptree_ids_match_trans; eauto.
   eapply locenv_setlvar_ptree_ids_match; eauto.
   red; simpl; intros ? ? A A1. destruct A; subst; try tauto.
   apply H7; auto. simpl; auto.
   eapply locenv_setarys_ptree_ids_match; eauto.
   red. intros. apply H7; auto. simpl; auto.
Qed.

Lemma eval_fbyn_init_ptree_ids_match:
  forall id1 id2 aid t i j v eh eh' l,
  eval_fbyn_init gc id1 id2 aid t i j v eh eh' ->
  list_disjoint (id1 :: nil) l ->
  ptree_ids_match l eh eh'.
Proof.
  induction 1; intros; auto.
  +apply ptree_ids_match_trans with eh1; auto.
   eapply locenv_setlvar_ptree_ids_match; eauto.
   subst; simpl; auto.
  +red; intros; auto.
Qed.

Lemma eval_assign_ptree_some_match:
  forall nk te e te' e' lh s ta ta',
  eval_stmt nk te e te' e' (Sassign lh (Expr s)) ta ta' ->
  ptree_some_match te' te /\ ptree_some_match te te'.
Proof.
  intros. inv H.
  eapply locenv_setlvar_ptree_some_match; eauto.
Qed.

Lemma eval_initstmts_ptree_some_match:
  forall nk te e te' e' l,
  eval_stmts nk te e te' e' l ->
  Forall is_assign l ->
  ptree_some_match te' te /\ ptree_some_match te te'.
Proof.
  induction 1; intros.
  +split; red; eauto.
  +inv H1. destruct s; try tauto.
   inv H. eapply locenv_setlvar_ptree_some_match in H15; eauto.
   destruct IHeval_stmts; auto. destruct H15.
   split; eapply ptree_some_match_trans; eauto.
Qed.

Lemma eval_hstmt_ptree_some_match:
  forall nk te e te' e' s ta ta',
  eval_hstmt nk te e te' e' s ta ta' ->
  ptree_some_match te' te /\ ptree_some_match te te'.
Proof.
  induction 1; intros; auto;
  try (eapply locenv_setlvar_ptree_some_match; eauto; fail);
  try (eapply eval_assign_ptree_some_match; eauto; fail).
  +inv H0. eapply locenv_setlvar_ptree_some_match; eauto.
  +inv H. eapply locenv_setlvar_ptree_some_match; eauto.
  +inv H. eapply locenv_setlvar_ptree_some_match; eauto.
  +inv H1. eapply locenv_setlvar_ptree_some_match; eauto.
  +split; red; intros; eauto.
  +eapply locenv_setarys_ptree_some_match; eauto.
  +eapply eval_assign_ptree_some_match in H0; eauto.
   eapply locenv_setlvar_ptree_some_match in H5; eauto.
   eapply locenv_setarys_ptree_some_match in H6; eauto.
   destruct H0,H5,H6. split.
   apply ptree_some_match_trans with te2; auto.
   apply ptree_some_match_trans with te1; auto.
   eapply ptree_some_match_trans with te1; auto.
   eapply ptree_some_match_trans with te2; auto.
Qed.

Lemma eval_stmt_ptree_some_match:
  forall nk te e te' e' s ta ta',
  eval_stmt nk te e te' e' s ta ta' ->
  ptree_some_match te' te /\ ptree_some_match te te'.
Proof.
  induction 1; simpl; intros; auto;
  try (eapply locenv_setlvar_ptree_some_match; eauto; fail);
  try (split; red; intros; eauto; fail).
  +eapply locenv_setvars_ptree_some_match; eauto.
  +eapply eval_initstmts_ptree_some_match in H; eauto.
   destruct H, IHeval_stmt. split; eapply ptree_some_match_trans; eauto.
   apply initstmtsof_is_assign.
  +eapply eval_hstmt_ptree_some_match in H0; eauto.
   destruct H0, IHeval_stmt. split; eapply ptree_some_match_trans; eauto.
  +apply locenv_setlvar_ptree_some_match in H3.
   destruct H3, IHeval_stmt. split; eapply ptree_some_match_trans; eauto.
  +apply store_env_ptree_some_match in H3.
   destruct H3, IHeval_stmt. split; eapply ptree_some_match_trans; eauto.
  +apply locenv_setlvar_ptree_some_match in H1.
   destruct H1, IHeval_stmt. split; eapply ptree_some_match_trans; eauto.
Qed.

Lemma eval_stmt_env_ids_match:
  forall nk te te' e e' s te1 te2,
  eval_stmt nk te e te' e' s te1 te2 ->
  (forall l1 l2 l3, list_disjoint (map fst (fbyvarsof_s s)) l1 ->
   list_disjoint (map instid (instidof_s s)) l2 ->
   list_disjoint (lidl_of_s s) l3 ->
   env_ids_match l1 l2 e e'
    /\ ptree_ids_match l3 te te').
Proof.
  induction 1; intros; try destruct e; split;
  try econstructor; try (red; eauto; fail);
  try (eapply locenv_setlvar_ptree_ids_match; eauto; fail);
  try (eapply locenv_setvars_ptree_ids_match; eauto; fail).
  +eapply eval_apply_ptree_ids_match; eauto.
  +destruct IHeval_stmt with l1 l2 l3; auto.
  +apply ptree_ids_match_trans with te1; auto.
   eapply eval_initstmt_ptree_ids_match; eauto.
   red; intros. apply H4; auto. simpl.
   eapply lidl_of_fs_incl; eauto.
   eapply initstmtsof_is_assign; eauto.
   destruct IHeval_stmt with l1 l2 l3; auto.
  +apply env_ids_match_trans with e1; auto.
   eapply eval_hstmt_env_ids_match; eauto.
   destruct IHeval_stmt with l1 l2 l3; auto.
  +apply ptree_ids_match_trans with te1; auto.
   eapply eval_hstmt_env_ids_match; eauto.
   destruct IHeval_stmt with l1 l2 l3; auto.
  +apply ptree_ids_match_trans with te1; auto.
   eapply locenv_setlvar_ptree_ids_match in H3; eauto.
   destruct IHeval_stmt with l1 l2 l3; auto.
  +apply ptree_ids_match_trans with te1; auto.
   inv H1. eapply locenv_setlvar_ptree_ids_match; eauto.
   inv H3. eapply ptree_ids_match_set; eauto.
  +apply ptree_ids_match_trans with te1; auto.
   eapply locenv_setlvar_ptree_ids_match in H1; eauto.
   destruct IHeval_stmt with l1 l2 l3; auto.
  +simpl in *. apply ptree_ids_match_trans with eh1; auto.
   eapply eval_fbyn_init_ptree_ids_match; eauto.
   inv H4. eapply locenv_setlvar_ptree_ids_match; eauto.
  +destruct IHeval_stmt with l1 l2 l3; destruct b;auto.
Qed.

Lemma env_ids_match_eval_assign:
  forall nk a s te1 te1' e1 e1' e2 te2 ta1 ta2 l1,
  eval_stmt nk te1 e1 te1' e1' (Sassign a (Expr s)) ta1 ta2 ->
  incl (get_expids s ++ fst a::nil) l1 ->
  ptree_ids_match l1 te1 te2 ->
  exists te2', eval_stmt nk te2 e2 te2' e2 (Sassign a (Expr s)) ta1 ta2
    /\ ptree_ids_match l1 te1' te2'
    /\ locenv_stmt_sets (fst a :: nil) te1 te1' te2 te2'.
Proof.
  intros. inv H.
  eapply ptree_ids_match_locenv_setlvar_exists in H14; eauto.
  destruct H14 as [te2' [ml [? [? [? ?]]]]].
  exists te2'. repeat (split; auto).
  +eapply eval_Sassign; eauto.
   inv H4. econstructor; eauto.
   eapply eval_sexp_ptree_ids_match; eauto.
   red. intros. apply H1. apply H0. apply in_or_app; auto.
  +constructor 1 with (fst a::nil) ml; simpl; auto;
   try red; auto; constructor.
  +simpl. red. intros. apply H0. apply in_or_app. auto.
Qed.

Lemma ptree_ids_match_eval_initstmt:
  forall l nk te1 e1 te1' e2,
  eval_stmts nk te1 e1 te1' e1 l ->
  forall te2, Forall is_assign l ->
  ptree_ids_match (flat_map ridl_of_s l ++ flat_map lidl_of_s l) te1 te2 ->
  exists te2', eval_stmts nk te2 e2 te2' e2 l
    /\ ptree_ids_match (flat_map ridl_of_s l ++ flat_map lidl_of_s l) te1' te2'
    /\ locenv_stmt_sets (flat_map lidl_of_s l) te1 te1' te2 te2'.
Proof.
  induction 1; simpl; intros.
  +exists te2. repeat (split; auto). constructor.
   apply locenv_stmt_sets_refl.
  +inv H1. destruct s; try tauto. destruct e4; try tauto. simpl in *.
   eapply env_ids_match_eval_assign with (e2:=e2) (te2:=te0) (l1:=(get_expids s++flat_map ridl_of_s ss)++fst p0::flat_map lidl_of_s ss) in H; eauto.
   destruct H as [te21 [? [? ?]]].
   destruct IHeval_stmts with te21 as [te2' [? [? ?]]]; auto.
   red; intros. apply H1. in_tac.
   exists te2'. repeat (split; auto).
   -econstructor; eauto.
   -red; intros. inv H8. eapply ptree_sets_match; eauto.
   -apply locenv_stmt_sets_incl with (s2:=fst p0 :: flat_map lidl_of_s ss) in H3; simpl.
    apply locenv_stmt_sets_incl with (s2:=fst p0 :: flat_map lidl_of_s ss) in H8; simpl.
    eapply locenv_stmt_sets_trans; eauto.
    incl_tac. incl_tac.
   -incl_tac.
Qed.

Lemma eval_apply_match_ptree_sets_exist:
  forall nk te1 se1 se1' al atys vas i c lhs rtys vrs,
  eval_apply nk te1 se1 se1' al atys vas i c lhs rtys vrs ->
  forall te2 se2, ptree_ids_match (map instid (cons_inst c)) se1 se2 ->
  ptree_some_match te1 te2 ->
  exists se2', eval_apply nk te2 se2 se2' al atys vas i c lhs rtys vrs
    /\ ptree_ids_match (map instid (cons_inst c)) se1' se2'
    /\ exists l el, incl l (map instid (cons_inst c))
        /\ ptree_sets se1 l el se1'
        /\ ptree_sets se2 l el se2'.
Proof.
  intros. inv H.
  eapply call_env_match_ptree_sets_exist in H7; eauto.
  destruct H7 as [se2' [? [? [l1 [el [? [? ?]]]]]]].
  exists se2'. repeat (split; auto).
  econstructor 1; eauto.
  destruct (te2 ! (callid c)) eqn:?; auto.
  destruct H1 with (callid c) p0; auto. congruence.
  exists l1, el; split; auto.
Qed.

Inductive env_stmt_sets(s: stmt): env -> env -> env -> env -> Prop :=
  | env_stmt_sets_: forall eh1 eh1' eh2 eh2' se1 se1' se2 se2' l1 l2 vl1 vl2,
     incl l1 (map fst (fbyvarsof_s s)) ->
     incl l2 (map instid (instidof_s s)) ->
     ptree_sets eh1 l1 vl1 eh1' ->
     ptree_sets se1 l2 vl2 se1' ->
     ptree_sets eh2 l1 vl1 eh2' ->
     ptree_sets se2 l2 vl2 se2' ->
     env_stmt_sets s (mkenv eh1 se1) (mkenv eh1' se1') (mkenv eh2 se2) (mkenv eh2' se2').

Lemma env_stmt_sets_trans:
  forall s e1 e1' e1'' e2 e2' e2'',
  env_stmt_sets s e1 e1' e2 e2' ->
  env_stmt_sets s e1' e1'' e2' e2''->
  env_stmt_sets s e1 e1'' e2 e2''.
Proof.
  intros. inv H; inv H0.
  constructor 1 with (l1++l0) (l2++l3) (vl1++vl0) (vl2++vl3);
  try (eapply ptree_sets_trans; eauto);
  apply incl_app; auto.
Qed.

Lemma env_stmt_sets_refl:
  forall s e1 e2,
  env_stmt_sets s e1 e1 e2 e2.
Proof.
  intros. destruct e1, e2.
  constructor 1 with nil nil nil nil;
  try constructor; red; intros ? A; inv A.
Qed.

Lemma env_ids_match_eval_htmt_exists:
  forall s nk te1 te1' e1 e1' ta ta1,
  eval_hstmt nk te1 e1 te1' e1' s ta ta1 ->
  forall te2 e2 j l, env_ids_match l (map instid (instidofh s)) e1 e2 ->
  ptree_ids_match (ridl_of_fs s ++ lidl_of_fs s) te1 te2 ->
  ptree_some_match te1 te2 ->
  exists te2' e2', eval_hstmt nk te2 e2 te2' e2' s ta ta1
    /\ env_ids_match l (map instid (instidofh s)) e1' e2'
    /\ ptree_ids_match (ridl_of_fs s ++ lidl_of_fs s) te1' te2'
    /\ env_stmt_sets (Sfor false s j) e1 e1' e2 e2'
    /\ locenv_stmt_sets (lidl_of_fs s) te1 te1' te2 te2'.
Proof.
  induction 1; simpl; intros.
  +eapply ptree_ids_match_locenv_setlvar_exists in H2; eauto.
   destruct H2 as [te2' [ml [? [? [? ?]]]]].
   exists te2', e2. repeat (split; auto).
   -eapply eval_Hmaptyeq; eauto.
    eapply eval_typecmp_match; eauto.
    simpl. red; intros. repeat rewrite <-app_nil_end in H9.
    apply H4. in_tac.
   -apply env_stmt_sets_refl.
   -econstructor 1 with (lid::nil) ml; simpl; eauto; try red; auto; constructor.
   -simpl. incl_tac.
  +eapply ptree_ids_match_locenv_setlvar_exists in H2; simpl; eauto.
   destruct H2 as [te2' [ml [? [? [? ?]]]]]. simpl in *.
   exists te2', e2. repeat (split; auto).
   -eapply eval_Hmapary; eauto.
    eapply eval_sexp_ptree_ids_match; simpl; eauto.
    repeat rewrite <-app_nil_end. red; intros. apply H4. in_tac.
   -apply env_stmt_sets_refl.
   -econstructor 1 with (lid::nil) ml; simpl; eauto; try red; auto; constructor.
   -simpl. incl_tac.
  +eapply ptree_ids_match_locenv_setlvar_exists in H5; simpl; eauto.
   destruct H5 as [te2' [ml [? [? [? ?]]]]]. simpl in *.
   exists te2', e2. repeat (split; auto).
   -eapply eval_Hmapunary; eauto.
    eapply eval_sexp_ptree_ids_match; simpl; eauto.
    red; intros. apply H7.
    destruct op; simpl in *; rewrite <-app_nil_end in *; in_tac.
   -apply env_stmt_sets_refl.
   -econstructor 1 with (lid::nil) ml; simpl; eauto; try red; auto; constructor.
   -incl_tac.
  +inv H0. eapply ptree_ids_match_locenv_setlvar_exists in H11; simpl; eauto.
   destruct H11 as [te2' [? [? [? [? ?]]]]].
   exists te2', e2. repeat (split; auto).
   -eapply eval_Hflodary; eauto.
    econstructor 1; eauto.
    eapply eval_sexp_ptree_ids_match; simpl; eauto.
    red; intros. apply H2. rewrite <-app_nil_end in *. in_tac.
    apply eval_sbinop_by_value in H6. destruct H6.
    econstructor; eauto.
   -apply env_stmt_sets_refl.
   -econstructor 1; eauto. red; auto.
   -simpl. incl_tac.
  +inv H. eapply ptree_ids_match_locenv_setlvar_exists in H10; simpl; eauto.
   destruct H10 as [te2' [? [? [? [? ?]]]]].
   exists te2', e2. repeat (split; auto).
   -eapply eval_Hflodunary; eauto.
    econstructor 1; eauto.
    eapply eval_sexp_ptree_ids_match; simpl; eauto.
    red; intros. apply H1. in_tac.
    apply eval_sunop_by_value in H5. destruct H5.
    econstructor; eauto.
   -apply env_stmt_sets_refl.
   -econstructor 1; eauto. red; auto.
   -simpl. incl_tac.
  +inv H. eapply ptree_ids_match_locenv_setlvar_exists in H10; simpl; eauto.
   destruct H10 as [te2' [? [? [? [? ?]]]]].
   exists te2', e2. repeat (split; auto).
   -eapply eval_Hflodcast; eauto.
    econstructor 1; eauto.
    eapply eval_sexp_ptree_ids_match; simpl; eauto.
    red; intros. apply H1. in_tac.
    apply eval_scast_by_value in H5. destruct H5.
    econstructor; eauto.
   -apply env_stmt_sets_refl.
   -econstructor 1; eauto. red; auto.
   -simpl. incl_tac.
  +eapply ptree_ids_match_locenv_setlvar_exists in H4; simpl; eauto.
   destruct H4 as [te2' [ml [? [? [? ?]]]]]. simpl in *.
   exists te2', e2. repeat (split; auto).
   -eapply eval_Harydef; eauto.
    eapply eval_sexp_ptree_ids_match; simpl; eauto.
    red; intros. apply H6. in_tac.
   -eapply env_stmt_sets_refl.
   -econstructor 1 with (lid::nil) ml; simpl; eauto; try red; auto; constructor.
   -incl_tac.
  +eapply ptree_ids_match_locenv_setlvar_exists in H3; simpl; eauto.
   destruct H3 as [te2' [ml [? [? [? ?]]]]]. simpl in *.
   exists te2', e2. repeat (split; auto).
   -eapply eval_Haryslc; eauto.
    eapply eval_sexp_ptree_ids_match; simpl; eauto.
    rewrite <-app_nil_end. red; intros. apply H5. in_tac.
   -apply env_stmt_sets_refl.
   -econstructor 1 with (lid::nil) ml; simpl; eauto; try red; auto; constructor.
   -incl_tac.
  +inv H1. eapply ptree_ids_match_locenv_setlvar_exists in H12; simpl; eauto.
   destruct H12 as [te2' [? [? [? [? ?]]]]].
   exists te2', e2. repeat (split; auto).
   -eapply eval_Hboolred_true; eauto.
    eapply eval_sexp_ptree_ids_match; simpl; eauto.
    rewrite <-app_nil_end. red; intros. apply H3. in_tac.
    econstructor 1; eauto.
    eapply eval_sexp_ptree_ids_match; simpl; eauto.
    red; intros. apply H3. in_tac.
    econstructor; simpl; eauto.
   -apply env_stmt_sets_refl.
   -econstructor 1; eauto. red; auto.
   -simpl. incl_tac.
  +exists te2, e2. repeat (split; auto).
   -eapply eval_Hboolred_false; eauto.
    eapply eval_sexp_ptree_ids_match; simpl; eauto.
    rewrite <-app_nil_end. red; intros. apply H2. in_tac.
   -apply env_stmt_sets_refl.
   -apply locenv_stmt_sets_refl.
  +inversion_clear H4. generalize H5. intros A.
   apply ptree_ids_match_app in H5. destruct H5.
   eapply ptree_ids_match_setarys_exists in H3; eauto.
   destruct H3 as [te2' [ml [? [? [? ?]]]]].
   eapply eval_apply_match_ptree_sets_exist in H2; eauto.
   destruct H2 as [se2' [? [? [l1 [el [? [? ?]]]]]]].
   exists te2', (mkenv eh2 se2'). repeat split; auto.
   -eapply eval_Hmapcall; eauto. eapply eval_sexps_ptree_ids_match; eauto.
   -constructor 1 with nil l1 nil el; simpl; eauto. red; auto.
    constructor. constructor.
   -constructor 1 with (map fst lhs) ml; simpl; auto. red; auto.
  +inversion_clear H7.
   apply env_ids_match_eval_assign with (e2:=mkenv eh2 se2) (te2:=te0) (l1:=(get_expids init++get_expsids args)++lid::tid::map fst lhs) in H0; eauto.
   destruct H0 as [te21 [? [? ?]]].
   eapply eval_apply_match_ptree_sets_exist with (te2:=te21) in H4; eauto.
   destruct H4 as [se2' [? [? [l1 [el [? [? ?]]]]]]].
   apply ptree_ids_match_locenv_setlvar_exists with _ _ _ _ _ te21 ((get_expids init ++ get_expsids args) ++ lid::tid::map fst lhs) in H5;
     try (apply in_or_app; right; simpl); eauto.
   destruct H5 as [te22 [ml [? [? [? ?]]]]].
   apply ptree_ids_match_setarys_exists with _ _ _ _ _ _ ((get_expids init ++get_expsids args)++lid::tid::nil) te22 in H6;
     simpl; try rewrite app_ass; eauto.
   destruct H6 as [te2' [ml1 [? [? [? ?]]]]].
   exists te2', (mkenv eh2 se2'). repeat (split; auto).
   -eapply eval_Hmapfoldcall; eauto.
    eapply eval_sexp_ptree_ids_match; eauto; simpl.
    red; intros. apply H7. in_tac.
    eapply eval_sexps_ptree_ids_match; eauto.
    red; intros. apply H7. in_tac.
   -repeat rewrite app_ass in H20. simpl in H20. auto.
   -constructor 1 with nil l1 nil el; simpl; auto; try constructor. red; auto.
   -apply locenv_stmt_sets_trans with te1 te21; auto.
    eapply locenv_stmt_sets_incl; eauto. simpl. incl_tac.
    apply locenv_stmt_sets_trans with te2 te22; auto.
    econstructor 1; eauto. simpl. incl_tac.
    constructor 1 with (map fst lhs) ml1; auto.
      simpl. red; simpl; auto.
   -simpl. incl_tac.
   -eapply locenv_stmt_sets_ptree_some_match; eauto.
   -simpl. incl_tac.
Qed.

Lemma eval_arydif_env:
  forall nk lh ta al i te e te' e',
  eval_stmt nk te e te' e' (Sarydif lh i al) ta ta ->
  e' = e.
Proof.
  induction al; intros; inv H; auto.
Qed.

Lemma eval_struct_env:
  forall nk lh ta al fld te e te' e',
  eval_stmt nk te e te' e' (Sstruct lh fld al) ta ta ->
  e' = e.
Proof.
  induction al; intros; inv H; auto.
Qed.


Lemma eval_stmts_swap_first:
  forall nk te1 e1 te1' e1' s ta ta',
  eval_stmt nk te1 e1 te1' e1' s ta ta' ->
  forall te2 e2,
  env_ids_match (ACG_INIT :: map fst (fbyvarsof_s s)) (map instid (instidof_s s)) e1 e2 ->
  ptree_ids_match (ridl_of_s s++lidl_of_s s) te1 te2 ->
  ptree_some_match te1 te2 ->
  exists te2' e2', eval_stmt nk te2 e2 te2' e2' s ta ta'
    /\ env_ids_match (ACG_INIT :: map fst (fbyvarsof_s s)) (map instid (instidof_s s)) e1' e2'
    /\ env_stmt_sets s e1 e1' e2 e2'
    /\ ptree_ids_match (lidl_of_s s) te1' te2'
    /\ locenv_stmt_sets (lidl_of_s s) te1 te1' te2 te2'.
Proof.
  induction 1; simpl; intros.
  +inversion_clear H3. apply ptree_ids_match_app in H4. destruct H4.
   apply eval_expr_ptree_ids_match with _ _ _ _ _ te2 in H; auto.
   eapply ptree_ids_match_locenv_setlvar_exists in H2; eauto.
   destruct H2 as [te21 [ml [? [? [? ?]]]]].
   exists te21, (mkenv eh2 se2). repeat (split; auto).
   -apply eval_Sassign with v v'; auto.
   -constructor 1 with nil nil nil nil; simpl;auto;try red; auto; constructor.
   -constructor 1 with (fst lh::nil) ml; simpl;auto;try red; auto; constructor.
   -simpl. incl_tac.
  +inversion_clear H2. apply ptree_ids_match_app in H3. destruct H3.
   apply eval_sexps_ptree_ids_match with _ _ _ te2 in H; auto.
   destruct ptree_ids_match_setvars_exists with te lhs vrets te' te2 as [te21 [ml [? [? [? ?]]]]]; auto.
   eapply eval_apply_match_ptree_sets_exist in H0; eauto.
   destruct H0 as [se2' [? [? [l [el [? [? ?]]]]]]].
   exists te21, (mkenv eh2 se2'). repeat (split; auto).
   -eapply eval_Scall; eauto.
   -constructor 1 with nil l nil el; simpl;auto;try red; auto; constructor.
   -constructor 1 with (map fst lhs) ml; simpl;auto. red; auto.
  +apply ptree_ids_match_eval_initstmt with (e2:=e2) (te2:=te0) in H; eauto.
   destruct H as [te21 [? [? ?]]].
   destruct IHeval_stmt with te21 e2 as [te2' [e2' [? [? [? [? ?]]]]]]; simpl; eauto.
     inv H6. red; intros. eapply ptree_sets_match; eauto.
     eapply locenv_stmt_sets_ptree_some_match; eauto.
   exists te2', e2'. repeat (split; auto).
   -apply eval_Sfor_start with te21 ta1; eauto.
   -inv H9. econstructor 1; eauto.
   -eapply locenv_stmt_sets_trans; eauto.
    eapply locenv_stmt_sets_incl; eauto.
    apply lidl_of_fs_incl.
   -apply initstmtsof_is_assign.
   -red; intros. apply in_app_or in H5. apply H3.
    destruct H5; [apply ridl_of_fs_incl in H5 | apply lidl_of_fs_incl in H5]; in_tac.
  +inversion_clear H0. eapply ptree_ids_match_app in H1. destruct H1.
   exists te2, (mkenv eh2 se2); repeat (split; auto).
   -eapply eval_Sfor_false; eauto.
   -constructor 1 with nil nil nil nil; try constructor; auto;
    red; intros ? A; inv A.
   -constructor 1 with nil nil; try constructor; auto; red; intros ? A; inv A.
  +eapply env_ids_match_eval_htmt_exists with (j:=j) in H0; eauto.
   destruct H0 as [te21 [e21 [? [? [? [? ?]]]]]].
   destruct IHeval_stmt with te21 e21 as [te2' [e2' [? [? [? [? ?]]]]]]; auto.
    eapply locenv_stmt_sets_ptree_some_match; eauto.
   exists te2', e2'. repeat (split; auto).
   -eapply eval_Sfor_loop; eauto.
   -eapply env_stmt_sets_trans; eauto.
   -eapply locenv_stmt_sets_trans; eauto.
  +exists te2, e2. inversion_clear H. repeat (split; auto).
   -constructor.
   -constructor 1 with nil nil nil nil;eauto; simpl; try apply incl_refl; try constructor.
   -constructor 1 with nil nil; eauto; simpl in *; try apply incl_refl; try constructor; tauto.
  +inv H5. apply ptree_ids_match_app in H6. destruct H6.
   eapply ptree_ids_match_locenv_setlvar_exists in H3; eauto.
   destruct H3 as [te12 [ml [? [? [? ?]]]]].
   destruct IHeval_stmt with te12 (mkenv eh2 se2) as [te2' [e2' [? [? [? [? ?]]]]]]; simpl; auto.
    econstructor 1; eauto.
    red; intros ? A. apply in_app_or in A. destruct A; auto.
     inv H10. inv H18. inv H11. inv H18. compare lid id; intros; subst.
     repeat rewrite PTree.gss; auto. repeat rewrite PTree.gso; auto.
     apply H1; auto. apply in_or_app; auto.
     eapply ptree_sets_some_match; eauto.
   cut (e2'= mkenv eh2 se2). intros. subst.
   exists te2', (mkenv eh2 se2). repeat (split; auto).
   -apply eval_Sarydif_cons with te12 v v'; auto.
    eapply eval_sexp_ptree_ids_match; eauto.
    red; intros. apply H1. apply in_or_app; auto.
   -constructor 1 with nil nil nil nil; eauto; simpl; try apply incl_refl; try constructor.
   -apply locenv_stmt_sets_trans with te1 te12; eauto.
    constructor 1 with (lid::nil) ml; auto; simpl; try apply incl_refl; repeat econstructor.
   -eapply eval_arydif_env; eauto.
   -simpl. apply incl_refl.
  +apply env_ids_match_eval_assign with (e2:=e2) (te2:=te0) (l1:=(get_expids a1 ++ get_lindexids lis ++ get_expids a3) ++ lid :: nil) in H1; eauto.
   destruct H1 as [te21 [? [? ?]]].
   apply ptree_ids_match_store_exists with (e2:=te21) (l:=lid::nil) in H3; simpl; eauto.
   destruct H3 as [te2' [m' [? [? [? [? ?]]]]]]. simpl in *.
   exists te2', e2. repeat (split; auto).
   -apply eval_Smix with te21 o v3 v; eauto.
    eapply eval_lindexs_ptree_ids_match; eauto.
     red; intros. apply in_or_app. left. apply in_or_app. right.
     apply in_or_app; auto.
    eapply eval_sexp_ptree_ids_match; eauto.
     red; intros. apply H6. apply in_or_app. left.
     repeat (apply in_or_app; right; auto).
   -apply env_stmt_sets_refl; auto.
   -apply locenv_stmt_sets_trans with te1 te21; auto.
    subst. constructor 1 with (lid::nil) (m'::nil); auto; simpl;
    try apply incl_refl; repeat econstructor.
   -red; simpl; intros. apply H8. apply in_or_app; right.
    destruct H10; subst; simpl; auto.
   -simpl. incl_tac.
  +exists te2, e2. inversion_clear H. repeat (split; auto).
   -constructor.
   -constructor 1 with nil nil nil nil;eauto; simpl; try apply incl_refl; try constructor.
   -constructor 1 with nil nil; eauto; simpl in *; try apply incl_refl; try constructor; tauto.
  +inv H5. apply ptree_ids_match_app in H6. destruct H6.
   eapply ptree_ids_match_locenv_setlvar_exists in H1; eauto.
   destruct H1 as [te12 [ml [? [? [? ?]]]]].
   destruct IHeval_stmt with te12 (mkenv eh2 se2) as [te2' [e2' [? [? [? [? ?]]]]]]; simpl; auto.
    econstructor 1; eauto.
    red; intros ? A. apply in_app_or in A. destruct A; auto.
     inv H10. inv H18. inv H11. inv H18. compare lid id; intros; subst.
     repeat rewrite PTree.gss; auto. repeat rewrite PTree.gso; auto.
     apply H3; auto. apply in_or_app; auto.
     eapply ptree_sets_some_match; eauto.
   cut (e2'= mkenv eh2 se2). intros. subst.
   exists te2', (mkenv eh2 se2). repeat (split; auto).
   -apply eval_Sstruct_cons with te12 v v'; auto.
    eapply eval_sexp_ptree_ids_match; eauto.
    red; intros. apply H3. apply in_or_app; auto.
   -constructor 1 with nil nil nil nil; eauto; simpl; try apply incl_refl; try constructor.
   -apply locenv_stmt_sets_trans with te1 te12; auto.
    constructor 1 with (lid::nil) ml; auto; simpl; try apply incl_refl; repeat econstructor.
   -eapply eval_struct_env; eauto.
   -simpl. apply incl_refl.
  +inversion_clear H. exists te2, (mkenv eh2 se2); repeat (split; auto).
   -constructor.
   -constructor 1 with nil nil nil nil; try constructor; auto;
    red; intros ? A; inv A.
   -constructor 1 with nil nil; try constructor; auto;
    red; intros ? A; inv A.
  +inversion_clear H5. eapply ptree_ids_match_locenv_setlvar_exists in H4; eauto.
   destruct H4 as [te2' [ml [? [? [? ?]]]]].
   exists te2', (mkenv eh2 se2); repeat (split; auto).
   -eapply eval_Sfby_cycle_1; eauto.
    *eapply eval_sexp_ptree_ids_match; simpl; eauto.
     red; simpl; intros ? A; destruct A; subst; try tauto.
     apply H8. simpl; auto.
    *eapply eval_sexp_ptree_ids_match; eauto.
     red; intros. apply H6. apply in_or_app; auto.
   -constructor 1 with nil nil nil nil; eauto; simpl;
    try apply incl_refl; try constructor. tauto.
   -red; intros. apply H5; auto. apply in_or_app; auto.
   -constructor 1 with (fst lh::nil) ml; auto; simpl;
    try apply incl_refl; constructor.
   -simpl. incl_tac.
  +inversion_clear H5. eapply ptree_ids_match_locenv_setlvar_exists in H3; eauto.
   destruct H3 as [te2' [ml [? [? [? ?]]]]].
   exists te2', (mkenv eh2 se2); repeat (split; auto).
   -eapply eval_Sfby_cycle_n; eauto.
    *eapply eval_sexp_ptree_ids_match; simpl; eauto.
     red; simpl; intros ? A; destruct A; subst; try tauto.
     apply H8. simpl; auto.
    *eapply eval_sexp_ptree_ids_match; simpl; eauto.
     red; simpl; intros ? A; destruct A; subst; try tauto.
     apply H8. simpl; auto.
   -constructor 1 with nil nil nil nil; eauto; simpl;
    try apply incl_refl; try constructor. tauto.
   -red; intros. apply H5. apply in_or_app; auto.
   -constructor 1 with (fst lh::nil) ml; auto; simpl;
    try apply incl_refl; constructor.
   -simpl. incl_tac.
  +inversion_clear H11. eapply ptree_ids_match_locenv_setlvar_exists in H9; eauto.
   destruct H9 as [te2' [ml [? [? [? ?]]]]].
   apply ptree_ids_match_eval_fbyn_init with (eh2:=eh3) in H3; auto.
   destruct H3 as [eh21 [l [ml1 [? [? [? [? ?]]]]]]].
   inv H4. eapply ptree_ids_match_locenv_setlvar_exists in H29; eauto.
   destruct H29 as [eh2' [ml2 [? [? [? ?]]]]].
   exists te2', (mkenv eh2' se2); repeat (split; auto).
   -eapply eval_Sfbyn_cycle_1; eauto.
    *eapply eval_sexp_ptree_ids_match; simpl; eauto.
     red; simpl; intros ? A; destruct A; subst; try tauto.
     apply H14. simpl; auto.
    *eapply eval_sexp_ptree_ids_match; eauto.
     red; intros. apply H12. apply in_or_app; auto.
    *econstructor; eauto. eapply eval_sexp_const; eauto.
     constructor 1 with Mint32; auto.
    *subst. eapply eval_sexp_ptree_ids_match; simpl; eauto.
     red; simpl; intros ? A; destruct A as [ | [ | ]]; subst; try tauto;
     apply H0; simpl; auto.
   -apply env_stmt_sets_trans with (mkenv eh1 se) (mkenv eh21 se2); auto.
    *constructor 1 with l nil ml1 nil; eauto; simpl;
     try apply incl_refl; try constructor.
    *constructor 1 with (id1::nil) nil ml2 nil; eauto; simpl;
     try apply incl_refl; try constructor.
   -red; intros ? A. apply H11. apply in_or_app; auto.
   -constructor 1 with (fst lh :: nil) ml; eauto; simpl;
     try apply incl_refl; try constructor.
   -simpl. incl_tac.
   -simpl. incl_tac.
  +inversion_clear H8. eapply ptree_ids_match_locenv_setlvar_exists in H6; eauto.
   destruct H6 as [te2' [ml [? [? [? ?]]]]].
   exists te2', (mkenv eh2 se2); repeat (split; auto).
   -eapply eval_Sfbyn_cycle_n; eauto.
    *eapply eval_sexp_ptree_ids_match; simpl; eauto.
     red; simpl; intros ? A; destruct A; subst; try tauto.
     apply H11. simpl; auto.
    *subst. eapply eval_sexp_ptree_ids_match; simpl; eauto.
     red; simpl; intros ? A; destruct A as [ | [ | ]]; subst; try tauto;
     apply H11; simpl; auto.
   -constructor 1 with nil nil nil nil; eauto; simpl;
    try apply incl_refl; try constructor. tauto.
   -red; intros. apply H8. apply in_or_app; auto.
   -constructor 1 with (fst lh::nil) ml; auto; simpl;
    try apply incl_refl; constructor.
   -simpl. incl_tac.
  +destruct IHeval_stmt with te2 e2 as [te2' [e2' [? [? [? [? ?]]]]]]; simpl; auto.
    red; intros. apply H3. destruct b; in_tac.
   inversion_clear H6.
   exists te2', e2. inversion_clear H2. repeat (split; auto); try (destruct b; auto; fail).
   -destruct b; inv H5; eapply eval_Sarrow; simpl in *; eauto.
    *eapply eval_sexp_ptree_ids_match; simpl; eauto.
    *simpl. econstructor; eauto.
    *eapply eval_sexp_ptree_ids_match; simpl; eauto.
    *simpl. econstructor; eauto.
   -apply env_stmt_sets_refl.
Qed.

Lemma eval_stmts_correct_swap:
  forall nk s1 s2 te1 e1 te2 e2,
  topo_sorted (deps_of_stmts_simpl (s1 :: s2 :: nil)) ->
  topo_sorted (deps_of_stmts_simpl (s2 :: s1 :: nil)) ->
  eval_stmts nk te1 e1 te2 e2 (s1 :: s2 :: nil) ->
  list_norepet (lidl_of_s s1 ++ lidl_of_s s2) ->
  list_norepet (map instid (instidof_s s1) ++ map instid (instidof_s s2)) ->
  list_norepet (ACG_INIT :: map fst (fbyvarsof_s s1) ++ map fst (fbyvarsof_s s2)) ->
  eval_stmts nk te1 e1 te2 e2 (s2 :: s1 :: nil).
Proof.
  intros. inv H1. inv H13. inv H14.
  generalize H2 H3; intros Hnd Hnd0.
  apply list_norepet_app in H2. destruct H2 as [Hnd1 [Hnd2 Hnd3]]; auto.
  apply list_norepet_app in H3. destruct H3 as [Hnd4 [Hnd5 Hnd6]]; auto.
  inversion_clear H4. apply list_norepet_app in H2. destruct H2 as [Hnd7 [Hnd8 Hnd9]]; auto.
  simpl in *. unfold dependonlist in *. simpl in *.
  destruct H as [? [? ?]]. destruct H0 as [? [? ?]].
  repeat rewrite <-app_nil_end in *.
  apply list_in_list_disjoint in H. apply list_in_list_disjoint in H2.
  apply list_in_list_disjoint in H0. apply list_in_list_disjoint in H4.
  apply list_disjoint_app_right in H. destruct H.
  apply list_disjoint_app_right in H0. destruct H0.
  assert(Hds1: list_disjoint (ACG_INIT :: map fst (fbyvarsof_s s1)) (map fst (fbyvarsof_s s2))).
    red; simpl; intros ? ? A ?. destruct A; subst; auto. red; intros; subst.
      apply H1; auto. apply in_or_app;auto.
  assert(Hds2: list_disjoint (map fst (fbyvarsof_s s1)) (ACG_INIT :: map fst (fbyvarsof_s s2))).
    red; simpl; intros ? ? ? A. destruct A; subst; auto. red; intros; subst.
      apply H1; auto. apply in_or_app;auto.
  assert (A: env_ids_match (ACG_INIT :: map fst (fbyvarsof_s s2)) (map instid (instidof_s s2)) e1 e0
              /\ ptree_ids_match (ridl_of_s s2++lidl_of_s s2) te1 te0).
    eapply eval_stmt_env_ids_match; eauto.
    apply <-list_disjoint_app_right; split; auto.
    apply list_disjoint_sym; auto.
  destruct A as [A A0].
  assert (A1: env_ids_match (ACG_INIT :: map fst (fbyvarsof_s s1)) (map instid (instidof_s s1)) e0 e2
               /\ ptree_ids_match (lidl_of_s s1) te0 te2).
    eapply eval_stmt_env_ids_match; eauto; apply list_disjoint_sym; auto.
  destruct A1 as [A1 A2].
  destruct eval_stmts_swap_first with nk te0 e0 te2 e2 s2 empty_locenv ta0 te1 e1 as [te21 [e21 [? [? [? [B B1]]]]]]; eauto.
    eapply env_ids_match_swap; eauto.
    eapply ptree_ids_match_swap; eauto.
    apply eval_stmt_ptree_some_match in H12; intuition.
  econstructor 2; eauto. constructor 2 with te2 e2 ta; eauto; try constructor.
  assert (A3: env_ids_match (ACG_INIT :: map fst (fbyvarsof_s s1)) (map instid (instidof_s s1)) e1 e21
              /\ ptree_ids_match (ridl_of_s s1++lidl_of_s s1) te1 te21).
    eapply eval_stmt_env_ids_match; eauto; apply list_disjoint_sym; auto.
    apply <-list_disjoint_app_left; split; auto.
  destruct A3 as [A3 A4].
  destruct eval_stmts_swap_first with nk te1 e1 te0 e0 s1 empty_locenv ta te21 e21 as [te2' [e2' [? [? [? [B2 B3]]]]]]; eauto.
    eapply eval_stmt_ptree_some_match; eauto.
  assert (A5: env_ids_match (ACG_INIT :: map fst (fbyvarsof_s s2)) (map instid (instidof_s s2)) e21 e2'
              /\ ptree_ids_match (ridl_of_s s2++lidl_of_s s2) te21 te2').
    eapply eval_stmt_env_ids_match; eauto.
    apply <-list_disjoint_app_right; split; auto.
    apply list_disjoint_sym; auto.
  destruct A5 as [A5 A6].
  assert (A7: e2 = e2').
    inv H9. inv H14. inv A. inv A1. inv A3. inv A5. inv H10. inv H15.
    f_equal.
    eapply ptree_sets_determ; eauto.
    eapply ptree_sets_swap; eauto.
    apply list_disjoint_incl with (map fst (fbyvarsof_s s2)) (map fst (fbyvarsof_s s1)); eauto.
    apply list_disjoint_sym; auto.
    eapply ptree_sets_determ; eauto.
    eapply ptree_sets_swap; eauto.
    apply list_disjoint_incl with (map instid (instidof_s s2)) (map instid (instidof_s s1)); eauto.
    apply list_disjoint_sym; auto.
  assert(A8: te2 = te2').
    inv B1. inv B3.
    eapply ptree_sets_determ; eauto.
    eapply ptree_sets_swap; eauto.
    apply list_disjoint_incl with (lidl_of_s s2) (lidl_of_s s1); eauto.
    apply list_disjoint_sym; auto.
  subst. auto.
Qed.

Lemma eval_index_stmts_correct_sup:
  forall nk eqlx eqly eq te e te' e',
  topo_sorted (deps_of_stmts_simpl (eq :: eqlx ++ eqly)) ->
  topo_sorted (deps_of_stmts_simpl (eqlx ++ eq :: eqly)) ->
  eval_stmts nk te e te' e' (eq :: eqlx ++ eqly) ->
  nodup_lids (deps_of_stmts_simpl (eq :: eqlx ++ eqly)) ->
  list_norepet (map instid (instidof_s eq) ++ map instid (instidof (eqlx ++ eqly))) ->
  list_norepet (ACG_INIT :: map fst (fbyvarsof (eq :: eqlx ++ eqly))) ->
  eval_stmts nk te e te' e' (eqlx ++ eq :: eqly).
Proof.
  induction eqlx; intros; auto.
  cut (eval_stmts nk te e te' e' (a :: eq :: eqlx ++ eqly)); intros.
  inv H5. econstructor 2; eauto.
  eapply IHeqlx; eauto.
  +simpl in *. intuition. eapply dependonlist_incl;eauto.
   incl_tac.
  +simpl in H0. intuition.
  +apply list_norepet_permut with (l2:=flat_map (fun a : depend => lidl a)
          (deps_of_stmts_simpl (a:: eq :: eqlx ++ eqly))) in H2.
   simpl in H2. apply list_norepet_app in H2. intuition.
   apply flat_map_permutation. simpl. constructor.
  +apply list_norepet_permut with (l2:=map instid (instidof ((a :: eq :: eqlx) ++ eqly))) in H3.
   simpl in H3. rewrite map_app, map_app in H3.
   apply list_norepet_app in H3. intuition.
   simpl. repeat rewrite map_app. repeat rewrite <-app_ass.
   apply Permutation_app_tail. apply Permutation_app_comm.
  +apply list_norepet_permut with (l2:=map fst (fbyvarsof_s a)++ ACG_INIT :: map fst (fbyvarsof (eq :: eqlx ++ eqly))) in H4.
   simpl in H4. apply list_norepet_app in H4. intuition.
   simpl. repeat rewrite map_app. repeat rewrite app_comm_cons.
   repeat rewrite <-app_ass. apply Permutation_app_tail. apply Permutation_app_comm.
  +change (eq :: (a :: eqlx) ++ eqly) with ((eq :: a :: nil) ++ eqlx ++ eqly) in *.
   apply eval_stmts_split in H1. destruct H1 as [te2 [e2 [? ?]]].
   change (a :: eq :: eqlx ++ eqly) with ((a :: eq :: nil) ++ eqlx ++ eqly).
   eapply eval_stmts_app; eauto.
   eapply eval_stmts_correct_swap; eauto.
   -rewrite deps_of_stmts_simpl_app in H. apply toposort_app in H. intuition.
   -simpl in *. intuition.
    *clear -H. eapply dependonlist_incl;eauto.
     rewrite deps_of_stmts_simpl_app. simpl. incl_tac.
    *eapply dependonlist_incl;eauto.
     rewrite deps_of_stmts_simpl_app. simpl. incl_tac.
   -rewrite deps_of_stmts_simpl_app in H2.  apply nodup_lids_sube in H2.
    unfold nodup_lids in H2. simpl in *. rewrite <-app_nil_end in *. intuition.
   -simpl in *. rewrite map_app in H3. rewrite <-app_ass in H3.
    apply list_norepet_app in H3. intuition.
   -simpl in *. rewrite map_app,map_app in H4. rewrite <-app_ass,app_comm_cons in H4.
    apply list_norepet_app in H4. intuition.
Qed.

Lemma eval_index_stmts_correct :
  forall nk eql1 te e te' e',
  topo_sorted (deps_of_stmts_simpl eql1) ->
  eval_stmts nk te e te' e' eql1->
  forall eql2,
  Permutation eql1 eql2 ->
  topo_sorted (deps_of_stmts_simpl eql2) ->
  nodup_lids (deps_of_stmts_simpl eql1) ->
  list_norepet (map instid (instidof eql1)) ->
  list_norepet (ACG_INIT :: map fst (fbyvarsof eql1)) ->
  eval_stmts nk te e te' e' eql2.
Proof.
  induction 2; intros.
  apply Permutation_nil in H0. rewrite H0.
  constructor.

  assert (A: In s eql2).
    apply Permutation_in with (s :: ss); simpl; auto.
  apply In_split in A. destruct A as [eqlx [eqly A]]. subst.
  assert (B: topo_sorted (deps_of_stmts_simpl (s :: eqlx ++ eqly))).
    simpl deps_of_stmts_simpl in *. rewrite deps_of_stmts_simpl_app in *.
    simpl deps_of_stmts_simpl in *. eapply topo_sorted_perm; eauto.
    apply Permutation_cons_app. rewrite <-deps_of_stmts_simpl_app.
    apply Permutation_map. apply Permutation_cons_app_inv with s; auto.
  assert (C: topo_sorted (deps_of_stmts_simpl ss)).
    simpl in H. destruct H; trivial.
  assert (D: topo_sorted (deps_of_stmts_simpl (eqlx++eqly))).
    simpl in B. destruct B; trivial.
  generalize H2 H4; intros.
  eapply Permutation_cons_app_inv in H7; eauto.
  simpl in *. apply nodup_lids_appa in H4; auto.
  apply Permutation_cons_app_inv in H2.
  apply IHeval_stmts in H2; auto.

  apply eval_index_stmts_correct_sup; auto.
  +econstructor 2; eauto.
  +apply nodup_lids_perm with (deps_of_stmts_simpl (s :: ss)); auto.
   apply Permutation_map. constructor; auto.
  +rewrite <-map_app. eapply list_norepet_permut in H5; eauto.
   apply Permutation_map. apply Permutation_app_head. apply flat_map_permutation; auto.
  +clear -H6 H7. eapply list_norepet_permut; eauto. constructor.
   apply Permutation_map. simpl. apply Permutation_app_head.
   apply flat_map_permutation; auto.
  +rewrite map_app in H5. apply list_norepet_app in H5.
   destruct H5 as [? [? ?]]; auto.
  +rewrite map_app in *. inv H6. constructor; auto.
   red; intros. apply H11. apply in_or_app; auto.
   apply list_norepet_app in H12. intuition.
Qed.

Lemma init_stmt_swap:
  forall nk c1 c2 e1 e2 l,
  init_stmt nk e1 e2 (c1 :: c2 :: l) ->
  instid c1 <> instid c2 ->
  init_stmt nk e1 e2 (c2 :: c1 :: l).
Proof.
  intros. inv H. inv H10.
  econstructor 2 with (fd:=fd0); eauto.
  econstructor 2 with (fd:=fd); eauto.
  rewrite ptree_set_swap; auto.
Qed.

Lemma alloc_index_stmt_correct :
  forall l1 l2,
  Permutation l1 l2 ->
  forall nk e e',
  init_stmt nk e e' l1->
  list_norepet (map instid l1) ->
  init_stmt nk e e' l2.
Proof.
  induction 1; intros; auto.
  +inv H0. inv H1. econstructor 2; eauto.
  +eapply init_stmt_swap; eauto.
   inv H0. red; intros. apply H3. rewrite H0; simpl; auto.
  +apply IHPermutation2; auto.
   apply list_norepet_permut with (map instid l); auto.
   apply Permutation_map; auto.
Qed.

Lemma eval_init_permut:
  forall s1 s2 eh1,
  eval_init ((length (fbyeqsof s1))) empty_locenv ((ACG_INIT, type_bool) :: fbyvarsof s1) eh1 ->
  Permutation s1 s2 ->
  list_norepet (map fst (fbyvarsof s1)) ->
  eval_init ((length (fbyeqsof s2))) empty_locenv ((ACG_INIT, type_bool) :: fbyvarsof s2) eh1.
Proof.
  intros. rewrite <-Permutation_length with (l:=fbyeqsof s1); auto.
  inv H.
  +constructor 1; auto.
  +constructor 2 with eh0;auto.
   inv H4. econstructor; eauto.
   eapply alloc_variables_permut in H9; eauto.
   apply flat_map_permutation; auto.
  +apply flat_map_permutation; auto.
Qed.

End SEMANTICS.