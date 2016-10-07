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

(** The Ctemp language. *)

Require Import Coqlib.
Require Import Errors.
Require Import Maps.
Require Import Integers.
Require Import Floats.
Require Import Lvalues.
Require Import Values.
Require Import AST.
Require Import Memory.
Require Import Events.
Require Import Globalenvs.
Require Import Ctypes.
Require Import Cop.
Require Import Cltypes.
Require Import Clop.
Require Import Clight.
Require Import ClightBigstep.
Require Import Lident.

(** * Abstract syntax *)

Fixpoint typelist_app(tyl1 tyl2: typelist) : typelist :=
  match tyl1 with
  | Tnil => tyl2
  | Tcons ty tyl => Tcons ty (typelist_app tyl tyl2)
  end.

Inductive expr : Type :=
  | Econst_int: int -> type -> expr       (**r integer literal *)
  | Econst_float: float -> type -> expr   (**r float literal *)
  | Econst_single: float32 -> type -> expr (**r single float literal *)
  | Evar: ident -> type -> expr           (**r variable *)
  | Etempvar: ident -> type -> expr       (**r temporary variable *)
  | Etempret: ident -> type -> expr
  | Ederef: expr -> type -> expr          (**r pointer dereference (unary [*]) *)
  | Eaddrof: expr -> type -> expr         (**r address-of operator ([&]) *)
  | Eunop: unary_operation -> expr -> type -> expr  (**r unary operation *)
  | Ebinop: binary_operation -> expr -> expr -> type -> expr (**r binary operation *)
  | Ecast: expr -> type -> expr   (**r type cast ([(ty) e]) *)
  | Efield: expr -> ident -> type -> expr (**r access to a member of a struct or union *)
  | Esizeof: type -> type -> expr         (**r size of a type *)
  | Ealignof: type -> type -> expr.       (**r alignment of a type *)

(** Extract the type part of a type-annotated Clight expression. *)

Definition typeof (e: expr) : type :=
  match e with
  | Econst_int _ ty => ty
  | Econst_float _ ty => ty
  | Econst_single _ ty => ty
  | Evar _ ty => ty
  | Etempvar _ ty => ty
  | Etempret _ ty => ty
  | Ederef _ ty => ty
  | Eaddrof _ ty => ty
  | Eunop _ _ ty => ty
  | Ebinop _ _ _ ty => ty
  | Ecast _ ty => ty
  | Efield _ _ ty => ty
  | Esizeof _ ty => ty
  | Ealignof _ ty => ty
  end.

(** ** Statements *)

Inductive statement : Type :=
  | Sskip : statement                   (**r do nothing *)
  | Sassign : expr -> expr -> statement (**r assignment [lvalue = rvalue] *)
  | Sset : ident -> expr -> statement   (**r assignment [tempvar = rvalue] *)
  | Smemcpy : type -> typelist ->  list expr -> statement  (**r memory copy call *)
  | Scall: option ident  -> expr -> list expr -> list expr -> statement (**r function call *)
  | Ssequence : statement -> statement -> statement  (**r sequence *)
  | Sifthenelse : expr  -> statement -> statement -> statement (**r conditional *)
  | Sfor: statement -> expr -> statement -> statement -> statement (**r [for] loop *)
  | Sbreak : statement                      (**r [break] statement *)
  | Sreturn : option expr -> statement      (**r [return] statement *)
  | Sswitch : expr -> labeled_statements -> statement  (**r [switch] statement *)

with labeled_statements : Type :=            (**r cases of a [switch] *)
  | LSdefault: statement -> labeled_statements
  | LScase: int -> statement -> labeled_statements -> labeled_statements.

(** ** Functions *)

Record function : Type := mkfunction {
  fn_return: type;
  fn_callconv: calling_convention;
  fn_params: list (ident * type);
  fn_vars: list (ident * type);
  fn_temps: list (ident * type);
  fn_body: statement
}.

Definition var_names (vars: list(ident * type)) : list ident :=
  List.map (@fst ident type) vars.

Inductive fundef : Type :=
  | Internal: function -> fundef.

(** The type of a function definition. *)

Definition type_of_function (f: function) : type :=
  Tfunction (type_of_params (fn_params f ++ fn_temps f)) (fn_return f) (fn_callconv f).

Definition type_of_fundef (f: fundef) : type :=
  match f with
  | Internal fd => type_of_function fd
  end.

(** ** Programs *)

Definition program : Type := AST.program fundef type.

(** * Operational semantics *)

(** The semantics uses two environments.  The global environment
  maps names of functions and global variables to memory block references,
  and function pointers to their definitions.  (See module [Globalenvs].) *)

Definition genv := Genv.t fundef type.

Definition env := PTree.t (block * type).

Definition empty_env: env := (PTree.empty (block * type)).

Definition temp_env := PTree.t (val*type).

Definition empty_temp := PTree.empty (val*type).

(** [deref_loc ty m b ofs v] computes the value of a datum
  of type [ty] residing in memory [m] at block [b], offset [ofs].
  If the type [ty] indicates an access by value, the corresponding
  memory load is performed.  If the type [ty] indicates an access by
  reference or by copy, the pointer [Vptr b ofs] is returned. *)

Inductive deref_loc (ty: type) (m: mem) (b: block) (ofs: int) : val -> Prop :=
  | deref_loc_value: forall chunk v,
      access_mode ty = By_value chunk ->
      Mem.loadv chunk m (Vptr b ofs) = Some v ->
      deref_loc ty m b ofs v
  | deref_loc_reference:
      access_mode ty = By_reference ->
      deref_loc ty m b ofs (Vptr b ofs)
  | deref_loc_copy:
      access_mode ty = By_copy ->
      deref_loc ty m b ofs (Vptr b ofs).

(** Symmetrically, [assign_loc ty m b ofs v m'] returns the
  memory state after storing the value [v] in the datum
  of type [ty] residing in memory [m] at block [b], offset [ofs].
  This is allowed only if [ty] indicates an access by value or by copy.
  [m'] is the updated memory state. *)

Inductive assign_loc (ty: type) (m: mem) (b: block) (ofs: int):
                                            val -> mem -> Prop :=
  | assign_loc_value: forall v chunk m',
      access_mode ty = By_value chunk ->
      Mem.storev chunk m (Vptr b ofs) v = Some m' ->
      assign_loc ty m b ofs v m'
  | assign_loc_copy: forall b' ofs' bytes m',
      access_mode ty = By_copy ->
      (sizeof ty > 0 -> (alignof_blockcopy ty | Int.unsigned ofs')) ->
      (sizeof ty > 0 -> (alignof_blockcopy ty | Int.unsigned ofs)) ->
      b' <> b \/ Int.unsigned ofs' = Int.unsigned ofs
              \/ Int.unsigned ofs' + sizeof ty <= Int.unsigned ofs
              \/ Int.unsigned ofs + sizeof ty <= Int.unsigned ofs' ->
      Mem.loadbytes m b' (Int.unsigned ofs') (sizeof ty) = Some bytes ->
      Mem.storebytes m b (Int.unsigned ofs) bytes = Some m' ->
      assign_loc ty m b ofs (Vptr b' ofs') m'.

(** Allocation of function-local variables.
  [alloc_variables e1 m1 vars e2 m2] allocates one memory block
  for each variable declared in [vars], and associates the variable
  name with this block.  [e1] and [m1] are the initial local environment
  and memory state.  [e2] and [m2] are the final local environment
  and memory state. *)

Inductive alloc_variables: env -> mem ->
                           list (ident * type) ->
                           env -> mem -> Prop :=
  | alloc_variables_nil:
      forall e m,
      alloc_variables e m nil e m
  | alloc_variables_cons:
      forall e m id ty vars m1 b1 m2 e2,
      Mem.alloc m 0 (sizeof ty) = (m1, b1) ->
      alloc_variables (PTree.set id (b1, ty) e) m1 vars e2 m2 ->
      alloc_variables e m ((id, ty) :: vars) e2 m2.

(** Initialization of temporary variables that are parameters to a function. *)

Fixpoint bind_parameter_temps (formals: list (ident * type)) (args: list val)
                              (le: temp_env) : option temp_env :=
 match formals, args with
 | nil, nil => Some le
 | (id, t) :: xl, v :: vl => bind_parameter_temps xl vl (PTree.set id (v,t) le)
 | _, _ => None
 end.

(** Return the list of blocks in the codomain of [e], with low and high bounds. *)

Definition block_of_binding (id_b_ty: ident * (block * type)) :=
  match id_b_ty with (id, (b, ty)) => (b, 0, sizeof ty) end.

Definition blocks_of_env (e: env) : list (block * Z * Z) :=
  List.map block_of_binding (PTree.elements e).

(** Selection of the appropriate case of a [switch], given the value [n]
  of the selector expression. *)

Fixpoint select_switch (n: int) (sl: labeled_statements)
                       {struct sl}: labeled_statements :=
  match sl with
  | LSdefault _ => sl
  | LScase c s sl' => if Int.eq c n then sl else select_switch n sl'
  end.

(** Turn a labeled statement into a sequence *)

Fixpoint seq_of_labeled_statement (sl: labeled_statements) : statement :=
  match sl with
  | LSdefault s => s
  | LScase c s sl' => Ssequence s (seq_of_labeled_statement sl')
  end.

Section SEMANTICS.

Variable ge: genv.

(** ** Evaluation of expressions *)

Section EXPR.

Variable e: env.
Variable le te: temp_env.
Variable m: mem.

(** [eval_expr ge e m a v] defines the evaluation of expression [a]
  in r-value position.  [v] is the value of the expression.
  [e] is the current environment and [m] is the current memory state. *)

Inductive eval_expr: expr -> val -> Prop :=
  | eval_Econst_int:   forall i ty,
      eval_expr (Econst_int i ty) (Vint i)
  | eval_Econst_float:   forall f ty,
      eval_expr (Econst_float f ty) (Vfloat f)
  | eval_Econst_single:   forall f ty,
      eval_expr (Econst_single f ty) (Vsingle f)
  | eval_Etempvar:  forall id ty v,
      le!id = Some (v,ty) ->
      eval_expr (Etempvar id ty) v
  | eval_Etempret:  forall id ty v,
      te!id = Some (v,ty) ->
      eval_expr (Etempret id ty) v
  | eval_Eaddrof: forall a ty loc ofs,
      eval_lvalue a loc ofs ->
      eval_expr (Eaddrof a ty) (Vptr loc ofs)
  | eval_Eunop:  forall op a ty v1 v,
      eval_expr a v1 ->
      sem_unary_operation op v1 (typeof a) = Some v ->
      eval_expr (Eunop op a ty) v
  | eval_Ebinop: forall op a1 a2 ty v1 v2 v,
      eval_expr a1 v1 ->
      eval_expr a2 v2 ->
      sem_binary_operation op v1 (typeof a1) v2 (typeof a2) m = Some v ->
      eval_expr (Ebinop op a1 a2 ty) v
  | eval_Ecast:   forall a ty v1 v,
      eval_expr a v1 ->
      sem_cast v1 (typeof a) ty = Some v ->
      eval_expr (Ecast a ty) v
  | eval_Esizeof: forall ty1 ty,
      eval_expr (Esizeof ty1 ty) (Vint (Int.repr (sizeof ty1)))
  | eval_Ealignof: forall ty1 ty,
      eval_expr (Ealignof ty1 ty) (Vint (Int.repr (alignof ty1)))
  | eval_Elvalue: forall a loc ofs v,
      eval_lvalue a loc ofs ->
      deref_loc (typeof a) m loc ofs v ->
      eval_expr a v

(** [eval_lvalue ge e m a b ofs] defines the evaluation of expression [a]
  in l-value position.  The result is the memory location [b, ofs]
  that contains the value of the expression [a]. *)

with eval_lvalue: expr -> block -> int -> Prop :=
  | eval_Evar_local:   forall id l ty,
      e!id = Some(l, ty) ->
      eval_lvalue (Evar id ty) l Int.zero
  | eval_Evar_global: forall id l ty,
      e!id = None ->
      Genv.find_symbol ge id = Some l ->
      eval_lvalue (Evar id ty) l Int.zero
  | eval_Ederef: forall a ty l ofs,
      eval_expr a (Vptr l ofs) ->
      eval_lvalue (Ederef a ty) l ofs
  | eval_Efield_struct:   forall a i ty l ofs id fList delta,
      eval_expr a (Vptr l ofs) ->
      typeof a = Tstruct id fList ->
      field_offset i fList = OK delta ->
      eval_lvalue (Efield a i ty) l (Int.add ofs (Int.repr delta)).

Scheme eval_expr_ind2 := Minimality for eval_expr Sort Prop
  with eval_lvalue_ind2 := Minimality for eval_lvalue Sort Prop.
Combined Scheme eval_expr_lvalue_ind from eval_expr_ind2, eval_lvalue_ind2.

(** [eval_exprlist ge e m al vl] evaluates a list of r-value
  expressions [al] to their values [vl]. *)

Inductive eval_exprlist: list expr -> typelist -> list val -> Prop :=
  | eval_Enil:
      eval_exprlist nil Tnil nil
  | eval_Econs:   forall a bl ty tyl v1 v2 vl,
      eval_expr a v1 ->
      sem_cast v1 (typeof a) ty = Some v2 ->
      eval_exprlist bl tyl vl ->
      eval_exprlist (a :: bl) (Tcons ty tyl) (v2 :: vl).

End EXPR.

Inductive outcome: Type :=
   | Out_break: outcome                 (**r terminated by [break] *)
   | Out_normal: outcome                (**r terminated normally *)
   | Out_return: option (val * type) -> outcome. (**r terminated by [return] *)

Inductive out_break_or_return : outcome -> outcome -> Prop :=
  | Out_break_or_return_B: out_break_or_return Out_break Out_normal
  | Out_break_or_return_R: forall ov,
      out_break_or_return (Out_return ov) (Out_return ov).

Definition outcome_switch (out: outcome) : outcome :=
  match out with
  | Out_break => Out_normal
  | o => o
  end.

Definition outcome_result_value (out: outcome) (t: type) (v: val) : Prop :=
  match out, t with
  | Out_normal, Tvoid => v = Vundef
  | Out_return None, Tvoid => v = Vundef
  | Out_return (Some (v',t')), ty => ty <> Tvoid /\ sem_cast v' t' t = Some v
  | _, _ => False
  end.

Inductive exec_stmt: env -> temp_env -> temp_env -> mem -> statement -> trace -> mem -> outcome -> Prop :=
  | exec_Sskip:   forall e le te m,
      exec_stmt e le te m Sskip
               E0 m Out_normal
  | exec_Sassign:   forall e le te m a1 a2 loc ofs v2 v m',
      eval_lvalue e le te m a1 loc ofs ->
      eval_expr e le te m a2 v2 ->
      sem_cast v2 (typeof a2) (typeof a1) = Some v ->
      assign_loc (typeof a1) m loc ofs v m' ->
      exec_stmt e le te m (Sassign a1 a2)
               E0 m' Out_normal
  | exec_Smemcpy:   forall e le te m ty tyargs al size algn bdst odst bsrc osrc t m' vres,
      eval_expr e le te m (Esizeof ty type_int32s) (Vint size) ->
      eval_expr e le te m (Ealignof ty type_int32s) (Vint algn) ->
      eval_exprlist e le te m al tyargs (Vptr bdst odst :: Vptr bsrc osrc :: nil) ->
      extcall_memcpy_sem (Int.intval size) (Int.intval algn) ge (Vptr bdst odst :: Vptr bsrc osrc :: nil) m t vres m' ->
      exec_stmt e le te m (Smemcpy ty tyargs al)
                t m' Out_normal
  | exec_Scall:   forall e le te m a al rets tyargs tyrets cconv vf vargs vrets f t m',
      classify_fun (typeof a) = fun_case_f (typelist_app tyargs tyrets) Tvoid cconv ->
      eval_expr e le te m a vf ->
      eval_exprlist e le te m al tyargs vargs ->
      eval_exprlist e le te m rets tyrets vrets ->
      Genv.find_funct ge vf = Some f ->
      type_of_fundef f = Tfunction (typelist_app tyargs tyrets) Tvoid cconv ->
      eval_funcall m f vargs vrets t m' Vundef ->
      exec_stmt e le te m (Scall None a al rets)
                t m' Out_normal
  | exec_Sseq_1:   forall e le te m s1 s2 t1 m1 t2 m2 out,
      exec_stmt e le te m s1 t1 m1 Out_normal ->
      exec_stmt e le te m1 s2 t2 m2 out ->
      exec_stmt e le te m (Ssequence s1 s2)
                (t1 ** t2) m2 out
  | exec_Sseq_2:   forall e le te m s1 s2 t1 m1 out,
      exec_stmt e le te m s1 t1 m1 out ->
      out <> Out_normal ->
      exec_stmt e le te m (Ssequence s1 s2)
                t1 m1 out
  | exec_Sifthenelse: forall e le te m a s1 s2 v1 b t m' out,
      eval_expr e le te m a v1 ->
      bool_val v1 (typeof a) = Some b ->
      exec_stmt e le te m (if b then s1 else s2) t m' out ->
      exec_stmt e le te m (Sifthenelse a s1 s2)
                t m' out
  | exec_Sreturn_none:   forall e le te m,
      exec_stmt e le te m (Sreturn None)
               E0 m (Out_return None)
  | exec_Sreturn_some: forall e le te m a v,
      eval_expr e le te m a v ->
      exec_stmt e le te m (Sreturn (Some a))
                E0 m (Out_return (Some (v, typeof a)))
  | exec_Sbreak:   forall e le te m,
      exec_stmt e le te m Sbreak
               E0 m Out_break
  | exec_Sfor_start: forall e le te m s a1 a2 a3 out m1 m2 t1 t2,
      a1 <> Sskip ->
      exec_stmt e le te m a1 t1 m1 Out_normal ->
      exec_stmt e le te m1 (Sfor Sskip a2 a3 s) t2 m2 out ->
      exec_stmt e le te m (Sfor a1 a2 a3 s)
                (t1 ** t2) m2 out
  | exec_Sfor_false: forall e le te m s a2 a3 v,
      eval_expr e le te m a2 v ->
      bool_val v (typeof a2) = Some false ->
      exec_stmt e le te m (Sfor Sskip a2 a3 s)
               E0 m Out_normal
  | exec_Sfor_stop: forall e le te m s a2 a3 v m1 t out1 out,
      eval_expr e le te m a2 v ->
      bool_val v (typeof a2) = Some true ->
      exec_stmt e le te m s t m1 out1 ->
      out_break_or_return out1 out ->
      exec_stmt e le te m (Sfor Sskip a2 a3 s)
                t m1 out
  | exec_Sfor_loop: forall e le te m s a2 a3 v m1 m2 m3 t1 t2 t3 out,
      eval_expr e le te m a2 v ->
      bool_val v (typeof a2) = Some true ->
      exec_stmt e le te m s t1 m1 Out_normal ->
      exec_stmt e le te m1 a3 t2 m2 Out_normal ->
      exec_stmt e le te m2 (Sfor Sskip a2 a3 s) t3 m3 out ->
      exec_stmt e le te m (Sfor Sskip a2 a3 s)
                (t1 ** t2 ** t3) m3 out
  | exec_Sswitch:   forall e le te m a t n sl m1 out,
      eval_expr e le te m a (Vint n) ->
      sem_switch_arg (Vint n) (typeof a) = Some (Int.unsigned n) ->
      exec_stmt e le te m (seq_of_labeled_statement (select_switch n sl)) t m1 out ->
      exec_stmt e le te m (Sswitch a sl)
                t m1 (outcome_switch out)

(** [eval_funcall m1 fd args t m2 res] describes the invocation of
  function [fd] with arguments [args].  [res] is the value returned
  by the call.  *)

with eval_funcall: mem -> fundef -> list val -> list val -> trace -> mem -> val -> Prop :=
  | eval_funcall_internal: forall le te m f vargs vrets t e m1 m2 m3 out vres,
      list_norepet (var_names f.(fn_vars)) ->
      list_norepet (var_names (f.(fn_params)++f.(fn_temps))) ->
      alloc_variables empty_env m f.(fn_vars) e m1 ->
      bind_parameter_temps f.(fn_params) vargs empty_temp = Some le ->
      bind_parameter_temps f.(fn_temps) vrets empty_temp = Some te ->
      exec_stmt e le te m1 f.(fn_body) t m2 out ->
      outcome_result_value out f.(fn_return) vres ->
      Mem.free_list m2 (blocks_of_env e) = Some m3 ->
      eval_funcall m (Internal f) vargs vrets t m3 vres.

Scheme exec_stmt_ind2 := Minimality for exec_stmt Sort Prop
  with eval_funcall_ind2 := Minimality for eval_funcall Sort Prop.
Combined Scheme exec_stmt_funcall_ind from exec_stmt_ind2, eval_funcall_ind2.

End SEMANTICS.


Section TRANSITIONS.

Require Import Streams.

Variable p: program.
Let ge : genv := Genv.globalenv p.

Variable bi bo: block.

Inductive type_of_fundef_case:type -> type -> type -> type -> bool -> Prop :=
  | type_of_fundef_anil_rnil:
    type_of_fundef_case (Tfunction Tnil Tvoid cc_default) (Tfunction Tnil Tvoid cc_default) Tvoid Tvoid false
  | type_of_fundef_anil_rcons: forall oty,
    type_of_fundef_case (Tfunction (Tcons (Tpointer oty) Tnil) Tvoid cc_default) (Tfunction (Tcons (Tpointer oty) Tnil) Tvoid cc_default) Tvoid oty true
  | type_of_fundef_acons_rnil: forall ity,
    type_of_fundef_case (Tfunction (Tcons (Tpointer ity) Tnil) Tvoid cc_default) (Tfunction Tnil Tvoid cc_default) ity Tvoid false
  | type_of_fundef_acons_rcons: forall ity oty,
    type_of_fundef_case (Tfunction (Tcons (Tpointer ity) (Tcons (Tpointer oty) Tnil)) Tvoid cc_default) (Tfunction (Tcons (Tpointer oty) Tnil) Tvoid cc_default) ity oty true.

Inductive initial_state(f: fundef): mem -> Prop :=
  | initial_state_: forall b1 b2 fi m_init m0 m1 m2 ity oty b,
      Genv.init_mem p = Some m_init ->
      Genv.find_symbol ge (reset_id p.(prog_main)) = Some b1 ->
      Genv.find_symbol ge p.(prog_main) = Some b2 ->
      Genv.find_funct_ptr ge b1 = Some fi ->
      Genv.find_funct_ptr ge b2 = Some f ->
      type_of_fundef_case (type_of_fundef f) (type_of_fundef fi) ity oty b ->
      Mem.alloc m_init 0 (sizeof ity) = (m0, bi) ->
      Mem.alloc m0 0 (sizeof oty) = (m1, bo) ->
      eval_funcall ge m1 fi nil (if b then Vptr bo Int.zero :: nil else nil) E0 m2 Vundef ->
      initial_state f m2.

Inductive classify_mvls:list mvl -> mvl -> bool -> Prop :=
  | classify_mvls_nil:
    classify_mvls nil nil false
  | classify_mvls_cons: forall mv2,
    classify_mvls (mv2::nil) mv2 true.

Inductive exec_prog (main: fundef)(m: mem)(n maxn: nat)(vass vrss: Stream (list mvl)): Prop :=
  | exec_prog_term:
    (n > maxn)%nat ->
    exec_prog main m n maxn vass vrss
  | exec_prog_cons: forall (b1 b2: bool) m1 mv1 mv2 m',
    (n <= maxn)%nat ->
    classify_mvls (hd vass) mv1 b1 ->
    classify_mvls (hd vrss) mv2 b2 ->
    Mem.storebytes m bi 0 mv1 = Some m1 ->
    eval_funcall ge m1 main (if b1 then Vptr bi Int.zero :: nil else nil) (if b2 then Vptr bo Int.zero :: nil else nil) E0 m' Vundef ->
    Mem.loadbytes m' bo 0 (Z_of_nat (length mv2)) = Some mv2 ->
    exec_prog main m' (n+1) maxn (tl vass) (tl vrss) ->
    exec_prog main m n maxn vass vrss.

End TRANSITIONS.
