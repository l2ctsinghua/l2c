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

(** Translation from LustreV to LustreS. *)

Require Import Coqlib.
Require Import Ctypes.
Require Import Cltypes.
Require Import AST.
Require Import Errors.
Require Import List.
Require Import Integers.
Require Import Floats.
Require Import Maps.
Require Import Bool.
Require Import Lop.
Require Import LustreV.
Require Import Lustre.
Require Import LustreS.
Require Import Lident.
Require Import Ltypes.
Require Import Cop.


Local Open Scope error_monad_scope.

Set Implicit Arguments.

Definition bind3 (A B C D: Type) (f: res (A * B * C)) (g: A -> B -> C -> res D) : res D :=
  match f with
  | OK (x, y, z) => g x y z
  | Error msg => Error msg
  end.

Definition bind4 (A B C D E: Type) (f: res (A * B * C * D)) (g: A -> B -> C -> D -> res E) : res E :=
  match f with
  | OK (x, y, z, z1) => g x y z z1
  | Error msg => Error msg
  end.

Notation "'do' ( X , Y , Z ) <- A ; B" := (bind3 A (fun X Y Z => B))
 (at level 200, X ident, Y ident, Z ident, A at level 100, B at level 200)
 : error_monad_scope.

Notation "'do' ( X , Y , Z , Z1 ) <- A ; B" := (bind4 A (fun X Y Z Z1 => B))
 (at level 200, X ident, Y ident, Z ident, Z1 ident, A at level 100, B at level 200)
 : error_monad_scope.

Remark bind3_inversion:
  forall (A B C D: Type) (f: res (A*B*C)) (g: A -> B -> C -> res D) (z: D),
  bind3 f g = OK z ->
  exists x x1 x2, f = OK (x, x1, x2) /\ g x x1 x2 = OK z.
Proof.
  intros until z. destruct f; simpl.
  destruct p. simpl.
  destruct p; simpl; intros. exists a, b, c; auto.
  intros; discriminate.
Qed.

Remark bind4_inversion:
  forall (A B C D E: Type) (f: res (A*B*C*D)) (g: A -> B -> C -> D -> res E) (z: E),
  bind4 f g = OK z ->
  exists x x1 x2 x3, f = OK (x, x1, x2, x3) /\ g x x1 x2 x3 = OK z.
Proof.
  intros until z. destruct f; simpl.
  destruct p. simpl. destruct p. simpl.
  destruct p; simpl; intros. exists a, b, c, d; auto.
  intros; discriminate.
Qed.

Definition Next_pid (id:ident) := Psucc id.

(** Translate enum constant to integer. Some points to note:
- enum type: enum (list ident); enum constant: ident.
- count_occ_pos: return position of ident in [(list ident)].
- 0 means that ident is not in[(list ident)]. *)

Fixpoint count_occ_pos (l: list ident) (x: ident): nat :=
  match l with
  | nil => 0%nat
  | y::tl =>
    if identeq y x then S (List.length tl) else count_occ_pos tl x
  end.

Fixpoint trans_type (ty:typeL) : type :=
  match ty with
  | LustreV.Tshort => Cltypes.Tint I16 Signed
  | LustreV.Tushort => Cltypes.Tint I16 Unsigned
  | LustreV.Tint => Cltypes.Tint I32 Signed
  | LustreV.Tuint => Cltypes.Tint I32 Unsigned
  | LustreV.Tfloat => Cltypes.Tfloat F32
  | LustreV.Treal => Cltypes.Tfloat F64
  | LustreV.Tbool => Cltypes.Tint IBool Signed
  | LustreV.Tchar => Cltypes.Tint I8 Signed
  | LustreV.Tarray id ty i => Cltypes.Tarray id (trans_type ty) i
  | LustreV.Tstruct id fdl => Cltypes.Tstruct id (trans_fieldlist fdl)
  | LustreV.Tenum id idl => Cltypes.Tint I32 Signed
  end

with trans_fieldlist (fdl: fieldlistL) : fieldlist :=
  match fdl with
  | LustreV.Fnil => Cltypes.Fnil
  | LustreV.Fcons id ty fdl => Cltypes.Fcons id (trans_type ty) (trans_fieldlist fdl)
  end.

Definition trans_type_declL (tc: ident*typeL): (ident* type) :=
  (fst tc, trans_type (snd tc)).

Definition trans_type_blocks (tydl: list (ident*typeL)): list(ident* type) :=
  map trans_type_declL tydl.

Fixpoint val_of_id (id : ident) (const_block : list const_declL) : res constL :=
  match const_block with
    | nil => Error (msg "LustreSGen.val_of_id: id is not defined")
    | (ConstDeclL id1 ty val1)::tl =>
      if (identeq id id1) then OK val1 else val_of_id id tl
  end.

Fixpoint trans_construct_list (const_list : const_listL) (id_val : list const_declL) : res const_listL :=
  match const_list with
  | ConstNilL => OK ConstNilL
  | ConstConL first rest =>
      do rest_val <- trans_construct_list rest id_val;
      match first with
      | ID id ty => (**r constL is "ID", enum const or const id *)
          match ty with
          | Tenum _ idl =>
              let num := (count_occ_pos idl id) in
              if beq_nat num 0%nat then
                 do first_val <- val_of_id id id_val;
                 OK (ConstConL first_val rest_val)
              else
                 OK (ConstConL (EnumConstL id ty) rest_val)
          | _ =>
              do first_val <- val_of_id id id_val;
              OK (ConstConL first_val rest_val)
        end
      | ConstructConstL const_list1 => (**r constL is "ConstructConstL", recursive process *)
          do const_val <- trans_construct_list const_list1 id_val;
          let first_val := ConstructConstL const_val in
          OK (ConstConL first_val rest_val)
      | _ => (**r othres, preserved *)
          OK (ConstConL first rest_val)
      end
  end.

Fixpoint translate_const_id (const_block : list const_declL) (id_val : list const_declL) : res (list const_declL)  :=  (*change-- translate id in ConstBlock to other forms\u00a3\u00ac const_block := rev ConstBlock*)
  match const_block with
  | nil => OK id_val
  | (ConstDeclL const_id ty const_value)::tl => (*ConstDeclL : visibilityL -> ident -> typeL -> constL -> constDeclL*)
      match const_value with
      | ID id ty =>
          match ty with
          | Tenum _ idl =>
              let num := (count_occ_pos idl id) in
              if beq_nat num 0%nat then
                 do const_val <- val_of_id id id_val;
                 translate_const_id tl ((ConstDeclL const_id ty const_val)::id_val)
              else translate_const_id tl ((ConstDeclL const_id ty (EnumConstL id ty))::id_val)
          | _ => do const_val <- val_of_id id id_val;
              translate_const_id tl ((ConstDeclL const_id ty const_val)::id_val)
          end
      | ConstructConstL const_list =>
          do const_list_val <- trans_construct_list const_list id_val;
          let const_val := (ConstructConstL const_list_val) in
          translate_const_id tl ((ConstDeclL const_id ty const_val)::id_val)
      | _ => translate_const_id tl ((ConstDeclL const_id ty const_value)::id_val)
      end
  end.

Fixpoint translate_const_value (item : constL)  : res (list AST.init_data) :=
  match item with
  | ShortConstL i => OK ((AST.Init_int16 i) :: nil)
  | UshortConstL i => OK ((AST.Init_int16 i) :: nil)
  | IntConstL i => OK ((AST.Init_int32 i) :: nil)
  | UintConstL i => OK ((AST.Init_int32 i) :: nil)
  | CharConstL c => OK ((AST.Init_int8 c) :: nil)
  | BoolConstL b => OK (AST.Init_int8 (trans_bool b) :: nil)
  | RealConstL r => OK ((AST.Init_float64 r) :: nil)
  | FloatConstL r => OK ((AST.Init_float32 r) :: nil)
  | ConstructConstL const_list =>
      translate_const_list const_list
  | EnumConstL id ty =>
      match ty with
      | Tenum _ idl =>
          let c_value := AST.Init_int32 (Int.repr ( Z_of_nat (count_occ_pos idl id) )) in
          OK (c_value::nil)
      | _ => Error (msg "LustreSGen.translate_const_value: not Tenum")
      end
  | ID id ty => Error (msg "LustreSGen.translate_const_value: not deal here")
  end

with translate_const_list (const_list: const_listL)
  : res (list AST.init_data) :=
  match const_list with
    | ConstNilL => OK nil
    | ConstConL l_item rest =>
      do c_item <- (translate_const_value l_item );
      do c_rest <- (translate_const_list rest );
      OK (app c_item c_rest)
  end.

Definition trans_const_decl (c: const_declL) : res (ident* globvar type) :=
  match c with
  | ConstDeclL const_id l_type const_val =>
      let ty := trans_type l_type in
      do s_value <- translate_const_value const_val;
      OK (const_id, (mkglobvar ty s_value true true))
  end.

Definition trans_var_decl (vdl: var_declL): (ident*type) :=
  match vdl with
  | VarDeclL id ty ck => (id, (trans_type ty))
  | ClockVarDeclL id ty ck => (id, (trans_type ty))
  end.

Definition trans_params (param: paramsL): Lustre.params :=
  map trans_var_decl param.

Definition headof(A: Type)(l: list A)(msg: errmsg): res A :=
  match l with
  | nil => Error msg
  | hd :: tl => OK hd
  end.

Fixpoint cons_type_init(ty: typeL)(pid: ident): ident*sexp*params*list stmt :=
  let t := trans_type ty in
  match ty with
  | LustreV.Tfloat =>
      let e := Sconst (Csingle Float32.zero) t in
      (pid,e,nil,nil)
  | LustreV.Treal =>
      let e := Sconst (Cfloat Float.zero) t in
      (pid,e,nil,nil)
  | LustreV.Tbool =>
      let e := Sconst (Cbool false) t in
      (pid,e,nil,nil)
  | LustreV.Tarray  _ aty z =>
      let '(id1,es1,lvar1,eqs1) := cons_type_init aty pid in
      let fs := Harydef (id1, t) es1 in
      let eq := Sfor true fs (Int.repr z) in
      (Next_pid id1, Svar id1 t,lvar1++(id1,t)::nil,eqs1++eq::nil)
  | LustreV.Tstruct _ fld =>
      let '(id1,es1,lvar1,eqs1) := cons_fld_init fld pid in
      let eq := Sstruct (id1,t) (trans_fieldlist fld) es1 in
      (Next_pid id1, Svar id1 t,lvar1++(id1,t)::nil,eqs1++eq::nil)
  | _ =>
      let e := Sconst (Cint Int.zero) t in
      (pid,e,nil,nil)
  end

with cons_fld_init(fld: fieldlistL)(pid: ident): ident*list sexp*params*list stmt  :=
  match fld with
  | LustreV.Fnil => (pid,nil,nil,nil)
  | LustreV.Fcons id ty ftl =>
      let '(id1,es1,lvar1,eqs1) := cons_type_init ty pid in
      let '(id2,es2,lvar2,eqs2) := cons_fld_init ftl id1 in
      (id2,es1::es2,lvar1++lvar2,eqs1++eqs2)
  end.

Fixpoint cons_type_inits(tyl: list typeL)(pid: ident): ident*list sexp*params*list stmt :=
  match tyl with
  | nil => (pid,nil,nil,nil)
  | ty :: tl =>
      let '(id1,es1,lvar1,eqs1) := cons_type_init ty pid in
      let '(id2,es2,lvar2,eqs2) := cons_type_inits tl id1 in
      (id2,es1::es2,lvar1++lvar2,eqs1++eqs2)
  end.

Definition mkstmt := (ident*type) -> stmt.

Fixpoint cons_fby(idl: list ident)(lx ly: list sexp): res (list mkstmt) :=
  match idl, lx, ly with
  | hd1::tl1, hd2::tl2, hd3::tl3 =>
    let eq := (fun lh => Sfby lh hd1 hd2 hd3) in
    do eqs <- cons_fby tl1 tl2 tl3;
    OK (eq:: eqs)
  | nil, nil,nil => OK nil
  | _, _,_ => Error (msg "LustreSGen.cons_fby")
  end.

Definition ids_of_fby (sty : type) : res (ident*ident) :=
  match sty with
  | Cltypes.Tstruct sid (Cltypes.Fcons _ _ (Cltypes.Fcons _ (Cltypes.Tarray aid _ _) Cltypes.Fnil)) =>
      OK (sid, aid)
  | _ => Error (msg"ids_of_fby error")
  end.

Definition cons_fbyn_exp(id: ident)(ty: type)(e1 e2: sexp) (n: int): res mkstmt :=
  if (Z_eq_dec 1 (Int.unsigned n)) then
    OK (fun lh => LustreS.Sfby lh id e1 e2)
  else
    do (sid,aid) <- ids_of_fby ty;
    OK (fun lh => LustreS.Sfbyn lh (id, sid, aid) n e1 e2).

Fixpoint cons_fbyn(idl: list (typeL*ident))(lx ly: list sexp) (n: int): res (list mkstmt) :=
  match idl, lx, ly with
  | (t,id)::tl1, hd2::tl2, hd3::tl3 =>
    let ty := trans_type t in
    do eq <- cons_fbyn_exp id ty hd2 hd3 n;
    do eqs <- cons_fbyn tl1 tl2 tl3 n;
    OK (eq:: eqs)
  | nil,nil,nil => OK nil
  | _,_,_ => Error (msg "LustreSGen.cons_fbyn")
  end.

Fixpoint cons_arrow(lx ly: list sexp): res (list mkstmt) :=
  match lx, ly with
  | hd2::tl2, hd3::tl3 =>
    let eq := (fun lh => Sarrow lh hd2 hd3) in
    do eqs <- cons_arrow tl2 tl3;
    OK (eq::eqs)
  | nil, nil => OK nil
  | _,_ => Error (msg "LustreSGen.cons_arrow")
  end.

Fixpoint cons_ifelse(lx ly: list sexp)(cond: sexp): res (list mkstmt) :=
  match lx, ly with
  | hd2::tl2, hd3::tl3 =>
    let eq := (fun lh => Sassign lh (Eif cond hd2 hd3)) in
    do eqs <- cons_ifelse tl2 tl3 cond;
    OK (eq::eqs)
  | nil, nil => OK nil
  | _,_ => Error (msg "LustreSGen.cons_ifelse")
  end.

Definition trans_var (id: ident)(ty: typeL): sexp :=
  let t := trans_type ty in
  match ty with
  | Tenum i idl =>
    let num := (count_occ_pos idl id) in
    if beq_nat num 0%nat then
      Svar id t
    else
      Sconst (Cint (Int.repr (Z_of_nat num))) t
  | _ => Svar id t
  end.

Definition trans_calldef(nh: nodehandlerL)(oi: option int): calldef :=
  match nh with
  | NodehandlerL id rettypes pt kind instance_id =>
    let in_type := map trans_type pt in
    mkcalldef kind instance_id id oi xH Cltypes.Fnil in_type nil
  end.

Definition trans_prefix_unary_fold (op: unary_operationL)(val: Lustre.sexp)(i: int): mkstmt :=
  match op with
  | LustreS.Oshort => (fun x => Sfor true (Hfoldcast x val (Cltypes.Tint I16 Signed)) i)
  | LustreS.Oint => (fun x => Sfor true (Hfoldcast x val (Cltypes.Tint I32 Signed)) i)
  | LustreS.Ofloat => (fun x => Sfor true (Hfoldcast x val (Cltypes.Tfloat F32)) i)
  | LustreS.Oreal => (fun x => Sfor true (Hfoldcast x val (Cltypes.Tfloat F64)) i)
  | LustreS.Onot => (fun x => Sfor true (Hfoldunary x  Cop.Onotbool val) i)
  | LustreS.Opos => (fun x => Sassign x (Expr val))
  | LustreS.Oneg => (fun x => Sfor true (Hfoldunary x Cop.Oneg val) i)
  end.

Fixpoint trans_la_lhs (lv:lhsL) (la: list sexp): res (list LustreS.stmt) :=
  match lv, la with
  | nil, nil => OK nil
  | hd1::tl1, hd2::tl2 =>
    do eqs1 <- trans_la_lhs tl1 tl2;
    match hd1 with
    | LhsID id t _ =>
      let eq := Sassign (id, trans_type t) (Expr hd2) in
      OK (eq::eqs1)
    end
  | _,_ => Error (msg "LustreSGen.trans_la_lhs ")
  end.

Fixpoint construct_lhs (tcl : list typeL) (pid : ident) : (ident * list Lustre.sexp * params) :=
  match tcl with
  | nil => (pid, nil, nil)
  | ty :: tl =>
    let t := trans_type ty in
    let '(id2,la2,lvar2) := construct_lhs tl (Next_pid pid) in
    (id2, Svar pid t :: la2, (pid,t) :: lvar2)
  end.

Definition trans_lhsid(a: lhs_idL) : ident*type :=
  match a with
  | LhsID id t ck => (id,trans_type t)
  end.

Definition cons_calhs (first: bool)(lv:lhsL)(tcl: list typeL)(pid: ident): (ident * list Lustre.sexp * params * list (ident*type)) :=
  if first then
    (pid, nil, nil, map trans_lhsid lv)
  else
    let '(id1, es1, lvar1) := construct_lhs tcl pid in
    (id1, es1, lvar1, lvar1).

Fixpoint cons_stmt (lv: list (ident*type)) (mkss: list mkstmt): res (list stmt) :=
  match lv, mkss with
  | nil, nil => OK nil
  | lh::tl1, mks::tl2 =>
    do eqs <- cons_stmt tl1 tl2;
    OK (mks lh :: eqs)
  | _,_ => Error (msg "LustreSGen.cons_stmt ")
  end.

Definition cons_lhs (first: bool)(lv:lhsL)(tcl: list typeL)(mkss: list mkstmt)(pid: ident): res (ident * list Lustre.sexp * params * list stmt) :=
  if first then
    do eqs <- cons_stmt (map trans_lhsid lv) mkss;
    OK (pid, nil, nil, eqs)
  else
    let '(id1, es1, lvar1) := construct_lhs tcl pid in
    do eqs <- cons_stmt lvar1 mkss;
    OK (id1, es1, lvar1, eqs).

Definition cons_patn (p: patternL): res patn :=
  match p with
  | PatternAny => OK Pany
  | PatternID vid vty =>
    match vty with
    | Tenum id idl =>
      let pccond := Int.repr (Z_of_nat (count_occ_pos idl vid)) in
      OK (Paint pccond)
    | _ => Error (msg "LustreSGen: cons_patn: switch wrong: pattern must be integer")
    end
  | PatternChar val => OK (Pachar val)
  | PatternInt i _ => OK (Paint i)
  | PatternBool b => OK (Pabool b)
  end.

Inductive classify_binop_case: Type :=
  | binop_case_normal
  | binop_case_typeeq
  | binop_case_typene.

Definition classify_binop(ty: type)(op: binary_operationL) :=
  match is_arystr ty, op with
  | true, Lop.Oeq => binop_case_typeeq
  | true, Lop.One => binop_case_typene
  | _, _ => binop_case_normal
  end.

Fixpoint trans_expr (lv:lhsL)(first: bool)(exp: LustreV.exprS) (pid: ident){struct exp}: res (ident* list sexp* params* list stmt) :=
  match exp with
  | EconstS c t _ => (**r sexp *)
    let els := Sconst c (trans_type t)::nil in
    if first then
      do eqs <- trans_la_lhs lv els;
      OK (pid, nil, nil, eqs)
    else
      OK (pid, els, nil, nil)
  | EvarS v t _ => (**r sexp *)
    let els := trans_var v t::nil in
    if first then
      do eqs <- trans_la_lhs lv els;
      OK (pid, nil, nil, eqs)
    else
      OK (pid, els, nil, nil)
  | EunopS op e tc => (**r Scast: sexp-> type-> sexp; Sunop: unary_operation -> sexp -> type -> sexp *)
    do (id1, es1, lvar1, eqs1) <- trans_expr nil false e pid;
    do hd <- headof es1 (msg "LustreSGen.trans_expr: EunopS: es1 null");
    let es := trans_prefix_unary_expr op hd (trans_type (fst tc)) :: nil in
    if first then
      do eqs2 <- trans_la_lhs lv es;
      OK (id1, nil, lvar1, eqs1++eqs2)
    else
      OK (id1, es, lvar1, eqs1)
  | EbinopS op e1 e2 tc =>
    do (id1, es1, lvar1, eqs1) <- trans_expr nil false e1 pid;
    do (id2, es2, lvar2, eqs2) <- trans_expr nil false e2 id1;
    do hd <- headof es1 (msg "LustreSGen.trans_expr: EbinopS");
    do hd1 <- headof es2 (msg "LustreSGen.trans_expr: EbinopS");
    match classify_binop (typeof hd) op with
    | binop_case_typeeq => (**r Etypecmp: sexp -> sexp -> expr *)
      let mks := (fun x => Sassign x (Etypecmp true hd hd1)) :: nil in
      do (id3, es3, lvar3, eqs3) <- cons_lhs first lv (fst tc::nil) mks id2;
      OK (id3, es3, lvar1++lvar2++lvar3, eqs1++eqs2++eqs3)
    | binop_case_typene => (**r Etypencmp: sexp -> sexp -> expr *)
      let mks := (fun x => Sassign x (Etypecmp false hd hd1)) :: nil in
      do (id3, es3, lvar3, eqs3) <- cons_lhs first lv (fst tc::nil) mks id2;
      OK (id3, es3, lvar1++lvar2++lvar3, eqs1++eqs2++eqs3)
    | binop_case_normal => (**r Sbinop: binary_operation -> sexp -> sexp -> type -> sexp *)
      let es := Sbinop op hd hd1 (trans_type (fst tc)) :: nil in
      if first then
        do eqs3 <- trans_la_lhs lv es;
        OK (id2, nil, lvar1++lvar2, eqs1++eqs2++eqs3)
      else
        OK (id2, es, lvar1++lvar2, eqs1++eqs2)
    end
  | EarrayaccS e i tc => (**r Saryacc: sexp -> sexp -> type -> sexp *)
    do (id1, es1, lvar1, eqs1) <- trans_expr nil false e pid;
    do hd1 <- headof es1 (msg "LustreSGen.trans_expr: EarrayaccS: es1 null");
    let es := Saryacc hd1 (Sconst(Cint i) type_int32s) (trans_type (fst tc)) :: nil in
    if first then
      do eqs2 <- trans_la_lhs lv es;
      OK (id1, nil, lvar1, eqs1++eqs2)
    else
      OK (id1, es, lvar1, eqs1)
  | EfieldS e id tc => (**r Sfield: sexp -> ident -> type -> sexp *)
    do (id1, es1, lvar1, eqs1) <- trans_expr nil false e pid;
    do hd <- headof es1 (msg "LustreSGen.trans_expr: EfieldS");
    let es := Sfield hd id (trans_type (fst tc))::nil in
    if first then
      do eqs2 <- trans_la_lhs lv es;
      OK (id1, nil, lvar1, eqs1++eqs2)
    else
      OK (id1, es, lvar1, eqs1)
  | ListExprS el => (**r list sexp *)
    do (id1, els, lvar1, eqs1) <- trans_expr_list el pid;
    if first then
      do eqs <- trans_la_lhs lv els;
      OK (id1, nil, lvar1, eqs1++eqs)
    else
      OK (id1, els, lvar1, eqs1)
  | ApplyExprS op el tcl=>
    let tyl := map fst tcl in
    do (id1, els1, lvar1, eqs1) <- trans_expr_list el pid;
    do (id2, els2, lvar2, eqs2) <- trans_operator lv first op tyl els1 id1;
    OK (id2, els2, lvar1++lvar2, eqs1++eqs2)
  | EconstructS estr tc => (**r Sstruct: ident*type -> list sexp -> stmt *)
    do (id1, es1, lvar1, eqs1) <- trans_expr_list estr pid;
    do fld <- fieldof_struct (trans_type (fst tc));
    let mks := (fun x => Sstruct x fld es1) :: nil in
    do (id2, es2, lvar2, eqs2) <- cons_lhs first lv (fst tc::nil) mks id1;
    OK (id2, es2, lvar1++lvar2, eqs1++eqs2)
  | EarraydefS e i tcl=> (**r Sfor:bool -> (Harydef: ident*type ->sexp -> hstmt) -> int -> stmt *)
    let tyl := map fst tcl in
    do (id1, es1, lvar1, eqs1) <- trans_expr nil false e pid;
    do hd1 <- headof es1 (msg "LustreSGen.trans_expr: EarraydefS");
    let mks := (fun x => Sfor true (Harydef x hd1) i) :: nil in
    do (id2, es2, lvar2, eqs2) <- cons_lhs first lv tyl mks id1;
    OK (id2, es2, lvar1++lvar2, eqs1++eqs2)
  | EarraydiffS el tc=> (**r Sarydif: ident*type -> list sexp -> stmt *)
    do (id1, es1, lvar1, eqs1) <- trans_expr_list el pid;
    let mks := (fun x => Sarydif x Int.zero es1) :: nil in
    do (id2, es2, lvar2,eqs2) <- cons_lhs first lv (fst tc::nil) mks id1;
    OK (id2, es2, lvar1++lvar2, eqs1++eqs2)
  | EarrayprojS e1 el e2 tc=> (**r Earyprj: sexp -> list sexp -> sexp -> expr*)
    do (id1, es1, lvar1, eqs1) <- trans_expr nil false e1 pid;
    do (id2, els, lvar2, eqs2) <- trans_expr_list el id1;
    do (id3, es3, lvar3, eqs3) <- trans_expr nil false e2 id2;
    do hd <- headof es1 (msg "LustreSGen.trans_expr: EarrayprojS: es1 or es3 null");
    do hd1 <- headof es3 (msg "LustreSGen.trans_expr: EarrayprojS: es1 or es3 null");
    let mks := (fun x => Sassign x (Earyprj hd els hd1)) :: nil in
    do (id4, es4, lvar4, eqs4) <- cons_lhs first lv (fst tc::nil) mks id3;
    OK (id4, es4, lvar1++lvar2++lvar3++lvar4, eqs1++eqs2++eqs3++eqs4)
  | EarraysliceS e i j tc=> (**r Sor: bool -> (Haryslc: ident*type -> sexp -> int -> hstmt) -> int -> stmt*)
    do (id1, es1, lvar1, eqs1) <- trans_expr nil false e pid;
    do hd1 <- headof es1 (msg "LustreSGen.trans_expr: EarraysliceS");
    if Int.lt i (Int.add j Int.one) then
      let mks := (fun x => Sfor true (Haryslc x hd1 i) (Int.sub (Int.add j Int.one) i)) :: nil in
      do (id2, es2, lvar2, eqs2) <- cons_lhs first lv (fst tc::nil) mks id1;
      OK (id2, es2, lvar1++lvar2, eqs1++eqs2)
    else Error (msg "LustreSGen.trans_expr: EarraysliceS: j < i")
  | EmixS e1 lindex e2 tc=> (**r Smix: ident*type -> sexp -> list lindex -> sexp -> stmt*)
    do (id1, es1, lvar1, eqs1) <- trans_expr nil false e1 pid;
    do (id2, lindexs, lvar2, eqs2) <- trans_label_index_list lindex id1;
    do (id3, es3, lvar3, eqs3) <- trans_expr nil false e2 id2;
    do hd1 <- headof es1 (msg "LustreSGen.trans_expr: EmixS");
    do hd2 <- headof es3 (msg "LustreSGen.trans_expr: EmixS");
    let mks := (fun x => Smix x hd1 lindexs hd2) :: nil in
    do (id4, es4, lvar4, eqs4) <- cons_lhs first lv (fst tc::nil) mks id3;
    OK (id4, es4, lvar1++lvar2++lvar3++lvar4, eqs1++eqs2++eqs3++eqs4)
  | EpreS idl e tcl=> (**r Sfby: ident*type -> ident -> sexp -> sexp -> stmt *)
    let tyl := map fst tcl in
    do (id1, es1, lvar1, eqs1) <- trans_expr nil false e pid;
    let '(id2, es2, lvar2, eqs2) := cons_type_inits tyl id1 in
    do mks <- cons_fby idl es1 es2;
    do (id3, es3, lvar3, eqs3) <- cons_lhs first lv tyl mks id2;
    OK (id3, es3, lvar1++lvar2++lvar3, eqs1++eqs2++eqs3)
  | EfbyS tyidl el1 i el2 tcl=> (**r Sfbyn ident*type -> (ident*ident*ident) -> int -> sexp -> sexp -> stmt *)
    let tyl := map fst tcl in
    do (id1, es1, lvar1, eqs1) <- trans_expr_list el1 pid;
    do (id2, es2, lvar2, eqs2) <- trans_expr_list el2 id1;
    do mks <- cons_fbyn tyidl es1 es2 i;
    do (id3, es3, lvar3, eqs3) <- cons_lhs first lv tyl mks id2;
    OK (id3, es3, lvar1++lvar2++lvar3, eqs1++eqs2++eqs3)
  | EarrowS e1 e2 tcl=> (**r Sarrow: ident*type -> sexp -> sexp -> stmt *)
    let tyl := map fst tcl in
    do (id1, es1, lvar1, eqs1) <- trans_expr nil false e1 pid;
    do (id2, es2, lvar2, eqs2) <- trans_expr nil false e2 id1;
    do mks <- cons_arrow es1 es2;
    do (id3, es3, lvar3, eqs3) <- cons_lhs first lv tyl mks id2;
    OK (id3, es3, lvar1++lvar2++lvar3, eqs1++eqs2++eqs3)
  | EwhenS _ _ _ => Error (msg "LustreSGen: trans_expr: EwhenS.")
  | EcurrentS _ _ => Error (msg "LustreSGen: trans_expr: EcurrentS.")
  | EifS e1 e2 e3 tcl=> (**r Eif: sexp -> sexp -> sexp -> expr *)
    let tyl := map fst tcl in
    do (id1, es1, lvar1, eqs1) <- trans_expr nil false e1 pid;
    do (id2, es2, lvar2, eqs2) <- trans_expr nil false e2 id1;
    do (id3, es3, lvar3, eqs3) <- trans_expr nil false e3 id2;
    do hd <- headof es1 (msg "LustreSGen.trans_expr: EifS");
    do mks <- cons_ifelse es2 es3 hd;
    do (id4, es4, lvar4, eqs4) <- cons_lhs first lv tyl mks id3;
    OK (id4, es4, lvar1++lvar2++lvar3++lvar4, eqs1++eqs2++eqs3++eqs4)
  | EcaseS e patl tcl=> (**r Ecase: sexp -> list (patternL*sexp) -> expr *)
    let tyl := map fst tcl in
    do (id1, es1, lvar1, eqs1) <- trans_expr nil false e pid;
    do (id2, patls, lvar2, eqs2) <- trans_pattern_list patl id1;
    do hd <- headof es1 (msg "LustreSGen.trans_expr: EcaseS: es1 null");
    let mks := (fun x => Sassign x (Ecase hd patls)) :: nil in
    do (id3, es3, lvar3, eqs3) <- cons_lhs first lv tyl mks id2;
    OK (id3, es3, lvar1++lvar2++lvar3, eqs1++eqs2++eqs3)
  | EboolredS i j e (ty, ck) =>
    do (aty, k) <- typeof_array (trans_type ty);
    do (id1, es1, lvar1, eqs1) <- trans_expr nil false e pid;
    do hd <- headof es1 (msg "LustreSGen.trans_expr: EboolredS: expr null");
    let fs := Sfor true (Hboolred (id1, type_int32s) hd) (Int.repr k) in
    let cond1 := Sbinop Lop.Ole (Sconst (Cint i) type_int32s) (Svar id1 type_int32s) type_bool in
    let cond2 := Sbinop Lop.Ole (Svar id1 type_int32s) (Sconst (Cint j) type_int32s) type_bool in
    let cond := Sbinop Lop.Oand cond1 cond2 type_bool in
    if first then
      do eqs2 <- trans_la_lhs lv (cond::nil);
      OK (Next_pid id1, nil, lvar1++(id1,type_int32s)::nil,eqs1++fs::eqs2)
    else
      OK (Next_pid id1, cond::nil,lvar1++(id1,type_int32s)::nil,eqs1++fs::nil)
  | EdieseS e (ty, ck) => (*boolred(0,1,n)[a1, ..., an]*)
    do (aty, k) <- typeof_array (trans_type ty);
    do (id1, es1, lvar1, eqs1) <- trans_expr nil false e pid;
    do hd <- headof es1 (msg "LustreSGen.trans_expr: EboolredS: expr null");
    let fs := Sfor true (Hboolred (id1, type_int32s) hd) (Int.repr k) in
    let cond1 := Sbinop Lop.Ole (Sconst (Cint Int.zero) type_int32s) (Svar id1 type_int32s) type_bool in
    let cond2 := Sbinop Lop.Ole (Svar id1 type_int32s) (Sconst (Cint Int.one) type_int32s) type_bool in
    let cond := Sbinop Lop.Oand cond1 cond2 type_bool in
    if first then
      do eqs2 <- trans_la_lhs lv (cond::nil);
      OK (Next_pid id1, nil, lvar1++(id1,type_int32s)::nil,eqs1++fs::eqs2)
    else
      OK (Next_pid id1, cond::nil,lvar1++(id1,type_int32s)::nil,eqs1++fs::nil)
  | EnorS e (ty, ck) => (*boolred(0,0,n)[a1, ..., an]*)
    do (aty, k) <- typeof_array (trans_type ty);
    do (id1, es1, lvar1, eqs1) <- trans_expr nil false e pid;
    do hd <- headof es1 (msg "LustreSGen.trans_expr: EboolredS: expr null");
    let fs := Sfor true (Hboolred (id1, type_int32s) hd) (Int.repr k) in
    let cond1 := Sbinop Lop.Ole (Sconst (Cint Int.zero) type_int32s) (Svar id1 type_int32s) type_bool in
    let cond2 := Sbinop Lop.Ole (Svar id1 type_int32s) (Sconst (Cint Int.zero) type_int32s) type_bool in
    let cond := Sbinop Lop.Oand cond1 cond2 type_bool in
    if first then
      do eqs2 <- trans_la_lhs lv (cond::nil);
      OK (Next_pid id1, nil, lvar1++(id1,type_int32s)::nil,eqs1++fs::eqs2)
    else
      OK (Next_pid id1, cond::nil,lvar1++(id1,type_int32s)::nil,eqs1++fs::nil)
  end

with trans_expr_list (exps: expr_listS) (pid:ident): res (ident* list sexp* params* list stmt) :=
  match exps with
  | Enil => OK (pid, nil, nil, nil)
  | Econs hd tl =>
    do (id1, es1, lvar1, eqs1) <- trans_expr nil false hd pid;
    do (id2, es2, lvar2, eqs2) <- trans_expr_list tl id1;
    OK (id2, es1++es2, lvar1++lvar2, eqs1++eqs2)
  end

with trans_pattern_list (patns:pattern_listS) (pid: ident): res (ident* list (patn*sexp)* params* list stmt) :=
  match patns with
  | PatternNilS => OK (pid, nil, nil, nil)
  | PatternConS pat e patl =>
    do (id1, es1, lvar1, eqs1) <- trans_expr nil false e pid;
    do (id2, patls, lvar2, eqs2) <- trans_pattern_list patl id1;
    do hd <- headof es1 (msg "LustreSGen.trans_pattern_list ");
    do pat1 <- cons_patn pat;
    OK (id2, (pat1,hd)::patls, lvar1++lvar2, eqs1++eqs2)
  end

with trans_label_index_list (la_index: label_index_listS) (pid: ident): res (ident* list lindex* params* list stmt) :=
  match la_index with
  | Lnil => OK (pid, nil, nil, nil)
  | LconsLabelS id tl =>
    do (id2, es2, lvar2, eqs2) <- trans_label_index_list tl pid;
    OK (id2, (Label id)::es2, lvar2, eqs2)
  | LconsIndexS e tl =>
    do (id1, es1, lvar1, eqs1) <- trans_expr nil false e pid;
    do (id2, es2, lvar2, eqs2) <- trans_label_index_list tl id1;
    do hd1 <- headof es1 (msg "LustreSGen.trans_label_index_list: es1 null ");
    OK (id2, (Index hd1)::es2, lvar1++lvar2, eqs1++eqs2)
  end

with trans_operator(lv:lhsL)(first: bool)(op: operatorS)(tyl: list typeL)(els: list sexp)(pid: ident) : res (ident* list sexp* params* list stmt) :=
  match op with
  | suboperatorS subop =>
    match subop with
    | Nodehandler nh => (**r Scall: lhs -> calldef -> list sexp -> stmt *)
      let caldef := trans_calldef nh None in
      let '(id2, es, lvar2, lhs2) := cons_calhs first lv tyl pid in
      let eq:= Scall lhs2 caldef els in
      OK (id2, es, lvar2, eq::nil)
    | prefixL_unary op => (**r Scast or Sunop or sexp *)
      do ty <- headof tyl (msg "LustreSGen.trans_expr: ApplyExprS: prefixL_unary");
      do hd <- headof els (msg "LustreSGen.trans_expr: ApplyExprS: prefixL_unary");
      let es := trans_prefix_unary_expr op hd (trans_type ty) in
      if first then
        do eqs <- trans_la_lhs lv (es::nil);
        OK (pid, nil, nil, eqs)
      else
        OK (pid, es::nil, nil, nil)
    | prefixL_binary op => (**r Eprefix: binary_operation -> list sexp -> expr *)
      let mks := (fun x => Sassign x (Eprefix op els)) :: nil in
      do (id2, es2, lvar2,eqs2) <- cons_lhs first lv tyl mks pid;
      OK (id2, es2, lvar2, eqs2)
    end
  | iteratorS highorder subop i =>
    match subop with
    | Nodehandler nh =>
      let caldef := trans_calldef nh (Some i) in
      match highorder with
      | Omap => (**r Hmapcall: lhs -> calldef -> list sexp -> hstmt *)
        let '(id2, es2, lvar2, lhs2) := cons_calhs first lv tyl pid in
        let eq := Sfor true (*bool*) (Hmapcall lhs2 caldef els) i in
	OK (id2, es2, lvar2, eq::nil)
      | Ored | Ofill | Ofillred => (**r Hmapfoldcall: ident*type -> ident*type -> lhs -> calldef -> sexp -> list sexp -> hstmt *)
        let '(id2, es2, lvar2, lhs2) := cons_calhs first lv tyl pid in
        match lhs2,els with
        | hd::tl, hd1::tl1 =>
          let fvar := (id2, snd hd) in
          let eq := Sfor true (Hmapfoldcall hd fvar tl caldef hd1 tl1) i in
          OK (Next_pid id2, es2,lvar2++fvar::nil, eq::nil)
        | _, _ =>  Error (msg "LustreSGen.trans_expr: ApplyExprS: mapfold: call")
        end
      end
    | prefixL_unary op =>
      match highorder with
      | Omap =>
        let '(id2, es2, lvar2, lhs2) := cons_calhs first lv tyl pid in
        do hd1 <- headof lhs2 (msg "LustreSGen.trans_expr: ApplyExprS: iteratorS: map: prefixL_unary: lhs2 null");
        (**r Hmapcast or Hmapunary or Hmappos *)
        do hd <- headof els (msg "LustreSGen.trans_expr: ApplyExprS: iteratorS: map: prefixL_unary: els null");
        let hs := Hmapunary hd1 op hd in
        let eq := Sfor true hs i in
        OK (id2, es2, lvar2, eq::nil)
      | Ored | Ofill | Ofillred => (**r Hfoldunary: ident*type -> unary_operation -> sexp -> hstmt *)
        do hd2 <- headof els (msg "LustreSGen.trans_expr: ApplyExprS: mapfold: prefixL_unary");
        let mks := trans_prefix_unary_fold op hd2 i :: nil in
        do (id2, es2, lvar2, eqs2) <- cons_lhs first lv tyl mks pid;
        OK (id2, es2,lvar2, eqs2)
      end
    | prefixL_binary op =>
      match highorder with
      | Omap =>
        match els with
        | hd2::hd3::_ =>
          do (aty, _) <- typeof_array (typeof hd2);
          match classify_binop aty op with
          | binop_case_typeeq => (**r HHmaptyeq: ident*type -> sexp -> sexp -> hstmt *)
            let mks := (fun x => Sfor true (Hmaptycmp x true hd2 hd3) i) :: nil in
            do (id2, es2, lvar2, eqs2) <- cons_lhs first lv tyl mks pid;
            OK (id2, es2, lvar2, eqs2)
          | binop_case_typene => (**r HHmaptyne: ident*type -> sexp -> sexp -> hstmt *)
            let mks := (fun x => Sfor true (Hmaptycmp x false hd2 hd3) i) :: nil in
            do (id2, es2, lvar2, eqs2) <- cons_lhs first lv tyl mks pid;
            OK (id2, es2, lvar2, eqs2)
          | binop_case_normal => (**r Hmapary: ident*type -> binary_operation -> sexp -> sexp -> hstmt *)
            let mks := (fun x => Sfor true (Hmapary x op hd2 hd3) i) :: nil in
            do (id2, es2, lvar2, eqs2) <- cons_lhs first lv tyl mks pid;
            OK (id2, es2, lvar2, eqs2)
          end
        | _ => Error (msg "LustreSGen.trans_expr: ApplyExprS: iteratorS: map: prefixL_binary")
        end
      | Ored | Ofill | Ofillred =>(**r Hfoldary: ident*type -> binary_operation -> sexp -> sexp -> hstmt *)
        match els with
        | hd2::hd3::_ =>
          let mks := (fun x => Sfor true (Hfoldary x op hd2 hd3) i) :: nil in
          do (id2, es2, lvar2, eqs2) <- cons_lhs first lv tyl mks pid;
          OK (id2, es2,lvar2, eqs2)
        | _ => Error (msg "LustreSGen.trans_expr: ApplyExprS: mapfold: prefixL_binary")
        end
      end
    end
  end.

Definition trans_equation (eq: equationS) (pid: ident): res (ident* params* (list stmt)) :=
  match eq with
  | EquationS lh_list exp =>
    do (id2, es2, lvar2, eqs2) <- trans_expr lh_list true exp pid;
    OK (id2, lvar2, eqs2)
  end.

Fixpoint trans_equation_list (eqs: list equationS) (pid: ident): res (ident*params* (list stmt)) :=
  match eqs with
  | nil => OK (pid, nil, nil)
  | hd::tl =>
    do (id1, lvar1, eqs1) <- trans_equation hd pid;
    do (id2, lvar2, eqs2) <- trans_equation_list tl id1;
    OK (id2, lvar1++lvar2, eqs1++eqs2)
  end.

Definition trans_node (nod: LustreV.nodeS)(pid: ident): res (ident* (ident*LustreS.node)) :=
  match nod with
  | NodeS kind id param rets vl eqs =>
    let params2 := trans_params param in
    let rets2 := trans_params rets in
    let vl2 := trans_params vl in
    do (id1, lvar1, eqs2) <- trans_equation_list eqs pid;
    OK (id1, (id,mknode kind params2 rets2 nil (vl2++lvar1) eqs2 xH Cltypes.Fnil))
  end.

Fixpoint trans_nodes (nodes: list nodeS) (pid: ident): res (list ident * list (ident* node)) :=
  match nodes with
  | nil => OK (nil,nil)
  | hd::tl =>
    do (id,f) <- trans_node hd pid;
    do (idl,fl) <- trans_nodes tl pid;
    OK (id::idl,f::fl)
  end.

(** -min_pid : to compute unused min_id after translating from [LustreV to LustreS] .
  -min_id : [id_max] in [id::idl] which have been used. *)

Fixpoint min_pid (id : ident)(idl: list ident) : ident :=
  match idl with
  | nil => id
  | hd :: tl => if Zle_bool (Zpos id) (Zpos hd) then (min_pid hd tl) else (min_pid id tl)
  end.

Definition trans_program (pid:ident)(p: programS) : res (ident*LustreS.program) :=
  let type_block1 := trans_type_blocks p.(type_blockS) in
  do const_block1 <- translate_const_id p.(const_blockS) nil;
  do const_block2 <- mmap trans_const_decl const_block1;
  do (idl,idnodelist) <- trans_nodes p.(node_blockS) pid;
  let pid := min_pid pid idl in
  OK (pid,Lustre.mkprogram type_block1 nil const_block2 idnodelist p.(node_mainS)).


Scheme exprs_ind2 :=
  Induction for exprS Sort Prop
with expr_lists_ind2 :=
  Induction for expr_listS Sort Prop
with pattern_lists_ind2 :=
  Induction for pattern_listS Sort Prop
with label_index_list_ind2 :=
  Induction for label_index_listS Sort Prop
with operator_ind2 :=
  Induction for operatorS Sort Prop.

Scheme exprs_ind3 := Minimality for exprS Sort Prop
  with expr_lists_ind3 := Minimality for expr_listS Sort Prop
  with pattern_lists_ind3 := Minimality for pattern_listS Sort Prop
  with label_lindex_lists_ind3 := Minimality for label_index_listS Sort Prop
  with operator_ind3 := Minimality for operatorS Sort Prop.

Definition vars_norepet(p: params)(pid id1: ident) :=
  list_norepet (map fst p) /\ Ple pid id1 /\
    (forall id : ident, In id (map fst p) -> Ple pid id /\ Plt id id1).

Lemma vars_norepet_app:
  forall (p p0: params) pid id1 id2,
  vars_norepet p pid id1 ->
  vars_norepet p0 id1 id2 ->
  vars_norepet (p++p0) pid id2.
Proof.
  unfold vars_norepet. intuition.
  +rewrite map_app. apply list_norepet_app.
   repeat (split; auto). red; intros.
   destruct H4 with x; auto. destruct H5 with y; auto.
   red; intros; subst. unfold Plt, Ple in *. omega.
  +unfold Ple in *. omega.
  +rewrite map_app in H3. apply in_app_or in H3.
   destruct H3.
   destruct H4 with id; auto.
   destruct H5 with id; auto. unfold Ple, Plt in *. omega.
  +rewrite map_app in H3. apply in_app_or in H3.
   destruct H3.
   destruct H4 with id; auto. unfold Ple, Plt in *. omega.
   destruct H5 with id; auto.
Qed.

Lemma vars_norepet_nil:
  forall id1, vars_norepet nil id1 id1.
Proof.
  unfold vars_norepet. intros. split; [|split].
   constructor. apply Ple_refl. intros. tauto.
Qed.

Lemma vars_norepet_cons:
  forall p pid id1 ty,
  vars_norepet p (Next_pid pid) id1 ->
  vars_norepet ((pid, ty) :: p) pid id1.
Proof.
  unfold vars_norepet. intros.
  destruct H as [? [? ?]]. split; [| split].
  +simpl. constructor; auto.
   red; intros. destruct H1 with pid; auto.
   unfold Ple,Plt,Next_pid in *.
   rewrite Psucc_Zsucc in H3. omega.
  +unfold Ple,Plt,Next_pid in *.
   rewrite Psucc_Zsucc in *. omega.
  +simpl in *. intros. destruct H2; subst.
   -unfold Ple,Plt,Next_pid in *.
    rewrite Psucc_Zsucc in *. omega.
   -destruct H1 with id; auto.
    unfold Ple,Plt,Next_pid in *.
    rewrite Psucc_Zsucc in *. omega.
Qed.

Lemma construct_lhs_vars_norepet:
  forall tyl pid id1 es1 lvar1,
  construct_lhs tyl pid = (id1, es1, lvar1) ->
  vars_norepet lvar1 pid id1.
Proof.
  induction tyl; simpl; intros.
  +inv H. simpl. apply vars_norepet_nil.
  +destruct (construct_lhs _ _) eqn:?; try (inv H; fail).
   destruct p. inv H.
   apply IHtyl in Heqp.
   eapply vars_norepet_cons; eauto.
Qed.

Lemma cons_lhs_vars_norepet:
  forall k lv tyl mks pid id1 es1 lvar1 eqs1,
  cons_lhs k lv tyl mks pid = OK (id1,es1,lvar1,eqs1) ->
  vars_norepet lvar1 pid id1.
Proof.
  unfold cons_lhs. destruct k; intros.
  +monadInv H. apply vars_norepet_nil.
  +destruct (construct_lhs _ _) eqn:?; try (inv H; fail).
   destruct p. monadInv H.
   eapply construct_lhs_vars_norepet; eauto.
Qed.

Lemma cons_calhs_vars_norepet:
  forall k lv tyl pid id1 es1 lvar1 eqs1,
  cons_calhs k lv tyl pid = (id1,es1,lvar1,eqs1) ->
  vars_norepet lvar1 pid id1.
Proof.
  unfold cons_calhs. destruct k; intros.
  +inv H. eapply vars_norepet_nil; eauto.
  +destruct (construct_lhs _ _) eqn:?.
   destruct p. inv H.
   eapply construct_lhs_vars_norepet; eauto.
Qed.

Lemma cons_type_init_vars_norepet:
  forall ty pid id1 es1 lvar1 eqs1,
  cons_type_init ty pid = (id1,es1,lvar1,eqs1) ->
  vars_norepet lvar1 pid id1
with cons_fld_init_vars_norepet:
  forall f pid id1 es1 lvar1 eqs1,
  cons_fld_init f pid = (id1,es1,lvar1,eqs1) ->
  vars_norepet lvar1 pid id1.
Proof.
 +induction ty; simpl; intros; inv H;
  try apply vars_norepet_nil.
  -destruct (cons_type_init _ _) eqn:?.
   destruct p as [[]]. inv H1.
   eapply vars_norepet_app; eauto.
   eapply vars_norepet_cons; eauto.
   apply vars_norepet_nil.
  -destruct (cons_fld_init _ _) eqn:?.
   destruct p as [[]]. inv H1.
   eapply vars_norepet_app; eauto.
   eapply vars_norepet_cons; eauto.
   apply vars_norepet_nil.
 +induction f; simpl; intros; inv H.
  -apply vars_norepet_nil.
  -destruct (cons_type_init _ _) eqn:?.
   destruct p as [[]].
   destruct (cons_fld_init _ _) eqn:?.
   destruct p0 as [[]]. inv H1.
   eapply vars_norepet_app; eauto.
Qed.

Lemma cons_type_inits_vars_norepet:
  forall tyl pid id1 es1 lvar1 eqs1,
  cons_type_inits tyl pid = (id1,es1,lvar1,eqs1) ->
  vars_norepet lvar1 pid id1.
Proof.
  induction tyl; simpl; intros.
  +inv H. apply vars_norepet_nil.
  +destruct (cons_type_init _ _) eqn:?.
   destruct p as [[]].
   destruct (cons_type_inits _ _) eqn:?.
   destruct p0 as [[]]. inv H.
   eapply cons_type_init_vars_norepet in Heqp; eauto.
   eapply vars_norepet_app; eauto.
Qed.

Lemma trans_expr_vars_norepet:
  forall e k l pid id1 e1 lvar1 eqs1,
  trans_expr l k e pid = OK (id1, e1, lvar1, eqs1) ->
  vars_norepet lvar1 pid id1.
Proof.
  induction e using exprs_ind2 with
  (P0 := fun es  =>
   forall pid id1 es1 lvar1 eqs1,
   trans_expr_list es pid = OK (id1, es1, lvar1, eqs1) ->
   vars_norepet lvar1 pid id1)
  (P1 := fun pl =>
   forall pid id1 es1 lvar1 eqs1,
   trans_pattern_list pl pid = OK (id1, es1, lvar1, eqs1) ->
   vars_norepet lvar1 pid id1)
  (P2 := fun l =>
   forall pid id1 es1 lvar1 eqs1,
   trans_label_index_list l pid = OK (id1, es1, lvar1, eqs1) ->
   vars_norepet lvar1 pid id1)
  (P3 := fun op =>
   forall lv k tyl els pid id1 es1 lvar1 eqs1,
   trans_operator lv k op tyl els pid = OK (id1, es1, lvar1, eqs1) ->
   vars_norepet lvar1 pid id1
   ); simpl; intros.
 +destruct k; monadInv H; apply vars_norepet_nil.
 +destruct k; monadInv H; apply vars_norepet_nil.
 +destruct (trans_expr_list e pid) eqn:?; try (inv H; fail).
   destruct p as [[[]]]. simpl in *.
   eapply IHe in Heqr; eauto.
   destruct k; monadInv H; auto.
 +destruct (trans_expr_list e pid) eqn:?; try (inv H; fail).
  destruct p as [[[]]]. simpl in *.
  eapply IHe0 in Heqr; eauto.
  destruct (trans_operator _ _ _ _ _ _) eqn:?; try (inv H; fail).
  destruct p0 as [[[]]]. simpl in *. inv H.
  eapply IHe in Heqr0; eauto.
  eapply vars_norepet_app; eauto.
 +destruct (trans_expr_list _ _) eqn:?; try (inv H; fail).
  destruct p0 as [[[]]]. simpl in *. monadInv H.
  destruct (cons_lhs _ _ _ _ _) eqn:?; try (inv EQ0; fail).
  destruct p1 as [[[]]]. inv EQ0.
  apply cons_lhs_vars_norepet in Heqr0.
  eapply vars_norepet_app; eauto.
 +destruct (trans_expr _ _ _ _) eqn:?; try (inv H; fail).
  destruct p0 as [[[]]]. simpl in *.
  monadInv H. destruct k; monadInv EQ0; eauto.
 +destruct (trans_expr _ _ _ _) eqn:?; try (inv H; fail).
  destruct p as [[[]]]. simpl in *.
  monadInv H. destruct (cons_lhs _ _ _ _ _) eqn:?; try (inv EQ0; fail).
  destruct p0 as [[[]]]. inv EQ0.
  apply cons_lhs_vars_norepet in Heqr0.
  eapply vars_norepet_app; eauto.
 +destruct (trans_expr_list _ _) eqn:?; try (inv H; fail).
  destruct p0 as [[[]]]. simpl in *.
  destruct (cons_lhs _ _ _ _ _) eqn:?; try (inv H; fail).
  destruct p1 as [[[]]]. inv H.
  apply cons_lhs_vars_norepet in Heqr0.
  eapply vars_norepet_app; eauto.
 +destruct (trans_expr _ _ _ _) eqn:?; try (inv H; fail).
  destruct p0 as [[[]]]. simpl in *.
  destruct (trans_expr_list _ _) eqn:?; try (inv H; fail).
  destruct p1 as [[[]]]. simpl in *.
  destruct (trans_expr _ _ _ i0) eqn:?; try (inv H; fail).
  destruct p2 as [[[]]]. simpl in *.
  monadInv H. destruct (cons_lhs _ _ _ _ _) eqn:?; try (inv EQ2; fail).
  destruct p3 as [[[]]]. inv EQ2.
  apply cons_lhs_vars_norepet in Heqr2.
  eapply vars_norepet_app; eauto.
  eapply vars_norepet_app; eauto.
  eapply vars_norepet_app; eauto.
 +destruct (trans_expr _ _ _ _) eqn:?; try (inv H; fail).
  destruct p0 as [[[]]]. simpl in *. monadInv H.
  destruct (Int.lt _ _); try congruence.
  destruct (cons_lhs _ _ _ _ _) eqn:?; try (inv EQ0; fail).
  destruct p1 as [[[]]]. inv EQ0.
  apply cons_lhs_vars_norepet in Heqr0.
  eapply vars_norepet_app; eauto.
 +destruct (trans_expr _ _ _ _) eqn:?; try (inv H; fail).
  destruct p0 as [[[]]]. simpl in *.
  destruct (trans_label_index_list _ _) eqn:?; try (inv H; fail).
  destruct p1 as [[[]]]. simpl in *.
  destruct (trans_expr _ _ _ i0) eqn:?; try (inv H; fail).
  destruct p2 as [[[]]]. simpl in *.
  monadInv H. destruct (cons_lhs _ _ _ _ _) eqn:?; try (inv EQ2; fail).
  destruct p3 as [[[]]]. inv EQ2.
  apply cons_lhs_vars_norepet in Heqr2.
  eapply vars_norepet_app; eauto.
  eapply vars_norepet_app; eauto.
  eapply vars_norepet_app; eauto.
 +destruct (trans_expr _ _ _ _) eqn:?; try (inv H; fail).
  destruct p0 as [[[]]]. simpl in *. monadInv H.
  destruct k; monadInv EQ0; eauto.
 +destruct (trans_expr _ _ _ _) eqn:?; try (inv H; fail).
  destruct p0 as [[[]]]. simpl in *.
  destruct (trans_expr _ _ _ i) eqn:?; try (inv H; fail).
  destruct p1 as [[[]]]. simpl in *.
  monadInv H. destruct (classify_binop _ _).
  -destruct k; monadInv EQ2; eapply vars_norepet_app; eauto.
  -destruct (cons_lhs _ _ _ _ _) eqn:?; try (inv EQ2; fail).
   destruct p2 as [[[]]]. simpl in *. inv EQ2.
   apply cons_lhs_vars_norepet in Heqr1.
   eapply vars_norepet_app; eauto.
   eapply vars_norepet_app; eauto.
  -destruct (cons_lhs _ _ _ _ _) eqn:?; try (inv EQ2; fail).
   destruct p2 as [[[]]]. simpl in *. inv EQ2.
   apply cons_lhs_vars_norepet in Heqr1.
   eapply vars_norepet_app; eauto.
   eapply vars_norepet_app; eauto.
 +destruct (trans_expr _ _ _ _) eqn:?; try (inv H; fail).
  destruct p0 as [[[]]]. simpl in *.
  monadInv H. destruct k; monadInv EQ0; eauto.
 +destruct (trans_expr _ _ _ _) eqn:?; try (inv H; fail).
  destruct p as [[[]]]. simpl in *.
  destruct (cons_type_inits _ _) eqn:?; try (inv H; fail).
  destruct p0 as [[]]. monadInv H.
  destruct (cons_lhs _ _ _ _ _) eqn:?; try (inv EQ0; fail).
  destruct p1 as [[[]]]. inv EQ0.
  apply cons_lhs_vars_norepet in Heqr0.
  eapply vars_norepet_app; eauto.
  eapply vars_norepet_app; eauto.
  eapply cons_type_inits_vars_norepet; eauto.
 +destruct (trans_expr_list _ _) eqn:?; try (inv H; fail).
  destruct p as [[[]]]. simpl in *.
  destruct (trans_expr_list _ i0) eqn:?; try (inv H; fail).
  destruct p0 as [[[]]]. simpl in *.
  monadInv H.
  destruct (cons_lhs _ _ _ _ _) eqn:?; try (inv EQ0; fail).
  destruct p1 as [[[]]]. inv EQ0.
  apply cons_lhs_vars_norepet in Heqr1.
  eapply vars_norepet_app; eauto.
  eapply vars_norepet_app; eauto.
 +destruct (trans_expr _ _ _ _) eqn:?; try (inv H; fail).
  destruct p as [[[]]]. simpl in *.
  destruct (trans_expr _ _ _ i) eqn:?; try (inv H; fail).
  destruct p0 as [[[]]]. simpl in *.
  monadInv H.
  destruct (cons_lhs _ _ _ _ _) eqn:?; try (inv EQ0; fail).
  destruct p1 as [[[]]]. inv EQ0.
  apply cons_lhs_vars_norepet in Heqr1.
  eapply vars_norepet_app; eauto.
  eapply vars_norepet_app; eauto.
 +monadInv H.
 +monadInv H.
 +destruct (trans_expr _ _ _ _) eqn:?; try (inv H; fail).
  destruct p as [[[]]]. simpl in *.
  destruct (trans_expr _ _ _ i) eqn:?; try (inv H; fail).
  destruct p0 as [[[]]]. simpl in *.
  destruct (trans_expr _ _ _ i0) eqn:?; try (inv H; fail).
  destruct p1 as [[[]]]. simpl in *.
  monadInv H.
  destruct (cons_lhs _ _ _ _ _) eqn:?; try (inv EQ2; fail).
  destruct p2 as [[[]]]. inv EQ2.
  apply cons_lhs_vars_norepet in Heqr2.
  eapply vars_norepet_app; eauto.
  eapply vars_norepet_app; eauto.
  eapply vars_norepet_app; eauto.
 +destruct (trans_expr _ _ _ _) eqn:?; try (inv H; fail).
  destruct p0 as [[[]]]. simpl in *.
  destruct (trans_pattern_list _ _) eqn:?; try (inv H; fail).
  destruct p1 as [[[]]]. simpl in *.
  monadInv H.
  destruct (cons_lhs _ _ _ _ _) eqn:?; try (inv EQ0; fail).
  destruct p2 as [[[]]]. inv EQ0.
  apply cons_lhs_vars_norepet in Heqr1.
  eapply vars_norepet_app; eauto.
  eapply vars_norepet_app; eauto.
 +destruct p. monadInv H.
  destruct (trans_expr _ _ _ _) eqn:?; try (inv EQ0; fail).
  destruct p as [[[]]]. simpl in *.
  monadInv EQ0. destruct k.
  -monadInv EQ2.
   eapply vars_norepet_app; eauto.
   eapply vars_norepet_cons; eauto.
   apply vars_norepet_nil.
  -inv EQ2. eapply vars_norepet_app; eauto.
   eapply vars_norepet_cons; eauto.
   apply vars_norepet_nil.
 +destruct p. monadInv H.
  destruct (trans_expr _ _ _ _) eqn:?; try (inv EQ0; fail).
  destruct p as [[[]]]. simpl in *.
  monadInv EQ0. destruct k.
  -monadInv EQ2.
   eapply vars_norepet_app; eauto.
   eapply vars_norepet_cons; eauto.
   apply vars_norepet_nil.
  -inv EQ2. eapply vars_norepet_app; eauto.
   eapply vars_norepet_cons; eauto.
   apply vars_norepet_nil.
 +destruct p. monadInv H.
  destruct (trans_expr _ _ _ _) eqn:?; try (inv EQ0; fail).
  destruct p as [[[]]]. simpl in *.
  monadInv EQ0. destruct k.
  -monadInv EQ2.
   eapply vars_norepet_app; eauto.
   eapply vars_norepet_cons; eauto.
   apply vars_norepet_nil.
  -inv EQ2. eapply vars_norepet_app; eauto.
   eapply vars_norepet_cons; eauto.
   apply vars_norepet_nil.
 +inv H. apply vars_norepet_nil.
 +destruct (trans_expr _ _ _ _) eqn:?; try (inv H; fail).
  destruct p as [[[]]]. simpl in *.
  destruct (trans_expr_list _ _) eqn:?; try (inv H; fail).
  destruct p0 as [[[]]]. simpl in *. inv H.
  eapply vars_norepet_app; eauto.
 +inv H. apply vars_norepet_nil.
 +destruct (trans_expr _ _ _ _) eqn:?; try (inv H; fail).
  destruct p1 as [[[]]]. simpl in *.
  destruct (trans_pattern_list _ _) eqn:?; try (inv H; fail).
  destruct p2 as [[[]]]. simpl in *.
  monadInv H.
  eapply vars_norepet_app; eauto.
 +inv H. apply vars_norepet_nil.
 +destruct (trans_label_index_list _ _) eqn:?; try (inv H; fail).
  destruct p as [[[]]]. simpl in *. inv H.
  eapply IHe; eauto.
 +destruct (trans_expr _ _ _ _) eqn:?; try (inv H; fail).
  destruct p as [[[]]]. simpl in *.
  destruct (trans_label_index_list _ _) eqn:?; try (inv H; fail).
  destruct p0 as [[[]]]. simpl in *.
  monadInv H. eapply vars_norepet_app; eauto.
 +destruct s; try congruence.
  -destruct (cons_calhs _ _ _ _) eqn:?.
   destruct p as [[]]. inv H.
   eapply cons_calhs_vars_norepet; eauto.
  -monadInv H. destruct k; monadInv EQ2; apply vars_norepet_nil.
  -destruct (cons_lhs _ _ _ _ _) eqn:?; try (inv H; fail).
   destruct p as [[[]]]. simpl in *. inv H.
   eapply cons_lhs_vars_norepet; eauto.
 +destruct i, s; try congruence.
  -destruct (cons_calhs _ _ _ _) eqn:?.
   destruct p as [[]]. inv H.
   eapply cons_calhs_vars_norepet; eauto.
  -destruct (cons_calhs _ _ _ _) eqn:?.
   destruct p as [[]]. monadInv H.
   eapply cons_calhs_vars_norepet; eauto.
  -destruct els; try congruence. destruct els; try congruence.
    monadInv H.
    destruct (classify_binop _ _);
    destruct (cons_lhs _ _ _ _ _) eqn:?; try (inv EQ0; fail);
    destruct p as [[[]]]; inv EQ0;
    eapply cons_lhs_vars_norepet; eauto.
  -destruct (cons_calhs _ _ _ _) eqn:?.
   destruct p as [[]].
   destruct l, els; try congruence. inv H.
   eapply cons_calhs_vars_norepet in Heqp; eauto.
   eapply vars_norepet_app; eauto.
   eapply vars_norepet_cons; eauto.
   apply vars_norepet_nil.
  -monadInv H.
   destruct (cons_lhs _ _ _ _ _) eqn:?; try (inv EQ0; fail).
   destruct p as [[[]]]. simpl in *. inv EQ0.
   eapply cons_lhs_vars_norepet; eauto.
  -destruct els;try congruence. destruct els; try congruence.
   destruct (cons_lhs _ _ _ _ _) eqn:?; try (inv H; fail).
   destruct p as [[[]]]. simpl in *. inv H.
   eapply cons_lhs_vars_norepet; eauto.
  -destruct (cons_calhs _ _ _ _) eqn:?.
   destruct p as [[]].
   destruct l, els; inv H.
   apply vars_norepet_app with i; auto.
   eapply cons_calhs_vars_norepet; eauto.
   eapply vars_norepet_cons; eauto.
   apply vars_norepet_nil.
  -monadInv H. destruct (cons_lhs _ _ _ _ _) eqn:?; try (inv EQ0; fail).
   destruct p as [[[]]]. simpl in *. inv EQ0.
   eapply cons_lhs_vars_norepet; eauto.
  -destruct els;try congruence. destruct els; try congruence.
   destruct (cons_lhs _ _ _ _ _) eqn:?; try (inv H; fail).
   destruct p as [[[]]]. simpl in *. inv H.
   eapply cons_lhs_vars_norepet; eauto.
  -destruct (cons_calhs _ _ _ _) eqn:?.
   destruct p as [[]].
   destruct l, els; inv H.
   apply vars_norepet_app with i; auto.
   eapply cons_calhs_vars_norepet; eauto.
   eapply vars_norepet_cons; eauto.
   apply vars_norepet_nil.
  -monadInv H. destruct (cons_lhs _ _ _ _ _) eqn:?; try (inv EQ0; fail).
   destruct p as [[[]]]. simpl in *. inv EQ0.
   eapply cons_lhs_vars_norepet; eauto.
  -destruct els;try congruence. destruct els; try congruence.
   destruct (cons_lhs _ _ _ _ _) eqn:?; try (inv H; fail).
   destruct p as [[[]]]. simpl in *. inv H.
   eapply cons_lhs_vars_norepet; eauto.
Qed.

Lemma trans_equation_vars_norepet:
  forall eq pid id1 lvar1 eqs1,
  trans_equation eq pid = OK (id1, lvar1, eqs1) ->
  list_norepet (map fst lvar1)
    /\ Ple pid id1
    /\ (forall id, In id (map fst lvar1) -> Ple pid id /\ Plt id id1).
Proof.
  destruct eq. simpl. intros.
  destruct (trans_expr l true e pid) eqn:?; try (inv H; fail).
  destruct p as [[[]]]. inv H.
  eapply trans_expr_vars_norepet; eauto.
Qed.

Lemma trans_equation_list_vars_norepet:
  forall eqs pid id1 lvar1 eqs1,
  trans_equation_list eqs pid = OK (id1, lvar1, eqs1) ->
  list_norepet (map fst lvar1)
    /\ Ple pid id1
    /\ (forall id, In id (map fst lvar1) -> Ple pid id /\ Plt id id1).
Proof.
  induction eqs; simpl; intros.
  +inv H. simpl. split; [| split].
   constructor.
   apply Ple_refl.
   intros. tauto.
  +destruct (trans_equation a pid) eqn:?; try (inv H; fail).
   destruct p as [[]]. inv H.
   destruct (trans_equation_list eqs i) eqn:?; try (inv H1; fail).
   destruct p0 as [[]]. inv H1.
   eapply trans_equation_vars_norepet in Heqr; eauto.
   eapply IHeqs in Heqr0; eauto.
   rewrite map_app.  intuition.
   -apply list_norepet_app. intuition.
    red; intros. apply H4 in H2. apply H5 in H6.
    unfold Plt,Ple in *.
    red; intros; subst; omega.
   -unfold Ple in *. omega.
   -apply in_app_or in H2. destruct H2.
    *apply H4 in H2. unfold Plt,Ple in *. omega.
    *apply H5 in H2. unfold Plt,Ple in *. omega.
   -apply in_app_or in H2. destruct H2.
    *apply H4 in H2. unfold Plt,Ple in *. omega.
    *apply H5 in H2. unfold Plt,Ple in *. omega.
Qed.
