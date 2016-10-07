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
Require Import Integers.
Require Import Floats.
Require Import AST.
Require Import Lop.
Require Import Lustre.
Require Import LustreS.

Definition null_id := 1%positive.

(** * Abstract syntax shared by LustreV *)


(** Part1 : Types *)

(** Types include short (signed 16 bits), ushort (unsigned 16 bits),int(signed 32 bits),
  uint(unsigned 32 bits), float (32 bits), real (64 bits), bool(true or false), char,
  array, struct and enum. *)

(** The syntax of type expressions.  Some points to note:
  - struct type, e.g type s1 = { n : int, m : real } is expressed by syntax as below:
<<
       Tstruct "s1" (Fcons "n" (Tint)
                    (Fcons "m" (Treal)
                    Fnil))
>>
  - no recursive type, e.g type s = { m : s } is not allowed, although it canbe expressed by syntax. *)

Inductive typeL : Type :=
  | Tshort : typeL                          (**r integer types, signed 16 bits *)
  | Tushort : typeL                         (**r integer types, unsigned 16 bits  *)
  | Tint : typeL                            (**r integer types, signed 32 bits *)
  | Tuint : typeL                           (**r integer types, unsigned 32 bits *)
  | Tfloat : typeL                          (**r floating-point types, 32 bits *)
  | Treal : typeL                           (**r floating-point types, 64 bits *)
  | Tbool : typeL                           (**r bool types *)
  | Tchar : typeL                           (**r char types *)
  | Tarray : ident -> typeL -> Z -> typeL   (**r array types: array_type_id(ty^len) *)
  | Tstruct : ident -> fieldlistL -> typeL  (**r struct types: struct_type_id {label1_id: type1; ...} *)
  | Tenum : ident -> list ident -> typeL    (**r enum types: enum_type_id {value1_id, ...} *)

with fieldlistL : Type :=
  | Fnil : fieldlistL
  | Fcons : ident -> typeL -> fieldlistL -> fieldlistL.

Lemma type_eqL: forall (ty1 ty2: typeL), {ty1=ty2} + {ty1<>ty2}
with fieldlist_eqL: forall (fld1 fld2: fieldlistL), {fld1=fld2} + {fld1<>fld2}.
Proof.
  repeat (decide equality).
  generalize ident_eq zeq. intros E1 E2.
  decide equality.
Defined.

Opaque type_eqL fieldlist_eqL.


(** Part3 : Global Declares
- const_block
<<
       Const block consisting of all character constants
>>*)

Inductive constL : Type := (* Only for const block*)
  | ShortConstL: int -> constL
  | UshortConstL: int -> constL
  | IntConstL: int -> constL
  | UintConstL: int -> constL
  | CharConstL: int -> constL
  | FloatConstL: float32 -> constL
  | RealConstL: float -> constL
  | BoolConstL: bool -> constL
  | ConstructConstL : const_listL -> constL     (* E.g struct {label1 : 1, label2 : 2}, or array [1, 2] *)
  | EnumConstL : ident -> typeL -> constL       (* to be fixed : typeL to be deled --redundancy *)
  | ID : ident -> typeL -> constL               (* to define other constant by character constant *)

with const_listL : Type :=
  | ConstNilL : const_listL
  | ConstConL : constL -> const_listL -> const_listL.

Record const_declL : Type :=
  | ConstDeclL : ident -> typeL -> constL -> const_declL.

Record var_declL : Type :=
  | VarDeclL : ident -> typeL -> clock -> var_declL
  | ClockVarDeclL : ident -> typeL -> clock -> var_declL.

Definition id_of_var_declL (v: var_declL) : ident :=
  match v with
  | VarDeclL id _ _ => id
  | ClockVarDeclL id _ _ => id
  end.

(** - Output parameters, Input parameters, and local variables*)

Definition paramsL := list var_declL.

(** Part6 : Lvalues of Equations *)

Record lhs_idL : Type :=
  | LhsID: ident -> typeL -> clock -> lhs_idL.

Definition lhsL := list lhs_idL.

(** Part7 : Rvalues of Equations - Expressions
- Arithmetic and logical operators *)

(** - Operators used for operator parameter of higher order operators *)

Record nodehandlerL: Type :=
  | NodehandlerL:  ident -> list typeL -> list typeL -> bool -> ident -> nodehandlerL.

Inductive suboperatorL : Type :=
  | Nodehandler : nodehandlerL -> suboperatorL
  | prefixL_unary : unary_operationL -> suboperatorL
  | prefixL_binary : binary_operationL -> suboperatorL.

(** - Iterator *)

Inductive iterator_operationL : Type :=
  | Omap : iterator_operationL          (**r or map <suboperatorL> <<INTEGER>> *)
  | Ored: iterator_operationL
  | Ofill: iterator_operationL
  | Ofillred: iterator_operationL.

(** - Pattern of case expr *)

Record patternL : Type :=
  | PatternID : ident -> typeL -> patternL
  | PatternChar : int -> patternL
  | PatternInt : int -> typeL-> patternL
  | PatternBool : bool -> patternL
  | PatternAny : patternL.

(** * LustreStar Syntax *)

(** Part1 : Expressions of LustreStar
- All expressions are annotated with their types and clocks. *)

Inductive exprS : Type :=
  | EconstS : const -> typeL -> clock -> exprS
  | EvarS : ident -> typeL -> clock -> exprS
  | ListExprS : expr_listS -> exprS                                           (* list expression *)
  | ApplyExprS : operatorS -> expr_listS -> list (typeL * clock) -> exprS 	                           (* operator application *)
  | EconstructS : expr_listS -> (typeL * clock) -> exprS                                         (* construct a struct, e.g {label1 : 3, label2 : false} *)
  | EarrayaccS : exprS -> int -> (typeL * clock) -> exprS                                        (* expr[i], access to (i+1)th member of an array "expr" *)
  | EarraydefS :  exprS -> int -> list (typeL * clock) -> exprS                                       (* expr ^ i, an array of size "i" with every element "expr" *)
  | EarraydiffS : expr_listS -> (typeL * clock) -> exprS                                         (* [list expression], build an array with elements "list expression", e.g [1,2]*)
  | EarrayprojS: exprS -> expr_listS -> exprS -> (typeL * clock) -> exprS                        (* dynamic projection, e.g (2^3^4.[7] default 100^3), value is 100^3 *)
  | EarraysliceS : exprS -> int -> int -> (typeL * clock) -> exprS                               (* a [i..j] is the sliced array [a_i, a_i+1, ... , a_j]*)
  | EmixS : exprS -> label_index_listS -> exprS -> (typeL * clock) -> exprS                      (* construct a new array or struct, e.g {label1:2^3} with label1.[0] = 7, value is {label1:[7,2]} *)
  | EunopS : unary_operationL -> exprS -> (typeL * clock) -> exprS                               (* unary operation *)
  | EbinopS : binary_operationL -> exprS -> exprS -> (typeL * clock) -> exprS                    (* binary operation *)
  | EfieldS : exprS -> ident -> (typeL * clock) -> exprS                                         (* access to a member of a struct *)
  | EpreS : list ident -> exprS -> list (typeL * clock) -> exprS                                      (* pre : shift flows on the last instant backward, producing an undefined value at first instant*)
  | EfbyS : list (typeL * ident) -> expr_listS -> int -> expr_listS -> list (typeL * clock) -> exprS  (* fby : fby(b; n; a) = a -> pre fby(b; n-1; a) *)
  | EarrowS : exprS -> exprS -> list (typeL * clock) -> exprS                                         (* -> : fix the inital value of flows*)
  | EwhenS : exprS -> clock -> list (typeL * clock) -> exprS                                         (* x when h: if h=false, then no value; otherwise x *)
  | EcurrentS: exprS ->  list (typeL * clock) -> exprS
  | EifS : exprS -> exprS -> exprS -> list (typeL * clock) -> exprS                                   (* conditional*)
  | EcaseS : exprS -> pattern_listS -> list (typeL * clock) -> exprS                                  (* case *)
  | EboolredS: int -> int -> exprS -> (typeL * clock) -> exprS
  | EdieseS: exprS -> (typeL * clock) -> exprS  (* #(a1, ..., an) -> boolred(0,1,n)[a1, ..., an] *)
  | EnorS: exprS -> (typeL * clock) -> exprS  (* nor(a1, ..., an) boolred(0,0,n)[a1, ..., an] *)

with expr_listS : Type :=
  | Enil: expr_listS
  | Econs: exprS -> expr_listS -> expr_listS

with label_index_listS: Type :=
  | Lnil: label_index_listS
  | LconsLabelS: ident -> label_index_listS -> label_index_listS
  | LconsIndexS: exprS -> label_index_listS -> label_index_listS

with pattern_listS : Type :=
  | PatternNilS : pattern_listS
  | PatternConS : patternL -> exprS -> pattern_listS -> pattern_listS

with operatorS : Type :=
  | suboperatorS : suboperatorL -> operatorS
  | iteratorS : iterator_operationL -> suboperatorL -> int -> operatorS.

Fixpoint typeclock_of (e: exprS) : list (typeL * clock) :=
  match e with
  | EconstS _ t c => (t,c)::nil
  | EvarS _ t c => (t,c)::nil
  | ListExprS l => typeclocks_of l
  | ApplyExprS _ _ tcl => tcl
  | EconstructS _ tc => tc::nil
  | EarrayaccS _ _ tc => tc::nil
  | EarraydefS _ _ tcl => tcl
  | EarraydiffS _ tc => tc::nil
  | EarrayprojS _ _ _ tc => tc::nil
  | EarraysliceS _ _ _ tc => tc::nil
  | EmixS _ _ _ tc => tc::nil
  | EunopS _ _ tc => tc::nil
  | EbinopS _ _ _ tc => tc::nil
  | EfieldS _  _ tc => tc::nil
  | EpreS _ _ tcl => tcl
  | EfbyS _ _ _ _ tcl => tcl
  | EarrowS _ _ tcl => tcl
  | EwhenS _ _ tcl => tcl
  | EcurrentS _ tcl => tcl
  | EifS _ _ _ tcl => tcl
  | EcaseS _ _ tcl => tcl
  | EboolredS _ _ _ tc => tc:: nil
  | EdieseS _ tc => tc:: nil
  | EnorS _ tc => tc :: nil
  end

with typeclocks_of (e: expr_listS) : list (typeL * clock) :=
  match e with
  | Enil => nil
  | Econs e etl => app (typeclock_of e) (typeclocks_of etl)
  end.

(** Part2 : Equations of LustreStar *)

Inductive equationS : Type :=
  | EquationS: lhsL -> exprS -> equationS.

(** Part3 : Node of LustreStar

- Node : kind -> ID -> parameters -> returns -> locals -> body **)

Record nodeS : Type :=
  | NodeS : bool -> ident -> paramsL -> paramsL -> paramsL -> list equationS -> nodeS.

(** Part4 : ProgramS *)

Inductive programS : Type := mkprogramS{
  type_blockS : list (ident*typeL);
  const_blockS : list const_declL;
  node_blockS : list nodeS;
  node_mainS : ident
}.
