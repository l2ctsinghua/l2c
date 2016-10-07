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

open Printf
open Format
open Camlcoq
open Datatypes
open AST
open Cop
open Lop
open Ctypes
open Cltypes
open Ltypes
open Lustre

let name_unop = function
  | Onotbool -> "!"
  | Onotint  -> "~"
  | Oneg     -> "-"
  | Oabsfloat -> "__builtin_fabs"

let name_binop = function
  | Oadd -> "+"
  | Osub -> "-"
  | Omul -> "*"
  | Odivint | Odivreal -> "/"
  | Omod -> "%"
  | Oand -> "&"
  | Oor  -> "|"
  | Oxor -> "^"
  | Oeq  -> "=="
  | One  -> "!="
  | Olt  -> "<"
  | Ogt  -> ">"
  | Ole  -> "<="
  | Oge  -> ">="


let name_inttype sz sg =
  match sz, sg with
  | I8, Signed -> "signed char"
  | I8, Unsigned -> "unsigned char"
  | I16, Signed -> "short"
  | I16, Unsigned -> "unsigned short"
  | I32, Signed -> "int"
  | I32, Unsigned -> "unsigned int"
  | IBool, _ -> "_Bool"

let name_floattype sz =
  match sz with
  | F32 -> "float"
  | F64 -> "double"

let name_longtype sg =
  match sg with
  | Signed -> "long long"
  | Unsigned -> "unsigned long long"

let name_optid id =
  if id = "" then "" else " " ^ id

let rec name_ldecl id ty =
  match ty with
  | Tint(sz, sg) ->
      name_inttype sz sg ^ name_optid id
  | Tfloat(sz) ->
      name_floattype sz ^ name_optid id
  | Tarray(_,t, n) ->
      name_ldecl (sprintf "%s[%ld]" id (camlint_of_coqint n)) t
  | Tstruct(name, fld) ->
      extern_atom name ^ name_optid id
  | _ -> ""

(* Type *)

let name_type ty = name_ldecl "" ty

let rec print_type t=
  match t with
  | Tint(sz, sg) -> name_inttype sz sg
  | Tfloat (sz) -> name_floattype sz
  | Tarray (_, ta, n) -> "ArrayType [" ^ (print_type ta) ^ " " ^ (Int32.to_string (camlint_of_coqint n)) ^ "]"
  | Tstruct (id, flist) -> "" ^ (extern_atom id) ^ "{ " ^ (print_fieldlist flist) ^ " }"
  | _ -> ""

and print_fieldlist lst=
  match lst with
    Fnil -> "";
  | Fcons (id, ty, tl) -> "(" ^ (extern_atom id) ^ " : " ^ (print_type ty) ^ ") " ^ (print_fieldlist tl)
  ;;

(* Precedences and associativity (H&S section 7.2) *)

type associativity = LtoR | RtoL | NA

let rec sprecedence = function
  | Svar _ -> (16, NA)
  | Scvar _ -> (16, NA)
  | Ssvar _ -> (16, NA)
  | Savar _ -> (16, NA)
  | Sfield _ -> (16, LtoR)
  | Saryacc _ -> (16, LtoR)
  | Sconst _ -> (16, NA)
  | Sunop _ -> (15, RtoL)
  | Scast _ -> (14, RtoL)
  | Sbinop((Omul|Odivint|Odivreal|Omod), _, _, _) -> (13, LtoR)
  | Sbinop((Oadd|Osub), _, _, _) -> (12, LtoR)
  | Sbinop((Olt|Ogt|Ole|Oge), _, _, _) -> (10, LtoR)
  | Sbinop((Oeq|One), _, _, _) -> (9, LtoR)
  | Sbinop(Oand, _, _, _) -> (8, LtoR)
  | Sbinop(Oxor, _, _, _) -> (7, LtoR)
  | Sbinop(Oor, _, _, _) -> (6, LtoR)

(* Expressions *)

let rec sexp p (prec, e) =
  let (prec', assoc) = sprecedence e in
  let (prec1, prec2) =
    if assoc = LtoR
    then (prec', prec' + 1)
    else (prec' + 1, prec') in
  if prec' < prec
  then fprintf p "@[<hov 2>("
  else fprintf p "@[<hov 2>";
  begin match e with
  | Svar(id, _) ->
      fprintf p "%s" (extern_atom id)
  | Scvar(id, _) ->
      fprintf p "%s" (extern_atom id)
  | Ssvar(id, _) ->
      fprintf p "%s" (extern_atom id)
  | Savar(id, _) ->
      fprintf p "%s" (extern_atom id)
  | Sfield(a1, f, _) ->
      fprintf p "%a.%s" sexp (prec', a1) (extern_atom f)
  | Saryacc(a1, a2, _) ->
      fprintf p "%a[%a]" sexp (prec', a1) sexp (prec', a2)
  | Sconst(Cint n, _) ->
      fprintf p "%ld" (camlint_of_coqint n)
  | Sconst(Cfloat f, _) -> fprintf p "%F" (camlfloat_of_coqfloat f)
  | Sconst(Csingle f, _) -> fprintf p "%Ff" (camlfloat_of_coqfloat32 f)
  | Sconst(Cbool b, _) ->
      fprintf p "%B" b
  | Sunop(op, a1, _) ->
      fprintf p "%s%a" (name_unop op) sexp (prec', a1)
  | Sbinop(op, a1, a2, _) ->
      fprintf p "%a@ %s %a"
                 sexp (prec1, a1) (name_binop op) sexp (prec2, a2)
  | Scast(a1, ty) ->
      fprintf p "(%s) %a" (name_type ty) sexp (prec', a1)
  end;
  if prec' < prec then fprintf p ")@]" else fprintf p "@]"

let print_sexp p e = sexp p (0, e)

let rec print_sexp_list p (first, rl) =
  match rl with
  | [] -> ()
  | r :: rl ->
      if not first then fprintf p ",@ ";
      sexp p (2, r);
      print_sexp_list p (false, rl)


let rec print_cases p cases =
  match cases with
  | [] -> ()
  | (Pany, r) :: rem ->
      fprintf p "@[<v 2>default:@ %a@]@ " print_sexp r;
      print_cases p rem
  | (Pachar c, r) :: rem ->
      fprintf p "@[<v 2>case %ld:@ %a@]@ %a"
              (camlint_of_coqint c)
              print_sexp r
              print_cases rem
  | (Paint i, r) :: rem ->
      fprintf p "@[<v 2>case %ld:@ %a@]@ %a"
              (camlint_of_coqint i)
              print_sexp r
              print_cases rem
  | (Pabool b, r) :: rem ->
      fprintf p "@[<v 2>case %B:@ %a@]@ %a"
              b
              print_sexp r
              print_cases rem

let rec print_lhs params =
  match params with
  | [] -> ""
  | (id, ty) :: [] -> (name_ldecl (extern_atom id) ty)
  | (id, ty) :: rem -> (name_ldecl (extern_atom id) ty) ^ ", " ^ (print_lhs rem)

let name_node_parameters fun_name params =
  let b = Buffer.create 20 in
  Buffer.add_string b fun_name;
  Buffer.add_char b '(';
  let rec add_params first = function
  | [] -> ()
  | (id, ty) :: rem ->
    if not first then Buffer.add_string b ", ";
      Buffer.add_string b (name_ldecl (extern_atom id) ty);
      add_params false rem in
  add_params true params;
  Buffer.add_char b ')';
  Buffer.contents b

let string_of_init id =
  let b = Buffer.create (List.length id) in
  let add_init = function
  | Init_int8 n ->
      let c = Int32.to_int (camlint_of_coqint n) in
      if c >= 32 && c <= 126 && c <> Char.code '\"' && c <> Char.code '\\'
      then Buffer.add_char b (Char.chr c)
      else Buffer.add_string b (Printf.sprintf "\\%03o" c)
  | _ ->
      assert false
  in List.iter add_init id; Buffer.contents b

let chop_last_nul id =
  match List.rev id with
  | Init_int8 BinNums.Z0 :: tl -> List.rev tl
  | _ -> id

let print_init p = function
  | Init_int8 n -> fprintf p "%ld,@ " (camlint_of_coqint n)
  | Init_int16 n -> fprintf p "%ld,@ " (camlint_of_coqint n)
  | Init_int32 n -> fprintf p "%ld,@ " (camlint_of_coqint n)
  | Init_int64 n -> fprintf p "%Ld,@ " (camlint64_of_coqint n)
  | Init_float32 n -> fprintf p "%F,@ " (camlfloat_of_coqfloat n)
  | Init_float64 n -> fprintf p "%F,@ " (camlfloat_of_coqfloat n)
  | Init_space n -> fprintf p "/* skip %ld, */@ " (camlint_of_coqint n)
  | Init_addrof(symb, ofs) ->
      let ofs = camlint_of_coqint ofs in
      if ofs = 0l
      then fprintf p "&%s,@ " (extern_atom symb)
      else fprintf p "(void *)((char *)&%s + %ld),@ " (extern_atom symb) ofs

let re_string_literal = Str.regexp "__stringlit_[0-9]+"

let print_gtype p (id, ty) =
  fprintf p "@[<v 2>TypeDecl:@ %s = %s @]@ " (extern_atom id) (print_type ty)

let print_gvar p (id,gv) =
  let name1 = "const " ^ extern_atom id in
  let t = gvar_info gv in
  let v = gvar_init gv in
  match v with
  | [] ->
      print_gtype p (id,t)
  | [Init_space _] ->
      fprintf p "%s;@ @ "
              (name_ldecl name1 t)
  | _ ->
      fprintf p "@[<hov 2>%s = "
              (name_ldecl name1 t);
      if Str.string_match re_string_literal (extern_atom id) 0
      && List.for_all (function Init_int8 _ -> true | _ -> false) v
      then
        fprintf p "\"%s\"" (string_of_init (chop_last_nul v))
      else begin
        fprintf p "{@ ";
        List.iter (print_init p) v;
        fprintf p "}"
      end;
      fprintf p ";@]@ @ "

let print_eqf p (e1, e2) =
  fprintf p "%a = %a" print_sexp e1 print_sexp e2
