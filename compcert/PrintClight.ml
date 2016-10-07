(* *********************************************************************)
(*                                                                     *)
(*              The L2C verified compiler                              *)
(*                                                                     *)
(*                   Tsinghua University                               *)
(*                                                                     *)
(*  Copyright Institut National de Recherche en Informatique et en     *)
(*  Automatique.  All rights reserved.  This file is distributed       *)
(*  under the terms of the GNU General Public License as published by  *)
(*  the Free Software Foundation, either version 2 of the License, or  *)
(*  (at your option) any later version.  This file is also distributed *)
(*  under the terms of the Tsinghua University License Agreement.      *)
(*                                                                     *)
(* *********************************************************************)

(** Pretty-printer for Clight *)

open Format
open Camlcoq
open Datatypes
open AST
open Clight
open Asti
open Options
open Ctypes
open Cop

let name_unop = function
  | Onotbool -> "!"
  | Onotint  -> "~"
  | Oneg     -> "-"
  | Oabsfloat -> "__builtin_fabs"

let name_binop = function
  | Oadd -> "+"
  | Osub -> "-"
  | Omul -> "*"
  | Odiv -> "/"
  | Omod -> "%"
  | Oand -> "&&"
  | Oor  -> "||"
  | Oxor -> "^"
  | Oshl -> "<<"
  | Oshr -> ">>"
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

(* Declarator (identifier + type) *)

let attributes a =
  let s1 = if a.attr_volatile then " volatile" else "" in
  match a.attr_alignas with
  | None -> s1
  | Some l ->
      sprintf " _Alignas(%Ld)%s" (Int64.shift_left 1L (N.to_int l)) s1

let attributes_space a =
  let s = attributes a in 
  if String.length s = 0 then s else s ^ " "

let name_optid id =
  if id = "" then "" else " " ^ id

let rec name_cdecl id ty =
  match ty with
  | Tvoid ->
      "void" ^ name_optid id
  | Tint(sz, sg, a) ->
      name_inttype sz sg ^ attributes a ^ name_optid id
  | Tfloat(sz, a) ->
      name_floattype sz ^ attributes a ^ name_optid id
  | Tlong(sg, a) ->
      name_longtype sg ^ attributes a ^ name_optid id
  | Tpointer(t, a) ->
      let id' =
        match t with
        | Tfunction _ | Tarray _ -> sprintf "(*%s%s)" (attributes_space a) id
        | _                      -> sprintf "*%s%s" (attributes_space a) id in
      name_cdecl id' t
  | Tarray(t, n, a) ->
      name_cdecl (sprintf "%s[%ld]" id (camlint_of_coqint n)) t
  | Tfunction(args, res, cconv) ->
      let b = Buffer.create 20 in
      if id = ""
      then Buffer.add_string b "(*)"
      else Buffer.add_string b id;
      Buffer.add_char b '(';
      let rec add_args first = function
      | Tnil ->
          if first then
            Buffer.add_string b
               (if cconv.cc_vararg then "..." else "void")
          else if cconv.cc_vararg then
            Buffer.add_string b ", ..."
          else
            ()
      | Tcons(t1, tl) ->
          if not first then Buffer.add_string b ", ";
          Buffer.add_string b (name_cdecl "" t1);
          add_args false tl in
      add_args true args;
      Buffer.add_char b ')';
      name_cdecl (Buffer.contents b) res
  | Tstruct(name, fld, a) ->
      extern_atom name ^ attributes a ^ name_optid id
  | Tunion(name, fld, a) ->
      extern_atom name ^ attributes a ^ name_optid id
  | Tcomp_ptr(name, a) ->
      extern_atom name ^ " *" ^ attributes a ^ id

(* Type *)

let name_type ty = name_cdecl "" ty

type associativity = LtoR | RtoL | NA

let rec precedence = function
  | Evar _ -> (16, NA)
  | Etempvar _ -> (16, NA)
  | Ederef _ -> (15, RtoL)
  | Efield _ -> (16, LtoR)
  | Econst_int _ -> (16, NA)
  | Econst_float _ -> (16, NA)
  | Econst_single _ -> (16, NA)
  | Econst_long _ -> (16, NA)
  | Eunop _ -> (15, RtoL)
  | Eaddrof _ -> (15, RtoL)
  | Ecast _ -> (14, RtoL)
  | Ebinop((Omul|Odiv|Omod), _, _, _) -> (13, LtoR)
  | Ebinop((Oadd|Osub), _, _, _) -> (12, LtoR)
  | Ebinop((Oshl|Oshr), _, _, _) -> (11, LtoR)
  | Ebinop((Olt|Ogt|Ole|Oge), _, _, _) -> (10, LtoR)
  | Ebinop((Oeq|One), _, _, _) -> (9, LtoR)
  | Ebinop(Oand, _, _, _) -> (8, LtoR)
  | Ebinop(Oxor, _, _, _) -> (7, LtoR)
  | Ebinop(Oor, _, _, _) -> (6, LtoR)

(* Expressions *)

let rec expr p (prec, e) =
  let (prec', assoc) = precedence e in
  let (prec1, prec2) =
    if assoc = LtoR
    then (prec', prec' + 1)
    else (prec' + 1, prec') in
  if prec' < prec 
  then fprintf p "@[<hov 2>("
  else fprintf p "@[<hov 2>";
  begin match e with
  | Evar(id, _) ->
      fprintf p "%s" (extern_atom id)
  | Etempvar(id, _) ->
      fprintf p "%s" (extern_atom id)
  | Ederef (Ebinop(Oadd, e1, e2,_), _) ->
      fprintf p "@[<hov 2>%a@,[%a]@]" 
                expr (prec1, e1)
                expr (prec2, e2)
  | Ederef(a1, _) ->
      fprintf p "*%a" expr (prec', a1)
  | Efield(a1, f, _) ->
      fprintf p "%a.%s" expr (prec', a1) (extern_atom f)
  | Econst_int(n, Tint(I32, Unsigned, _)) ->
      fprintf p "%luU" (camlint_of_coqint n)
  | Econst_int(n, _) ->
      fprintf p "%ld" (camlint_of_coqint n)
  | Econst_float(f, _) ->
      fprintf p "%F" (camlfloat_of_coqfloat f)
  | Econst_single(f, _) ->
      fprintf p "%Ff" (camlfloat_of_coqfloat32 f)
  | Econst_long(n, Tlong(Unsigned, _)) ->
      fprintf p "%LuLLU" (camlint64_of_coqint n)
  | Econst_long(n, _) ->
      fprintf p "%LdLL" (camlint64_of_coqint n)
  | Eunop(Oabsfloat, a1, _) ->
      fprintf p "__builtin_fabs(%a)" expr (2, a1)
  | Eunop(op, a1, _) ->
      fprintf p "%s%a" (name_unop op) expr (prec', a1)
  | Eaddrof(a1, _) ->
      fprintf p "&%a" expr (prec', a1)
  | Ebinop(op, a1, a2, _) ->
      fprintf p "%a@ %s %a"
                 expr (prec1, a1) (name_binop op) expr (prec2, a2)
  | Ecast(a1, ty) ->
      fprintf p "(%s) %a" (name_type ty) expr (prec', a1)
  end;
  if prec' < prec then fprintf p ")@]" else fprintf p "@]"

let print_expr p e = expr p (0, e)

let rec print_expr_list p (first, rl) =
  match rl with
  | [] -> ()
  | r :: rl ->
      if not first then fprintf p ",@ ";
      expr p (2, r);
      print_expr_list p (false, rl)

(* Statements *)

let rec print_stmt p s =
  match s with
  | Sskip ->
      fprintf p "/*skip*/;"
  | Sassign(e1, e2) ->
      fprintf p "@[<hv 2>%a =@ %a;@]" print_expr e1 print_expr e2
  | Sset(id, e2) ->
      fprintf p "@[<hv 2>%s =@ %a;@]" (extern_atom id) print_expr e2
  | Scall(None, e1, el) ->
      fprintf p "@[<hv 2>%a@,(@[<hov 0>%a@]);@]"
                print_expr e1
                print_expr_list (true, el)
  | Scall(Some id, e1, el) ->
      fprintf p "@[<hv 2>%s =@ %a@,(@[<hov 0>%a@]);@]"
                (extern_atom id)
                print_expr e1
                print_expr_list (true, el)
  | Sbuiltin(_, EF_memcpy(sz, al), tyargs, el) ->
      fprintf p "__builtin_memcpy_aligned@[<hov 1>(%a,@ %ld,@ %ld);@]"
                print_expr_list (true, el)
                (camlint_of_coqint sz) (camlint_of_coqint al)
  | Sbuiltin(_, _, _, args) ->
      fprintf p "<unknown builtin>@[<hov 1>(%a)@]" print_expr_list (true, args)
  | Ssequence(Sskip, s2) ->
      print_stmt p s2
  | Ssequence(s1, Sskip) ->
      print_stmt p s1
  | Ssequence(s1, s2) ->
      fprintf p "%a@ %a" print_stmt s1 print_stmt s2
  | Sifthenelse(e, s1, Sskip) ->
      fprintf p "@[<v 2>if (%a) {@ %a@;<0 -2>}@]"
              print_expr e
              print_stmt s1
  | Sifthenelse(e, Sskip, s2) ->
      fprintf p "@[<v 2>if (! %a) {@ %a@;<0 -2>}@]"
              expr (15, e)
              print_stmt s2
  | Sifthenelse(e, s1, s2) ->
      fprintf p "@[<v 2>if (%a) {@ %a@;<0 -2>} else {@ %a@;<0 -2>}@]"
              print_expr e
              print_stmt s1
              print_stmt s2
  | Sloop(s1, Sskip) ->
      fprintf p "@[<v 2>while (1) {@ %a@;<0 -2>}@]"
              print_stmt s1
  | Sloop(s1, s2) ->
      fprintf p "@[<v 2>for (@[<hv 0>;@ 1;@ %a) {@]@ %a@;<0 -2>}@]"
              print_stmt_for s2
              print_stmt s1
  | Sbreak ->
      fprintf p "break;"
  | Scontinue ->
      fprintf p "continue;"
  | Sswitch(e, cases) ->
      fprintf p "@[<v 2>switch (%a) {@ %a@;<0 -2>}@]"
              print_expr e
              print_cases cases
  | Sreturn None ->
      fprintf p "return;"
  | Sreturn (Some e) ->
      fprintf p "return %a;" print_expr e
  | Slabel(lbl, s1) ->
      fprintf p "%s:@ %a" (extern_atom lbl) print_stmt s1
  | Sgoto lbl ->
      fprintf p "goto %s;" (extern_atom lbl)

and print_cases p cases =
  match cases with
  | LSnil ->
      ()
  | LScons(lbl, s, rem) ->
      fprintf p "@[<v 2>%a:@ %a@]@ %a"
              print_case_label lbl
              print_stmt s
              print_cases rem

and print_case_label p = function
  | None -> fprintf p "default"
  | Some lbl -> fprintf p "case %ld" (camlint_of_coqint lbl)

and print_stmt_for p s =
  match s with
  | Sskip ->
      fprintf p "/*nothing*/"
  | Sassign(e1, e2) ->
      fprintf p "%a = %a" print_expr e1 print_expr e2
  | Sset(id, e2) ->
      fprintf p "%s = %a" (extern_atom id) print_expr e2
  | Ssequence(s1, s2) ->
      fprintf p "%a, %a" print_stmt_for s1 print_stmt_for s2
  | Scall(None, e1, el) ->
      fprintf p "@[<hv 2>%a@,(@[<hov 0>%a@])@]"
                print_expr e1
                print_expr_list (true, el)
  | Scall(Some id, e1, el) ->
      fprintf p "@[<hv 2>%s =@ %a@,(@[<hov 0>%a@])@]"
                (extern_atom id)
                print_expr e1
                print_expr_list (true, el)
  | _ ->
      fprintf p "({ %a })" print_stmt s

let name_function_parameters fun_name params cconv =
  let b = Buffer.create 20 in
  Buffer.add_string b fun_name;
  Buffer.add_char b '(';
  begin match params with
  | [] ->
      Buffer.add_string b (if cconv.cc_vararg then "..." else "void")
  | _ ->
      let rec add_params first = function
      | [] ->
          if cconv.cc_vararg then Buffer.add_string b "..."
      | (id, ty) :: rem ->
          if not first then Buffer.add_string b ", ";
          Buffer.add_string b (name_cdecl (extern_atom id) ty);
          add_params false rem in
      add_params true params
  end;
  Buffer.add_char b ')';
  Buffer.contents b

let print_function p id f =
  fprintf p "%s@ "
            (name_cdecl (name_function_parameters (extern_atom id)
                                                  f.fn_params f.fn_callconv)
                        f.fn_return);
  fprintf p "@[<v 2>{@ ";
  List.iter
    (fun (id, ty) ->
      fprintf p "%s;@ " (name_cdecl (extern_atom id) ty))
    f.fn_vars;
  List.iter
    (fun (id, ty) ->
      fprintf p "register %s;@ " (name_cdecl (extern_atom id) ty))
    f.fn_temps;
  print_stmt p f.fn_body;
  fprintf p "@;<0 -2>}@]@ @ "

let print_fundef p id fd =
  match fd with
  | External(EF_external(_,_), args, res, cconv) ->
      fprintf p "extern %s;@ @ "
                (name_cdecl (extern_atom id) (Tfunction(args, res, cconv)))
  | External(_, _, _, _) ->
      ()
  | Internal f ->
      print_function p id f

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
  | Init_int8 Z.Z0 :: tl -> List.rev tl
  | _ -> id

let print_init p = function
  | Init_int8 n -> fprintf p "%ld" (camlint_of_coqint n)
  | Init_int16 n -> fprintf p "%ld" (camlint_of_coqint n)
  | Init_int32 n -> fprintf p "%ld" (camlint_of_coqint n)
  | Init_int64 n -> fprintf p "%LdLL" (camlint64_of_coqint n)
  | Init_float32 n -> fprintf p "%F" (camlfloat_of_coqfloat n)
  | Init_float64 n -> fprintf p "%F" (camlfloat_of_coqfloat n)
  | Init_space n -> fprintf p "/* skip %ld */@ " (camlint_of_coqint n)
  | Init_addrof(symb, ofs) ->
      let ofs = camlint_of_coqint ofs in
      if ofs = 0l
      then fprintf p "&%s" (extern_atom symb)
      else fprintf p "(void *)((char *)&%s + %ld)" (extern_atom symb) ofs

let print_composite_init p il =
  fprintf p "{@ ";
  List.iter
    (fun i ->
      print_init p i;
      match i with Init_space _ -> () | _ -> fprintf p ",@ ")
    il;
  fprintf p "}"

let print_struct_or_union p (name, fld) = 
  fprintf p "@[<v 2>typedef struct {"; 
  let rec print_fields = function
  | Fnil -> ()
  | Fcons(id, ty, rem) ->
     fprintf p "@ %s;" (name_cdecl (extern_atom id) ty);
     print_fields rem 
  in          
  print_fields fld;
  fprintf p "@;<0 -2>}%s;@ "name;
  fprintf p "@]@ @ "

let re_string_literal = Str.regexp "__stringlit_[0-9]+"

let print_globvar p id v =
  let name1 = extern_atom id in
  let name2 = if v.gvar_readonly then "const " ^ name1 else name1 in
  match v.gvar_init with
  | [] ->
      begin match v.gvar_info with
     | Tstruct (_, fld,_) -> 
          print_struct_or_union p (name1, fld);
     | _ -> ();
     end
  | [Init_space _] ->
      fprintf p "%s;@ @ "
              (name_cdecl name2 v.gvar_info)
  | _ ->
      fprintf p "@[<hov 2>%s = "
              (name_cdecl name2 v.gvar_info);
      begin match v.gvar_info, v.gvar_init with
      | (Tint _ | Tlong _ | Tfloat _ | Tpointer _ | Tfunction _ | Tcomp_ptr _),
        [i1] ->
          print_init p i1
      | _, il ->
          if Str.string_match re_string_literal (extern_atom id) 0
          && List.for_all (function Init_int8 _ -> true | _ -> false) il
          then fprintf p "\"%s\"" (string_of_init (chop_last_nul il))
          else print_composite_init p il
      end;
      fprintf p ";@]@ @ "

let print_globdef p (id, gd) =
  match gd with
  | Gfun f -> print_fundef p id f
  | Gvar v -> print_globvar p id v 

let print_program p prog = 
  fprintf p "@[<v 0>";
  List.iter (print_globdef p) prog.prog_defs;
  fprintf p "@]@."
  ;;


