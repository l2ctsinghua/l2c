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

(** Pretty-printer for Clight *)

open Format
open Camlcoq
open Datatypes
open AST
open Integers
open PrintClight
open Ctemp
open Asti
open Options
open Ctypes
open Cop
open Cltypes

let parenthesize_if_pointer id =
  if String.length id > 0 && id.[0] = '*' then "(" ^ id ^ ")" else id

let rec name_cdecl id ty =
  match ty with
  | Tvoid ->
      "void" ^ name_optid id
  | Tint(sz, sg) ->
      name_inttype sz sg ^ name_optid id ;
  | Tfloat sz ->
      name_floattype sz ^ name_optid id
  | Tpointer t ->
      name_cdecl ("*" ^ id) t
  | Tarray(name ,t, n) ->
      extern_atom name ^ name_optid id
  | Tfunction(args, res, _) ->
      let b = Buffer.create 20 in
      if id = ""
      then Buffer.add_string b "(*)"
      else Buffer.add_string b (parenthesize_if_pointer id);
      Buffer.add_char b '(';
      begin match args with
      | Tnil ->
          Buffer.add_string b "void"
      | _ ->
          let rec add_args first = function
          | Tnil -> ()
          | Tcons(t1, tl) ->
              if not first then Buffer.add_string b ", ";
              Buffer.add_string b (name_cdecl "" t1);
              add_args false tl in
          add_args true args
      end;
      Buffer.add_char b ')';
      name_cdecl (Buffer.contents b) res
  | Tstruct(name, fld) ->
      extern_atom name ^ name_optid id

(* Type *)

let name_type ty = name_cdecl "" ty

(* Expressions *)

let parenthesis_level e =
  match e with
  | Econst_int _ -> 0
  | Econst_float _ -> 0
  | Econst_single _ -> 0
  | Evar _ -> 0
  | Etempvar _ -> 0
  | Etempret _ -> 0
  | Eunop(_, _, _) -> 30
  | Ederef _ -> 20
  | Eaddrof _ -> 30
  | Ebinop(op, _, _, _) ->
      begin match op with
      | Oand | Oor | Oxor -> 75
      | Oeq | One | Olt | Ogt | Ole | Oge -> 70
      | Oadd | Osub | Oshl | Oshr -> 60
      | Omul | Odiv | Omod -> 40
      end
  | Ecast _ -> 30
  | Esizeof _ -> 20
  | Ealignof _ -> 20
  | Efield _ -> 20

let rec print_expr p e =
  let level = parenthesis_level e in
  match e with
  | Econst_int (n, ty) ->
      begin match ty with
      | Tint (I8, Signed) -> fprintf p "'%c'" (char_of_int (Int32.to_int (camlint_of_coqint n)))
      | _ ->  fprintf p "%ld" (camlint_of_coqint n)
      end
  | Econst_float(f, _) ->
      fprintf p "%F" (camlfloat_of_coqfloat f)
  | Econst_single(f, _) ->
      fprintf p "%Ff" (camlfloat_of_coqfloat32 f)
  | Evar (id,ty) ->
      fprintf p "%s" (extern_atom id)
  | Etempvar (id,ty) ->
      fprintf p "%s" (extern_atom id)
  | Etempret (id,ty) ->
      fprintf p "%s" (extern_atom id)
  | Eunop(op, e1,ty) ->
      fprintf p "%s%a" (name_unop op) print_expr_prec (level, e1)
  | Ederef (Ebinop(Oadd, e1, e2,_), _) ->
      fprintf p "@[<hov 2>%a@,[%a]@]"
                print_expr_prec_access e1
                print_expr_prec_access e2
  | Ederef (e, ty) ->
      fprintf p "*%a" print_expr_prec (level, e)
  | Eaddrof (e,ty) ->
     fprintf p "&%a" print_expr_prec (level, e)
  | Ebinop(op, e1, e2, ty) ->
      fprintf p "@[<hov 0>%a@ %s %a@]"
                print_expr_prec (level, e1)
                (name_binop op)
                print_expr_prec (level, e2)
  | Ecast(e1,ty) ->
      fprintf p "@[<hov 2>(%s)@,%a@]"
                (name_type ty)
                print_expr_prec (level, e1)
  | Esizeof (ty,_) ->
      fprintf p "sizeof(%s)" (name_type ty)
  | Ealignof(ty, _) ->
      fprintf p "__alignof__(%s)" (name_type ty)
  | Efield(e1, id, ty) ->
      begin match e1 with
      | Ederef ((Ebinop (Oadd, _, _, _)) , _ ) ->
          fprintf p "%a.%s" print_expr_prec_access e1 (extern_atom id)
      | Ederef (e2, _) ->
          fprintf p "%a->%s" print_expr_prec_access e2 (extern_atom id)
      | _ ->
          fprintf p "%a.%s" print_expr_prec_access e1 (extern_atom id)
      end

and print_expr_prec p (context_prec, e) =
  let this_prec = parenthesis_level e in
  if this_prec >= context_prec
  then fprintf p "(%a)" print_expr e
  else print_expr p e

and print_expr_prec_access p e =
  match e with
  | Ederef ((Ebinop (Oadd, _, _, _)) , _ ) ->
      fprintf p "%a" print_expr e
  | Ederef (_, _) ->
      fprintf p "(%a)" print_expr e
  | _ -> print_expr p e

let rec print_expr_list p (first, el) =
  match el with
  | [] -> ()
  | e1 :: et ->
      if not first then fprintf p ",@ ";
      print_expr p e1;
      print_expr_list p (false, et)

let rec print_stmt p s =
  match s with
  | Sskip ->
      fprintf p "/*skip*/;"
  | Sassign(e1, e2) ->
      fprintf p "@[<hv 2>%a =@ %a;@]" print_expr e1 print_expr e2
  | Sset(id, e2) ->
      fprintf p "@[<hv 2>%s =@ %a;@]" (extern_atom id) print_expr e2
  | Scall(None, e1, el1, el2) ->
      fprintf p "@[<hv 2> %a (@[<hov 0>%a@]);@]"
                print_expr e1
                print_expr_list (true, app el1 el2)
  | Scall(Some lhs, e1, el1, el2) ->
      fprintf p "@[<hv 2>%s =@ %a@,(@[<hov 0>%a@]);@]"
                (extern_atom lhs)
                print_expr e1
                print_expr_list (true, app el1 el2)
  | Smemcpy(ty, tyargs, el) ->
      let size = Esizeof (ty, type_int32s) in
      let algn = Ealignof (ty, type_int32s) in
      fprintf p "__builtin_memcpy_aligned@[<hov 1>(%a,@ %a,@ %a);@]"
                print_expr_list (true, el)
                print_expr size
                print_expr algn
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
              print_expr e
              print_stmt s2
  | Sifthenelse(e, s1, s2) ->
      fprintf p "@[<v 2>if (%a) {@ %a@;<0 -2>} else {@ %a@;<0 -2>}@]"
              print_expr e
              print_stmt s1
              print_stmt s2
  | Sfor(s_init, e, s_iter, s_body) ->
      fprintf p "@[<v 2>for (@[<hv 0>%a;@ %a;@ %a) {@]@ %a@;<0 -2>}@]"
              print_stmt_for s_init
              print_expr e
              print_stmt_for s_iter
              print_stmt s_body
  | Sbreak ->
      fprintf p "break;"
  | Sswitch(e, cases) ->
      fprintf p "@[<v 2>switch (%a) {@ %a@;<0 -2>}@]"
              print_expr e
              print_cases cases
  | Sreturn None ->
      fprintf p "return;"
  | Sreturn (Some e) ->
      fprintf p "return %a;" print_expr e


and print_cases p cases =
  match cases with
  | LSdefault s ->
      fprintf p "@[<v 2>default:@ %a@]" print_stmt s
  | LScase(lbl, s, rem) ->
      fprintf p "@[<v 2>case %ld:@ %a@]@ %a"
              (camlint_of_coqint lbl)
              print_stmt s
              print_cases rem

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
  | Scall(None, e1, el1, el2) ->
      fprintf p "@[<hv 2>%a@,(@[<hov 0>%a@])@]"
                print_expr e1
                print_expr_list (true, app el1 el2)
  | Scall(Some id, e1, el1, el2) ->
      fprintf p "@[<hv 2>%s =@ %a@,(@[<hov 0>%a@])@]"
                (extern_atom id)
                print_expr e1
                print_expr_list (true, app el1 el2)
  | _ ->
      fprintf p "({ %a })" print_stmt s

let name_function_parameters fun_name params =
  let b = Buffer.create 20 in
  Buffer.add_string b fun_name;
  Buffer.add_char b '(';
  begin match params with
  | [] ->
      Buffer.add_string b "void"
  | _ ->
      let rec add_params first = function
      | [] -> ()
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
            (name_cdecl (name_function_parameters (extern_atom id) (app f.fn_params f.fn_temps))
                        f.fn_return);
  fprintf p "@[<v 2>{@ ";
  List.iter
    (fun (id, ty) -> fprintf p "%s;@ " (name_cdecl (extern_atom id) ty))
    f.fn_vars;
  print_stmt p f.fn_body;
 fprintf p "@;<0 -2>}@]@ @ "
 ;;

let print_fundef p id f =
  print_function p id f

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

let rec cal_type_nums ty =
  let rec cal_struct_nums fld =
     begin match fld with
       Fnil -> 0
     | Fcons (id, ty, tl) -> (cal_type_nums ty) + (cal_struct_nums tl)
     end
  in
  begin match ty with
      Tstruct (id, fld) -> cal_struct_nums fld
    | Tarray(_, t, n) -> (cal_type_nums t) * (Int32.to_int (camlint_of_coqint n))
    | _ -> 1
  end;;

let rec firstn n l =
  match n with
  | 0 -> []
  | _ -> (List.hd l):: firstn (n-1) (List.tl l) ;;

let rec skipn n l =
  match n with
  | 0 -> l
  | _ -> skipn (n-1) (List.tl l);;

let rec print_array_struct p init ty =
  match init with
  | [] -> ()
  | [Init_space _] -> ()
  | _ ->
      begin match ty with
        | Tstruct(tid, fl) ->
            fprintf p "{";
            let rec print_fl_const p fl init =
                match fl with
                  Fnil -> ()
                | Fcons (fid,fty,tfl) ->
                    let n = cal_type_nums fty in
                    let init_fty = firstn n init in
                    print_array_struct p init_fty fty;
                    if tfl <> Fnil then
                       ( fprintf p ",";
                         print_fl_const p tfl (skipn n init) )
		    else ()
            in
            print_fl_const p fl init;
            fprintf p "}";
        | Tarray(_, t, n) ->
            fprintf p "{";
            let rec print_array_const p t init =
                match init with
                  [] -> ()
                | _ ->
                    let num = cal_type_nums t in
                    let init_t = firstn num init in
                    print_array_struct p init_t t;
                    let init_tl = skipn num init in
                    if init_tl <> [] then
                       ( fprintf p ",";
                         print_array_const p t init_tl)
                    else ()
            in
            print_array_const p t init;
            fprintf p "}"
        | _ -> print_init p (List.hd init)
      end;;

let rec name_cdecl_type name t n =
  let id = extern_atom name in
  begin match t with
  | Tarray (name1,t1,n1) ->
      (extern_atom name1) ^ (sprintf " %s[%ld]" (parenthesize_if_pointer id) (camlint_of_coqint n))
  | _ ->
      name_cdecl (sprintf "%s[%ld]" (parenthesize_if_pointer id) (camlint_of_coqint n)) t
  end
  ;;

let print_globvar p id v =
  let init = gvar_init v in
  let ty = gvar_info v in
  match init with
  | [] ->
     begin match ty with
     | Tstruct (_, fld) ->
          let str_id = extern_atom id in
          print_struct_or_union p (str_id, fld);
     | Tarray(_, t, n) ->
          fprintf p "@[<v 2>typedef %s;" (name_cdecl_type id t n);
          fprintf p "@;<0 -2>@]@ ";
     | _ -> ();
     end
  | [Init_space _] -> ()
  | _ ->
      fprintf p "@[<hov 2>";
      begin match ty with
      | Tstruct(_, _) | Tarray (_,_,_) ->
          fprintf p "const %s =  " (name_cdecl (extern_atom id) ty);
          print_array_struct p init ty;
          fprintf p ";";
          fprintf p "@]@ @ "
      | _ ->
          fprintf p "#define%s" (name_optid (extern_atom id));
	  fprintf p "@ ";
	  List.iter (print_init p) init;
          fprintf p "@]@ @ ";
      end;;

let print_globdef p (id, gd) =
  match gd with
  | Gfun f -> print_fundef p id f
  | Gvar v -> print_globvar p id v

let print_program p prog =
  fprintf p "@[<v 0>";
  List.iter (print_globdef p) prog.prog_defs;
  fprintf p "@]@."
  ;;

let destination : string option ref = ref None

let print_if prog =
  match !destination with
  | None -> ()
  | Some f ->
      let oc = open_out f in
      print_program (formatter_of_out_channel oc) prog;
      close_out oc
