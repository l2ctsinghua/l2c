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
open Options
open Cop
open Lop
open Ltypes
open Lustre
open LustreS
open PrintLustre

let rec print_lindex p s =
  match s with
  | Label id -> fprintf p "%s" (extern_atom id)
  | Index e -> sexp p (2, e)

let rec print_lindex_list p (first, rl) =
  match rl with
  | [] -> ()
  | r :: rl ->
      if not first then fprintf p ",@ ";
      print_lindex p r;
      print_lindex_list p (false, rl)

let str_prefixop = function
  | Oint -> "int$"
  | Oshort -> "short$"
  | Ofloat -> "float$"
  | Oreal -> "real$"
  | Onot -> "not$"
  | Opos -> "+$"
  | Oneg -> "-$"


let print_hstmt p s =
  match s with
  | Hmaptycmp ((id,ty),k, e1, e2) ->
      fprintf p "@[<hv 2>maptycmp(%s,%s,%a,%a);@]"
                (extern_atom id)
                (if k then "true" else "false")
                print_sexp e1
                print_sexp e2
  | Hmapary((id,ty), op, e1, e2) ->
      fprintf p "@[<hv 2>mapary(%s,%s,%a,%a);@]"
                (extern_atom id)
                (name_binop op)
                print_sexp e1
                print_sexp e2
  | Hfoldary((id,ty), op, e1, e2) ->
      fprintf p "@[<hv 2>foldary(%s,%s,%a,%a);@]"
                (extern_atom id)
                (name_binop op)
                print_sexp e1
                print_sexp e2
  | Hfoldunary((id,ty), op, e1) ->
      fprintf p "@[<hv 2>foldary(%s,%s,%a);@]"
                (extern_atom id)
                (name_unop op)
                print_sexp e1
  | Hfoldcast((id,ty), e1, t) ->
      fprintf p "@[<hv 2>foldcast(%s,%a,%s);@]"
                (extern_atom id)
                print_sexp e1
                (name_type t)
  | Hmapunary((id,ty), op, e1) ->
      fprintf p "@[<hv 2>mapary(%s,%s,%a);@]"
                (extern_atom id)
                (str_prefixop op)
                print_sexp e1
  | Harydef((id,ty), e1) ->
      fprintf p "@[<hv 2>arydef(%s,%a);@]"
                (extern_atom id)
                print_sexp e1
  | Haryslc((id,ty), e1, n) ->
      fprintf p "@[<hv 2>aryslc(%s,%a,%ld);@]"
                (extern_atom id)
                print_sexp e1
                (camlint_of_coqint n)
  | Hboolred((id,ty), e1) ->
      fprintf p "@[<hv 2>boolred(%s,%a);@]"
                (extern_atom id)
                print_sexp e1
  | Hmapcall(lh, c, el) ->
      fprintf p "@[<hv 2>mapcall: %s =@ %s.%s@,(@[<hov 0>%a@]);@]"
                (print_lhs lh)
                (extern_atom c.callid)
                (extern_atom c.instid)
                print_sexp_list (true, el)
  | Hmapfoldcall((id,ty), _, lh, c, e1, el) ->
      fprintf p "@[<hv 2>mapfoldcall: %s,%s =@ %s.%s@,(@[<hov 0>%a, %a@]);@]"
                (extern_atom id)
                (print_lhs lh)
                (extern_atom c.callid)
                (extern_atom c.instid)
                print_sexp e1
                print_sexp_list (true, el)

let rec print_stmt p s =
  match s with
  | Sassign((id,ty), Expr e1) ->
      fprintf p "@[<hv 2>%s =@ %a;@]" (extern_atom id) print_sexp e1
  | Sassign((id,ty), Earyprj(e1, el, d)) ->
      fprintf p "@[<hv 2>%s =@ %a[%a],default: %a;@]"
                (extern_atom id)
                print_sexp e1
                print_sexp_list (true, el)
                print_sexp d
  | Sassign((id,ty), Ecase(e, cases)) ->
      fprintf p "@[<v 2>%s =@ switch (%a) {@ %a@;<0 -2>}@]"
              (extern_atom id)
              print_sexp e
              print_cases cases
  | Sassign((id,ty), Eif(e1, e2, e3)) ->
      fprintf p "@[<v 2>%s =@ if (%a) {@ %a@;<0 -2>} else {@ %a@;<0 -2>}@]"
              (extern_atom id)
              print_sexp e1
              print_sexp e2
              print_sexp e3
  | Sarrow ((id,ty),e1, e2) ->
      fprintf p "@[<hv 2>%s =@ arrow@,(@[<hov 0>%a,%a@]);@]"
                (extern_atom id)
                print_sexp e1
                print_sexp e2
  | Sassign((id,ty),Eprefix(op, el)) ->
      fprintf p "@[<hv 2>%s =@ prefix@,(@[<hov 0>%s,%a@]);@]"
                (extern_atom id)
                (name_binop op)
                print_sexp_list (true, el)
  | Sassign ((id,ty),Etypecmp(k, e1, e2)) ->
      fprintf p "@[<hv 2>typecmp(%s,%s,%a,%a);@]"
                (extern_atom id)
                (if k then "true" else "false")
                print_sexp e1
                print_sexp e2
  | Sfby ((id,ty),id1,e1, e2) ->
      fprintf p "@[<hv 2>%s =@ fby@,(@[<hov 0>%a,%a@]);@]"
                (extern_atom id)
                print_sexp e1
                print_sexp e2
  | Sfbyn ((id,ty),(id1,id2),n, e1, e2) ->
      fprintf p "@[<hv 2>%s =@ fby@,(@[<hov 0>%a,%ld,%a@]);@]"
                (extern_atom id)
                print_sexp e1
                (camlint_of_coqint n)
                print_sexp e2
  | Scall(lhs, e1, el) ->
      fprintf p "@[<hv 2>%s =@ %s.%s@,(@[<hov 0>%a@]);@]"
                (print_lhs lhs)
                (extern_atom e1.callid)
                (extern_atom e1.instid)
                print_sexp_list (true, el)
  | Sfor(b, e1, n) ->
      fprintf p "@[<v 2>for %ld {@]@ %a@;<0 -2>}@]"
              (camlint_of_coqint n)
              print_hstmt e1
  | Sarydif((id,ty),_,el) ->
      fprintf p "@[<hv 2>%s =@ arydif@,(@[<hov 0>%a@]);@]"
                (extern_atom id)
                print_sexp_list (true, el)
  | Smix ((id,ty),e1, el, e2) ->
      fprintf p "@[<hv 2>%s =@ mix@,(@[<hov 0>%a[%a],%a @]);@]"
                (extern_atom id)
                print_sexp e1
                print_lindex_list (true, el)
                print_sexp e2
  | Sstruct ((id,ty),_,el) ->
      fprintf p "@[<hv 2>%s =@ struct@,(@[<hov 0>%a@]);@]"
                (extern_atom id)
                print_sexp_list (true, el)
  | Sskip ->
      fprintf p "/*skip*/;"


let print_node p (id, f) =
  fprintf p "%s@ " (name_node_parameters (extern_atom id) f.nd_args);
  fprintf p "@[<v 2>{@ ";
  List.iter
    (fun (id, ty) ->
      fprintf p "return %s;@ " (name_ldecl (extern_atom id) ty))
    f.nd_rets;
  List.iter
    (fun (id, ty) ->
      fprintf p "register %s;@ " (name_ldecl (extern_atom id) ty))
    f.nd_svars;
  List.iter
    (fun (id, ty) ->
      fprintf p "%s;@ " (name_ldecl (extern_atom id) ty))
    f.nd_vars;
  List.iter (fun a -> print_stmt p a) f.nd_stmt;
  fprintf p "@;<0 -2>}@]@ @ "


let print_program p prog =
  fprintf p "@[<v 0>";
  List.iter (print_gtype p) prog.type_block;
  List.iter (print_gvar p) prog.const_block;
  List.iter (print_node p) prog.node_block;
  fprintf p "@]@."

let print_if optdest prog =
  match !optdest with
  | None -> ()
  | Some f ->
      let oc = open_out f in
      let pp = formatter_of_out_channel oc in
      print_program pp prog;
      close_out oc

let destination_t : string option ref = ref None
let print_LustreT = print_if destination_t

let destination_s : string option ref = ref None
let print_LustreS = print_if destination_s
