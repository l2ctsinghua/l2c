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
open Ltypes
open Lustre
open LustreR
open PrintLustre

let rec print_stmt p s =
  match s with
  | Sassign(e1, e2) ->
      fprintf p "@[<hv 2>%a =@ %a;@]" print_sexp e1 print_sexp e2
  | Scall(None, lhs, e1, el) ->
      fprintf p "@[<hv 2>%a =@ %s.%s@,(@[<hov 0>%a@]);@]"
                print_sexp_list (true, lhs)
                (extern_atom e1.callid)
                (extern_atom e1.instid)
                print_sexp_list (true, el)
  | Scall(Some i, lhs, e1, el) ->
      fprintf p "@[<hv 2>%a =@ %s.%s[%a]@,(@[<hov 0>%a@]);@]"
                print_sexp_list (true, lhs)
                (extern_atom e1.callid)
                (extern_atom e1.instid)
                print_sexp i
                print_sexp_list (true, el)
  | Sfor(Some s_init, e, s_iter, s_body) ->
      fprintf p "@[<v 2>for (@[<hv 0>%a;@ %a;@ %a) {@]@ %a@;<0 -2>}@]"
              print_eqf s_init
              print_sexp e
              print_eqf s_iter
              print_stmt s_body
  | Sfor(None, e, s_iter, s_body) ->
      fprintf p "@[<v 2>for (@[<hv 0>;@ %a;@ %a) {@]@ %a@;<0 -2>}@]"
              print_sexp e
              print_eqf s_iter
              print_stmt s_body
  | Sseq(Sskip, s2) ->
      print_stmt p s2
  | Sseq(s1, Sskip) ->
      print_stmt p s1
  | Sseq(s1, s2) ->
      fprintf p "%a@ %a" print_stmt s1 print_stmt s2
  | Sskip ->
      fprintf p "/*skip*/;"
  | Sifs(e, s1, Sskip) ->
      fprintf p "@[<v 2>if (%a) {@ %a@;<0 -2>}@]"
              print_sexp e
              print_stmt s1
  | Sifs(e, Sskip, s2) ->
      fprintf p "@[<v 2>if (! %a) {@ %a@;<0 -2>}@]"
              sexp (15, e)
              print_stmt s2
  | Sifs(e, s1, s2) ->
      fprintf p "@[<v 2>if (%a) {@ %a@;<0 -2>} else {@ %a@;<0 -2>}@]"
              print_sexp e
              print_stmt s1
              print_stmt s2
  | Scase(lhs, e, cases) ->
      fprintf p "@[<v 2>%a =@ switch (%a) {@ %a@;<0 -2>}@]"
              print_sexp lhs
              print_sexp e
              print_cases cases
  | Sfby(lh, id1, e1, e2) ->
      fprintf p "@[<hv 2>%a =@ fby@,(@[<hov 0>%a,%a@]);@]"
                print_sexp lh
                print_sexp e1
                print_sexp e2
  | Sfbyn(lh, (id1,id2), n, e1, e2) ->
      fprintf p "@[<hv 2>%a =@ fby@,(@[<hov 0>%a,%ld,%a@]);@]"
                print_sexp lh
                print_sexp e1
                (camlint_of_coqint n)
                print_sexp e2
  | Sarrow(lh, e1, e2) ->
      fprintf p "@[<hv 2>%a =@ arrow@,(@[<hov 0>%a,%a@]);@]"
                print_sexp lh
                print_sexp e1
                print_sexp e2
  | Stypecmp(lh, e1, e2) ->
      fprintf p "@[<hv 2>%a =@ typecmp@,(@[<hov 0>%a,%a@]);@]"
                print_sexp lh
                print_sexp e1
                print_sexp e2


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
  print_stmt p f.nd_stmt;
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

let destination_r1 : string option ref = ref None
let print_LustreR1 = print_if destination_r1

let destination_r2 : string option ref = ref None
let print_LustreR2 = print_if destination_r2

let destination_r3 : string option ref = ref None
let print_LustreR3 = print_if destination_r3
