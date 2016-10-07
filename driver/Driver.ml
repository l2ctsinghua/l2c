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

open Fileutil
open Camlcoq
open Printf
open Options
open Format
open AST
open PrintClight
open Datatypes
open BinPos

let print_error oc msg =
  let print_one_error = function
  | Errors.MSG s -> output_string oc (Camlcoq.camlstring_of_coqstring s)
  | Errors.CTX i -> output_string oc (Camlcoq.extern_atom i)
  | Errors.POS i -> output_string oc (Camlcoq.extern_atom i)
  in
    List.iter print_one_error msg;
    output_char oc '\n'

let set_target_dir_path fn =
    let mfn=Filename.basename (Filename.chop_extension fn) in
    let dirmfn=Filename.dirname fn in
    let fullpath=dirmfn ^ "/" ^ mfn in
    if !target_dir="" then fullpath
    else mfn
    ;;

let output_path main mfn=
    let fn=set_target_dir_path mfn in
    let fn =
      if !output_file="" then (Filename.concat !target_dir fn)
      else if (Filename.is_implicit !output_file) then (Filename.concat !target_dir !output_file)
      else !output_file in

    let str_node =
       if !output_file = "" then extern_atom main
       else Filename.basename (Filename.chop_extension !output_file) in

    Filename.concat (Filename.dirname (fn ^ ".ast")) (str_node)
    ;;

let output_c_file prog path=
    let channel = open_out (path ^ ".c") in
    print_program (formatter_of_out_channel channel) prog;
    close_out channel;
  ;;


ignore (intern_string "acg_global_clock");; (*1*)
ignore (intern_string "acg_global_2");; (*2*)
ignore (intern_string "acg_global_3");; (*3*)
ignore (intern_string "acg_global_4");; (*4*)
ignore (intern_string "acg_global_5");; (*5*)
ignore (intern_string "acg_global_6");; (*6*)
ignore (intern_string "acg_dest");; (*7*)
ignore (intern_string "acg_src");; (*8*)
ignore (intern_string "acg_size");; (*9*)
ignore (intern_string "acg_d");; (*10*)
ignore (intern_string "acg_s");; (*11*)
ignore (intern_string "acg_memcpy");; (*12*)
ignore (intern_string "outC");; (*13*)
ignore (intern_string "acg_j");; (*14*)
ignore (intern_string "acg_init");; (*15*)
ignore (intern_string "idx");; (*16*)
ignore (intern_string "items");; (*17*)
ignore (intern_string "inC");; (*18*)
ignore (intern_string "acg_i");; (*19*)
ignore (intern_string "acg_b");; (*20*)
ignore (intern_string "acg_local");; (*21*)
ignore (intern_string "acg_c1");; (*22*)
ignore (intern_string "acg_c2");; (*23*)
ignore (intern_string "acg_equ");; (*24*)


let translate fn=
  let mfn = fn in
  let content=read_whole_file fn in
  let (main, astI)=Asti.construct_L_ast content in

  let local_id_P = ref (intern_string "acg_L1") in
  let (pidS , astS) =
    match LustreSGen.trans_program !local_id_P astI with
    | Errors.OK x -> x
    | Errors.Error msg ->
        print_error stderr msg;
        exit 2 in

  for i=2 to (Int32.to_int (P.to_int32 pidS)) do
    ignore (intern_string ("acg_L" ^ (string_of_int i)) )
  done;

  let path = output_path main mfn in

  let set_dest dst opt f =
    dst := if !opt then Some f
                   else None in
  set_dest PrintLustreS.destination_t flag_save_temp (path ^ ".lust");
  set_dest PrintLustreS.destination_s flag_save_temp (path ^ ".luss");
  set_dest PrintLustreR.destination_r1 flag_save_temp (path ^ ".lusr1");
  set_dest PrintLustreR.destination_r2 flag_save_temp (path ^ ".lusr2");
  set_dest PrintLustreR.destination_r3 flag_save_temp (path ^ ".lusr3");
  set_dest PrintLustreF.destination_f1 flag_save_temp (path ^ ".lusf1");
  set_dest PrintLustreF.destination_f2 flag_save_temp (path ^ ".lusf2");
  set_dest PrintLustreF.destination_e1 flag_save_temp (path ^ ".luse1");
  set_dest PrintLustreF.destination_e2 flag_save_temp (path ^ ".luse2");
  set_dest PrintLustreF.destination_d flag_save_temp (path ^ ".lusd");
  set_dest PrintLustreF.destination_c flag_save_temp (path ^ ".lusc");

  set_dest PrintCtemp.destination flag_ctemp (path ^ ".c");

  let astC =
    match Compiler.transf_lt_program astS with
    | Errors.OK x -> x
    | Errors.Error msg ->
        print_error stderr msg;
        exit 2 in
  (* Print Clight *)
  if !flag_ctemp then ()
  else output_c_file astC path;
  ;;

let parse_command () =
    if (Array.length Sys.argv)=1 then
      print_string usage_msg
    else
      Arg.parse (Arg.align options) translate usage_msg;;

parse_command ();;
