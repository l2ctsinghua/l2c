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

open Arg
open Version

let usage_msg="\
USAGE:	l2c [options] <source.ast>

options:
	-save-temp:		Save temporary intermediate files
        -ctemp:                 Output ctemp source
	-target_dir <dir>:	Set the directory of target files to <dir>
	-o <file>:		Indicate the output file name
	-version:		Print version information
	-help:			Print this usage message

";;

let flag_save_temp = ref false;;
let flag_ctemp = ref false;;
let target_dir = ref "";;
let output_file = ref "";;

let options = [
    ("-save-temp", Set flag_save_temp, "Save temporary immediate files");
    ("-ctemp", Set flag_ctemp, "Output ctemp source");
    ("-target_dir", Set_string target_dir, "The directory of generated target files");
    ("-o", Set_string output_file, "Indicate the output file name");
    ("-version", Unit (fun()->(print_string version_msg)), "Print version information");
    ("-help", Unit (fun()->(print_string usage_msg)), "Print this usage message");
];;
