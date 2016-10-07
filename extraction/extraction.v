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

Require AST.
Require Floats.
Require Compiler.

Extract Inductive bool => "bool" [ "true" "false" ].
Extract Inductive List.list => "list" [ "[]" "(::)" ].

(* Standard lib *)
Require Import ExtrOcamlBasic.
Require Import ExtrOcamlString.

(* AST *)
Extract Constant AST.ident_of_string =>
  "fun s -> Camlcoq.intern_string (Camlcoq.camlstring_of_coqstring s)".

(* Memory - work around an extraction bug. *)
Extraction NoInline Memory.Mem.valid_pointer.

(* Errors *)
Extraction Inline Errors.bind Errors.bind2.

(* Avoid name clashes *)
Extraction Blacklist List String Int.

(* Float *)

(* Compiler *)
Extract Constant Compiler.print_LustreT => "PrintLustreS.print_LustreT".
Extract Constant Compiler.print_LustreS => "PrintLustreS.print_LustreS".
Extract Constant Compiler.print_LustreR1 => "PrintLustreR.print_LustreR1".
Extract Constant Compiler.print_LustreR2 => "PrintLustreR.print_LustreR2".
Extract Constant Compiler.print_LustreR3 => "PrintLustreR.print_LustreR3".
Extract Constant Compiler.print_LustreF1 => "PrintLustreF.print_LustreF1".
Extract Constant Compiler.print_LustreF2 => "PrintLustreF.print_LustreF2".
Extract Constant Compiler.print_LustreE1 => "PrintLustreF.print_LustreE1".
Extract Constant Compiler.print_LustreE2 => "PrintLustreF.print_LustreE2".
Extract Constant Compiler.print_LustreD => "PrintLustreF.print_LustreD".
Extract Constant Compiler.print_LustreC => "PrintLustreF.print_LustreC".
Extract Constant Compiler.print_Ctemp => "PrintCtemp.print_if".
Extract Constant Compiler.print => "fun (f: 'a -> unit) (x: 'a) -> f x; x".

(* Cutting the dependancy to R. *)
Extract Inlined Constant Fcore_defs.F2R => "fun _ -> assert false".
Extract Inlined Constant Fappli_IEEE.FF2R => "fun _ -> assert false".
Extract Inlined Constant Fappli_IEEE.B2R => "fun _ -> assert false".
Extract Inlined Constant Fappli_IEEE.round_mode => "fun _ -> assert false".
Extract Inlined Constant Fcalc_bracket.inbetween_loc => "fun _ -> assert false".

Cd "extraction".
Recursive Extraction Library LustreSGen.
Recursive Extraction Library Compiler.
