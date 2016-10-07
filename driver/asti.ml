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

open Strutil
open Lop
open Lustre
open LustreS
open LustreV
open Camlcoq
open Options
open Datatypes
open BinPos
open BinInt
open BinNums

type position = {line : int; col : int };;
type 'a ast = {data : 'a; kids : 'a ast list; posf : position; post: position};;

let string_of_position pos=
    "(line = " ^ (string_of_int pos.line) ^ ", col = " ^ (string_of_int pos.col) ^ ")";;

let fail_ast from_pos to_pos msg=
    failwith (msg ^ ": " ^ (string_of_position from_pos) ^ " => " ^ (string_of_position to_pos) );;

let fail_lparser t msg=
    failwith (msg ^ ": " ^ (string_of_position t.posf) ^ " => " ^ (string_of_position t.post) );;

let parenthese_match_flag s =
    let len = String.length s in
    let matched_right_paranthese_pos = Array.create len (-1) in
    let rec aux s i circle matched_right_paranthese_pos left_paranthese_index =
        if i < circle then (
          if s.[i]='(' then (
             let left_paranthese_index1 = i :: left_paranthese_index in
             aux s (i+1) circle matched_right_paranthese_pos left_paranthese_index1 )
          else if s.[i]=')' then (
             matched_right_paranthese_pos.(List.hd left_paranthese_index) <- i;
             let left_paranthese_index1 = List.tl left_paranthese_index in
             aux s (i+1) circle matched_right_paranthese_pos left_paranthese_index1 )
          else aux s (i+1) circle matched_right_paranthese_pos left_paranthese_index )
        else matched_right_paranthese_pos
    in
    aux s 0 len matched_right_paranthese_pos [];;

let str_position_line s =
    let len = String.length s in
    let line_nums = Array.create len (-1) in
    let rec aux s i circle pre_line line_nums =
        if i < circle then (
          if s.[i]= '\n' then (
             line_nums.(i) <- pre_line;
             aux s (i + 1) circle (pre_line + 1) line_nums )
          else (
             line_nums.(i) <- pre_line;
             aux s (i + 1) circle pre_line line_nums )
          )
        else line_nums
    in
    aux s 0 len 1 line_nums;;

let str_position_col s =
    let len = String.length s in
    let col_nums = Array.create len (-1) in
    let rec aux s i circle pre_col col_nums =
        if i < circle then (
          if s.[i]= '\n' then (
             col_nums.(i) <- pre_col + 1;
             aux s (i + 1) circle 0 col_nums )
          else (
             let this_col = pre_col + 1 in
             col_nums.(i) <- this_col;
             aux s (i+1) circle this_col col_nums )
          )
        else col_nums
    in
    aux s 0 len 0 col_nums;;

let construct_common_ast s=
    let s_parenthese = parenthese_match_flag s in
    let line_nums = str_position_line s in
    let col_nums = str_position_col s in
    let len = String.length s in
    let rec aux i j s_parenthese =
      if i>j then []
      else (
        let k = find_first s "(,)" i in
        let str = trim (String.sub s i (k-i)) in
        if k>j || s.[k]=')' then (
          if str="" then []
          else {data=str; kids=[];posf={line = line_nums.(i); col = col_nums.(i)}; post={line = line_nums.(j); col = col_nums.(j)}}::[]
        )
        else if s.[k]='(' then (
          let l = s_parenthese.(k) in
          let m = find_first_not s " \t\n\r" (l+1) in
          if m<=j && s.[m]<>',' then
              fail_ast {line = line_nums.(k); col = col_nums.(k)}  {line = line_nums.(l); col = col_nums.(l)} "construct_common_ast: invalid input string"
          else
              {data=str; kids=aux (k+1) (l-1) s_parenthese;
                 posf={line = line_nums.(i); col = col_nums.(i)};
                 post={line = line_nums.(l); col = col_nums.(l)}} :: aux (m+1) j s_parenthese
        )
        else {data=str; kids=[];
                posf={line = line_nums.(i); col = col_nums.(i)};
                post={line = line_nums.(k); col = col_nums.(k)}} :: aux (k+1) j s_parenthese
      )
    in
    let trees=aux 0 (len-1) s_parenthese in
  List.hd trees;;

(** ********************* Convert to Lustre* AST *********************** **)

let get_node_kind s=
    if s = "node" then true else false;;

let is_str_atom s=
    if s="INT" || s="UINT" || s="SHORT" || s="USHORT" || s="CHAR" || s="FLOAT" ||  s="REAL" || s="BOOL" || s="ID" then true
    else false;;

let is_str_unop s=
    if s="unop_shortcast" || s="unop_intcast" || s="unop_floatcast" ||  s="unop_realcast"
      || s="unop_not" || s="unop_pos" || s="unop_neg" then true
    else false;;

let is_str_prefixop s=
    if s="short$" || s="int$" || s="float$" ||  s="real$" || s="not$" ||s="+$" || s="-$" then true
    else false;;

let str_to_unop s=
    if s="unop_shortcast" then Oshort
    else if s="unop_intcast" then Oint
    else if s="unop_floatcast" then Ofloat
    else if s="unop_realcast" then Oreal
    else if s="unop_not" then Onot
    else if s="unop_pos" then Opos
    else if s="unop_neg" then Oneg
    else failwith ("Invalid source: invalid unop: " ^ s);;

let str_to_prefixop s=
    if s="short$" then Oshort
    else if s="int$" then Oint
    else if s="float$" then Ofloat
    else if s="real$" then Oreal
    else if s="not$" then Onot
    else if s="+$" then Opos
    else if s="-$" then Oneg
    else failwith ("Invalid source: invalid prefixop: " ^ s);;

let is_str_binop s=
    if s="binop_add" || s="binop_subtract" || s="binop_multiply"
      || s="binop_divide" || s="binop_div" || s="binop_mod"
      || s="binop_and" || s="binop_or" || s="binop_xor"
      || s="binop_gt" || s="binop_lt" || s="binop_ge"
      || s="binop_le" || s="binop_eq" || s="binop_neq" then true
    else false;;

let str_to_binop s=
    if s="binop_add" then Oadd
    else if s="binop_subtract" then Osub
    else if s="binop_multiply" then Omul
    else if s="binop_divide" then Odivreal
    else if s="binop_div" then Odivint
    else if s="binop_mod" then Omod
    else if s="binop_and" then Oand
    else if s="binop_or" then Oor
    else if s="binop_xor" then Oxor
    else if s="binop_gt" then Ogt
    else if s="binop_lt" then Olt
    else if s="binop_ge" then Oge
    else if s="binop_le" then Ole
    else if s="binop_eq" then Oeq
    else if s="binop_neq" then One
    else failwith ("Invalid source: invalid binop: " ^ s);;

let is_str_prefixbinop s=
    if s="$+$" || s="$-$" || s="$*$"
      || s="$/$" || s="$div$" || s="$mod$"
      || s="$and$" || s="$or$" ||s="$xor$"
      || s="$=$" || s="$<>$" || s="$<$"
      ||s="$>$" || s="$>=$" || s="$<=$" then true
    else false;;

let str_to_prefixbinop s=
    if s="$+$" then Oadd
    else if s="$-$" then Osub
    else if s="$*$" then Omul
    else if s="$/$" then Odivreal
    else if s="$div$" then Odivint
    else if s="$mod$" then Omod
    else if s="$and$" then Oand
    else if s="$or$" then Oor
    else if s="$xor$" then Oxor
    else if s="$=$" then Oeq
    else if s="$<>$" then One
    else if s="$<$" then Olt
    else if s="$>$" then Ogt
    else if s="$>=$" then Oge
    else if s="$<=$" then Ole
    else failwith ("Invalid source: invalid prefixbinop: " ^ s);;

let get_boolL s=
    if s="true" then true else false;;

let get_intL s=
    try
      if s.[0]='+' then
        coqint_of_camlint (Int32.of_string (String.sub s 1 (String.length s-1)))
      else
        coqint_of_camlint (Int32.of_string s)
    with Failure msg ->
        failwith ("Invalid source: get_intL: " ^ s ^ ": " ^ msg);;

let get_realL s=
    coqfloat_of_camlfloat (float_of_string s);;

let get_floatL s=
    coqfloat32_of_camlfloat (float_of_string s);;

let camlint_of_coqcomparison = function
      Eq -> 0
    | Lt -> -1
    | Gt -> 1
  ;;

(** -------------------------------------------------- typedefs ------------------------------------------- **)

let rec typeL_compare t1 t2=
  let rec type_list_compare l1 l2=
    match (l1,l2) with
        (Fnil,Fnil) -> 0
      | (Fnil, Fcons _) -> -1
      | (Fcons _, Fnil) -> 1
      | (Fcons (id1, ty1, tl1), Fcons (id2, ty2, tl2)) ->
	   let b = camlint_of_coqcomparison (Pos.compare_cont id1 id2 Eq) in
           if (b <> 0) then b
           else
              let c = typeL_compare ty1 ty2 in
              (if (c <> 0) then c else type_list_compare tl1 tl2)
  in
  match (t1,t2) with
      (Tstruct (id1, lst1), Tstruct (id2, lst2)) -> type_list_compare lst1 lst2
    | (Tshort, Tshort) -> 0
    | (Tshort, _) -> -1
    | (Tushort, Tushort) -> 0
    | (Tushort, _) -> -1
    | (Tint, Tint) -> 0
    | (Tint, _) -> -1
    | (Tuint, Tuint) -> 0
    | (Tuint, _) -> -1
    | (Tbool, Tbool) -> 0
    | (Tbool, _) -> -1
    | (Tchar, Tchar) -> 0
    | (Tchar, _) -> -1
    | (Tfloat, Tfloat) -> 0
    | (Tfloat, _) -> -1
    | (Treal, Treal) -> 0
    | (Treal, _) -> -1
    | (Tarray (id1 ,t1, n1), Tarray (id2,t2, n2)) ->
       ( let x = typeL_compare t1 t2 in
         if x = 0 then camlint_of_coqcomparison (Z.compare n1 n2)
         else x )
    | (Tenum (id1,idL1), Tenum (id2,idL2)) ->
       camlint_of_coqcomparison (Pos.compare_cont id1 id2 Eq)
    | _ -> 1
  ;;

let typeblock = ref [];;
let typedecls = ref [];;

let rec find_ty ty tyl =
  match tyl with
  | [] -> None
  | (_,hd) :: tl ->
      let b = typeL_compare ty hd in
      if (b=0) then Some hd else find_ty ty tl;;

let type_auto_id = ref 0;;
let register_struct_typeL flist id=
    let ty = Tstruct (id, flist) in
    match find_ty ty !typedecls with
    | None ->
      let id =
        if extern_atom id = "acg_s" then (
          type_auto_id := !type_auto_id + 1;
          let acg_s_id = intern_string ("acg_s" ^ (string_of_int !type_auto_id)) in
          ignore (intern_string ("acg_comp_acg_s" ^ (string_of_int !type_auto_id)) );
          acg_s_id
        )
        else id
      in
      let ty = Tstruct (id, flist) in
      typedecls := (id, ty) :: !typedecls;
      ty
    | Some t -> t ;;

let type_auto_id_arr = ref 0;;
let register_array_typeL id ele_ty n=
    let ty = Tarray (id, ele_ty, n) in
    match find_ty ty !typedecls with
    | None ->
      let id =
        if extern_atom id = "acg_arr" then (
          type_auto_id_arr := !type_auto_id_arr + 1;
          let acg_arr_id = intern_string ("acg_arr" ^ (string_of_int !type_auto_id_arr)) in
          ignore (intern_string ("acg_comp_acg_arr" ^ (string_of_int !type_auto_id_arr)) );
          acg_arr_id
        )
        else id
      in
      let ty = Tarray (id, ele_ty, n) in
      typedecls := (id, ty) :: !typedecls;
      ty
    | Some t -> t;;

module Map_ident = Map.Make (
  struct
    type t = positive
    let compare x y = camlint_of_coqcomparison (Pos.compare_cont x y Eq)
  end);;
let atomL_map = ref Map_ident.empty;;
let nodeL_map = ref Map_ident.empty;;
let constL_map = ref Map_ident.empty;;

let calc_array_len t=
    if t.data = "ID" then (
      if (List.length t.kids) <> 2 then fail_lparser t ("Invalid source: calc_array_len: 'ID' should have 2 kids");
      let id = intern_string (List.hd t.kids).data in
      Map_ident.find id !constL_map
    )
    else get_intL (List.hd t.kids).data;;

let get_data t = intern_string t.data;;

let rec convert_typeL t typename=
    if t.data = "bool" then Tbool
    else if t.data = "short" then Tshort
    else if t.data = "ushort" then Tushort
    else if t.data = "int" then Tint
    else if t.data = "uint" then Tuint
    else if t.data = "float" then Tfloat
    else if t.data = "real" then Treal
    else if t.data = "char" then Tchar
    else if t.data = "construct" then (
      if typename = "" then (
         let id = intern_string ("acg_s") in
         let flist = get_fieldlistL t.kids in
         register_struct_typeL flist id )
      else (
        let id = intern_string typename in
        ignore (intern_string ("acg_comp_" ^ typename));
        let flist = get_fieldlistL t.kids in
        register_struct_typeL flist id
      )
    )
    else if t.data = "construct_enum" then (
      let id = intern_string  typename in
      let idL = List.map get_data t.kids in
      Tenum(id,idL)
    )
    else if t.data = "array" then (
      if (List.length t.kids) <> 2 then fail_lparser t ("Invalid source: get_typeL: 'array' should have 2 kids");
      if typename = "" then (
         let id = intern_string ("acg_arr") in
         let ty = convert_anonymous_typeL (List.hd t.kids) in
         let n = calc_array_len (List.nth t.kids 1) in
         register_array_typeL id ty n )
      else (
         let id = intern_string typename in
         ignore (intern_string ("acg_comp_" ^ typename));
         let ty = convert_anonymous_typeL (List.hd t.kids) in
         let n = calc_array_len (List.nth t.kids 1) in
         register_array_typeL id ty n)
    )
    else if t.data = "typename" then (
      let tyname = (List.hd t.kids).data in
      construct_typename t tyname
    )
    else fail_lparser t ("Invalid source: get_typeL: invalid type '" ^ t.data ^ "'")

  and get_fieldlistL lst=
    match lst with
      [] -> Fnil
    | hd :: tl ->
      if List.length hd.kids <> 2 then fail_lparser hd ("Invalid source: get_fieldL: 'field' should have 2 kids");
      let id = intern_string (List.hd hd.kids).data in
      let head = convert_anonymous_typeL (List.nth hd.kids 1) in
      let tail = get_fieldlistL tl in
      Fcons (id, head, tail)

  and construct_typename t typename=
    let rec find_typeblock lst=
      match lst with
        [] -> fail_lparser t ("Invalid source: construct_typename: typename '" ^ typename ^ "' is not declared");
      | hd :: tl ->
          if (List.length hd.kids) <> 2 then fail_lparser hd ("Invalid source: construct_typename: 'type' should have 2 kids");
          if (List.hd hd.kids).data = typename then convert_typeL (List.nth hd.kids 1) typename
          else find_typeblock tl
    in
    find_typeblock !typeblock

  and convert_anonymous_typeL t=
    convert_typeL t "";;

(** -------------------------------------------------- constants ------------------------------------------- **)

let rec gather_ast_field_names slist=
    match slist with
      [] -> []
    | hd :: tl ->
      if List.length hd.kids <> 2 then fail_lparser hd "Invalid source: gather_ast_field_names: label_expr should have 2 kids"
      else (intern_string (List.hd hd.kids).data) :: gather_ast_field_names tl
    ;;

let rec convert_constL t=
    if t.data = "construct" then convert_construct_constL t
    else if t.data = "construct_array" then
        let cl = convert_list_constL t.kids in
        ConstructConstL cl
    else if t.data = "ID" then
        let id = intern_string (List.hd t.kids).data in
        let ty = convert_anonymous_typeL (List.nth t.kids 1) in
        match ty with
          Tenum (idt , idl) -> match_id_with_enumidl_constL id idl ty
        | _ -> ID (id , ty)
    else (
      if List.length t.kids <> 1 then fail_lparser t ("Invalid source: convert_constL: '" ^ t.data ^ "' should have 1 kid");
      let s=(List.hd t.kids).data in
      if t.data="BOOL" then BoolConstL (get_boolL s)
      else if t.data="CHAR" then CharConstL (get_intL s)
      else if t.data="SHORT" then ShortConstL (get_intL s)
      else if t.data="USHORT" then UshortConstL (get_intL s)
      else if t.data="INT" then IntConstL (get_intL s)
      else if t.data="UINT" then UintConstL (get_intL s)
      else if t.data="FLOAT" then FloatConstL (get_realL s)
      else if t.data="REAL" then RealConstL (get_realL s)
      else fail_lparser t ("Invalid source: invalid const: " ^ t.data)
    )
  and convert_construct_constL t=
    let rec construct_const kids =
      match kids with
      |  []-> ConstNilL
      | hd :: tl -> ConstConL (convert_constL (List.nth hd.kids 1), construct_const tl)
    in
    ConstructConstL (construct_const t.kids)

  and match_id_with_enumidl_constL id idl ty=
    match idl with
      [] -> ID (id , ty)
    | hd::tl -> if hd = id then EnumConstL (id , ty) else match_id_with_enumidl_constL id tl ty

  and convert_list_constL cl=
    match cl with
      [] -> ConstNilL
    | hd :: tl -> ConstConL (convert_constL hd, convert_list_constL tl)
    ;;

(** ----------------------------------------------------- expressions ----------------------------------------- **)

let convert_patternL t=
    if t.data = "pattern_any" then PatternAny
    else if t.data="ID" then (
      if List.length t.kids <> 2 then fail_lparser t ("Invalid source: convert_patternL syntax => 'ID' should have 2 kids");
      PatternID (intern_string (List.hd t.kids).data, convert_anonymous_typeL (List.nth t.kids 1))
    )
    else (
      if List.length t.kids <> 1 then fail_lparser t ("Invalid source: convert_patternL syntax => '" ^ t.data ^ "' should have 1 kid");
      let s=(List.hd t.kids).data in
      if t.data="BOOL" then PatternBool (get_boolL s)
      else if t.data="CHAR" then PatternChar (get_intL s)
      else if t.data="INT" then PatternInt ((get_intL s), Tint)
      else if t.data="UINT" then PatternInt ((get_intL s), Tuint)
      else if t.data="SHORT" then PatternInt ((get_intL s), Tshort)
      else if t.data="USHORT" then PatternInt ((get_intL s), Tushort)
      else fail_lparser t ("Invalid source: invalid pattern: " ^ t.data)
    );;

let call = ref 0;;

let convert_suboperatorL t=
   if t.data = "prefix" then(
      if is_str_prefixbinop (List.hd t.kids).data then(
         let binop = str_to_prefixbinop (List.hd t.kids).data in
      	 Coq_prefixL_binary binop
      )
      else if is_str_prefixop (List.hd t.kids).data then (
         let unop = str_to_prefixop (List.hd t.kids).data in
         Coq_prefixL_unary unop
      )
      else(
         let id = intern_string (List.hd t.kids).data in
         let node = (Map_ident.find id !nodeL_map) in
         match node with
         | Nodehandler (NodehandlerL (id, rt, pt, kind, _)) ->
             if kind then (
                 call := !call + 1;
                 let context = (intern_string ("acg_context" ^ (string_of_int !call))) in
                 (Nodehandler (NodehandlerL (id, rt, pt, kind, context)))
             )
             else (
                 let context = (intern_string ("acg_context" )) in
                 (Nodehandler (NodehandlerL (id, rt, pt, kind, context)))
             )
         | _ -> fail_lparser t "invalid source: convert_exprS: Nodehandler";
      )
   )
   else fail_lparser t ("Invalid source: convert_suboperatorL: invalid type '" ^ t.data ^ "'")
    ;;

let convert_iterator_operationL t =
    if t.data = "highorder_map" then Omap
    else if t.data = "highorder_red" then Ored
    else if t.data = "highorder_fill" then Ofill
    else if t.data = "highorder_fillred" then Ofillred
    else fail_lparser t ("Invalid source: convert_iterator_operationL: invalid type '" ^ t.data ^ "'")
   ;;

let rec convert_atomL t=
   if t.data="ID" then (
      if List.length t.kids <> 3 then fail_lparser t ("Invalid source: convert_atomL syntax => 'ID' should have 3 kids");
      let id = intern_string (List.hd t.kids).data in
      let ty = convert_anonymous_typeL (List.nth t.kids 1) in
      match ty with
        Tenum (_ , idl) -> match_id_with_enumidl_atomL t id idl ty
      | _ ->
      	try
          let (id, ty, ck) = Map_ident.find id !atomL_map in
          EvarS (id, ty, ck)
        with Not_found ->
          fail_lparser t ("Invalid source: convert_atomL: var '" ^ (extern_atom id) ^ "' not declared");
   )
   else (
      if List.length t.kids <> 1 then fail_lparser t ("Invalid source: convert_atomL: '" ^ t.data ^ "' should have 1 kid");
      let s=(List.hd t.kids).data in
      if t.data="BOOL" then EconstS (Cbool (get_boolL s), Tbool, global_clock)
      else if t.data="CHAR" then EconstS (Cint (get_intL s),Tchar, global_clock)
      else if t.data="SHORT" then EconstS (Cint (get_intL s),Tshort, global_clock)
      else if t.data="USHORT" then EconstS (Cint (get_intL s),Tushort, global_clock)
      else if t.data="INT" then EconstS (Cint (get_intL s),Tint, global_clock)
      else if t.data="UINT" then EconstS (Cint (get_intL s),Tuint, global_clock)
      else if t.data="FLOAT" then EconstS (Csingle (get_floatL s),Tfloat, global_clock)
      else if t.data="REAL" then EconstS (Cfloat (get_realL s),Treal, global_clock)
      else fail_lparser t ("Invalid source: invalid atom: " ^ t.data)
    )
  and match_id_with_enumidl_atomL t id idl ty=
    match idl with
      hd::tl ->
      if hd = id then
         EvarS (id, ty, global_clock)
      else match_id_with_enumidl_atomL t id tl ty
    | [] ->
      try
         let (id, ty, ck) = Map_ident.find id !atomL_map in
         EvarS (id, ty, ck)
      with Not_found ->
         fail_lparser t ("Invalid source: convert_atomL: var '" ^ (extern_atom id) ^ "' not declared")   ;;

let tempo_add_when t =
  if t.kids <> [] then(
    let id = (List.hd t.kids).data in
    (false,intern_string id) )
  else(
    let id = t.data in
    (true,intern_string id))
  ;;

let convert_type_and_clock t1 t2 =
  let t = convert_anonymous_typeL t1 in
  let c = (List.map tempo_add_when t2.kids) @ global_clock in
  (t,c)
  ;;

let rec convert_types_and_clocks t1 t2 =
  convert_tcls t1.kids t2.kids
  and convert_tcls types clocks =
    match types , clocks with
    | [],[] -> []
    | ty :: tyl , ck :: ckl ->
        let (t, c) = convert_type_and_clock ty ck in
        ( (t,c))::(convert_tcls tyl ckl)
    | _ , _ -> failwith ("length (type) != length (clock) ")
  ;;

let pre = ref 0;;
let rec pre_mem_vars t =
  pre_vars t.kids
  and pre_vars types =
    match types with
    | [] -> []
    | ty :: tyl ->
        pre := !pre + 1;
        let preid = (intern_string ("acg_pre" ^ (string_of_int !pre))) in
        preid :: (pre_vars tyl)
  ;;

let fby = ref 0;;
let rec fby_mem_struct_vars t n =
  fby_structs t.kids n
  and fby_structs types n =
    match types with
    | [] -> []
    | ty :: tyl ->
         fby := !fby + 1;
         let sid = (intern_string ("acg_fby" ^ (string_of_int !fby))) in
         let idx = (intern_string "idx") in
         let items = (intern_string "items") in
         let t = convert_anonymous_typeL ty in
         let items_ty = register_array_typeL (intern_string "acg_arr") t n in
         let fl = Fcons (idx, Tint,(Fcons (items, items_ty, Fnil))) in
         let sty = register_struct_typeL fl (intern_string ("acg_s")) in
         ((sty,sid)):: (fby_structs tyl n)
  ;;

let rec convert_exprS t=
     if t.data = "list_expr" then (
       let exprlist = convert_expr_listS t.kids in
       ListExprS exprlist)

     else if t.data = "apply_expr" then (
           if (List.length t.kids) < 2 then fail_lparser t "invalid source: convert_exprS: too few argument for applyexpr.";
           let tcl = convert_types_and_clocks (List.hd t.kids) (List.nth t.kids 1) in
           let tt = (List.nth t.kids 2) in
           let tl = List.tl (List.tl (List.tl t.kids)) in
           if tt.data = "high_order" then
                let iterator = convert_iterator_operationL(List.hd tt.kids) in
                let op = convert_suboperatorL (List.nth tt.kids 1) in
                let size = get_intL (List.hd (List.nth tt.kids 2).kids).data in
		let args = convert_expr_listS tl in
	        ApplyExprS (Coq_iteratorS(iterator,op,size),args,tcl)
          else if tt.data ="prefix" then (
	        let ttt = List.hd tt.kids in
		if is_str_prefixbinop ttt.data then
                   let prefixbion = str_to_prefixbinop ttt.data in
                   let args = convert_expr_listS tl in
                   ApplyExprS (Coq_suboperatorS(Coq_prefixL_binary(prefixbion)), args,tcl)
                else if is_str_prefixop ttt.data then
                   let prefixop = str_to_prefixop ttt.data in
                   let args = convert_expr_listS tl in
                   ApplyExprS (Coq_suboperatorS(Coq_prefixL_unary(prefixop)), args,tcl)
                else (
		   let id = intern_string (List.hd tt.kids).data in
                   let args = convert_expr_listS tl in

                   let node = (Map_ident.find id !nodeL_map) in
		   match node with
                   | Nodehandler (NodehandlerL (id, rt, pt, kind, _)) ->
                    if kind then (
                        call := !call + 1;
                        let context = (intern_string ("acg_context" ^ (string_of_int !call))) in
                        ApplyExprS (Coq_suboperatorS (Nodehandler (NodehandlerL (id, rt, pt, kind, context))), args,tcl);
                    )
                    else (
                        let context = (intern_string ("acg_context" )) in
                        ApplyExprS (Coq_suboperatorS(Nodehandler (NodehandlerL (id, rt, pt, kind, context))), args,tcl);
		    )
                   | _ -> fail_lparser t "invalid source: convert_exprS: Nodehandler";

		)
              )
          else fail_lparser t ("error: convert_exprS: ApplyExprS = "^(List.hd t.kids).data^" = invalid expression type")
      )

    else if t.data = "array_index" then (
      if (List.length t.kids) <> 4 then fail_lparser t "invalid source: convert_exprS: array_index should have 2 kids.";
      let tcl = convert_type_and_clock (List.hd t.kids) (List.nth t.kids 1) in
      let expr = convert_exprS (List.nth t.kids 2) in
      let index = get_intL (List.hd (List.nth t.kids 3).kids).data in
      EarrayaccS (expr, index, tcl)
    )
    else if t.data = "construct_array" then (
      if (List.length t.kids) = 0 then fail_lparser t "invalid source: construct_arrayS: empty list expression.";
      let tcl = convert_type_and_clock (List.hd t.kids) (List.nth t.kids 1) in
      let arglist = convert_expr_listS (List.tl (List.tl t.kids)) in
      EarraydiffS (arglist,tcl)
    )
    else if t.data = "dynamic_project" then (
      if (List.length t.kids) = 0 then fail_lparser t "invalid source: dynamic_exprS: empty list expression.";
      let tcl = convert_type_and_clock (List.hd t.kids) (List.nth t.kids 1) in
      let expr = convert_exprS (List.nth t.kids 2) in
      let arglist = convert_expr_listS (List.nth t.kids 3).kids in
      let expr1 = convert_exprS (List.nth t.kids 4) in
      EarrayprojS (expr,arglist,expr1,tcl)
    )
    else if t.data = "mixed_constructor" then(
      if (List.length t.kids) <> 5 then fail_lparser t "invalid source: mixed_constructorS: tree sub expression.";
      let tcl = convert_type_and_clock (List.hd t.kids) (List.nth t.kids 1) in
      let expr = convert_exprS (List.nth t.kids 2) in
      let index = convert_label_index_listS (List.nth t.kids 3).kids in
      let expr1 = convert_exprS (List.nth t.kids 4) in
      EmixS(expr, index,expr1,tcl)
    )
    else if t.data = "array_slice" then (
      if (List.length t.kids) <> 5 then fail_lparser t "invalid source: array_slice: tree sub expression.";
      let tcl = convert_type_and_clock (List.hd t.kids) (List.nth t.kids 1) in
      let e1 = convert_exprS (List.nth t.kids 2) in
      let x = convert_exprS (List.nth t.kids 3) in
      let y = convert_exprS (List.nth t.kids 4) in
      match (x,y) with
         (EconstS (Cint i, _ , _),EconstS (Cint j, _, _)) ->
                     EarraysliceS (e1, i, j, tcl)
        | _ -> fail_lparser t "invalid source: convert_exprS: array_slice error.";
    )
    else if t.data = "array_dim" then (
      if (List.length t.kids) <> 4 then fail_lparser t "invalid source: convert_exprS: array_dim should have 2 kids.";
      let tcl = convert_types_and_clocks (List.hd t.kids) (List.nth t.kids 1) in
      let expr = convert_exprS (List.nth t.kids 2) in
      let num = get_intL (List.hd (List.nth t.kids 3).kids).data in
      EarraydefS (expr, num, tcl)
    )
    else if t.data = "field_access" then (
      if (List.length t.kids) <> 4 then fail_lparser t "invalid source: convert_exprS: field_access should have 2 kids.";
      let tcl = convert_type_and_clock (List.hd t.kids) (List.nth t.kids 1) in
      let expr = convert_exprS (List.nth t.kids 2) in
      let fid = intern_string (List.nth t.kids 3).data in
      EfieldS (expr, fid, tcl)
    )
    else if t.data = "boolred" then (
      if (List.length t.kids) <> 5 then fail_lparser t "invalid source: convert_exprS: boolred should have 3 kids.";
      let tcl = convert_type_and_clock (List.hd t.kids) (List.nth t.kids 1) in
      let i = get_intL (List.hd (List.nth t.kids 2).kids).data in
      let j = get_intL (List.hd (List.nth t.kids 3).kids).data in
      let expr = convert_exprS (List.nth t.kids 4) in
      EboolredS (i, j, expr, tcl)
    )
    else if t.data = "diese" then (
      if (List.length t.kids) <> 3 then fail_lparser t "invalid source: convert_exprS: diese should have 1 kids.";
      let tcl = convert_type_and_clock (List.hd t.kids) (List.nth t.kids 1) in
      let expr = convert_exprS (List.nth t.kids 2) in
      EdieseS (expr, tcl)
    )
    else if t.data = "nor" then (
      if (List.length t.kids) <> 3 then fail_lparser t "invalid source: convert_exprS: nor should have 1 kids.";
      let tcl = convert_type_and_clock (List.hd t.kids) (List.nth t.kids 1) in
      let expr = convert_exprS (List.nth t.kids 2) in
      EnorS (expr, tcl)
    )
    else if t.data = "if_expr" then (
      if (List.length t.kids) <> 5 then fail_lparser t "invalid source: convert_exprS: if_expr should have 3 kids.";
      let tcl = convert_types_and_clocks (List.hd t.kids) (List.nth t.kids 1) in
      let cond = convert_exprS (List.nth t.kids 2) and
          e1 = convert_exprS (List.nth t.kids 3) and
          e2 = convert_exprS (List.nth t.kids 4) in
      EifS (cond, e1, e2, tcl)
    )
    else if t.data = "switch_expr" then (
      if (List.length t.kids) < 2 then fail_lparser t "invalid source: convert_exprS: too few kids for switch_expr.";
      let tcl = convert_types_and_clocks (List.hd t.kids) (List.nth t.kids 1) in
      let cond = convert_exprS (List.nth t.kids 2) in
      let lst = convert_pattern_listS (List.tl (List.tl (List.tl t.kids))) in
      EcaseS (cond, lst, tcl)
    )
    else if t.data = "construct" then (
      convert_expr_structS t
    )
    else if is_str_atom t.data then (
      convert_atomL t
    )
    else if (String.length t.data) > 6 && (String.sub t.data 0 6)="tempo_" then (
      convert_tempo_exprS t
    )
    else if is_str_binop t.data then (
      let binop = str_to_binop t.data in
      if (List.length t.kids) <> 4 then fail_lparser t "invalid source: convert_exprS: binop oprands count <> 2.";
      let tcl = convert_type_and_clock (List.hd t.kids) (List.nth t.kids 1) in
      let left = convert_exprS (List.nth t.kids 2) and
          right = convert_exprS (List.nth t.kids 3) in
      EbinopS (binop, left, right, tcl)
    )
    else if is_str_unop t.data then (
      let unop = str_to_unop t.data in
      if (List.length t.kids) <> 3 then fail_lparser t "invalid source: convert_exprS: unop oprands count <> 1.";
      let tcl = convert_type_and_clock (List.hd t.kids) (List.nth t.kids 1) in
      let e = convert_exprS (List.nth t.kids 2) in
      EunopS (unop, e, tcl)
    )
   else fail_lparser t ("Invalid source: convert_exprS: invalid expression type '" ^ t.data ^ "'")

  and convert_expr_listS lst=
    match lst with
      [] -> Enil
    | hd :: tl -> Econs ((convert_exprS hd), (convert_expr_listS tl))

  and convert_label_index_listS label_index=
    match label_index with
      [] -> Lnil
    | hd :: tl ->
        if hd.data = "struct_item" then
	  ( let id = (List.hd hd.kids).data in
          (LconsLabelS (intern_string id, convert_label_index_listS tl)))
        else
          (let id = convert_exprS hd in
          (LconsIndexS (id,convert_label_index_listS tl)))

  and convert_tempo_exprS t=
    if t.data="tempo_pre" then (
      if List.length t.kids <> 3 then fail_lparser t "invalid source: convert_exprS: pre tempo expression should have 1 kid.";
      let tcl = convert_types_and_clocks (List.hd t.kids) (List.nth t.kids 1) in
      let e = convert_exprS (List.nth t.kids 2) in
      let idl = pre_mem_vars (List.hd t.kids) in
      EpreS (idl, e, tcl)
    )
    else if t.data="tempo_arrow" then (
      if List.length t.kids <> 4 then fail_lparser t "invalid source: convert_exprS: arrow tempo expression should have 2 kids.";
      let tcl = convert_types_and_clocks (List.hd t.kids) (List.nth t.kids 1) in
      let e1 = convert_exprS (List.nth t.kids 2) and
          e2 = convert_exprS (List.nth t.kids 3) in
      EarrowS (e1, e2, tcl)
    )
    else if t.data="tempo_when" then (
      if List.length t.kids <> 4 then fail_lparser t "invalid source: convert_exprS: when tempo expression should have 2 kids.";
        let tcl = convert_types_and_clocks (List.hd t.kids) (List.nth t.kids 1) in
        let e = convert_exprS (List.nth t.kids 2) and
	clocklist = List.map tempo_add_when ((List.nth t.kids 3).kids) in
	EwhenS (e, (clocklist @ global_clock), tcl)
    )
    else if t.data="tempo_current" then (
      if List.length t.kids <> 3 then fail_lparser t "invalid source: convert_exprS: current tempo expression should have 1 kids.";
        let tcl = convert_types_and_clocks (List.hd t.kids) (List.nth t.kids 1) in
        let e = convert_exprS (List.nth t.kids 2) in
	EcurrentS (e, tcl)
    )
    else if t.data="tempo_fby" then (
      if List.length t.kids <> 5 then fail_lparser t "invalid source: convert_exprS: fby tempo expression should have 3 kids.";
      let tcl = convert_types_and_clocks (List.hd t.kids) (List.nth t.kids 1) in
      let e1 = convert_expr_listS (List.nth t.kids 2).kids in
      let x =  convert_exprS (List.nth t.kids 3) in
      let e2 = convert_expr_listS (List.nth t.kids 4).kids in
      match x with
          EconstS (Cint n, _, _) ->
          let tidl = fby_mem_struct_vars (List.hd t.kids) n in
          EfbyS (tidl, e1, n, e2, tcl)
        | _ -> fail_lparser t ("invalid source: convert_tempo_exprS: the 2nd operand of tempo_fby must be integer const")
    )
    else fail_lparser t ("invalid source: convert_exprS: invalid tempo expression: " ^ t.data)

  and convert_expr_structS t=
    let rec map_field slist id=
      match slist with
          [] -> fail_lparser t ("Internal Error: find_field: field '" ^ (extern_atom id) ^ "' not found")
        | hd :: tl -> if List.length hd.kids <> 2 then
                        fail_lparser t "Internal error: find_field: label_expr should have been checked by gather_fields";
                      if (intern_string (List.hd hd.kids).data) = id then convert_exprS (List.nth hd.kids 1)
                      else map_field tl id
    in
    let rec construct_fields slist flist=
      match flist with
          Fnil -> Enil
        | Fcons (id, ty, tl) -> Econs ((map_field slist id), construct_fields slist tl)
    in
    let tcl = convert_type_and_clock (List.hd t.kids) (List.nth t.kids 1) in
    let fields = List.tl (List.tl t.kids) in
    let ty = convert_anonymous_typeL (List.hd t.kids) in
    match ty with
        Tstruct (id, flist) -> let c = construct_fields fields flist in
                               EconstructS (c, tcl)
      | _ -> fail_lparser t ("Invalid source: convert_constructL: struct type with fields [" ^
                            (concat_string_list (List.map extern_atom (gather_ast_field_names fields)) ", ") ^ "] not found")

  and convert_pattern_listS lst=
    match lst with
        [] -> PatternNilS
      | hd :: tl -> if List.length hd.kids <> 2 then
                      fail_lparser hd "invalid source: convert_pattern_listS: pattern expression should have 2 kids.";
                    PatternConS (convert_patternL (List.hd hd.kids), convert_exprS (List.nth hd.kids 1), convert_pattern_listS tl)
;;


(** ------------------------------------------------------ nodes ---------------------------------------------------- **)

let convert_lhs_idL t=
    if t.data <> "ID" then fail_lparser t "invalid source: convert_lhs_idL: 'lhs' must be 'ID' or 'anonymous_id'";
    let (id, ty, ck) = Map_ident.find (intern_string (List.hd t.kids).data) !atomL_map in
    LhsID (id, ty, ck);;

let rec convert_lhsL lst=
    match lst with
        [] -> []
      | hd :: tl -> (convert_lhs_idL hd) :: (convert_lhsL tl);;

let convert_equationS t=
    if t.data = "=" then (
      if (List.length t.kids) <> 2 then fail_lparser t "invalid source: convert_equationS: '=' has 2 kids";
      let lhs = convert_lhsL (List.hd t.kids).kids in
      let expr = convert_exprS (List.nth t.kids 1) in
      EquationS (lhs, expr)
    )
    else fail_lparser t "Invalid source: convert_equationS: '=' not found";;

let rec convert_equationListS lst=
    List.map convert_equationS lst;;

let convert_varL ty clock t=
    let id = intern_string t.data in
    atomL_map := Map_ident.add id (id, ty, clock) !atomL_map;
    if t.kids = [] then
      VarDeclL (id, ty, clock)
    else (
      if ((List.hd t.kids).data) <> "clock" then fail_lparser t "invalid source: convert_varL: missing (clock)";
      ignore (intern_string ("acg_" ^ t.data ^ "_init1" ));
      ignore (intern_string ("acg_" ^ t.data ^ "_init" ));
      ClockVarDeclL (id, ty, clock)
    );;

let add_whenck t idl =
    let id = intern_string (List.hd t.kids).data in
    id::idl;;

let convert_var_declL t=
  let n = List.length t.kids in
  if n<2 then fail_lparser t "Invalid source: convert_var_declL: kids num < 2"
  else (
    let vars = (List.hd t.kids).kids in
    if (List.length vars) = 0 then fail_lparser t "Invalid source: convert_var_declL: var num = 0";
    let ty = convert_anonymous_typeL (List.nth t.kids 1) in
    let clock = if n = 2 then global_clock
    else List.append (List.map tempo_add_when (((List.hd (List.nth t.kids 2).kids) ).kids)) global_clock in
    List.map (convert_varL ty clock) vars
    );;

let convert_paramsL t=
  let vardecls = (List.map convert_var_declL t.kids) in
  List.concat vardecls
;;

let convert_bodyS t=
    if List.length t.kids = 0 then ([],[])
    else if (List.hd t.kids).data <> "localvars" then
      ([], convert_equationListS t.kids)
    else(
      let vars = convert_paramsL (List.hd t.kids) in
      let eqs = convert_equationListS (List.tl t.kids) in
      (vars, eqs)
    );;

let analyze_nodehandler fid params returns kind =
    let find_var_typeclock var=
      match var with
        VarDeclL (_, ty, _) -> ty
      | ClockVarDeclL (_, ty, _) -> ty
    in
    Nodehandler (NodehandlerL (fid, List.map find_var_typeclock returns, List.map find_var_typeclock params, kind, null_id))
;;

let get_nodekindL_str kind=
    if kind then "node" else "function";;

let convert_nodeS t=
    if List.length t.kids = 5 then (
      let kind = get_node_kind (List.hd t.kids).data in
      let id = intern_string (List.nth t.kids 1).data in
      let params = convert_paramsL (List.nth t.kids 2) in
      let returns = convert_paramsL (List.nth t.kids 3) in
      let (locals, body) = convert_bodyS (List.nth t.kids 4) in
      NodeS (kind, id, params, returns,locals, body)
    )
   else fail_lparser t "Invalid source: convert_nodeS: 'node' has 5 kids"
;;
(** ---------------------------------------------------- Global declares ---------------------------------------------- **)

let convert_const_declL t=
    if List.length t.kids = 3 then(
      let id = intern_string (List.hd t.kids).data in
      let ty = convert_anonymous_typeL (List.nth t.kids 1) in
      let value = convert_constL (List.nth t.kids 2) in
      atomL_map := Map_ident.add id (id, ty, global_clock) !atomL_map;
      ( match value with
          IntConstL i -> constL_map := Map_ident.add id i !constL_map;
        | _ -> ()
      );
      ConstDeclL(id, ty, value)
    )
  else fail_lparser t "Invalid source: convert_const_declL: const_decl must have 2 kids"
;;

let rec gather_const_blockS lst=
    match lst with
      [] -> []
    | hd :: tl ->
      let l = if hd.data = "const_block" then (List.map convert_const_declL hd.kids) else [] in
      l @ gather_const_blockS tl;;

let rec gather_node_blockS lst=
    match lst with
      [] -> []
    | hd :: tl ->
      if hd.data = "node" then (convert_nodeS hd) :: (gather_node_blockS tl)
      else gather_node_blockS tl;;

let declare_nodes t=
    if t.data = "node" then (
      if List.length t.kids == 5 then (
        let kind = get_node_kind (List.hd t.kids).data in
        let id = intern_string (List.nth t.kids 1).data in
        ignore (intern_string ("inC_" ^ (List.nth t.kids 1).data));
        ignore (intern_string ("outC_" ^ (List.nth t.kids 1).data));
        ignore (intern_string ((List.nth t.kids 1).data ^"_reset"));
        let params = convert_paramsL (List.nth t.kids 2) in
        let returns = convert_paramsL (List.nth t.kids 3) in
        nodeL_map := Map_ident.add id (analyze_nodehandler id params returns kind) !nodeL_map;
      ) else
   	fail_lparser t "Invalid source: convert_nodeS: 'node' has 5 kids"
   );;

let first_pass_scan t=
    let gather_type_blocks t=
      if t.data = "type_block" then( typeblock := !typeblock @ t.kids;)
    in
    let register_types t=
      if List.length t.kids = 2 then ignore (convert_typeL (List.nth t.kids 1) (List.hd t.kids).data)
      else fail_lparser t "Invalid source:type  2 kids"
    in
    List.iter gather_type_blocks t.kids;
    List.iter register_types !typeblock;
    ignore (gather_const_blockS t.kids);
    List.iter declare_nodes t.kids;;

let convert_programS t main=
    first_pass_scan t;
    let consts = gather_const_blockS t.kids in
    let nodes = gather_node_blockS t.kids in
    { type_blockS = List.rev !typedecls;
      const_blockS = consts;
      node_blockS = nodes;
      node_mainS = intern_string main};;

let convert_top_level t=
    if List.length t.kids != 2 then fail_lparser t "Invalid source: TopLevel must have 2 kids"
    else (
      let main = (List.hd (List.hd t.kids).kids).data in
      let prog = convert_programS (List.nth t.kids 1) main in
      (intern_string main, prog)
    );;

let construct_L_ast s=
    let t=construct_common_ast s in
    convert_top_level t;;
