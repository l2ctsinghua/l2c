(**
  val find_first : string -> string -> int -> int = <fun>
  # find_first "a(b,c)" "(,)" 0;;
  - : int = 1
**)
let find_first s t p =
    if p>=String.length s then p
    else(
      let m=ref (String.length s) in
      for i=0 to (String.length t - 1) do
        if String.contains_from s p t.[i] then
          m := min !m (String.index_from s p t.[i])
      done;
      !m
    );;

(** 
  val split : string -> char -> string list = <fun>
  # split "abc bcd ab" ' ';;
  - : string list = ["abc"; "bcd"; "ab"]
**)
let split s token = 
    let len=String.length s in
    let rec aux i j=
      if i>=len then [String.sub s j (i-j)]
      else if s.[i]=token then (String.sub s j (i-j))::aux (i+1) (i+1)
      else aux (i+1) j
    in
    aux 0 0;;

(**
  val find_first_not : string -> string -> int -> int = <fun>
  # find_first_not " \ta\nb\r" " \t\r\n" 0;;
  - : int = 2
**)
let find_first_not s t p=
    let len=String.length s in
    let rec aux i=
      if i<len && String.contains t s.[i] then aux (i+1)
      else i
    in
    if p>= String.length s then p
    else aux p;;

(**
  val find_last_not : string -> string -> int -> int = <fun>
  # find_last_not " \ta\nb\r" " \t\r\n" 5;;
  - : int = 4
**)
let find_last_not s t p=
    let rec aux i=
      if i>0 && String.contains t s.[i] then aux (i-1)
      else i
    in
    if p>= String.length s then p
    else aux p;;

(**
  val trim : string -> string = <fun>
  # trim " \ta\nb\r";;
  - : string = "a\nb" 
**)
let trim s=
    let len=String.length s in
    let i=find_first_not s " \t\r\n" 0 in 
    let j=find_last_not s " \t\r\n" (len-1) in
    if i>j then ""
    else String.sub s i (j-i+1);;

(**
  val next_matched : string -> char -> char -> int -> int = <fun>
  # next_matched "a(b,c),d" '(' ')' 2;;
  - : int = 5
**)
let next_matched s b e p =
    let rec aux i level=
      if level=0 then i-1
      else if s.[i]=b then aux (i+1) (level+1)
      else if s.[i]=e then aux (i+1) (level-1)
      else aux (i+1) level
    in
    if p >= String.length s then p
    else aux p 1;;

let rec concat_string_list l token=
    match l with
        [] -> ""
      | hd :: [] -> hd
      | hd :: tl -> (hd ^ token ^ (concat_string_list tl token))
    ;;

