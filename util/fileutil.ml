(**
  val read_whole_channel : in_channel -> string = <fun>
**)
let read_whole_channel ic = 
    let buf=Buffer.create 4096 in
    try 
      while true do
        let line=input_line ic in
        Buffer.add_string buf line;
        Buffer.add_char buf '\n'
      done;
      failwith "read_whole_channel: out of infinite loop"
    with
      End_of_file -> Buffer.contents buf;;

(**
  val read_whole_file : string -> string = <fun>
**)
let read_whole_file fn=
    let ic=open_in fn in
    read_whole_channel ic;;
