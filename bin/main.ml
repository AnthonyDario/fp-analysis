open Interp
open Parse
open Tree

(* Command Line Arguments *)
let usage_msg = "analyze [-test] <file1> -f <function-name> -sf <spec-file>" ;;

let input_file = ref "" ;;
let fun_name = ref "" ;;
let testing = ref false ;;
let spec_file = ref "" ;;

let anon_fun filename = input_file := filename ;;

let speclist =
    [
        ("-f", Arg.Set_string fun_name, "Specify function to analyze");
        ("-sf", Arg.Set_string spec_file, "Specify variable range file");
        ("-test", Arg.Set testing, "Run tests");
    ] ;;

let () = Arg.parse speclist anon_fun usage_msg ;;


(* Running the analyzer *)
let analyze filename = 
    Format.printf "\nanalyzing %s in %s\n" !fun_name !input_file ;
    let amem = if !spec_file = "" 
               then amem_bot 
               else Spec.parse_spec_file !spec_file in
    let cstmt = transform (parse_file filename) !fun_name in
    let astmt = abst_stmt cstmt in
    (* printfile cstmt amem ; *)
    abst_interp astmt amem ;;

let write_file name mem =
    let oc = open_out name in
    Printf.fprintf oc "%s" (Printing.csv_amem mem);;

let () =
    if !testing 
    then Test.runtests () 
    else
        let mem = (analyze !input_file) in
        (* Format.printf "%s\n\n" (str_amem mem) ; *)
        write_file "out.csv" mem ;;
