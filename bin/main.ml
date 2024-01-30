open Printing
open Interp
open Parse
open Tree

(* Command Line Arguments *)
let usage_msg = "analyze [-test] <file1> -f <function-name>" ;;

let input_file = ref "" ;;
let fun_name = ref "" ;;
let testing = ref false ;;

let anon_fun filename = input_file := filename ;;

let speclist =
    [
        ("-f", Arg.Set_string fun_name, "Specify function to analyze");
        ("-test", Arg.Set testing, "Run tests");
    ] ;;

let () = Arg.parse speclist anon_fun usage_msg ;;

(* Running the analyzer *)
let analyze filename = 
    str_amem (abst_interp astmt amem_bot) ;;

let () =
    if !testing then Test.runtests () else
    Format.printf "%s\n\n" (analyze !input_file)
