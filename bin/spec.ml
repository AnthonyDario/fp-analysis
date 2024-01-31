(* Parse a specification file for the tool 
 * The file gives a variable and its range of values on a new line
 * Example:
 *
 * x = [ -0.1 ; 9.3 ]
 * y = [ -8.2 ; -1.2]
 *)

open In_channel
open String
open Str
open List

open Segment
open Tree

exception SpecFileError of string ;;

let rec input_lines (f : in_channel) : string list =
    match input_line f with
    | Some l -> l :: input_lines f
    | None -> [] ;;

let parse_aval (str : string) = 
    let no_brackets = global_replace (regexp "[][]") "" str in
    let split = map trim (split_on_char ';' no_brackets) in
    AFloat (Eterm [seg_of (Float.of_string (nth split 0)) 
                          (Float.of_string (nth split 1)) 
                          0.0]) ;;

let parse_line (l : string) : (string * aval) = 
   let split = map trim (split_on_char '=' l) in
   (nth split 0, (parse_aval (nth split 1))) ;;

(* Split the file by lines *)
(* grab each line and turn it into a value *)
let parse_spec_file (filename : string) : amem = 
    let ic = open_in filename in
    fold_left (fun acc l -> 
        let (n, aval) = parse_line l in
        amem_update (Id n) aval acc) 
        amem_bot 
        (input_lines ic) ;;
