
open Arg
open Qhasm

exception OutputCreationFailure of string

(** The action to be performed. *)
type action = Parse | Generate 

(** Generates verification conditions by default. *)
let act = ref Generate
                        
(** A file containing constants. *)
let cfile = ref None
                        
(*
let o_formats = ref []
 *)

(** Suggests a filename for outputting verification conditions. *)
let suggest_filename fn = Filename.chop_suffix (Filename.basename fn) ".q"

(** Reads constants from a file. *)
let read_consts () =
  match !cfile with
    None -> Hashtbl.create 0
  | Some fn ->
     let _ = print_endline ("Reading predefined constants from " ^ fn ^ ".") in
     let map = Hashtbl.create 10 in
     let ic = open_in fn in
     let _ =
       try
         while true do
           let line = input_line ic in
          match Str.split (Str.regexp "=") line with
            n::v::[] -> Hashtbl.add map (String.trim n) (String.trim v)
          | _ -> print_endline ("Warning: Failed to read predefined constants from " ^ line ^ ".")
         done
       with End_of_file ->
         () in
     map

let args = 
  [
    ("-c", String (fun str -> cfile := Some str), "Specify a file containing predefined constants.");
    ("-p", Unit (fun () -> act := Parse), "Only parse a Qhasm file without generating any verification condition.");
  ]

let parse_qhasm ?(verbose=false) file =
  let _ = if verbose then print_endline ("Parsing Qhasm file " ^ file ^ ".") in
  Parser.qhasm_from_file file

let action_parse file =
  let qfile = parse_qhasm file in
  print_endline (Qhasm.string_of_qprog qfile.program)

let action_generate file =
  let qfile = parse_qhasm file in
  let mqhasm = Generator.mqhasm_from_qfile qfile in
  print_endline (Generator.string_of_mqhasm mqhasm)
                
(*
let get_options format = 
  { sConjunction = !o_split_conj;
    sAssertion = !o_single_assertion;
    slice = !o_slice;
    oApproximate = !o_approximate }
 *)
                
let usage = "qv [-a] [-c CONSTS] [-p] FILE"

let anon file =
  (* Inserts the default output format if no format is specified. *)
  match !act with
    Parse -> action_parse file
  | Generate -> action_generate file

let _ = 
  parse args anon usage
