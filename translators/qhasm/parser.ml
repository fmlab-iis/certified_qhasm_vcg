
open Qhasm

let qhasm_from_lexbuf lexbuf = 
  try
    QhasmParser.program QhasmLexer.token lexbuf
  with
  | Failure msg ->
    let l = !QhasmLexer.lnum in
    let c = !QhasmLexer.cnum in
    (Printf.eprintf "Parser error at line %d char %d." l c;
     Printf.eprintf "Lexer error: %s!@." msg;
     raise (Failure msg))
  | Parsing.Parse_error ->
    let l = !QhasmLexer.lnum in
    let c = !QhasmLexer.cnum in
    (Printf.eprintf "Parser error at line %d char %d." l c;
     raise Parsing.Parse_error)

let qhasm_from_file file =
  { filename = file;
    program = qhasm_from_lexbuf (Lexing.from_channel (open_in file)) }

let qhasm_from_string str =
  { filename = "";
    program = qhasm_from_lexbuf (Lexing.from_string str) }
