{
  open Big_int
  open QhasmParser
  exception Eof
  let lnum = ref 1
  let cnum = ref 0
  let get_len lexbuf = String.length (Lexing.lexeme lexbuf)
  let upd_cnum lexbuf = cnum := !cnum + get_len lexbuf
  let reset_cnum () = cnum := 0
}

let letter = ['a'-'z' 'A'-'Z' '_']
let number = ['0'-'9']
let hex = ['0'-'9' 'a'-'f' 'A'-'F']
let identity = letter (letter | number)* (['''])*

rule token = parse
    [' ' '\t']                   { upd_cnum lexbuf; token lexbuf }
  | "enter"                      { upd_cnum lexbuf; ENTER }
  | "leave"                      { upd_cnum lexbuf; LEAVE }
  | "return"                     { upd_cnum lexbuf; RETURN }
  | "#//" ([^'\n''\r']* as a)    { upd_cnum lexbuf; ANNOT (!lnum, a) }
  | '#' ([^'\n''\r''/'] [^'\n''\r''/'] [^'\n''\r']* as c)
  | '#' ([^'\n''\r''/'] [^'\n''\r']* as c)
  | '#' ([' ' '\t']* as c)       { COMMENT c }
  | ("\r\n"|'\n'|'\r')           { reset_cnum(); incr lnum; EOL }
  | "!="                         { upd_cnum lexbuf; NE }
  | "+="                         { upd_cnum lexbuf; PLUSEQ }
  | "-="                         { upd_cnum lexbuf; MINUSEQ }
  | "*="                         { upd_cnum lexbuf; MULTEQ }
  | "&="                         { upd_cnum lexbuf; ANDEQ }
  | "|="                         { upd_cnum lexbuf; OREQ }
  | "^="                         { upd_cnum lexbuf; XOREQ }
  | "<<="                        { upd_cnum lexbuf; SHIFTLEQ }
  | ">>="                        { upd_cnum lexbuf; SHIFTREQ }
  | "**"                         { upd_cnum lexbuf; POWER }
  | "mod"                        { upd_cnum lexbuf; EQMOD }
  | "/\\"                        { upd_cnum lexbuf; CONJUNCTION }
  | "\\/"                        { upd_cnum lexbuf; DISJUNCTION }
  | "&&"                         { upd_cnum lexbuf; CONJUNCTION }
  | "||"                         { upd_cnum lexbuf; DISJUNCTION }
  | "->"                         { upd_cnum lexbuf; RARR }
  | ">=u"                        { upd_cnum lexbuf; UGE }
  | "<=u"                        { upd_cnum lexbuf; ULE }
  | ">="                         { upd_cnum lexbuf; SGE }
  | "<="                         { upd_cnum lexbuf; SLE }
  | '+'                          { upd_cnum lexbuf; PLUS }
  | '-'                          { upd_cnum lexbuf; MINUS }
  | '~'                          { upd_cnum lexbuf; NOT }
  | '!'                          { upd_cnum lexbuf; NOT }
  | '*'                          { upd_cnum lexbuf; MULT }
  | '%'                          { upd_cnum lexbuf; MOD }
  | '('                          { upd_cnum lexbuf; LPAREN }
  | ')'                          { upd_cnum lexbuf; RPAREN }
  | '['                          { upd_cnum lexbuf; LSQUARE }
  | ']'                          { upd_cnum lexbuf; RSQUARE }
  | '&'                          { upd_cnum lexbuf; AND }
  | '|'                          { upd_cnum lexbuf; OR }
  | '^'                          { upd_cnum lexbuf; XOR }
  | '?'                          { upd_cnum lexbuf; QUESTION }
  | '='                          { upd_cnum lexbuf; EQ }
  | '.'                          { upd_cnum lexbuf; DOT }
  | ','                          { upd_cnum lexbuf; COMMA }
  | "<<"                         { upd_cnum lexbuf; SHIFTL }
  | ">>u"                        { upd_cnum lexbuf; USHIFTR }
  | ">>"                         { upd_cnum lexbuf; SHIFTR }
  | "unsigned>>"                 { upd_cnum lexbuf; UNSIGNED_SHIFTR }
  | "signed>>"                   { upd_cnum lexbuf; SIGNED_SHIFTR }
  | "<u"                         { upd_cnum lexbuf; ULT }
  | ">u"                         { upd_cnum lexbuf; UGT }
  | '<'                          { upd_cnum lexbuf; SLT }
  | '>'                          { upd_cnum lexbuf; SGT }
  | ':'                          { upd_cnum lexbuf; COLON }
  | "carry"                      { upd_cnum lexbuf; CARRY }
  | "int32323232"                { upd_cnum lexbuf; INT32323232 }
  | "int3232"                    { upd_cnum lexbuf; INT3232 }
  | "int6464"                    { upd_cnum lexbuf; INT6464 }
  | "int8"                       { upd_cnum lexbuf; INT8 }
  | "int16"                      { upd_cnum lexbuf; INT16 }
  | "int32"                      { upd_cnum lexbuf; INT32 }
  | "int64"                      { upd_cnum lexbuf; INT64 }
  | "int128"                     { upd_cnum lexbuf; INT128 }
  | "float64"                    { upd_cnum lexbuf; FLOAT64 }
  | "float80"                    { upd_cnum lexbuf; FLOAT80 }
  | "stack32"                    { upd_cnum lexbuf; STACK32 }
  | "stack64"                    { upd_cnum lexbuf; STACK64 }
  | "stack128"                   { upd_cnum lexbuf; STACK128 }
  | "stack256"                   { upd_cnum lexbuf; STACK256 }
  | "stack512"                   { upd_cnum lexbuf; STACK512 }
  | "uint32323232"               { upd_cnum lexbuf; UINT32323232 }
  | "uint8"                      { upd_cnum lexbuf; UINT8 }
  | "uint16"                     { upd_cnum lexbuf; UINT16 }
  | "uint32"                     { upd_cnum lexbuf; UINT32 }
  | "uint64"                     { upd_cnum lexbuf; UINT64 }
  | "uint128"                    { upd_cnum lexbuf; UINT128 }
  | "caller"                     { upd_cnum lexbuf; CALLER }
  | "mem64"                      { upd_cnum lexbuf; MEM64 }
  | "mem32"                      { upd_cnum lexbuf; MEM32 }
  | "input"                      { upd_cnum lexbuf; INPUT }
  | "if"                         { upd_cnum lexbuf; IF }
  | "assume"                     { upd_cnum lexbuf; ASSUME }
  | "assert"                     { upd_cnum lexbuf; ASSERT }
  | "cut"                        { upd_cnum lexbuf; CUT }
  | "@l"                         { upd_cnum lexbuf; LOW }
  | "@h"                         { upd_cnum lexbuf; HIGH }
  | '@' ('u'? number+ as c)      
      {
        let _ = upd_cnum lexbuf in
        if String.get c 0 = 'u' then
          CAST (false, int_of_string (String.sub c 1 ((String.length c) - 1)))
        else
          CAST (true, int_of_string c)
      }
  | ('-'? "0x" hex+) as hex   { 
                                   let _ = upd_cnum lexbuf in
                                   let num = 
                                     if hex.[0] = '-' then
                                       "-" ^ String.sub hex 3 (String.length hex - 3)
                                     else
                                       String.sub hex 2 (String.length hex - 2) in
                                   HEX num
                                 }
  | ('-'? number+) as num        { upd_cnum lexbuf; NUM (int_of_string num) }
  | identity as id               { upd_cnum lexbuf; VAR id }
  | eof                          { EOF }
