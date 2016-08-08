{
  open AnnotParser
  exception Eof
}

let letter = ['a'-'z' 'A'-'Z' '_']
let number = ['0' - '9']
let identity = letter (letter | number | ''')*

rule token = parse
    [' ' '\t']                   { token lexbuf }
  | "!="                         { NE }
  | "+="                         { PLUSEQ }
  | "-="                         { MINUSEQ }
  | "*="                         { MULTEQ }
  | "&="                         { ANDEQ }
  | "|="                         { OREQ }
  | "^="                         { XOREQ }
  | "<<="                        { SHIFTLEQ }
  | ">>="                        { SHIFTREQ }
  | "**"                         { POWER }
  | "/\\"                        { CONJUNCTION }
  | "\\/"                        { DISJUNCTION }
  | "&&"                         { CONJUNCTION }
  | "||"                         { DISJUNCTION }
  | "->"                         { RARR }
  | ">=u"                        { UGE }
  | "<=u"                        { ULE }
  | ">="                         { SGE }
  | "<="                         { SLE }
  | '+'                          { PLUS }
  | '-'                          { MINUS }
  | '~'                          { NOT }
  | '*'                          { MULT }
  | "%u"                         { UMOD }
  | '%'                          { SMOD }
  | '('                          { LPAREN }
  | ')'                          { RPAREN }
  | '['                          { LSQUARE }
  | ']'                          { RSQUARE }
  | '&'                          { AND }
  | '|'                          { OR }
  | '^'                          { XOR }
  | '?'                          { QUESTION }
  | '$'                          { SPLIT }
  | '='                          { EQ }
  | '.'                          { DOT }
  | ','                          { COMMA }
  | "<<"                         { SHIFTL }
  | ">>u"                        { USHIFTR }
  | ">>"                         { SHIFTR }
  | "<u"                         { ULT }
  | ">u"                         { UGT }
  | '<'                          { SLT }
  | '>'                          { SGT }
  | ':'                          { COLON }
  | "uint64"                     { UINT64 }
  | "mem64"                      { MEM64 }
  | "mem32"                      { MEM32 }
  | "var"                        { AUXVAR }
  | "const"                      { CONST }
  | "inv"                        { INV }
  | "predicate"                  { PREDICATE }
  | "assume"                     { ASSUME }
  | "assert"                     { ASSERT }
  | "cut"                        { CUT }
  | "true"                       { TRUE }
  | "@l"                         { LOW }
  | "@h"                         { HIGH }
  | '@' ('u'? number+ as c)      
      {
        if String.get c 0 = 'u' then
          CAST (false, int_of_string (String.sub c 1 ((String.length c) - 1)))
        else
          CAST (true, int_of_string c)
      }
  | number+ as num               { NUM num }
  | identity as id               { VAR id }
  | eof                          { EOF }
