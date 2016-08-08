%{
  open Qhasm
  open Big_int

  exception Undefined of string
  exception Redefined of string
  exception InvalidStatement of string

  let lnum = ref 1
%}

%token <string> COMMENT
%token <int> NUM
%token <string> HEX
%token <string> VAR
%token <bool * int> CAST
%token EOL LPAREN RPAREN LSQUARE RSQUARE COMMA
%token <int * string> ANNOT
%token COLON ASSUME ASSERT CUT EQMOD MOD POWER CONJUNCTION DISJUNCTION RARR
%token UNSIGNED_SHIFTR SIGNED_SHIFTR
%token PLUSEQ MINUSEQ MULTEQ ANDEQ OREQ XOREQ SHIFTLEQ SHIFTREQ
%token PLUS MINUS MULT AND OR XOR QUESTION EQ NE DOT SLT SGT SLE SGE ULT UGT ULE UGE CARRY NOT SHIFTL SHIFTR USHIFTR
%token INT8 INT16 INT32 INT64 INT128 INT3232 INT6464 INT32323232
%token FLOAT64 FLOAT80
%token STACK32 STACK64 STACK128 STACK256 STACK512
%token UINT8 UINT16 UINT32 UINT64 UINT128 UINT32323232
%token MEM32 MEM64 LOW HIGH
%token CALLER INPUT ENTER LEAVE RETURN IF
%token EOF

%start program

%type <Qhasm.qprog> program

%%

program:
  statements EOF
  {
    (** A map from a Qhasm variable to its type. *)
    let vmap = Hashtbl.create 100 in

    (** A map from an instrumentation variable to its bit-width. *)
    let imap = Hashtbl.create 100 in

    (** A map from a function name to its definition. *)
    let fmap = Hashtbl.create 100 in

    (** A map from a predicate name to its definition. *)
    let pmap = Hashtbl.create 100 in

    (** Add predefined variables. *)
    let _ = List.map (fun v -> Hashtbl.add vmap v !arch_type) 
      ["input_0"; "input_1"; "input_2"; "input_3"; "input_4"; "input_5"; "input_6"; "input_7";
      "caller_r4"; "caller_r5"; "caller_r6"; "caller_r7"; "caller_r8"; "caller_r9"; "caller_r10"; "caller_r11"; "caller_r14"] in

    $1 vmap imap fmap pmap
  }
;

statements:
   statement spaces statements
   {
     fun vmap imap fmap pmap -> 
       let stmt = $1 vmap imap fmap pmap in
       let stmts = $3 vmap imap fmap pmap in
       stmt::stmts
   }
 | annotations statements
     {
       fun vmap imap fmap pmap ->
         let annots = $1 vmap imap fmap pmap in
         let stmts = $2 vmap imap fmap pmap in
         annots@stmts
     }
 |   { fun vmap imap fmap pmap -> [] }
;

spaces:
   EOL spaces   { incr lnum }
 | EOL          { incr lnum }
;

annotations:
  annots
     {
       let rec split (res : (int * string list) list) (cur : (int * string list)) (annots : (int * string) list) : (int * string list) list =
         match annots with
           [] -> if snd cur <> [] then res@[cur] else res
         | hd::tl -> 
           if Str.string_match (Str.regexp "[ ]*\\(var\\|const\\|inv\\|assume\\|assert\\|cut\\).*") (snd hd) 0 then
             let res = if snd cur <> [] then res@[cur] else res in
             split res (fst hd, [snd hd]) tl
           else
             let cur = (fst cur, snd cur@[snd hd]) in
             split res cur tl in
       let annots = split [] (0, []) $1 in
       let start_line = fst (List.hd $1) in 
       let end_line = fst (List.hd (List.rev $1)) in
       let linestr = 
         if start_line = end_line then 
           "at line " ^ string_of_int start_line
         else
           "between lines " ^ string_of_int start_line ^ "-" ^ string_of_int end_line in
       fun vmap imap fmap pmap ->
         List.flatten (List.map (fun (line, annots) ->
           let annots = String.concat "" annots in
           try
             List.map (fun annot -> {skind = QAnnot annot; sline = line})
               ((AnnotParser.annotations AnnotLexer.token (Lexing.from_string annots)) vmap imap fmap pmap)
           with
           | InvalidAnnotation msg ->
             raise (InvalidAnnotation ("Invalid annotations " ^ linestr ^ ".\n" ^
                                          "Error message: " ^ msg ^ "\n" ^
                                          "Annotation: " ^ annots
                                          ))
           | Failure msg ->
             raise (Failure ("Invalid annotations " ^ linestr ^ ": " ^ msg))
           | Parsing.Parse_error ->
             raise (InvalidAnnotation ("Invalid annotations " ^ linestr ^ ":\n" ^ annots))
         ) annots)
     }
;

annots:
   ANNOT spaces annots    { $1::$3 }
 | ANNOT spaces           { [$1] }
;

statement:
  stmtkind { let l = !lnum in fun vmap imap fmap pmap -> { skind = $1 vmap imap fmap pmap; sline = l } }
;

stmtkind:
  typed VAR
  {
    let line = string_of_int !lnum in
    fun vmap imap fmap pmap ->
      if Hashtbl.mem vmap $2 then
        raise (Redefined ("Line " ^ line ^ ": Variable " ^ $2 ^ " is redefined."))
      else if Hashtbl.mem imap $2 then
        raise (Redefined ("Line " ^ line ^ ": Variable " ^ $2 ^ " is defined as an instrumentation variable already."))
      else
        let _ = Hashtbl.add vmap $2 $1 in
        QVar ($1, mkpvar $2 $1)
  }
 | var EQ cast LPAREN addr RPAREN                 { fun vmap imap fmap pmap -> QLoad ($1 vmap imap fmap pmap, $3, $5 vmap imap fmap pmap) }
 | var EQ typem LSQUARE addr RSQUARE              { fun vmap imap fmap pmap -> QLoad ($1 vmap imap fmap pmap, $3, $5 vmap imap fmap pmap) }
 | cast LPAREN addr RPAREN EQ atomic              { fun vmap imap fmap pmap -> QStore ($1, $3 vmap imap fmap pmap, $6 vmap imap fmap pmap) }
 | typem LSQUARE addr RSQUARE EQ atomic           { fun vmap imap fmap pmap -> QStore ($1, $3 vmap imap fmap pmap, $6 vmap imap fmap pmap) }
 | var EQ expr ifcarry
     {
       fun vmap imap fmap pmap ->
         match $4 with
           None -> QAssign ($1 vmap imap fmap pmap, $3 vmap imap fmap pmap)
         | Some neg -> QAssignIfCarry ($1 vmap imap fmap pmap, $3 vmap imap fmap pmap, neg)
     }
 | var PLUSEQ addexpr                             { fun vmap imap fmap pmap -> QAdd ($1 vmap imap fmap pmap, $3 vmap imap fmap pmap) }
 | CARRY QUESTION var PLUSEQ addexpr              { fun vmap imap fmap pmap -> QAddCarry ($3 vmap imap fmap pmap, $5 vmap imap fmap pmap) }
 | var MINUSEQ subexpr                            { fun vmap imap fmap pmap -> QSub ($1 vmap imap fmap pmap, $3 vmap imap fmap pmap) }
 | CARRY QUESTION var MINUSEQ subexpr             { fun vmap imap fmap pmap -> QSubCarry ($3 vmap imap fmap pmap, $5 vmap imap fmap pmap) }
 | var MULTEQ atomic                              { fun vmap imap fmap pmap -> QMul ($1 vmap imap fmap pmap, $3 vmap imap fmap pmap) }
 | var ANDEQ atomic                               { fun vmap imap fmap pmap -> QAnd ($1 vmap imap fmap pmap, $3 vmap imap fmap pmap) }
 | var OREQ atomic                                { fun vmap imap fmap pmap -> QOr ($1 vmap imap fmap pmap, $3 vmap imap fmap pmap) }
 | var XOREQ atomic                               { fun vmap imap fmap pmap -> QXor ($1 vmap imap fmap pmap, $3 vmap imap fmap pmap) }
 | cast2 var var EQ atomic MULT atomic
     {
       fun vmap imap fmap pmap -> 
         QConcatMul (signed $1, $2 vmap imap fmap pmap, $3 vmap imap fmap pmap, $5 vmap imap fmap pmap, $7 vmap imap fmap pmap) 
     }
 | var var EQ atomic MULT atomic
     {
       fun vmap imap fmap pmap -> 
         QConcatMul (false, $1 vmap imap fmap pmap, $2 vmap imap fmap pmap, $4 vmap imap fmap pmap, $6 vmap imap fmap pmap) 
     }
 | cast2 var var PLUSEQ atomic MULT atomic
     {
       fun vmap imap fmap pmap -> 
         QAddConcatMul (signed $1, $2 vmap imap fmap pmap, $3 vmap imap fmap pmap, $5 vmap imap fmap pmap, $7 vmap imap fmap pmap) 
     }
 | var var PLUSEQ atomic MULT atomic
     {
       fun vmap imap fmap pmap -> 
         QAddConcatMul (false, $1 vmap imap fmap pmap, $2 vmap imap fmap pmap, $4 vmap imap fmap pmap, $6 vmap imap fmap pmap) 
     }
 | var EQ MINUS var
     { 
       let line = string_of_int !lnum in
       fun vmap imap fmap pmap ->
         let v1 = $1 vmap imap fmap pmap in
         let v2 = $4 vmap imap fmap pmap in
         if v1 = v2 then
           QNeg v1
         else
            raise (InvalidStatement ("Line " ^ line ^ ": The variables should be the same."))
     }
 | var EQ NOT var
     {
       let line = string_of_int !lnum in
       fun vmap imap fmap pmap ->
         let v1 = $1 vmap imap fmap pmap in
         let v2 = $4 vmap imap fmap pmap in
         if v1 = v2 then
           QNot v1
         else
            raise (InvalidStatement ("Line " ^ line ^ ": The variables should be the same."))
     }
 | var EQ LPAREN var DOT var RPAREN SHIFTL atomic
     {
       let line = string_of_int !lnum in
       fun vmap imap fmap pmap ->
         let v1 = $1 vmap imap fmap pmap in
         let v2 = $4 vmap imap fmap pmap in
         let v3 = $6 vmap imap fmap pmap in
         if v1 = v2 then
           QConcatShiftLeft (v1, v3, $9 vmap imap fmap pmap)
         else
            raise (InvalidStatement ("Line " ^ line ^ ": The first and second variables should be the same."))       
     }
 | var SHIFTLEQ atomic                           { fun vmap imap fmap pmap -> QShiftLeft ($1 vmap imap fmap pmap, $3 vmap imap fmap pmap) }
 | var EQ LPAREN var var RPAREN SHIFTR atomic
     {
       let line = string_of_int !lnum in
       fun vmap imap fmap pmap ->
         let v1 = $1 vmap imap fmap pmap in
         let v2 = $4 vmap imap fmap pmap in
         let v3 = $5 vmap imap fmap pmap in
         if v1 = v3 then
           QConcatShiftRight (v1, v2, $8 vmap imap fmap pmap)
         else
            raise (InvalidStatement ("Line " ^ line ^ ": The first and third variables should be the same."))       
     }
 | cast2 var SHIFTREQ atomic                      { fun vmap imap fmap pmap -> QShiftRight (signed $1, $2 vmap imap fmap pmap, $4 vmap imap fmap pmap) }
 | INPUT VAR                                      { fun vmap imap fmap pmap -> QInput (mkqvar $2 0) }
 | CALLER VAR                                     { fun vmap imap fmap pmap -> QCaller (mkqvar $2 0) }
 | ENTER VAR                                      { fun vmap imap fmap pmap -> QEnter (mkqvar $2 0) }
 | LEAVE                                          { fun vmap imap fmap pmap -> QLeave }
 | RETURN                                         { fun vmap imap fmap pmap -> QLeave }
 | COMMENT                                        { fun vmap imap fmap pmap -> QComment $1 }
;

ifcarry:
  IF NOT CARRY { Some true }
| IF CARRY     { Some false }
|              { None }
;

expr:
   atomic                                            { fun vmap imap fmap pmap -> QExprAtomic ($1 vmap imap fmap pmap) }
 | atomic PLUS atomic                                { fun vmap imap fmap pmap -> QExprAdd2 ($1 vmap imap fmap pmap, $3 vmap imap fmap pmap) }
 | atomic PLUS atomic PLUS atomic                    { fun vmap imap fmap pmap -> QExprAdd3 ($1 vmap imap fmap pmap, $3 vmap imap fmap pmap, $5 vmap imap fmap pmap) }
 | atomic MULT atomic                                { fun vmap imap fmap pmap -> QExprMul2 ($1 vmap imap fmap pmap, $3 vmap imap fmap pmap) }
 | atomic AND atomic                                 { fun vmap imap fmap pmap -> QExprAnd2 ($1 vmap imap fmap pmap, $3 vmap imap fmap pmap) }
 | LPAREN atomic SHIFTL atomic RPAREN
                                                     { fun vmap imap fmap pmap -> QExprSll ($2 vmap imap fmap pmap, $4 vmap imap fmap pmap) }
 | LPAREN atomic UNSIGNED_SHIFTR atomic RPAREN
                                                     { fun vmap imap fmap pmap -> QExprSrl ($2 vmap imap fmap pmap, $4 vmap imap fmap pmap) }
 | atomic PLUS LPAREN atomic SHIFTL atomic RPAREN
                                                     { fun vmap imap fmap pmap -> QExprAdd2Sll ($1 vmap imap fmap pmap, $4 vmap imap fmap pmap, $6 vmap imap fmap pmap) }
 | atomic PLUS LPAREN atomic UNSIGNED_SHIFTR atomic RPAREN
                                                     { fun vmap imap fmap pmap -> QExprAdd2Srl ($1 vmap imap fmap pmap, $4 vmap imap fmap pmap, $6 vmap imap fmap pmap) }
;

addexpr:
   atomic                                             { fun vmap imap fmap pmap -> QAddExprAtomic ($1 vmap imap fmap pmap) }
 | atomic PLUS atomic                                 { fun vmap imap fmap pmap -> QAddExprAdd2 ($1 vmap imap fmap pmap, $3 vmap imap fmap pmap) }
;

subexpr:
   atomic                                             { fun vmap imap fmap pmap -> QSubExprAtomic ($1 vmap imap fmap pmap) }
 | atomic MINUS atomic                                { fun vmap imap fmap pmap -> QSubExprSub2 ($1 vmap imap fmap pmap, $3 vmap imap fmap pmap) }
;

atomic:
   const                                              { fun vmap imap fmap pmap -> QAConst $1 }
 | CARRY                                              { fun vmap imap fmap pmap -> QACarry }
 | var                                                { fun vmap imap fmap pmap -> QAVar ($1 vmap imap fmap pmap) }
 | cast LPAREN addr RPAREN                            { fun vmap imap fmap pmap -> QADeref ($3 vmap imap fmap pmap) }
 | typem LSQUARE addr RSQUARE                         { fun vmap imap fmap pmap -> QADeref ($3 vmap imap fmap pmap) }
 | cast AND VAR                                       { fun vmap imap fmap pmap -> QACoef (mkqvar $3 !wordsize) }
 | typem LSQUARE VAR RSQUARE                          { fun vmap imap fmap pmap -> QACoef (mkqvar $3 (size_of_qtypec $1)) }
;

addr:
  var PLUS num                            { fun vmap imap fmap pmap -> QAddrBO ($1 vmap imap fmap pmap, $3) }
 | var PLUS var                           { fun vmap imap fmap pmap -> QAddrBI ($1 vmap imap fmap pmap, $3 vmap imap fmap pmap) }
 | var PLUS var MULT num
     {
       if $5 == 8 then
         fun vmap imap fmap pmap -> QAddrBIS ($1 vmap imap fmap pmap, $3 vmap imap fmap pmap)
       else
         raise (InvalidStatement ("Line " ^ string_of_int !lnum ^ ": The scale must be 8."))
     }
 | var PLUS num PLUS var MULT num
     {
       if $7 == 8 then
         fun vmap imap fmap pmap -> QAddrBOIS ($1 vmap imap fmap pmap, $3, $5 vmap imap fmap pmap)
       else
         raise (InvalidStatement ("Line " ^ string_of_int !lnum ^ ": The scale must be 8."))
     }
;

var:
  VAR
  {
    let line = string_of_int !lnum in
    fun vmap imap fmap pmap ->
      try
        mkpvar $1 (Hashtbl.find vmap $1)
      with Not_found ->
        raise (Undefined ("Line " ^ line ^ ": Variable " ^ $1 ^ " is not defined."))
  }
;

const:
   num  { QCDec (big_int_of_int $1) }
 | HEX  { QCHex $1 }
;

num:
  NUM { $1 }
;

typem:
  MEM64        { QCastInt64 }
| MEM32        { QCastInt32 }
;

typed:
  INT64        { QInt64 }
| INT32        { QInt32 }
| INT3232      { QInt3232 }
| INT6464      { QInt6464 }
| FLOAT80      { QFloat80 }
| STACK32      { QStack32 }
| STACK64      { QStack64 }
| STACK128     { QStack128 }
| STACK256     { QStack256 }
| STACK512     { QStack512 }
;

cast:
  MULT LPAREN typec MULT RPAREN { $3 }
;

cast2:
  LPAREN typec RPAREN  { $2 }
;

typec:
  INT8     { QCastInt8 }
| INT16    { QCastInt16 }
| INT32    { QCastInt32 }
| INT64    { QCastInt64 }
| UINT8    { QCastUInt8 }
| UINT16   { QCastUInt16 }
| UINT32   { QCastUInt32 }
| UINT64   { QCastUInt64 }
| UINT128  { QCastUInt128 }
;
