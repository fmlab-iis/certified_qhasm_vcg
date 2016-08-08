%{
  open Qhasm
  open Big_int

  let err msg = raise (InvalidAnnotation msg)

  type mix = E of qexp | B of qbexp

  let ase e =
    fun vmap imap fmap pmap ->
      match e vmap imap fmap pmap with
        E e -> e
      | B e -> err("Encountered a Boolean expression " ^ string_of_qbexp e ^ ". An expression is expected.")

  let asb e =
    fun vmap imap fmap pmap ->
      match e vmap imap fmap pmap with
        E e -> err("Encountered an expression " ^ string_of_qexp e ^ ". A Boolean expression is expected.")
      | B e -> e

  let hf fn idx = "$" ^ fn ^ "@" ^ string_of_int idx

  (** Parse an expression with formal variables defined. *)
  let parse_with vmap imap fmap pmap formals e =
    let vmap = Hashtbl.copy vmap in
    let imap = Hashtbl.copy imap in
    let fmap = Hashtbl.copy fmap in
    let pmap = Hashtbl.copy pmap in
    let _ = List.iter (fun formal ->
      Hashtbl.remove vmap formal.vname;
      Hashtbl.remove fmap formal.vname;
      Hashtbl.remove pmap formal.vname;
      Hashtbl.add imap formal.vname formal.vsize
    ) formals in
    e vmap imap fmap pmap

  let rec estimate vmap imap fmap pmap exp =
    match exp with
      QExpConst n -> None
    | QExpCarry -> Some 1
    | QExpVar v -> Some v.vsize
    | QExpDeref _ -> Some !wordsize
    | QExpCoef _ -> Some !wordsize
    | QExpNeg e -> estimate vmap imap fmap pmap e
    | QExpNot e -> estimate vmap imap fmap pmap e
    | QExpCast (signed, e, n) -> Some n
    | QExpAdd (e1, e2)
    | QExpSub (e1, e2)
    | QExpMul (e1, e2)
    | QExpAnd (e1, e2)
    | QExpOr (e1, e2)
    | QExpXor (e1, e2)
    | QExpSmod (e1, e2)
    | QExpUmod (e1, e2) ->
      begin
        match estimate vmap imap fmap pmap e1, estimate vmap imap fmap pmap e2 with
          None, None -> None
        | Some n, None
        | None, Some n -> Some n
        | Some n, Some m -> Some (max n m)
      end
    | QExpPow (e, _) -> estimate vmap imap fmap pmap e
    | QExpConcat (e1, e2) ->
      begin
        match estimate vmap imap fmap pmap e1, estimate vmap imap fmap pmap e2 with
          None, None
        | Some _, None
        | None, Some _ -> err "The bit-widths of expressions in concatenation should be specified explicitly."
        | Some n, Some m -> Some (n + m)
      end
    | QExpSll (e, _)
    | QExpSrl (e, _)
    | QExpSra (e, _) -> estimate vmap imap fmap pmap e
    | QExpSlice (_, i, j) -> Some (i - j + 1)
    | QExpApp (fd, _) -> Some fd.svar.vsize
    | QExpIte (_, e1, e2) -> 
      begin
        match estimate vmap imap fmap pmap e1, estimate vmap imap fmap pmap e2 with
          None, None -> None
        | Some n, None
        | None, Some n -> Some n
        | Some n, Some m -> Some (max n m)
      end

  let apply_binary vmap imap fmap pmap f e1 e2 =
    match estimate vmap imap fmap pmap e1, estimate vmap imap fmap pmap e2 with
      None, None
    | None, Some _
    | Some _, None -> f e1 e2
    | Some n, Some m ->
      if n = m then
        f e1 e2
      else
        err (string_of_qexp e1 ^ " and " ^ string_of_qexp e2 ^ " have different bit-widths. " ^
        string_of_qexp e1 ^ ": " ^ string_of_int n ^ "-bits, " ^ string_of_qexp e2 ^ ": " ^ string_of_int m ^ "-bits")
%}

%token <string> NUM
%token <string> VAR
%token <bool * int> CAST
%token LPAREN RPAREN LSQUARE RSQUARE COMMA
%token COLON AUXVAR CONST INV ASSUME ASSERT CUT PREDICATE SMOD UMOD POWER CONJUNCTION DISJUNCTION RARR
%token PLUSEQ MINUSEQ MULTEQ ANDEQ OREQ XOREQ SHIFTLEQ SHIFTREQ
%token PLUS MINUS MULT AND OR XOR QUESTION EQ NE DOT SLT SGT SLE SGE ULT UGT ULE UGE CARRY NOT SHIFTL SHIFTR USHIFTR
%token LOW HIGH
%token UINT64 MEM64 MEM32 SPLIT TRUE EOF

%right RARR
%left DISJUNCTION
%left CONJUNCTION
%nonassoc EQ NE ULT ULE UGT UGE SLT SLE SGT SGE
%left PLUS MINUS
%left MULT OR XOR AND SMOD UMOD SHIFTL SHIFTR USHIFTR
%left DOT POWER
%left UMINUS
%right NOT
%nonassoc CAST HIGH LOW
%right LPAREN RPAREN LSQUARE RSQUARE

%start annotations

%type <(string, Qhasm.qtype) Hashtbl.t -> (string, int) Hashtbl.t -> (string, Qhasm.qfun) Hashtbl.t -> (string, Qhasm.qpred) Hashtbl.t -> Qhasm.qannot list> annotations

%%



/* ==================== Annotations ==================== */

annotations:
   annot annotations
   {
     fun vmap imap fmap pmap ->
       let annot = $1 vmap imap fmap pmap in
       let annots = $2 vmap imap fmap pmap in
       annot@annots
   }
 | annot                         { fun vmap imap fmap pmap -> $1 vmap imap fmap pmap }
;

annot:
  CONST consts                { fun vmap imap fmap pmap -> $2 vmap imap fmap pmap }
| AUXVAR auxvars              { fun vmap imap fmap pmap -> $2 vmap imap fmap pmap }
| PREDICATE predicates        { fun vmap imap fmap pmap -> $2 vmap imap fmap pmap }
| INV bexp                    { fun vmap imap fmap pmap -> [ QInvariant ($2 vmap imap fmap pmap) ] }
| ASSUME bexp                 { fun vmap imap fmap pmap -> [ QAssume ($2 vmap imap fmap pmap) ] }
| ASSERT bexp                 { fun vmap imap fmap pmap -> [ QAssert ($2 vmap imap fmap pmap) ] }
| CUT bexp                    { fun vmap imap fmap pmap -> [ QCut ($2 vmap imap fmap pmap) ] }
| CONST error                 { err "Constants are expected after \"const\"." }
| INV error                   { err "A Boolean expression is expected after \"inv\"." }
| PREDICATE error             { err "A Boolean expression is expected after \"predicate\"." }
| ASSUME error                { err "A Boolean expression is expected after \"assume\"." }
| ASSERT error                { err "A Boolean expression is expected after \"assert\"." }
| CUT error                   { err "A Boolean expression is expected after \"cut\"." }
| error                       { err "An annotation must start with const, var, predicate, inv, assume, assert, or cut." }
;



/* ==================== Pre-declared Constants ==================== */

consts:
  exp consts
  {
    fun vmap imap fmap pmap ->
      let c = QConst ($1 vmap imap fmap pmap) in
      let cs = $2 vmap imap fmap pmap in
      c::cs
  }
| exp { fun vmap imap fmap pmap -> [QConst ($1 vmap imap fmap pmap)] }
;



/* ==================== Logical Variables and Functions ==================== */

auxvars:
  auxvar auxvars
  {
    fun vmap imap fmap pmap ->
      let v = $1 vmap imap fmap pmap in
      let vs = $2 vmap imap fmap pmap in
      v::vs
  }
| auxvar { fun vmap imap fmap pmap -> [$1 vmap imap fmap pmap] }
;

auxvar:
  VAR EQ exp
  {
    fun vmap imap fmap pmap ->
      let v = $1 in
      let e = $3 vmap imap fmap pmap in
      if Hashtbl.mem vmap v then
        err ("The auxiliary variable " ^ v ^ " cannot be a program variable.")
      else
        match estimate vmap imap fmap pmap e with
          None -> err ("The bit-width of " ^ string_of_qexp e ^ " cannot be estimated.")
        | Some n ->
          let _ = Hashtbl.add imap v n in
          QAuxVar (mkqvar v n, Some e)
  }
| VAR LPAREN formals RPAREN EQ exp
  {
    fun vmap imap fmap pmap ->
      let v = $1 in
      let formals = $3 in
      if Hashtbl.mem vmap v then
        err ("Function " ^ v ^ " is already a program variable.")
      else if Hashtbl.mem imap v then
        err ("Function " ^ v ^ " is already defined as a logical variable or function.")
      else if Hashtbl.mem pmap v then
        err ("Function " ^ v ^ " is already defined as a predicate.")
      else
        let e = parse_with vmap imap fmap pmap formals $6 in
        match estimate vmap imap fmap pmap e with
          None -> err ("The bit-width of " ^ string_of_qexp e ^ " cannot be estimated.")
        | Some n ->
          let _ = Hashtbl.add imap v n in
        (** Remember the bit-widths of the formals. *)
          let _ = List.fold_left (
            fun idx formal -> 
              let _ = Hashtbl.add imap (hf v idx) formal.vsize in
              idx + 1
          ) 0 formals in
          let qfun = {svar = mkqvar v n; sformals = formals; sexp = e} in
          let _ = Hashtbl.add fmap v qfun in
          QFunction qfun
  }
| VAR LPAREN formals RPAREN EQ error  { err ("Invalid definition of function " ^ $1 ^ ".") }
| VAR CAST
  {
    fun vmap imap fmap pmap ->
      let v = $1 in
      let n = snd $2 in
      let _ = Hashtbl.add imap v n in
      QAuxVar (mkqvar v n, None)
  }
| VAR CAST EQ error
  { 
    err ("Invalid definition of logic variables. Expected: \n" ^
           "  var v = e\n" ^
             "  var v (e1, e2, ..., en) = e\n" ^
               "  var v@n")
  }
;



/* ==================== Predicates ==================== */

predicates:
  predicate predicates        { fun vmap imap fmap pmap -> ($1 vmap imap fmap pmap)::($2 vmap imap fmap pmap) }
| predicate                   { fun vmap imap fmap pmap -> [$1 vmap imap fmap pmap] }
;

predicate:
  VAR LPAREN formals RPAREN EQ bexp
  {
    fun vmap imap fmap pmap ->
      let v = $1 in
      let formals = $3 in
      if Hashtbl.mem vmap v then
        err ("Predicate " ^ v ^ " is already a program variable.")
      else if Hashtbl.mem imap v then
        err ("Predicate " ^ v ^ " is already defined as a logical variable or function.")
      else if Hashtbl.mem pmap v then
        err ("Predicate " ^ v ^ " is re-defined.")
      else
        let e = parse_with vmap imap fmap pmap formals $6 in
          (** Remember the bit-widths of the formals. *)
        let _ = List.fold_left (
          fun idx formal -> 
            let _ = Hashtbl.add imap (hf v idx) formal.vsize in
            idx + 1
        ) 0 formals in
        let qpred = {pvar = mkqvar v 1; pformals = formals; pbexp = e} in
        let _ = Hashtbl.add pmap v qpred in
        QPredicate qpred
  }
;



/* ==================== Expressions and Boolean Expressions ==================== */

bexp: mix                               { asb $1 };
exp: mix                                { ase $1 };

mix:
  exp_logical                           { $1 }
| exp_logical_b QUESTION exp_logical_e COLON exp_logical_e
  {
    fun vmap imap fmap pmap ->
      E (QExpIte ($1 vmap imap fmap pmap, $3 vmap imap fmap pmap, $5 vmap imap fmap pmap))
  }
;

exp_logical_b: exp_logical              { asb $1 };
exp_logical_e: exp_logical              { ase $1 };

exp_logical:
  exp_logical RARR exp_logical          { fun vmap imap fmap pmap -> B (QBexpImp (asb $1 vmap imap fmap pmap, asb $3 vmap imap fmap pmap)) }
| exp_logical DISJUNCTION exp_logical   { fun vmap imap fmap pmap -> B (QBexpOr (asb $1 vmap imap fmap pmap, asb $3 vmap imap fmap pmap)) }
| exp_logical CONJUNCTION exp_logical   { fun vmap imap fmap pmap -> B (QBexpAnd (asb $1 vmap imap fmap pmap, asb $3 vmap imap fmap pmap)) }
| NOT atomic
  {
    fun vmap imap fmap pmap -> 
      match $2 vmap imap fmap pmap with
        E e -> E (QExpNot e)
      | B e -> B (QBexpNeg e)
  }
| exp_compare                           { $1 }
;

exp_compare:
  exp_arith lessop actuals bless %prec ULT
  {
    fun vmap imap fmap pmap ->
      let e1 = ase $1 vmap imap fmap pmap in
      let op1 = $2 in
      let es = $3 vmap imap fmap pmap in
      match $4 vmap imap fmap pmap with
        None -> B (qands (List.map (fun e2 -> QBexpComp (e1, op1, e2)) es))
      | Some (op2, e2) -> B (qands (List.map (fun e -> qrange e1 op1 e op2 e2) es))
  }
| exp_arith moreop actuals bmore %prec ULT
  {
    fun vmap imap fmap pmap ->
      let e1 = ase $1 vmap imap fmap pmap in
      let op1 = $2 in
      let es = $3 vmap imap fmap pmap in
      match $4 vmap imap fmap pmap with
        None -> B (qands (List.map (fun e2 -> QBexpComp (e1, op1, e2)) es))
      | Some (op2, e2) -> B (qands (List.map (fun e -> qrange e1 op1 e op2 e2) es))
  }
| exp_arith EQ exp_arith
  { 
    fun vmap imap fmap pmap -> 
      B (apply_binary vmap imap fmap pmap (fun e1 e2 -> QBexpEq (e1, e2)) (ase $1 vmap imap fmap pmap) (ase $3 vmap imap fmap pmap))
  }
| exp_arith NE exp_arith
  {
    fun vmap imap fmap pmap ->
      B (apply_binary vmap imap fmap pmap (fun e1 e2 -> QBexpNe (e1, e2)) (ase $1 vmap imap fmap pmap) (ase $3 vmap imap fmap pmap))
  }
| exp_arith                             { $1 }
;

bless:
  lessop exp_arith %prec ULT            { fun vmap imap fmap pmap -> Some ($1, ase $2 vmap imap fmap pmap) }
|                                       { fun vmap imap fmap pmap -> None }
;

bmore:
  moreop exp_arith %prec ULT            { fun vmap imap fmap pmap -> Some ($1, ase $2 vmap imap fmap pmap) }
|                                       { fun vmap imap fmap pmap -> None }
;

exp_arith:
  atomic                                { $1 }
| exp_arith PLUS exp_arith
  {
    fun vmap imap fmap pmap -> 
      E (apply_binary vmap imap fmap pmap (fun e1 e2 -> QExpAdd (e1, e2)) (ase $1 vmap imap fmap pmap) (ase $3 vmap imap fmap pmap))
  }
| exp_arith MINUS exp_arith
  {
    fun vmap imap fmap pmap -> 
      E (apply_binary vmap imap fmap pmap (fun e1 e2 -> QExpSub (e1, e2)) (ase $1 vmap imap fmap pmap) (ase $3 vmap imap fmap pmap))
  }
| exp_arith MULT exp_arith
  {
    fun vmap imap fmap pmap -> 
      E (apply_binary vmap imap fmap pmap (fun e1 e2 -> QExpMul (e1, e2)) (ase $1 vmap imap fmap pmap) (ase $3 vmap imap fmap pmap))
  }
| exp_arith AND exp_arith
  {
    fun vmap imap fmap pmap -> 
      E (apply_binary vmap imap fmap pmap (fun e1 e2 -> QExpAnd (e1, e2)) (ase $1 vmap imap fmap pmap) (ase $3 vmap imap fmap pmap))
  }
| exp_arith OR exp_arith
  {
    fun vmap imap fmap pmap -> 
      E (apply_binary vmap imap fmap pmap (fun e1 e2 -> QExpOr (e1, e2)) (ase $1 vmap imap fmap pmap) (ase $3 vmap imap fmap pmap))
  }
| exp_arith XOR exp_arith
  {
    fun vmap imap fmap pmap -> 
      E (apply_binary vmap imap fmap pmap (fun e1 e2 -> QExpXor (e1, e2)) (ase $1 vmap imap fmap pmap) (ase $3 vmap imap fmap pmap))
  }
| exp_arith SMOD exp_arith
  {
    fun vmap imap fmap pmap -> 
      E (apply_binary vmap imap fmap pmap (fun e1 e2 -> QExpSmod (e1, e2)) (ase $1 vmap imap fmap pmap) (ase $3 vmap imap fmap pmap))
  }
| exp_arith UMOD exp_arith
  {
    fun vmap imap fmap pmap -> 
      E (apply_binary vmap imap fmap pmap (fun e1 e2 -> QExpUmod (e1, e2)) (ase $1 vmap imap fmap pmap) (ase $3 vmap imap fmap pmap))
  }
| exp_arith SHIFTL exp_arith            { fun vmap imap fmap pmap -> E (QExpSll (ase $1 vmap imap fmap pmap, ase $3 vmap imap fmap pmap)) }
| exp_arith USHIFTR exp_arith           { fun vmap imap fmap pmap -> E (QExpSrl (ase $1 vmap imap fmap pmap, ase $3 vmap imap fmap pmap)) }
| exp_arith SHIFTR exp_arith            { fun vmap imap fmap pmap -> E (QExpSra (ase $1 vmap imap fmap pmap, ase $3 vmap imap fmap pmap)) }
| exp_arith POWER exp_arith             { fun vmap imap fmap pmap -> E (QExpPow (ase $1 vmap imap fmap pmap, ase $3 vmap imap fmap pmap)) }
| MINUS exp_arith %prec UMINUS
  {
    fun vmap imap fmap pmap ->
      let e = ase $2 vmap imap fmap pmap in
      E (match e with
        QExpConst n -> QExpConst (minus_big_int n)
      | _ -> QExpNeg e)
  }
;

atomic_e: atomic                        { ase $1 };

atomic:
  big                                   { fun vmap imap fmap pmap -> E (QExpConst $1) }
| CARRY                                 { fun vmap imap fmap pmap -> E (QExpCarry) }
| var                                   { fun vmap imap fmap pmap -> E ($1 vmap imap fmap pmap) }
| TRUE                                  { fun vmap imap fmap pmap -> B (QBexpTrue) }
| LPAREN mix RPAREN                     { $2 }
| LPAREN mix RPAREN SPLIT num
  {
    fun vmap imap fmap pmap ->
      let n = $5 in
      match asb $2 vmap imap fmap pmap with
        QBexpEq (e1, e2) ->
          begin
            match estimate vmap imap fmap pmap e1 with
              None -> err "Unable to estimate the bit-width for bit splitting."
            | Some s ->
              if s mod n <> 0 then
                err "The number of splits should be a factor of the bit-width."
              else
                let inc = s / n in
                let rec helper upper lower =
                  if lower < 0 then
                    assert false
                  else if lower == 0 then
                    QBexpEq (QExpSlice (e1, upper, lower), QExpSlice (e2, upper, lower))
                  else
                    QBexpAnd (QBexpEq (QExpSlice (e1, upper, lower), QExpSlice (e2, upper, lower)), helper (upper - inc) (lower - inc)) in
                B (helper (s - 1) (s - inc))
          end
      | _ -> err "Bit splitting is only supported by equality."
  }
| atomic_e DOT atomic_e                 { fun vmap imap fmap pmap -> E (QExpConcat ($1 vmap imap fmap pmap, $3 vmap imap fmap pmap)) }
| atomic_e CAST                         { fun vmap imap fmap pmap -> E (QExpCast (fst $2, $1 vmap imap fmap pmap, snd $2)) }
| atomic_e LOW
  {
    fun vmap imap fmap pmap ->
      let e = $1 vmap imap fmap pmap in
      match estimate vmap imap fmap pmap e with
        None -> err ("Unknown bit-width of " ^ string_of_qexp e)
      | Some s -> E (QExpSlice (e, s / 2 - 1, 0))
  }
| atomic_e HIGH
  {
    fun vmap imap fmap pmap ->
      let e = $1 vmap imap fmap pmap in
      match estimate vmap imap fmap pmap e with
        None -> err ("Unknown bit-width of " ^ string_of_qexp e)
      | Some s -> E (QExpSlice (e, s - 1, s / 2))
  }
| atomic_e LSQUARE num COMMA num RSQUARE
  {
    if $3 < $5 then
      err ("The starting index should be greater than or equal to the ending index.")
    else
      fun vmap imap fmap pmap -> E (QExpSlice ($1 vmap imap fmap pmap, $3, $5))
  }
| atomic_e LSQUARE num RSQUARE
  {
    fun vmap imap fmap pmap ->
      if $3 mod !bytesize <> 0 then
        err ("The offset of memory access " ^ string_of_qexp ($1 vmap imap fmap pmap) ^
                "[" ^ string_of_int $3 ^ "] should be a multiple of " ^ string_of_int !bytesize ^ ".")
      else
        match $1 vmap imap fmap pmap with
          QExpVar v -> E (QExpDeref (QAddrBO (v, $3)))
        | _ -> err "Deference can be used in variables only."
  }
| VAR LPAREN RPAREN
  {
    fun vmap imap fmap pmap ->
      if Hashtbl.mem fmap $1 then
        let fd = Hashtbl.find fmap $1 in
        E (QExpApp (fd, []))
      else if Hashtbl.mem pmap $1 then
        let p = Hashtbl.find pmap $1 in
        B (QBexpApp (p, []))
      else
        err ($1 ^ " is neither a function nor a predicate.")
  }
| VAR LPAREN actuals RPAREN
  {
    let get_actuals vmap imap fmap pmap fn= 
      let actuals = $3 vmap imap fmap pmap in
      (* Check if the bit-widths of the actuals match the formals. *)
      let _ = List.fold_left (
        fun idx actual ->
          let sf = Hashtbl.find imap (hf fn idx) in
          let sa = size_of_exp actual in
          if sf <> sa then
            err ("The bit-width of the actual " ^ 
                    string_of_qexp actual ^ " is " ^ string_of_int sa ^ 
                    " but the bit-width of the corresponding formal is " ^ string_of_int sf ^ ".")
          else
            idx + 1
      ) 0 actuals in
      actuals in
    fun vmap imap fmap pmap ->
      if Hashtbl.mem fmap $1 then
        let fd = Hashtbl.find fmap $1 in
        let actuals = get_actuals vmap imap fmap pmap fd.svar.vname in
        E (QExpApp (fd, actuals))
      else if Hashtbl.mem pmap $1 then
        let p = Hashtbl.find pmap $1 in
        let actuals = get_actuals vmap imap fmap pmap p.pvar.vname in
        B (QBexpApp (p, actuals))
      else
        err ($1 ^ " is neither a function nor a predicate.")
  }
| atomic_e LSQUARE error
  {
    fun vmap imap fmap pmap ->
      let e = string_of_qexp ($1 vmap imap fmap pmap) in
      err ("Use \"" ^ e ^ "[n:m]\" to extract a bit-vector from " ^ e ^ ". " ^
              "Use \"" ^ e ^ "[n]\" as a shorthand of mem64[" ^ e ^ " + m] where m = n * 8 or mem32[" ^ e ^ " + m] where m = n * 4.")
  }
;


num:
  NUM { int_of_string $1 }
;

big:
  NUM { big_int_of_string $1 }
;

var:
| VAR %prec RPAREN
    {
      fun vmap imap fmap pmap ->
        if $1 = "carry" then
          QExpCarry
        else
          try
            QExpVar (mkpvar $1 (Hashtbl.find vmap $1))
          with Not_found ->
            begin
              try
                QExpVar (mkqvar $1 (Hashtbl.find imap $1))
              with Not_found ->
                (* Create a new logical variable if the variable is not defined. *)
                let _ = Hashtbl.add imap $1 !wordsize in
                QExpVar (mkqvar $1 !wordsize)
            end
    }
/* The following two rules will produce shift/reduce conflicts. */
/*
| MULT LPAREN UINT64 MULT RPAREN LPAREN qvar PLUS num RPAREN { fun vmap imap fmap pmap -> QExpVar (QVDDeref ($7 vmap imap fmap pmap, $9)) }
| MULT LPAREN UINT64 MULT RPAREN AND VAR                     { fun vmap imap fmap pmap -> QExpVar (QVDCoef (mkqvar $7 64)) } 
*/
| typem LSQUARE qaddr RSQUARE                                { fun vmap imap fmap pmap -> QExpDeref ($3 vmap imap fmap pmap) }
| typem LSQUARE VAR RSQUARE                                  { fun vmap imap fmap pmap -> QExpCoef (mkqvar $3 (size_of_qtypec $1)) }
| typem error
    {
      err "Use mem64[v + n] or mem32[v + n] to load a value from the memory. Use mem64[v] or mem32[v] to refer to a predefined constant."
    }
;

qaddr:
   qvar PLUS num                        { fun vmap imap fmap pmap -> QAddrBO ($1 vmap imap fmap pmap, $3) }
 | qvar PLUS qvar                       { fun vmap imap fmap pmap -> QAddrBI ($1 vmap imap fmap pmap, $3 vmap imap fmap pmap) }
 | qvar PLUS qvar MULT num
     {
       if $5 == 8 then
         fun vmap imap fmap pmap -> QAddrBIS ($1 vmap imap fmap pmap, $3 vmap imap fmap pmap)
       else
         err ("The scale in an address must be 8.")
     }
 | qvar PLUS num PLUS qvar MULT num
     {
       if $7 == 8 then
         fun vmap imap fmap pmap -> QAddrBOIS ($1 vmap imap fmap pmap, $3, $5 vmap imap fmap pmap)
       else
         err ("The scale in an address must be 8.")
     }
;

qvar:
  VAR
  {
    fun vmap imap fmap pmap ->
      try
        mkpvar $1 (Hashtbl.find vmap $1)
      with Not_found ->
        err ("Variable " ^ $1 ^ " is not defined.")
  }
;



/* ==================== Formal and Actual Parameters ==================== */

formals:
  formals_rev                           { List.rev $1 }
|                                       { [] }
;

formals_rev:
  formals_rev COMMA fparam              { $3::$1 }
| fparam                                { [ $1 ] }
;

fparam: VAR CAST                        { mkqvar $1 (snd $2) };

actuals:
  actuals_rev                           { fun vmap imap fmap pmap -> List.rev ($1 vmap imap fmap pmap) }
;

actuals_rev:
  actuals_rev COMMA exp_arith           { fun vmap imap fmap pmap -> (ase $3 vmap imap fmap pmap)::($1 vmap imap fmap pmap)}
| exp_arith                             { fun vmap imap fmap pmap -> [ase $1 vmap imap fmap pmap] }
;

typem:
  MEM64        { QCastInt64 }
| MEM32        { QCastInt32 }
;



/* ==================== Comparison Operators ==================== */

lessop:
  ULT                      { Ult }
| ULE                      { Ule }
| SLT                      { Slt }
| SLE                      { Sle }
;

moreop:
  UGT                      { Ugt }
| UGE                      { Uge }
| SGT                      { Sgt }
| SGE                      { Sge }
;
