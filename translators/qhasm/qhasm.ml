
(** Qhasm *)

open Big_int

exception EvaluationException of string
exception InvalidOperation of string
exception InvalidAnnotation of string
exception Undefined of string

let shorthand = ref true

let big_int_of_hex str =
  let sixteen = big_int_of_int 16 in
  let rec h res i str =
    let n = big_int_of_int (int_of_string ("0x" ^ String.make 1 (str.[i]))) in
    let res = add_big_int (mult_big_int res sixteen) n in
    if i == String.length str - 1 then
      res
    else
      h res (i + 1) str in
  let (neg, str) = 
    if str.[0] = '-' then
      (true, String.sub str 1 (String.length str - 1))
    else
      (false, str) in
  let num = h zero_big_int 0 str in
  if neg then
    minus_big_int num
  else
    num





(** ========== Basic Types ========== *)


(** a list of Qhasm types for variable declarations. *)
type qtype =
  QInt64
| QInt32
| QInt3232
| QInt6464
| QFloat80
| QStack32
| QStack64
| QStack128
| QStack256
| QStack512

(** a list of Qhasm types for casting. *)
type qtypec =
  QCastInt8
| QCastInt16
| QCastInt32
| QCastInt64
| QCastInt128
| QCastUInt8
| QCastUInt16
| QCastUInt32
| QCastUInt64
| QCastUInt128

let size_of_qtype qt =
  match qt with
    QInt64 -> 64
  | QInt32 -> 32
  | QInt3232 -> 64
  | QInt6464 -> 128
  | QFloat80 -> 80
  | QStack32 -> 32
  | QStack64 -> 64
  | QStack128 -> 128
  | QStack256 -> 256
  | QStack512 -> 512

let size_of_qtypec qt =
  match qt with
    QCastInt8
  | QCastUInt8 -> 8
  | QCastInt16
  | QCastUInt16 -> 16
  | QCastInt32
  | QCastUInt32 -> 32
  | QCastInt64
  | QCastUInt64 -> 64
  | QCastInt128
  | QCastUInt128 -> 128



(** ========== Qhasm Syntax ========== *)


(** 
 * A Qhasm variable has a name and a fixed size.
 * If the variable is a declared program variable, it will has a type.
 *)
type qvar = {
  mutable vname: string;
  mutable vsize: int;
  mutable vtype: qtype option
}

(** Makes a program variable declared with a type. *)
let mkpvar n t = { vname = n; vsize = size_of_qtype t; vtype = Some t }

(** Makes a general variable with a bit-width. *)
let mkqvar n s = { vname = n; vsize = s; vtype = None }

let carry_var = mkqvar "carry" 1

(**
   addr =
   * base + offset
   * base + index
   * base + index * scale            -- the scale is always bytesize
   * base + offset + index * scale   -- the scale is always bytesize
*)
type qaddr =
  QAddrBO of qvar * int
| QAddrBI of qvar * qvar
| QAddrBIS of qvar * qvar
| QAddrBOIS of qvar * int * qvar

(** Constants *)
type qconst =
  QCDec of big_int
| QCHex of string

(** Atomics
    - constant
    - carry
    - var
    - *( uint64 * )( addr )
    - &var
*)
type qatomic =
  QAConst of qconst
| QACarry
| QAVar of qvar
| QADeref of qaddr
| QACoef of qvar

(**
   var = expr where expr is
   * atomic
   * atomic + atomic
   * atomic + atomic + atomic
   * atomic * atomic
   * atomic & atomic
   * atomic << atomic
   * atomic unsigned>> atomic
   * atomic + (atomic << atomic)
   * atomic + (atomic unsigned>> atomic)
*)
type qexpr =
  QExprAtomic of qatomic
| QExprAdd2 of qatomic * qatomic
| QExprAdd3 of qatomic * qatomic * qatomic
| QExprMul2 of qatomic * qatomic
| QExprAnd2 of qatomic * qatomic
| QExprSll of qatomic * qatomic
| QExprSrl of qatomic * qatomic
| QExprAdd2Sll of qatomic * qatomic * qatomic
| QExprAdd2Srl of qatomic * qatomic * qatomic

(**
   var += expr where expr is
   * atomic
   * atomic + atomic
*)
type qaddexpr =
  QAddExprAtomic of qatomic
| QAddExprAdd2 of qatomic * qatomic

(**
   var -= expr where expr is
   * atomic
   * atomic - atomic
*)
type qsubexpr = 
  QSubExprAtomic of qatomic
| QSubExprSub2 of qatomic * qatomic

type cop = Slt | Sle | Ult | Ule | Sgt | Sge | Ugt | Uge

(** Returns the dual of a comparison operator. It must satisfy that a op b is
    equivalent to b (dual_of_cop op) a. *)
let dual_of_cop op =
  match op with
    Slt -> Sgt
  | Sle -> Sge
  | Ult -> Ugt
  | Ule -> Uge
  | Sgt -> Slt
  | Sge -> Sle
  | Ugt -> Ult
  | Uge -> Ule

let neg_of_cop op =
  match op with
    Slt -> Sge
  | Sle -> Sgt
  | Ult -> Uge
  | Ule -> Ugt
  | Sgt -> Sle
  | Sge -> Slt
  | Ugt -> Ule
  | Uge -> Ult

let string_of_cop op =
  match op with
    Slt -> "<"
  | Sle -> "<="
  | Ult -> "<u"
  | Ule -> "<=u" 
  | Sgt -> ">"
  | Sge -> ">="
  | Ugt -> ">u"
  | Uge -> ">=u"

let cop_signed op =
  match op with
    Slt | Sle | Sgt | Sge -> true
  | Ult | Ule | Ugt | Uge -> false

type qfun = {
  svar: qvar;
  sformals: qvar list;
  sexp: qexp
}

(** Predicates *)
and qpred = {
  pvar: qvar;
  pformals: qvar list;
  pbexp: qbexp
}

(**
   * Expressions in annotations.
*)
and qexp =
  QExpConst of big_int
| QExpCarry
| QExpVar of qvar
| QExpDeref of qaddr
| QExpCoef of qvar
| QExpNeg of qexp
| QExpNot of qexp
| QExpCast of bool * qexp * int
| QExpAdd of qexp * qexp
| QExpSub of qexp * qexp
| QExpMul of qexp * qexp
| QExpAnd of qexp * qexp
| QExpOr of qexp * qexp
| QExpXor of qexp * qexp
| QExpSmod of qexp * qexp
| QExpUmod of qexp * qexp
| QExpPow of qexp * qexp
| QExpConcat of qexp * qexp
| QExpSll of qexp * qexp
| QExpSrl of qexp * qexp
| QExpSra of qexp * qexp
| QExpSlice of qexp * int * int
| QExpApp of qfun * qexp list
| QExpIte of qbexp * qexp * qexp

(**
   * Boolean expressions in annotations.
*)
and qbexp =
  QBexpTrue
| QBexpEq of qexp * qexp
| QBexpNe of qexp * qexp
| QBexpComp of qexp * cop * qexp
| QBexpNeg of qbexp
| QBexpAnd of qbexp * qbexp
| QBexpOr of qbexp * qbexp
| QBexpImp of qbexp * qbexp
| QBexpApp of qpred * qexp list

(** 
 * Returns e1 /\ e2 /\ ... /\ en for a list of expressions [e1; e2; ...; en].
 * Returns QBexpTrue if the list is empty.
 *)
let qands es =
  match es with
    [] -> QBexpTrue
  | hd::tl -> List.fold_left (
    fun res e ->
      match e with
        QBexpTrue -> res
      | _ -> QBexpAnd (res, e)
  ) hd tl

(** 
 * Returns e1 \/ e2 \/ ... \/ en for a list of expressions [e1; e2; ...; en].
 * Returns (QBexpNeg QBexpTrue) if the list is empty.
 *)
let qors es = 
  match es with
    [] -> QBexpNeg QBexpTrue
  | hd::tl -> List.fold_left (
    fun res e ->
      match e with
        QBexpNeg QBexpTrue -> res
      | _ -> QBexpOr (res, e)
  ) hd tl

(**
 * Returns (e1 op1 e) /\ (e op2 e2) for qrange e1 op1 e op2 e2.
 *)
let qrange e1 op1 e op2 e2 =
  QBexpAnd (QBexpComp (e1, op1, e), QBexpComp (e, op2, e2))

(**
 * Annotations.
 *)
type qannot = 
  QAuxVar of qvar * qexp option
| QConst of qexp
| QFunction of qfun
| QPredicate of qpred
| QInvariant of qbexp
| QAssume of qbexp
| QAssert of qbexp
| QCut of qbexp

(**
 * QVar: type var
 * QLoad: var = *( type * ) (address)
 * QStore: *( type * ) (addr) = atomic, we allow more than Qhasm
 * QAssign: var = expr
 * QAssignIfCarry: var = expr if carry, var = expr if !carry
 * QAdd: var += expr
 * QAddCarry: carry ? var += expr
 * QSub: var -= expr
 * QSubCarry: carry ? var -= expr
 * QMul: var *= expr
 * QAnd: var &= expr
 * QOr: var |= expr
 * QXor: var ^= expr
 * QConcatMul: (int128) t r = r * s, (uint128) t r = r * s on AMD64 and 
 *             a b = c * d on ARM, 
 *             the first argument indicates if the operation is signed
 * QAddConcatMul: a b += c * d,
 *                the first argument indicates if the operation is signed
 * QNeg: r = -r, two's complement
 * QNot: r = ~r, one's complement
 * QConcatShiftLeft: r = (r.t) << s, r = (r.t) << n
 * QShiftLeft: r <<= s, r <<= n
 * QConcatShiftRight: r = (t r) >> s, r = (t r) >> n
 * QShiftRight: (int64) r >>= s, (uint64) r >>= s, 
 *              (int64) r >>= n, (uint64) r >>= n, 
 *              the first argument is true if signed
 * QInput: input var
 * QCaller: caller var
 * QEnter: enter name
 * QLeave: leave
 * QComment: comments
 * QAnnot: annotations
 *)
type qstmtkind =
  QVar of qtype * qvar
| QLoad of qvar * qtypec * qaddr
| QStore of qtypec * qaddr * qatomic
| QAssign of qvar * qexpr
| QAssignIfCarry of qvar * qexpr * bool
| QAdd of qvar * qaddexpr
| QAddCarry of qvar * qaddexpr
| QSub of qvar * qsubexpr
| QSubCarry of qvar * qsubexpr
| QMul of qvar * qatomic
| QAnd of qvar * qatomic
| QOr of qvar * qatomic
| QXor of qvar * qatomic
| QConcatMul of bool * qvar * qvar * qatomic * qatomic
| QAddConcatMul of bool * qvar * qvar * qatomic * qatomic
| QNeg of qvar
| QNot of qvar
| QConcatShiftLeft of qvar * qvar * qatomic
| QShiftLeft of qvar * qatomic
| QConcatShiftRight of qvar * qvar * qatomic
| QShiftRight of bool * qvar * qatomic
| QInput of qvar
| QCaller of qvar
| QEnter of qvar
| QLeave
| QComment of string
| QAnnot of qannot

type qstmt = {
  (** the kind of statement *)
  skind: qstmtkind;

  (** the line number *)
  sline: int
}

type qprog = qstmt list

type qfile = {
  (** the filename of Qhasm code *)
  filename: string;

  (** the Qhasm code *)
  program: qprog
}





(** ========== Equalities ========== *)

(** Check the syntactical equality of two expressions up to commutativity. *)
let rec eq_qexp e1 e2 =
  match e1, e2 with
    QExpConst n1, QExpConst n2 -> n1 = n2
  | QExpCarry, QExpCarry -> true
  | QExpVar v1, QExpVar v2 -> v1 = v2
  | QExpDeref v1, QExpDeref v2 -> v1 = v2
  | QExpCoef v1, QExpCoef v2 -> v1 = v2
  | QExpNeg e1, QExpNeg e2
  | QExpNot e1, QExpNot e2 -> eq_qexp e1 e2
  | QExpCast (b1, e1, n1), QExpCast (b2, e2, n2) -> b1 = b2 && eq_qexp e1 e2 && n1 = n2
  | QExpAdd (a1, a2), QExpAdd (b1, b2) -> (eq_qexp a1 b1 && eq_qexp a2 b2) || (eq_qexp a1 b2 && eq_qexp a2 b1)
  | QExpSub (a1, a2), QExpSub (b1, b2) -> eq_qexp a1 b1 && eq_qexp a2 b2
  | QExpMul (a1, a2), QExpMul (b1, b2)
  | QExpAnd (a1, a2), QExpAnd (b1, b2)
  | QExpOr (a1, a2), QExpOr (b1, b2)
  | QExpXor (a1, a2), QExpXor (b1, b2) -> (eq_qexp a1 b1 && eq_qexp a2 b2) || (eq_qexp a1 b2 && eq_qexp a2 b1)
  | QExpSmod (a1, a2), QExpSmod (b1, b2)
  | QExpUmod (a1, a2), QExpUmod (b1, b2)
  | QExpPow (a1, a2), QExpPow (b1, b2)
  | QExpConcat (a1, a2), QExpConcat (b1, b2)
  | QExpSll (a1, a2), QExpSll (b1, b2)
  | QExpSrl (a1, a2), QExpSrl (b1, b2)
  | QExpSra (a1, a2), QExpSra (b1, b2) -> eq_qexp a1 b1 && eq_qexp a2 b2
  | QExpSlice (e1, n1, n2), QExpSlice (e2, m1, m2) -> eq_qexp e1 e2 && n1 = m1 && n2 = m2
  | QExpApp (f1, args1), QExpApp (f2, args2) -> f1 = f2 && List.for_all2 eq_qexp args1 args2
  | QExpIte (c1, a1, a2), QExpIte (c2, b1, b2) -> eq_qbexp c1 c2 && eq_qexp a1 b1 && eq_qexp a2 b2
  | _ -> false

(** Check the syntactical equality of two Boolean expressions up to commutativity. *)
and eq_qbexp e1 e2 =
  match e1, e2 with
    QBexpTrue, QBexpTrue -> true
  | QBexpEq (a1, a2), QBexpEq (b1, b2)
  | QBexpNe (a1, a2), QBexpNe (b1, b2) -> (eq_qexp a1 b1 && eq_qexp a2 b2) || (eq_qexp a1 b2 && eq_qexp a2 b1)
  | QBexpComp (a1, c1, a2), QBexpComp (b1, c2, b2) -> (eq_qexp a1 b1 && eq_qexp a2 b2) || (dual_of_cop c1 = c2 && eq_qexp a1 b2 && eq_qexp a2 b1)
  | QBexpNeg e1, QBexpNeg e2 -> eq_qbexp e1 e2
  | QBexpAnd (a1, a2), QBexpAnd (b1, b2)
  | QBexpOr (a1, a2), QBexpOr (b1, b2) -> (eq_qbexp a1 b1 && eq_qbexp a2 b2) || (eq_qbexp a1 b2 && eq_qbexp a2 b1)
  | QBexpImp (a1, a2), QBexpImp (b1, b2) -> eq_qbexp a1 b1 && eq_qbexp a2 b2
  | QBexpApp (p1, args1), QBexpApp (p2, args2) -> p1 = p2 && List.for_all2 eq_qexp args1 args2
  | _ -> false





(** ========== Architectures ========== *)


(** Supported architecture. *)
type architecture = AMD64 | ARM

(** The target architecture. *)
let architecture = ref AMD64

let wordsize = ref 64

let bytesize = ref 8

(** A list of supported architectures. *)
let architectures = [AMD64; ARM]

let string_of_architecture arch =
  match arch with
    AMD64 -> "amd64"
  | ARM -> "arm"

let architecture_of_string str =
  if str = "amd64" || str = "AMD64" then
    Some AMD64
  else if str = "arm" || str = "ARM" then
    Some ARM
  else
    None

(** Returns the default variable type in the current architecture. *)
let arch_type = ref QInt64

(** Returns the default signed variable type for casting in the current architecture. *)
let arch_typecs = ref QCastInt64

(** Returns the default unsigned variable type for casting in the current architecture. *)
let arch_typecu = ref QCastUInt64

(** Returns the default signed type for variable multiplication with double wordsizes. *)
let arch_mul_typecs = ref QCastInt128

(** Returns the default unsigned type for variable multiplication with double wordsizes. *)
let arch_mul_typecu = ref QCastUInt128

let set_architecture arch = 
  let _ = architecture := arch in
  match !architecture with
    AMD64 ->
      wordsize := 64;
      bytesize := !wordsize / 8;
      arch_type := QInt64;
      arch_typecs := QCastInt64;
      arch_typecu := QCastUInt64;
      arch_mul_typecs := QCastInt128;
      arch_mul_typecu := QCastUInt128
  | ARM ->
    wordsize := 32;
    bytesize := !wordsize / 8;
    arch_type := QInt32;
    arch_typecs := QCastInt32;
    arch_typecu := QCastUInt32;
    arch_mul_typecs := QCastInt64;
    arch_mul_typecu := QCastUInt64

let get_architecture () = !architecture





(** ========== String Outputs ========== *)


let string_of_qtype t =
  match t with
  | QInt64 -> "int64"
  | QInt32 -> "int32"
  | QInt3232 -> "int3232"
  | QInt6464 -> "int6464"
  | QFloat80 -> "float80"
  | QStack32 -> "stack32"
  | QStack64 -> "stack64"
  | QStack128 -> "stack128"
  | QStack256 -> "stack256"
  | QStack512 -> "stack512"

let string_of_qtypec t =
  match t with
    QCastInt8 -> "int8"
  | QCastInt16 -> "int16"
  | QCastInt32 -> "int32"
  | QCastInt64 -> "int64"
  | QCastInt128 -> "int128"
  | QCastUInt8 -> "uint8"
  | QCastUInt16 -> "uint16"
  | QCastUInt32 -> "uint32"
  | QCastUInt64 -> "uint64"
  | QCastUInt128 -> "uint128"

let string_of_qaddr addr =
  match addr with
    QAddrBO (base, offset) -> base.vname ^ " + " ^ string_of_int offset
  | QAddrBI (base, index) -> base.vname ^ " + " ^ index.vname
  | QAddrBIS (base, index) -> base.vname ^ " + " ^ index.vname ^ " * " ^ string_of_int !bytesize
  | QAddrBOIS (base, offset, index) -> base.vname ^ " + " ^ string_of_int offset ^ " + " ^ index.vname ^ " * " ^ string_of_int !bytesize

let string_of_qaddr_short addr =
  match addr with
    QAddrBO (base, offset) -> base.vname ^ "[" ^ string_of_int offset ^ "]"
  | QAddrBI (base, index) -> base.vname ^ "[" ^ index.vname ^ "]"
  | QAddrBIS (base, index) -> base.vname ^ "[" ^ index.vname ^ " * " ^ string_of_int !bytesize ^ "]"
  | QAddrBOIS (base, offset, index) -> base.vname ^ "[" ^ string_of_int offset ^ " + " ^ index.vname ^ " * " ^ string_of_int !bytesize ^ "]"

let string_of_qconst c =
  match c with
    QCDec n -> string_of_big_int n
  | QCHex n -> 
    if n.[0] = '-' then
      "- 0x" ^ (String.sub n 1 (String.length n - 1))
    else
      "0x" ^ n

let string_of_qatomic e =
  match e with
    QAConst n -> string_of_qconst n
  | QACarry -> "carry"
  | QAVar v -> v.vname
  | QADeref addr -> "*(" ^ string_of_qtypec !arch_typecu ^ " *)(" ^ string_of_qaddr addr ^ ")"
  | QACoef v -> "*(" ^ string_of_qtypec !arch_typecu ^ " *) &" ^ v.vname

let string_of_qatomic_short e =
  match e with
    QAConst n -> string_of_qconst n
  | QACarry -> "carry"
  | QAVar v -> v.vname
  | QADeref addr -> string_of_qaddr_short addr
  | QACoef v -> "*(" ^ string_of_qtypec !arch_typecu ^ " *) &" ^ v.vname

let string_of_qexpr e =
  match e with
    QExprAtomic v -> if !shorthand then string_of_qatomic_short v else string_of_qatomic v
  | QExprAdd2 (v1, v2) -> string_of_qatomic v1 ^ " + " ^ string_of_qatomic v2
  | QExprAdd3 (v1, v2, v3) -> string_of_qatomic v1 ^ " + " ^ string_of_qatomic v2 ^ " + " ^ string_of_qatomic v3
  | QExprMul2 (v1, v2) -> string_of_qatomic v1 ^ " * " ^ string_of_qatomic v2
  | QExprAnd2 (v1, v2) -> string_of_qatomic v1 ^ " & " ^ string_of_qatomic v2
  | QExprSll (v1, v2) -> string_of_qatomic v1 ^ " << " ^ string_of_qatomic v2
  | QExprSrl (v1, v2) -> string_of_qatomic v1 ^ " unsigned>> " ^ string_of_qatomic v2
  | QExprAdd2Sll (v1, v2, v3) -> string_of_qatomic v1 ^ " + (" ^ string_of_qatomic v2 ^ " << " ^ string_of_qatomic v3 ^ ")"
  | QExprAdd2Srl (v1, v2, v3) -> string_of_qatomic v1 ^ " + (" ^ string_of_qatomic v2 ^ " unsigned>> " ^ string_of_qatomic v3 ^ ")"

let string_of_qaddexpr e =
  match e with
    QAddExprAtomic v -> string_of_qatomic v
  | QAddExprAdd2 (v1, v2) -> string_of_qatomic v1 ^ " + " ^ string_of_qatomic v2

let string_of_qsubexpr e = 
  match e with
    QSubExprAtomic v -> string_of_qatomic v
  | QSubExprSub2 (v1, v2) -> string_of_qatomic v1 ^ " - " ^ string_of_qatomic v2

let precedence_of_qexp e =
  match e with
    QExpConst _
  | QExpCarry
  | QExpVar _ 
  | QExpDeref _
  | QExpCoef _ -> 0
  | QExpNeg _
  | QExpNot _ -> 2
  | QExpCast _ -> 1
  | QExpAdd _
  | QExpSub _ -> 5
  | QExpMul _
  | QExpAnd _
  | QExpOr _
  | QExpXor _
  | QExpSmod _
  | QExpUmod _ -> 4
  | QExpPow _
  | QExpConcat _ -> 3
  | QExpSll _
  | QExpSrl _
  | QExpSra _ -> 4
  | QExpSlice _ -> 0
  | QExpApp _ -> 0
  | QExpIte _ -> 6

let precedence_of_qbexp e =
  match e with
    QBexpTrue -> 0
  | QBexpEq _
  | QBexpNe _
  | QBexpComp _ -> 2
  | QBexpNeg _ -> 1
  | QBexpAnd _ -> 3
  | QBexpOr _ -> 4
  | QBexpImp _ -> 5
  | QBexpApp _ -> 0

(**
   * Expressions in annotations.
*)
let rec string_of_qexp e =
  let p = precedence_of_qexp e in
  match e with
    QExpConst n -> string_of_big_int n
  | QExpCarry -> "carry"
  | QExpVar v -> v.vname
  | QExpDeref addr ->
    begin
      if !shorthand then
        match addr with
          QAddrBO (b, o) -> b.vname ^ "[" ^ string_of_int o ^ "]"
        | QAddrBI (b, i) -> b.vname ^ "[" ^ i.vname ^ "]"
        | QAddrBIS (b, i) -> b.vname ^ "[" ^ i.vname ^ " * " ^ string_of_int !bytesize ^ "]"
        | QAddrBOIS (b, o, i) -> b.vname ^ "[" ^ string_of_int o ^ " + " ^ i.vname ^ " * " ^ string_of_int !bytesize ^ "]"
      else
        "mem" ^ string_of_int !wordsize ^ "[" ^
          (
            match addr with
              QAddrBO (b, o) -> b.vname ^ " + " ^ string_of_int o
            | QAddrBI (b, i) -> b.vname ^ " + " ^ i.vname
            | QAddrBIS (b, i) -> b.vname ^ " + " ^ i.vname ^ " * " ^ string_of_int !bytesize
            | QAddrBOIS (b, o, i) -> b.vname ^ " + " ^ string_of_int o ^ " + " ^ i.vname ^ " * " ^ string_of_int !bytesize
        ) ^ "]"
    end
  | QExpCoef v -> "mem" ^ string_of_int !wordsize ^ "[" ^ v.vname ^ "]"
  | QExpNeg e -> "-" ^ enclose p e
  | QExpNot e -> "~" ^ enclose p e
  | QExpCast (signed, e, n) -> enclose p e ^ "@" ^ (if signed then "" else "u") ^ string_of_int n
  | QExpAdd (e1, e2) -> enclose p e1 ^ " + " ^ enclose p e2
  | QExpSub (e1, e2) -> enclose p e1 ^ " - " ^ enclose p e2
  | QExpMul (e1, e2) -> enclose p e1 ^ " * " ^ enclose p e2
  | QExpAnd (e1, e2) -> enclose p e1 ^ " & " ^ enclose p e2
  | QExpOr (e1, e2) -> enclose p e1 ^ " | " ^ enclose p e2
  | QExpXor (e1, e2) -> enclose p e1 ^ " ^ " ^ enclose p e2
  | QExpSmod (e1, e2) -> enclose p e1 ^ " % " ^ enclose p e2
  | QExpUmod (e1, e2) -> enclose p e1 ^ " %u " ^ enclose p e2
  | QExpPow (e, n) -> enclose p e ^ " ** " ^ enclose p n
  | QExpConcat (e1, e2) -> enclose p e1 ^ "." ^ enclose p e2
  | QExpSll(e1, e2) -> enclose p e1 ^ " << " ^ enclose p e2
  | QExpSrl (e1, e2) -> enclose p e1 ^ " >> " ^ enclose p e2
  | QExpSra (e1, e2) -> enclose p e1 ^ " >>a " ^ enclose p e2
  | QExpSlice (e, i, j) -> enclose p e ^ "[" ^ string_of_int i ^ ", " ^ string_of_int j ^ "]"
  | QExpApp (fd, actuals) -> fd.svar.vname ^ "(" ^ String.concat ", " (List.map string_of_qexp actuals) ^ ")"
  | QExpIte (b, e1, e2) -> enclose_b 5 b ^ " ? " ^ enclose p e1 ^ " : " ^ enclose p e2
and enclose p e =
  if precedence_of_qexp e >= p then
    "(" ^ string_of_qexp e ^ ")"
  else
    string_of_qexp e

(**
   * Boolean expressions in annotations.
*)
and string_of_qbexp be =
  let p = precedence_of_qbexp be in
  match be with
    QBexpTrue -> "true"
  | QBexpEq (e1, e2) -> string_of_qexp e1 ^ " = " ^ string_of_qexp e2
  | QBexpNe (e1, e2) -> string_of_qexp e1 ^ " != " ^ string_of_qexp e2
  | QBexpComp (e1, op, e2) -> string_of_qexp e1 ^ " " ^ string_of_cop op ^ " " ^ string_of_qexp e2
  | QBexpNeg e -> "~ " ^ enclose_b p e
  | QBexpAnd (e1, e2) -> enclose_b p e1 ^ " /\\ " ^ enclose_b p e2
  | QBexpOr (e1, e2) -> enclose_b p e1 ^ " \\/ " ^ enclose_b p e2
  | QBexpImp (e1, e2) -> enclose_b p e1 ^ " -> " ^ enclose_b p e2
  | QBexpApp (p, actuals) -> p.pvar.vname ^ "(" ^ String.concat ", " (List.map string_of_qexp actuals) ^ ")"
and enclose_b p e =
  if precedence_of_qbexp e >= p then
    "(" ^ string_of_qbexp e ^ ")"
  else
    string_of_qbexp e

(**
   * Annotations.
*)
let string_of_qannot annot =
  match annot with
    QAuxVar (v, eop) ->
      begin
        match eop with
          None -> "var " ^ v.vname ^ "@u" ^ string_of_int v.vsize
        | Some e -> "var " ^ v.vname ^ " = " ^ string_of_qexp e
      end
  | QConst e -> "const " ^ string_of_qexp e
  | QFunction fd -> "var " ^ fd.svar.vname ^ "(" ^
    (String.concat ", " (List.map (fun v -> v.vname ^ "@u" ^ string_of_int v.vsize) fd.sformals)) ^ ") = " ^ string_of_qexp fd.sexp
  | QPredicate p -> "predicate " ^ p.pvar.vname ^ "(" ^
    (String.concat ", " (List.map (fun v -> v.vname ^ "@u" ^ string_of_int v.vsize) p.pformals)) ^ ") = " ^ string_of_qbexp p.pbexp
  | QInvariant e -> "inv " ^ string_of_qbexp e
  | QAssume e -> "assume " ^ string_of_qbexp e
  | QAssert e -> "assert " ^ string_of_qbexp e
  | QCut e -> "cut " ^ string_of_qbexp e

let string_of_qstmtkind k =
  match k with
    QVar (t, v) -> string_of_qtype t ^ " " ^ v.vname
  | QLoad (v, t, addr) -> v.vname ^ " = *(" ^ string_of_qtypec t ^ " *)(" ^ string_of_qaddr addr ^ ")"
  | QStore (t, addr, v) -> "*(" ^ string_of_qtypec t ^ " *)(" ^ string_of_qaddr addr ^ ") = " ^ string_of_qatomic v
  | QAssign (v, e) -> v.vname ^ " = " ^ string_of_qexpr e
  | QAssignIfCarry (v, e, negative) -> v.vname ^ " = " ^ string_of_qexpr e ^ " if " ^ (if negative then "!" else "") ^ "carry"
  | QAdd (v, e) -> v.vname ^ " += " ^ string_of_qaddexpr e
  | QAddCarry (v, e) -> "carry ? " ^ v.vname ^ " += " ^ string_of_qaddexpr e
  | QSub (v, e) -> v.vname ^ " -= " ^ string_of_qsubexpr e
  | QSubCarry (v, e) -> "carry ? " ^ v.vname ^ " -= " ^ string_of_qsubexpr e
  | QMul (v, e) -> v.vname ^ " *= " ^ string_of_qatomic e
  | QAnd (v, e) -> v.vname ^ " &= " ^ string_of_qatomic e
  | QOr (v, e) -> v.vname ^ " |= " ^ string_of_qatomic e
  | QXor (v, e) -> v.vname ^ " ^= " ^ string_of_qatomic e
  | QConcatMul (s, v1, v2, v3, v4) -> 
    "(" ^ (if s then string_of_qtypec !arch_mul_typecs else string_of_qtypec !arch_mul_typecu) ^ ") " ^
      v1.vname ^ " " ^ v2.vname ^ " = " ^ string_of_qatomic v3 ^ " * " ^ string_of_qatomic v4
  | QAddConcatMul (s, v1, v2, v3, v4) -> 
    "(" ^ (if s then string_of_qtypec !arch_mul_typecs else string_of_qtypec !arch_mul_typecu) ^ ") " ^
      v1.vname ^ " " ^ v2.vname ^ " += " ^ string_of_qatomic v3 ^ " * " ^ string_of_qatomic v4
  | QNeg v -> v.vname ^ " = -" ^ v.vname
  | QNot v -> v.vname ^ " = ~" ^ v.vname
  | QConcatShiftLeft (v1, v2, e) -> v1.vname ^ " = (" ^ v1.vname ^ "." ^ v2.vname ^ ") << " ^ string_of_qatomic e
  | QShiftLeft (v, e) -> v.vname ^ " <<= " ^ string_of_qatomic e
  | QConcatShiftRight (v1, v2, e) -> v1.vname ^ " = (" ^ v2.vname ^ " " ^ v1.vname ^ ") >> " ^ string_of_qatomic e
  | QShiftRight (s, v, e) -> 
    "(" ^ (if s then string_of_qtypec !arch_typecs else string_of_qtypec !arch_typecu) ^ ") " ^ 
      v.vname ^ " >>= " ^ string_of_qatomic e
  | QInput v -> "input " ^ v.vname
  | QCaller v -> "caller " ^ v.vname
  | QEnter v -> "enter " ^ v.vname
  | QLeave -> "leave"
  | QComment str -> "#" ^ str
  | QAnnot annot -> "#// " ^ string_of_qannot annot

let string_of_qstmt stmt = string_of_qstmtkind stmt.skind

let string_of_qprog prog = String.concat "\n" (List.map string_of_qstmt prog)





(** ========== Conversions from Qhasm Expressions to Annotation Expressions ========== *)


let qexp_of_const n = QExpConst (big_int_of_int n)

let qexp_of_qvar v = QExpVar v

let qexp_of_qconst e =
  match e with
    QCDec n -> QExpConst n
  | QCHex n -> QExpConst (big_int_of_hex n)

let qexp_of_qaddr addr = QExpDeref addr

let qexp_of_deref (v, n) = QExpDeref (QAddrBO (v, n))

let qexp_of_coef v = QExpCoef v

let qexp_of_qatomic e =
  match e with
    QAConst n -> qexp_of_qconst n
  | QACarry -> QExpCast (false, QExpCarry, !wordsize)
  | QAVar v -> qexp_of_qvar v
  | QADeref addr -> qexp_of_qaddr addr
  | QACoef v -> qexp_of_coef v

let qexp_of_qexpr e =
  match e with
    QExprAtomic v -> qexp_of_qatomic v
  | QExprAdd2 (v1, v2) -> QExpAdd (qexp_of_qatomic v1, qexp_of_qatomic v2)
  | QExprAdd3 (v1, v2, v3) -> QExpAdd (QExpAdd (qexp_of_qatomic v1, qexp_of_qatomic v2), qexp_of_qatomic v3)
  | QExprMul2 (v1, v2) -> QExpMul (qexp_of_qatomic v1, qexp_of_qatomic v2)
  | QExprAnd2 (v1, v2) -> QExpAnd (qexp_of_qatomic v1, qexp_of_qatomic v2)
  | QExprSll (v1 ,v2) -> QExpSll (qexp_of_qatomic v1, qexp_of_qatomic v2)
  | QExprSrl (v1 ,v2) -> QExpSrl (qexp_of_qatomic v1, qexp_of_qatomic v2)
  | QExprAdd2Sll (v1 ,v2, v3) -> QExpAdd (qexp_of_qatomic v1, QExpSll (qexp_of_qatomic v2, qexp_of_qatomic v3))
  | QExprAdd2Srl (v1, v2, v3) -> QExpAdd (qexp_of_qatomic v1, QExpSrl (qexp_of_qatomic v2, qexp_of_qatomic v3))

let qexp_of_qaddexpr e =
  match e with
    QAddExprAtomic v -> qexp_of_qatomic v
  | QAddExprAdd2 (v1, v2) -> QExpAdd (qexp_of_qatomic v1, qexp_of_qatomic v2)

let qexp_of_qsubexpr e =
  match e with
    QSubExprAtomic v -> qexp_of_qatomic v
  | QSubExprSub2 (v1, v2) -> QExpSub (qexp_of_qatomic v1, qexp_of_qatomic v2)





(** ========== Free Variables ========== *)


module VarElm =
struct
  type t = qvar
  let compare v1 v2 = Pervasives.compare v1.vname v2.vname
end

module VarSet = Set.Make(VarElm)

let unions ss = List.fold_left (fun res s -> VarSet.union res s) VarSet.empty ss

let vars_of_qaddr addr =
  match addr with
    QAddrBO (base, _) -> VarSet.singleton base
  | QAddrBI (base, index)
  | QAddrBIS (base, index)
  | QAddrBOIS (base, _, index) -> VarSet.add base (VarSet.singleton index)

let vars_of_qatomic e =
  match e with
    QAConst _
  | QACarry -> VarSet.empty
  | QAVar v -> VarSet.singleton v
  | QADeref addr -> vars_of_qaddr addr
  | QACoef v -> VarSet.singleton v

let vars_of_qexpr e =
  match e with
    QExprAtomic v -> vars_of_qatomic v
  | QExprAdd2 (v1, v2) -> VarSet.union (vars_of_qatomic v1) (vars_of_qatomic v2)
  | QExprAdd3 (v1, v2, v3) -> VarSet.union (VarSet.union (vars_of_qatomic v1) (vars_of_qatomic v2)) (vars_of_qatomic v3)
  | QExprMul2 (v1, v2)
  | QExprAnd2 (v1, v2)
  | QExprSll (v1 ,v2)
  | QExprSrl (v1 ,v2) -> VarSet.union (vars_of_qatomic v1) (vars_of_qatomic v2)
  | QExprAdd2Sll (v1 ,v2, v3)
  | QExprAdd2Srl (v1, v2, v3) -> VarSet.union (VarSet.union (vars_of_qatomic v1) (vars_of_qatomic v2)) (vars_of_qatomic v3)

let vars_of_qaddexpr e =
  match e with
    QAddExprAtomic v -> vars_of_qatomic v
  | QAddExprAdd2 (v1, v2) -> VarSet.union (vars_of_qatomic v1) (vars_of_qatomic v2)

let vars_of_qsubexpr e = 
  match e with
    QSubExprAtomic v -> vars_of_qatomic v
  | QSubExprSub2 (v1, v2) -> VarSet.union (vars_of_qatomic v1) (vars_of_qatomic v2)

(** Returns the variables in an expression. *)
let rec vars_of_qexp e =
  match e with
    QExpConst n -> VarSet.empty
  | QExpCarry -> VarSet.singleton carry_var
  | QExpVar v -> VarSet.singleton v
  | QExpDeref addr ->
    begin
      match addr with
        QAddrBO (b, o) -> VarSet.singleton b
      | QAddrBI (b, i)
      | QAddrBIS (b, i)
      | QAddrBOIS (b, _, i) -> VarSet.add b (VarSet.singleton i)
    end
  | QExpCoef v -> VarSet.singleton v
  | QExpNeg e
  | QExpNot e
  | QExpCast (_, e, _) -> vars_of_qexp e
  | QExpAdd (e1, e2)
  | QExpSub (e1, e2)
  | QExpMul (e1, e2)
  | QExpAnd (e1, e2)
  | QExpOr (e1, e2)
  | QExpXor (e1, e2)
  | QExpSmod (e1, e2)
  | QExpUmod (e1, e2)
  | QExpPow (e1, e2)
  | QExpConcat (e1, e2)
  | QExpSll(e1, e2)
  | QExpSrl (e1, e2)
  | QExpSra (e1, e2) -> VarSet.union (vars_of_qexp e1) (vars_of_qexp e2)
  | QExpSlice (e, _, _) -> vars_of_qexp e
  | QExpApp (fd, actuals) ->
    let vars = List.fold_left (fun vars formal -> VarSet.remove formal vars) (vars_of_qexp fd.sexp) fd.sformals in
    List.fold_left (fun vars actual -> VarSet.union vars (vars_of_qexp actual)) vars actuals
  | QExpIte (b, e1, e2) -> VarSet.union (VarSet.union (vars_of_qbexp b) (vars_of_qexp e1)) (vars_of_qexp e2)

(** Returns the variables in a Boolean expression. *)
and vars_of_qbexp e =
  match e with
    QBexpTrue -> VarSet.empty
  | QBexpEq (e1, e2)
  | QBexpNe (e1, e2)
  | QBexpComp (e1, _, e2) -> VarSet.union (vars_of_qexp e1) (vars_of_qexp e2)
  | QBexpNeg e -> vars_of_qbexp e
  | QBexpAnd (e1, e2)
  | QBexpOr (e1, e2)
  | QBexpImp (e1, e2) -> VarSet.union (vars_of_qbexp e1) (vars_of_qbexp e2)
  | QBexpApp (p, actuals) ->
    let vars = List.fold_left (fun vars formal -> VarSet.remove formal vars) (vars_of_qbexp p.pbexp) p.pformals in
    List.fold_left (fun vars actual -> VarSet.union vars (vars_of_qexp actual)) vars actuals

let vars_of_qannot annot =
  match annot with
    QAuxVar (v, eop) ->
      begin
        match eop with
          None -> VarSet.singleton v
        | Some e -> VarSet.add v (vars_of_qexp e)
      end
  | QConst e -> vars_of_qexp e
  | QFunction fd -> VarSet.singleton fd.svar
  | QPredicate p -> VarSet.singleton p.pvar
  | QInvariant e
  | QAssume e
  | QAssert e
  | QCut e -> vars_of_qbexp e

let vars_of_qstmtkind k =
  match k with
    QVar (_, v) -> VarSet.singleton v
  | QLoad (v, _, addr) -> VarSet.add v (vars_of_qaddr addr)
  | QStore (_, addr, v) -> VarSet.union (vars_of_qaddr addr) (vars_of_qatomic v)
  | QAssign (v, e) -> VarSet.add v (vars_of_qexpr e)
  | QAssignIfCarry (v, e, _) -> VarSet.add carry_var (VarSet.add v (vars_of_qexpr e))
  | QAdd (v, e) -> VarSet.add v (vars_of_qaddexpr e)
  | QAddCarry (v, e) -> VarSet.add v (VarSet.add carry_var (vars_of_qaddexpr e))
  | QSub (v, e) -> VarSet.add v (vars_of_qsubexpr e)
  | QSubCarry (v, e) -> VarSet.add v (VarSet.add carry_var (vars_of_qsubexpr e))
  | QMul (v, e) -> VarSet.add v (vars_of_qatomic e)
  | QAnd (v, e)
  | QOr (v, e)
  | QXor (v, e) -> VarSet.add v (vars_of_qatomic e)
  | QConcatMul (s, v1, v2, v3, v4) -> VarSet.add v1 (VarSet.add v2 (VarSet.union (vars_of_qatomic v3) (vars_of_qatomic v4)))
  | QAddConcatMul (s, v1, v2, v3, v4) -> VarSet.add v1 (VarSet.add v2 (VarSet.union (vars_of_qatomic v3) (vars_of_qatomic v4)))
  | QNeg v
  | QNot v -> VarSet.singleton v
  | QConcatShiftLeft (v1, v2, e) -> VarSet.add v1 (VarSet.add v2 (vars_of_qatomic e))
  | QShiftLeft (v, e) -> VarSet.add v (vars_of_qatomic e)
  | QConcatShiftRight (v1, v2, e) -> VarSet.add v1 (VarSet.add v2 (vars_of_qatomic e))
  | QShiftRight (s, v, e) -> VarSet.add v (vars_of_qatomic e)
  | QInput _
  | QCaller _
  | QEnter _
  | QLeave
  | QComment _ -> VarSet.empty
  | QAnnot annot -> vars_of_qannot annot

let vars_of_qstmt stmt = vars_of_qstmtkind stmt.skind

let vars_of_qprog prog = List.fold_left (fun vars stmt -> VarSet.union vars (vars_of_qstmt stmt)) VarSet.empty prog

let lvals_of_qstmtkind k =
  match k with
    QVar (_, v)
  | QLoad (v, _, _) -> VarSet.singleton v
  | QStore (_, addr, v) -> vars_of_qaddr addr
  | QAssign (v, _)
  | QAssignIfCarry (v, _, _)
  | QAdd (v, _) -> VarSet.singleton v
  | QAddCarry (v, _) -> VarSet.add carry_var (VarSet.singleton v)
  | QSub (v, _) -> VarSet.singleton v
  | QSubCarry (v, _) -> VarSet.add carry_var (VarSet.singleton v)
  | QMul (v, _)
  | QAnd (v, _)
  | QOr (v, _)
  | QXor (v, _) -> VarSet.singleton v
  | QConcatMul (_, v1, v2, _, _) -> VarSet.add v1 (VarSet.singleton v2)
  | QAddConcatMul (_, v1, v2, _, _) -> VarSet.add v1 (VarSet.singleton v2)
  | QNeg v
  | QNot v -> VarSet.singleton v
  | QConcatShiftLeft (v, _, _)
  | QShiftLeft (v, _)
  | QConcatShiftRight (v, _, _)
  | QShiftRight (_, v, _) -> VarSet.singleton v
  | QInput _
  | QCaller _
  | QEnter _
  | QLeave
  | QComment _ -> VarSet.empty
  | QAnnot annot -> VarSet.empty

let lvals_of_qstmt stmt = lvals_of_qstmtkind stmt.skind





(** ========== Bit-Width ========== *)


(**
   * Returns the estimated size of an expression. The wordsize is always returned
   * for constants and carry.
*)
let rec size_of_exp exp =
  match exp with
    QExpConst n -> !wordsize
  | QExpCarry -> 1
  | QExpVar v -> v.vsize
  | QExpDeref _ -> !wordsize
  | QExpCoef _ -> !wordsize
  | QExpNeg e
  | QExpNot e -> size_of_exp e
  | QExpCast (signed, e, n) -> n
  | QExpAdd (e1, e2)
  | QExpSub (e1, e2)
  | QExpMul (e1, e2)
  | QExpAnd (e1, e2)
  | QExpOr (e1, e2)
  | QExpXor (e1, e2)
  | QExpSmod (e1, e2) -> max (size_of_exp e1) (size_of_exp e2)
  | QExpUmod (e1, e2) -> (max (size_of_exp e1) (size_of_exp e2) + 1)
  | QExpPow (e, _) -> size_of_exp e
  | QExpConcat (e1, e2) -> (size_of_exp e1) + (size_of_exp e2)
  | QExpSll (e, _)
  | QExpSrl (e, _)
  | QExpSra (e, _) -> size_of_exp e
  | QExpSlice (_, i, j) -> i - j + 1
  | QExpApp (fd, actuals) -> fd.svar.vsize
  | QExpIte (_, e1, e2) -> max (size_of_exp e1) (size_of_exp e2)



(** ========== Others ========== *)


let signed qt =
  match qt with
    QCastInt8
  | QCastInt16
  | QCastInt32
  | QCastInt64
  | QCastInt128 -> true
  | QCastUInt8
  | QCastUInt16
  | QCastUInt32
  | QCastUInt64
  | QCastUInt128 -> false

(** 
    * Returns true if an expression is pure. An expression is pure if it has
    * neither variable, carry, type casting, concatenation, nor slicing.
*)
let rec pure e =
  match e with
    QExpConst _ -> true
  | QExpCarry
  | QExpVar _
  | QExpDeref _
  | QExpCoef _
  | QExpCast _ -> false
  | QExpNeg e
  | QExpNot e -> pure e
  | QExpAdd (e1, e2)
  | QExpSub (e1, e2)
  | QExpMul (e1, e2)
  | QExpAnd (e1, e2)
  | QExpOr (e1, e2)
  | QExpXor (e1, e2)
  | QExpSmod (e1, e2)
  | QExpUmod (e1, e2) -> pure e1 && pure e2
  | QExpPow (e, n) -> pure e && pure n
  | QExpConcat _ -> false
  | QExpSll (e1, e2)
  | QExpSrl (e1, e2)
  | QExpSra (e1, e2) -> pure e1 && pure e2
  | QExpSlice (e, _, _) -> false
  | QExpApp _ -> false
  | QExpIte (b, e1, e2) -> bpure b && pure e1 && pure e2

(** Returns true if a Boolean expression is pure. *)
and bpure e =
  match e with
    QBexpTrue -> true
  | QBexpEq (e1, e2)
  | QBexpNe (e1, e2)
  | QBexpComp (e1, _, e2) -> pure e1 && pure e2
  | QBexpNeg e -> bpure e
  | QBexpAnd (e1, e2)
  | QBexpOr (e1, e2)
  | QBexpImp (e1, e2) -> bpure e1 && bpure e2
  | QBexpApp _ -> false

(** Evaluates a pure expression. *)
let rec eval e =
  match e with
    QExpConst n -> n
  | QExpCarry -> raise (EvaluationException ("Carry cannot be evaluated."))
  | QExpVar v -> raise (EvaluationException ("Variable " ^ v.vname ^ " cannot be evaluated."))
  | QExpDeref addr -> raise (EvaluationException ("Address " ^ string_of_qaddr addr ^ " cannot be evaluated."))
  | QExpCoef v -> raise (EvaluationException ("Variable " ^ v.vname ^ " cannot be evaluated."))
  | QExpNeg e -> minus_big_int (eval e)
  | QExpNot e -> raise (EvaluationException ("Bit-wise not of pure expressions is not supported."))
  | QExpCast _ -> raise (EvaluationException ("Type casting cannot be evaluated."))
  | QExpAdd (e1, e2) -> add_big_int (eval e1) (eval e2)
  | QExpSub (e1, e2) -> sub_big_int (eval e1) (eval e2)
  | QExpMul (e1, e2) -> mult_big_int (eval e1) (eval e2)
  | QExpAnd (e1, e2) -> and_big_int (eval e1) (eval e2)
  | QExpOr (e1, e2) -> or_big_int (eval e1) (eval e2)
  | QExpXor (e1, e2) -> xor_big_int (eval e1) (eval e2)
  | QExpSmod (e1, e2) -> mod_big_int (eval e1) (eval e2)
  | QExpUmod (e1, e2) -> mod_big_int (eval e1) (eval e2)
  | QExpPow (e, n) -> power_big_int_positive_big_int (eval e) (eval n)
  | QExpConcat _ -> raise (EvaluationException ("Concatenation cannot be evaluated."))
  | QExpSll (e1, e2) -> shift_left_big_int (eval e1) (int_of_big_int (eval e2))
  | QExpSrl (e1, e2) -> shift_right_towards_zero_big_int (eval e1) (int_of_big_int (eval e2))
  | QExpSra (e1, e2) -> shift_right_big_int (eval e1) (int_of_big_int (eval e2)) 
  | QExpSlice _ -> raise (EvaluationException ("Slicing cannot be evaluated."))
  | QExpApp _ -> raise (EvaluationException ("Function application cannot be evaluated."))
  | QExpIte _ -> raise (EvaluationException ("If-then-else cannot be evaluated."))

(** Evaluates a pure expression as an integer. Raise EvaluationException if the expression cannot be expressed as an integer. *)
let rec eval_int e =
  let n = eval e in
  if is_int_big_int n then
    int_of_big_int n
  else
    raise (EvaluationException (string_of_qexp e ^ " cannot be evaluated as an integer."))

let ucast e n = QExpCast (false, e, n)

let cast e n = QExpCast (true, e, n)

let slice e n m = QExpSlice (e, n, m)

let int_of_qconst c =
  match c with
    QCDec n -> int_of_big_int n
  | QCHex n -> int_of_big_int (big_int_of_hex n)

let mkand p q =
  if p == QBexpTrue then
    q
  else if q == QBexpTrue then
    p
  else
    QBexpAnd (p, q)

let addr_base addr =
  match addr with
    QAddrBO (v, _)
  | QAddrBI (v, _)
  | QAddrBIS (v, _)
  | QAddrBOIS (v, _, _) -> v

let carryb = QBexpEq (QExpCarry, QExpConst unit_big_int)

let slice_upper e = QExpSlice (e, !wordsize * 2 - 1, !wordsize)

let slice_lower e = QExpSlice (e, !wordsize - 1, 0)



(** ========== Transformation ========== *)

(** Converts a QInvariant to a QAssume and asserts the invariant in all QCut. *)
let elim_qinvariant p =
  let rec helper invs res unprocessed =
    match unprocessed with
      [] -> res
    | hd::tl ->
      begin
        match hd.skind with
          QAnnot (QInvariant e) -> helper (e::invs) (res@[{skind = QAnnot (QAssume e); sline = hd.sline}]) tl
        | QAnnot (QCut e) -> 
          let e = List.fold_left (fun res inv -> QBexpAnd (res, inv)) e invs in
          helper invs (res@[{skind = QAnnot (QCut e); sline = hd.sline}]) tl
        | _ -> helper invs (res@[hd]) tl
      end in
  helper [] [] p

let find_coef cmap v =
  let c = 
    try
      Hashtbl.find cmap v.vname
    with Not_found ->
      raise (Undefined ("The constant " ^ v.vname ^ " is undefined.")) in
  if String.length c > 2 && String.sub c 0 2 = "0x" then
    big_int_of_hex (String.sub c 2 (String.length c - 2))
  else
    big_int_of_string c

(** Replaces predefined variables by constants. *)
let rec elim_qexp_coef cmap e =
  match e with
    QExpConst _
  | QExpCarry
  | QExpVar _
  | QExpDeref _ -> e
  | QExpCoef v -> QExpConst (find_coef cmap v)
  | QExpNeg e -> QExpNeg (elim_qexp_coef cmap e)
  | QExpNot e -> QExpNot (elim_qexp_coef cmap e)
  | QExpCast (signed, e, n) -> QExpCast (signed, elim_qexp_coef cmap e, n)
  | QExpAdd (e1, e2) -> QExpAdd (elim_qexp_coef cmap e1, elim_qexp_coef cmap e2)
  | QExpSub (e1, e2) -> QExpSub (elim_qexp_coef cmap e1, elim_qexp_coef cmap e2)
  | QExpMul (e1, e2) -> QExpMul (elim_qexp_coef cmap e1, elim_qexp_coef cmap e2)
  | QExpAnd (e1, e2) -> QExpAnd (elim_qexp_coef cmap e1, elim_qexp_coef cmap e2)
  | QExpOr (e1, e2) -> QExpOr (elim_qexp_coef cmap e1, elim_qexp_coef cmap e2)
  | QExpXor (e1, e2) -> QExpXor (elim_qexp_coef cmap e1, elim_qexp_coef cmap e2)
  | QExpSmod (e1, e2) -> QExpSmod (elim_qexp_coef cmap e1, elim_qexp_coef cmap e2)
  | QExpUmod (e1, e2) -> QExpUmod (elim_qexp_coef cmap e1, elim_qexp_coef cmap e2)
  | QExpPow (e1, e2) -> QExpPow (elim_qexp_coef cmap e1, elim_qexp_coef cmap e2)
  | QExpConcat (e1, e2) -> QExpConcat (elim_qexp_coef cmap e1, elim_qexp_coef cmap e2)
  | QExpSll (e1, e2) -> QExpSll (elim_qexp_coef cmap e1, elim_qexp_coef cmap e2)
  | QExpSrl (e1, e2) -> QExpSrl (elim_qexp_coef cmap e1, elim_qexp_coef cmap e2)
  | QExpSra (e1, e2) -> QExpSra (elim_qexp_coef cmap e1, elim_qexp_coef cmap e2)
  | QExpSlice (e, n, m) -> QExpSlice (elim_qexp_coef cmap e, n, m)
  | QExpApp (fn, actuals) -> QExpApp (fn, List.map (elim_qexp_coef cmap) actuals)
  | QExpIte (b, e1, e2) -> QExpIte (elim_qbexp_coef cmap b, elim_qexp_coef cmap e1, elim_qexp_coef cmap e2)

(** Replaces predefined variables by constants. *)
and elim_qbexp_coef cmap b =
  match b with
    QBexpTrue -> b
  | QBexpEq (e1, e2) -> QBexpEq (elim_qexp_coef cmap e1, elim_qexp_coef cmap e2)
  | QBexpNe (e1, e2) -> QBexpNe (elim_qexp_coef cmap e1, elim_qexp_coef cmap e2)
  | QBexpComp (e1, op, e2) -> QBexpComp (elim_qexp_coef cmap e1, op, elim_qexp_coef cmap e2)
  | QBexpNeg e -> QBexpNeg (elim_qbexp_coef cmap e)
  | QBexpAnd (e1, e2) -> QBexpAnd (elim_qbexp_coef cmap e1, elim_qbexp_coef cmap e2)
  | QBexpOr (e1, e2) -> QBexpOr (elim_qbexp_coef cmap e1, elim_qbexp_coef cmap e2)
  | QBexpImp (e1, e2) -> QBexpImp (elim_qbexp_coef cmap e1, elim_qbexp_coef cmap e2)
  | QBexpApp (p, actuals) -> QBexpApp (p, List.map (elim_qexp_coef cmap) actuals)

(**
 * Splits an annotated Qhasm program at every QCut.
 * A QCut will become a QAssert of the former program and will become a QAssume
 * of the latter program. Note that this funcion assumes that there is no
 * QInvariant in the annotated Qhasm program. Also, after splitting, programs
 * may not be well-formed because variables may be used without declarations.
 *)
let elim_qcut prog =
  (* res: the result in the reverse order
   * cur: the processed program in the reverse order
   * stmt: the next statement
   *)
  let helper (res, cur) stmt =
    match stmt.skind with
      QVar _ -> (res, stmt::cur)
    | QAnnot (QCut p) -> 
       let ast = {skind = QAnnot (QAssert p); sline = stmt.sline} in
       let asu = {skind = QAnnot (QAssume p); sline = stmt.sline} in
       ((ast::cur)::res, [asu])
    | _ -> (res, stmt::cur) in
  let (resv, nextv) = List.fold_left helper ([], []) prog in
  let resv =
    match nextv with
      [] -> resv
    | _ -> nextv::resv in
  List.rev (List.map List.rev resv)

(** 
 * Splits an annotated Qhasm program such that a program only has one QAssert.
 * Note that this function assumes that there is no QCut and QInvariant.
 *)
let single_qassert prog =
  let helper (res, cur) stmt =
    match stmt.skind with
      QAnnot (QAssert p) -> ((stmt::cur)::res, cur) 
     | _ -> (res, stmt::cur) in
  let (res, nextv) = List.fold_left helper ([], []) prog in
  let res =
    match nextv with
      [] -> res
    | _ -> res@[nextv] in
  List.rev (List.map List.rev res)

let rec split_conj e =
  match e with
    QBexpAnd (e1, e2) -> (split_conj e1)@(split_conj e2)
  | _ -> [e]

let rec split_disj e =
  match e with
    QBexpOr (e1, e2) -> (split_disj e1)@(split_disj e2)
  | _ -> [e]

(** 
 * Splits conjunctions in every QAssert.
 * Note that this function implies single_qassert and assumes that there is
 * no QCut and QInvariant.
 *)
let split_conjunction prog =
  let helper (res, cur) stmt =
    match stmt.skind with
      QAnnot (QAssert p) -> 
      let progs = List.map (fun e -> {skind = QAnnot (QAssert e); sline = stmt.sline}::cur) (split_conj p) in
      (res@progs, cur)
     | _ -> (res, stmt::cur) in
  let (res, nextv) = List.fold_left helper ([], []) prog in
  let res =
    match nextv with
      [] -> res
    | _ -> res@[nextv] in
  List.map List.rev res

(** Removes statements after the last assertion. *)
let trim prog =
  let rec helper prog =
    match prog with
      [] -> []
    | hd::tl -> 
      begin
        match hd.skind with
          QAnnot (QAssert _) -> prog
        | _ -> helper tl
      end in
  List.rev (helper (List.rev prog))

(** 
    * Removes statements after the last assertion for each program.
    * Empty programs will be discarded.
*)
let trims progs = List.filter (fun prog -> prog <> []) (List.map trim progs)

(** 
    * Over-approximates an annotated program by removing unnecessary assumptions.
    * The input program is assumed to contain neither QCut nor QInvariant.
    * NOTE: If the over-approximated program is verified, the original program
    *       is verified as well.
    * NOTE: If the over-approximated program is not verified, the original
    *       program needs to be verified.
*)
let over_approximate prog =
  let related_assumption vars e = qands (List.filter (fun e -> VarSet.subset (vars_of_qbexp e) vars) (split_conj e)) in
  let remove_useless (oprog, vars) stmt =
    let mkstmt kind = {skind = kind; sline = stmt.sline} in
    match stmt.skind with
      QAnnot (QAuxVar (v, eop)) -> 
      if VarSet.mem v vars then
        (stmt::oprog, VarSet.union (vars_of_qstmt stmt) vars)
      else
        (oprog, vars)
    | QAnnot (QConst _) -> (stmt::oprog, vars)
    | QAnnot (QFunction fd) ->
       if VarSet.mem fd.svar vars then
         (stmt::oprog, vars)
       else
         (oprog, vars)
    | QAnnot (QPredicate p) ->
       if VarSet.mem p.pvar vars then
         (stmt::oprog, vars)
       else
         (oprog, vars)
    | QAnnot (QAssume e) ->
       let related = related_assumption vars e in
       (mkstmt (QAnnot (QAssume related))::oprog, VarSet.union (vars_of_qbexp related) vars)
    | QAnnot (QAssert e) -> (stmt::oprog, VarSet.union (vars_of_qbexp e) vars)
    | QAnnot a -> failwith ("Unexpected annotation in simplifying Qhasm programs:\n" ^ string_of_qannot a)
    | _ -> 
       if VarSet.is_empty (VarSet.inter (lvals_of_qstmt stmt) vars) then
         (stmt::oprog, vars)
       else
         (stmt::oprog, VarSet.union (vars_of_qstmt stmt) vars) in
  let (oprog, _) = List.fold_left remove_useless ([], VarSet.empty) (List.rev prog) in
  oprog

(** Slices a program and keeps only statements relevant to 
    assertions to be proven. *)
let slice_qprog prog =
  let of_list vars = List.fold_left (fun vs v -> VarSet.add v vs) VarSet.empty vars in
  let vars_of_qexp_opt eop = 
    match eop with
      None -> VarSet.empty
    | Some e -> vars_of_qexp e in
  let rec slice_qbexps vars es =
    let (es', vars') = List.fold_left (
      fun (es, vars) e ->
        let vs = vars_of_qbexp e in
        if VarSet.is_empty (VarSet.inter vars vs) then
          (es, vars)
        else
          (e::es, VarSet.union vars vs)
    ) ([], vars) es in
    if VarSet.cardinal vars' > VarSet.cardinal vars then
      slice_qbexps vars' es'
    else
      (es', vars') in
  let helper (processed, vars) stmt =
    match stmt.skind with
      QAnnot (QAuxVar (v, eop)) ->
      if VarSet.mem v vars then
        (stmt::processed, VarSet.union vars (vars_of_qexp_opt eop))
      else
        (processed, vars)
    | QAnnot (QConst e) -> 
       let vars_e = vars_of_qexp e in
       if VarSet.is_empty (VarSet.inter vars vars_e) then
         (processed, vars)
       else
         (stmt::processed, VarSet.union vars vars_e)
    | QAnnot (QFunction fd) ->
       if VarSet.mem fd.svar vars then
         (stmt::processed, 
          VarSet.union vars (VarSet.diff (vars_of_qexp fd.sexp) (of_list fd.sformals)))
       else
         (processed, vars)
    | QAnnot (QPredicate pd) ->
       if VarSet.mem pd.pvar vars then
         (stmt::processed, 
          VarSet.union vars (VarSet.diff (vars_of_qbexp pd.pbexp) (of_list pd.pformals)))
       else
         (processed, vars)
    | QAnnot (QInvariant b)
    | QAnnot (QAssume b) ->
      begin
        match slice_qbexps vars (split_conj b) with
          ([], _) -> (processed, vars)
        | (bs, vars') -> ({skind = QAnnot (QAssume (qands bs)); sline = stmt.sline}::processed, vars')
      end
    | QAnnot (QAssert b)
    | QAnnot (QCut b) -> (stmt::processed, VarSet.union vars (vars_of_qbexp b))
    | _ -> 
       let lvals = lvals_of_qstmt stmt in
       if VarSet.is_empty (VarSet.inter vars lvals) then
         (processed, vars)
       else
         (stmt::processed, VarSet.union vars (vars_of_qstmt stmt))
  in
  let (sliced, _) = List.fold_left helper ([], VarSet.empty) (List.rev prog) in
  sliced



(** ========== Substitution ========== *)

module QExpElm : Set.OrderedType with type t = qexp =
struct
  type t = qexp
  let compare = Pervasives.compare
end

module QExpMap : Map.S with type key = qexp = Map.Make(QExpElm)

module type Subst_t =
sig

  type t

  val empty : t

  val add : t -> qexp -> qexp -> t
    
  val singleton : qexp -> qexp -> t

  val from_list : (qexp * qexp) list -> t
    
  val to_list : t -> (qexp * qexp) list

  val merge : t -> t -> t

  val filter : qexp list -> t -> t

  val to_string : t -> string

end

module Subst =
struct

  type t = qexp QExpMap.t

  let empty = QExpMap.empty

  let add m p e = QExpMap.add p e m

  let addv m v e = add m (QExpVar v) e
    
  let singleton p e = add empty p e

  let singletonv v e = addv empty v e

  let from_list pes = List.fold_left (fun m (p, e) -> add m p e) empty pes

  let from_listv ves = List.fold_left (fun m (v, e) -> addv m v e) empty ves

  let to_list m = QExpMap.bindings m

  let merge subst1 subst2 = QExpMap.merge (
    fun p e1op e2op ->
      match e1op, e2op with
        None, None -> None
      | Some e, None
      | None, Some e -> Some e
      | Some e1, Some e2 when e1 = e2 -> Some e1
      | _ -> raise (InvalidOperation "The substitutions are inconsistent.")
  ) subst1 subst2

  let filter es m = QExpMap.filter (fun key _ -> List.mem key es) m

  let to_string m = String.concat ", " (QExpMap.fold (fun k v res -> (string_of_qexp k ^ " => " ^ string_of_qexp v)::res) m [])

end

let rec sube m exp =
  if QExpMap.mem exp m then
    QExpMap.find exp m
  else
    match exp with
      QExpConst _
    | QExpCarry
    | QExpVar _ -> exp
    | QExpDeref addr ->
      let s v =
        if QExpMap.mem (QExpVar v) m then
          match QExpMap.find (QExpVar v) m with
            QExpVar v -> v
          | _ -> raise (InvalidOperation "The base address or index of a dereference can only be replaced by a variable.")
        else 
          v in
      begin
        match addr with
          QAddrBO (b, o) -> QExpDeref (QAddrBO (s b, o))
        | QAddrBI (b, i) -> QExpDeref (QAddrBI (s b, s i))
        | QAddrBIS (b, i) -> QExpDeref (QAddrBIS (s b, s i))
        | QAddrBOIS (b, o, i) -> QExpDeref (QAddrBOIS (s b, o, s i))
      end
    | QExpCoef _ -> exp
    | QExpNeg e -> QExpNeg (sube m e)
    | QExpNot e -> QExpNot (sube m e)
    | QExpCast (signed, e, n) -> QExpCast (signed, sube m e, n)
    | QExpAdd (e1, e2) -> QExpAdd (sube m e1, sube m e2)
    | QExpSub (e1, e2) -> QExpSub (sube m e1, sube m e2)
    | QExpMul (e1, e2) -> QExpMul (sube m e1, sube m e2)
    | QExpAnd (e1, e2) -> QExpAnd (sube m e1, sube m e2)
    | QExpOr (e1, e2) -> QExpOr (sube m e1, sube m e2)
    | QExpXor (e1, e2) -> QExpXor (sube m e1, sube m e2)
    | QExpSmod (e1, e2) -> QExpSmod (sube m e1, sube m e2)
    | QExpUmod (e1, e2) -> QExpUmod (sube m e1, sube m e2)
    | QExpPow (e, n) -> QExpPow (sube m e, sube m n)
    | QExpConcat (e1, e2) -> QExpConcat (sube m e1, sube m e2)
    | QExpSll (e1, e2) -> QExpSll (sube m e1, sube m e2)
    | QExpSrl (e1, e2) -> QExpSrl (sube m e1, sube m e2)
    | QExpSra (e1, e2) -> QExpSra (sube m e1, sube m e2)
    | QExpSlice (e, i, j) -> QExpSlice (sube m e, i, j)
    | QExpApp (fn, actuals) -> QExpApp (fn, List.map (sube m) actuals)
    | QExpIte (b, e1, e2) -> QExpIte (subb m b, sube m e1, sube m e2)

and subb m e =
  match e with
    QBexpTrue -> QBexpTrue
  | QBexpEq (e1, e2) -> QBexpEq (sube m e1, sube m e2)
  | QBexpNe (e1, e2) -> QBexpNe (sube m e1, sube m e2)
  | QBexpComp (e1, op, e2) -> QBexpComp (sube m e1, op, sube m e2)
  | QBexpNeg e -> QBexpNeg (subb m e)
  | QBexpAnd (e1, e2) -> QBexpAnd (subb m e1, subb m e2)
  | QBexpOr (e1, e2) -> QBexpOr (subb m e1, subb m e2)
  | QBexpImp (e1, e2) -> QBexpImp (subb m e1, subb m e2)
  | QBexpApp (p, actuals) -> QBexpApp (p, List.map (sube m) actuals)

(** 
    * Returns a functor that takes a list of expressions and returns an
    * expression obtained by substituting the expressions for the specified
    * variables in the specified expression.
*)
let mkfunctor e formals =
  fun actuals ->
    try
      sube (Subst.from_listv (List.combine formals actuals)) e
    with (Invalid_argument _) ->
        raise (InvalidOperation ("The number of actuals (" ^ string_of_int (List.length actuals) ^ 
                 ") does not match the number of formals (" ^ string_of_int (List.length formals) ^ ")."))

(** 
    * Returns a functor that takes a list of expressions and returns a Boolean
    * expression obtained by substituting the expressions for the specified
    * variables in the specified Boolean expression.
*)
let mkfunctor_b e formals =
  fun actuals ->
    try
      subb (Subst.from_listv (List.combine formals actuals)) e
    with (Invalid_argument _) ->
        raise (InvalidOperation ("The number of actuals (" ^ string_of_int (List.length actuals) ^ 
                 ") does not match the number of formals (" ^ string_of_int (List.length formals) ^ ")."))

(** Apply a function to actual parameters. *)
let apply f actuals = mkfunctor f.sexp f.sformals actuals

(** Apply a predicate to actual parameters. *)
let apply_b p actuals = mkfunctor_b p.pbexp p.pformals actuals

(** Applies functions and predicates in a Boolean expression. *)
let rec appe e =
  match e with
    QExpConst _
  | QExpCarry
  | QExpVar _
  | QExpDeref _
  | QExpCoef _ -> e
  | QExpNeg e -> QExpNeg (appe e)
  | QExpNot e -> QExpNot (appe e)
  | QExpCast (signed, e, n) -> QExpCast (signed, appe e, n)
  | QExpAdd (e1, e2) -> QExpAdd (appe e1, appe e2)
  | QExpSub (e1, e2) -> QExpSub (appe e1, appe e2)
  | QExpMul (e1, e2) -> QExpMul (appe e1, appe e2)
  | QExpAnd (e1, e2) -> QExpAnd (appe e1, appe e2)
  | QExpOr (e1, e2) -> QExpOr (appe e1, appe e2)
  | QExpXor (e1, e2) -> QExpXor (appe e1, appe e2)
  | QExpSmod (e1, e2) -> QExpSmod (appe e1, appe e2)
  | QExpUmod (e1, e2) -> QExpUmod (appe e1, appe e2)
  | QExpPow (e1, e2) -> QExpPow (appe e1, appe e2)
  | QExpConcat (e1, e2) -> QExpConcat (appe e1, appe e2)
  | QExpSll (e1, e2) -> QExpSll (appe e1, appe e2)
  | QExpSrl (e1, e2) -> QExpSrl (appe e1, appe e2)
  | QExpSra (e1, e2) -> QExpSra (appe e1, appe e2)
  | QExpSlice (e, n, m) -> QExpSlice (appe e, n, m)
  | QExpApp (f, actuals) -> appe (apply f (List.map appe actuals))
  | QExpIte (b, e1, e2) -> QExpIte (appb b, appe e1, appe e2)
and appb q =
  match q with
    QBexpTrue -> q
  | QBexpEq (e1, e2) -> QBexpEq (appe e1, appe e2)
  | QBexpNe (e1, e2) -> QBexpNe (appe e1, appe e2)
  | QBexpComp (e1, op, e2) -> QBexpComp (appe e1, op, appe e2)
  | QBexpNeg b -> QBexpNeg (appb b)
  | QBexpAnd (b1, b2) -> QBexpAnd (appb b1, appb b2)
  | QBexpOr (b1, b2) -> QBexpOr (appb b1, appb b2)
  | QBexpImp (b1, b2) -> QBexpImp (appb b1, appb b2)
  | QBexpApp (p, actuals) -> appb (apply_b p (List.map appe actuals))

let appp prog =
  let f stmt =
    let h kind = {sline = stmt.sline; skind = kind} in
    match stmt.skind with
      QAnnot (QAuxVar (v, eop)) ->
        begin
          match eop with
            None -> stmt
          | Some e -> h (QAnnot (QAuxVar (v, Some (appe e))))
        end
    | QAnnot (QConst e) -> h (QAnnot (QConst (appe e)))
    | QAnnot (QFunction _)
    | QAnnot (QPredicate _) -> stmt
    | QAnnot (QInvariant b) -> h (QAnnot (QInvariant (appb b)))
    | QAnnot (QAssume b) -> h (QAnnot (QAssume (appb b)))
    | QAnnot (QAssert b) -> h (QAnnot (QAssert (appb b)))
    | QAnnot (QCut b) -> h (QAnnot (QCut (appb b)))
    | _ -> stmt in
  List.map f prog

(** Eliminates functions and predicates. *)
let elim_func_pred = appp



(** ========== Unification ========== *)

(** Create a unification variable. *)
let uvar vn = {vname = "?" ^ vn; vsize = 0; vtype = None}

(** Create a unification variable that should match an expression of a specified bit-width. *)
let uvar_of_size vn size = {vname = "?" ^ vn; vsize = size; vtype = None}

(** Check if a variable is a unification variable. *)
let is_uvar v = try String.index v.vname '?' = 0 with Not_found -> false

let combine_subst s1 s2 =
  try
    Some (Subst.merge s1 s2)
  with (InvalidOperation _) ->
    None

let is_some o =
  match o with
    Some x -> true
  | _ -> false

let get_some o =
  match o with
    Some x -> x
  | _ -> raise (InvalidOperation "Encounter None in get_some.")


               

(** ========== Weakest Precondition ========== *)

(** Extends the bit-widths of carries in an expression. *)
let rec extend_carry size e =
  match e with
    QExpConst _ -> e
  | QExpCarry ->
    if size = 0 then
      e
    else
      ucast QExpCarry size
  | QExpVar _
  | QExpDeref _
  | QExpCoef _ -> e
  | QExpNeg e' -> QExpNeg (extend_carry size e')
  | QExpNot e' -> QExpNot (extend_carry size e')
  | QExpCast (signed, e', n) -> QExpCast (signed, extend_carry (size_of_exp e') e', n)
  | QExpAdd (e1, e2) -> QExpAdd (extend_carry size e1, extend_carry size e2)
  | QExpSub (e1, e2) -> QExpSub (extend_carry size e1, extend_carry size e2)
  | QExpMul (e1, e2) -> QExpMul (extend_carry size e1, extend_carry size e2)
  | QExpAnd (e1, e2) -> QExpAnd (extend_carry size e1, extend_carry size e2)
  | QExpOr (e1, e2) -> QExpOr (extend_carry size e1, extend_carry size e2)
  | QExpXor (e1, e2) -> QExpXor (extend_carry size e1, extend_carry size e2)
  | QExpSmod (e1, e2) -> QExpSmod (extend_carry size e1, extend_carry size e2)
  | QExpUmod (e1, e2) -> QExpUmod (extend_carry size e1, extend_carry size e2)
  | QExpPow (e1, e2) -> QExpPow (extend_carry size e1, extend_carry size e2)
  | QExpConcat (e1, e2) -> QExpConcat (extend_carry size e1, extend_carry size e2)
  | QExpSll (e1, e2) -> QExpSll (extend_carry size e1, extend_carry size e2)
  | QExpSrl (e1, e2) -> QExpSrl (extend_carry size e1, extend_carry size e2)
  | QExpSra (e1, e2) -> QExpSra (extend_carry size e1, extend_carry size e2)
  | QExpSlice (e', n, m) -> QExpSlice (extend_carry size e', n, m)
  | QExpApp (fd, args) -> QExpApp (fd, List.map2 (fun formal arg -> extend_carry formal.vsize arg) fd.sformals args)
  | QExpIte (b, e1, e2) -> QExpIte (bextend_carry b, extend_carry size e1, extend_carry size e2)
and bextend_carry b =
  match b with
    QBexpTrue -> b
  | QBexpEq (e1, e2) -> QBexpEq (extend_carry (size_of_exp e1) e1, extend_carry (size_of_exp e2) e2)
  | QBexpNe (e1, e2) -> QBexpNe (extend_carry (size_of_exp e1) e1, extend_carry (size_of_exp e2) e2)
  | QBexpComp (e1, op, e2) -> QBexpComp (extend_carry (size_of_exp e1) e1, op, extend_carry (size_of_exp e2) e2)
  | QBexpNeg b' -> QBexpNeg (bextend_carry b')
  | QBexpAnd (b1, b2) -> QBexpAnd (bextend_carry b1, bextend_carry b2)
  | QBexpOr (b1, b2) -> QBexpOr (bextend_carry b1, bextend_carry b2)
  | QBexpImp (b1, b2) -> QBexpImp (bextend_carry b1, bextend_carry b2)
  | QBexpApp (pred, args) -> QBexpApp (pred, List.map2 (fun formal arg -> extend_carry formal.vsize arg) pred.pformals args)

let extend_carry e = extend_carry (size_of_exp e) e

(** Computes weakest preconditions assuming that the program has no address alias. *)
let wp s q =
  (* Apply functions and predicates first. *)
  let q = appb q in
  match s with
    QVar _ -> q
  | QLoad (v, ty, addr) -> subb (Subst.singletonv v (qexp_of_qaddr addr)) q
  | QStore (ty, addr, v) -> subb (Subst.singleton (qexp_of_qaddr addr) (qexp_of_qatomic v)) q
  | QAssign (v, e) -> subb (Subst.singletonv v (extend_carry (qexp_of_qexpr e))) q
  | QAssignIfCarry (v, e, negative) ->
    let b =
      if negative then
        QBexpEq (QExpCarry, qexp_of_const 0)
      else
        QBexpEq (QExpCarry, qexp_of_const 1) in
    subb
      (Subst.singletonv v (QExpIte (b, qexp_of_qexpr e, qexp_of_qvar v)))
      q
  | QAdd (v, e) -> subb (Subst.singletonv v (QExpAdd (qexp_of_qvar v, extend_carry (qexp_of_qaddexpr e)))) q
  | QAddCarry (v, e) ->
    let add = QExpAdd (ucast (qexp_of_qvar v) (v.vsize + 1), ucast (extend_carry (qexp_of_qaddexpr e)) (v.vsize + 1)) in
    let carry = slice add v.vsize v.vsize in
    let e = slice add (v.vsize - 1) 0 in
    subb (Subst.add (Subst.singletonv v e) QExpCarry carry) q
  | QSub (v, e) -> subb (Subst.singletonv v (QExpSub (qexp_of_qvar v, extend_carry (qexp_of_qsubexpr e)))) q
  | QSubCarry (v, e) ->
    let sub = QExpSub (ucast (qexp_of_qvar v) (v.vsize + 1), ucast (qexp_of_qsubexpr e) (v.vsize + 1)) in
    let carry = slice sub v.vsize v.vsize in
    let e = slice sub (v.vsize - 1) 0 in
    subb (Subst.add (Subst.singletonv v e) QExpCarry carry) q
  | QMul (v, cv) -> subb (Subst.singletonv v (QExpMul (qexp_of_qvar v, qexp_of_qatomic cv))) q
  | QAnd (v, vd) -> subb (Subst.singletonv v (QExpAnd (qexp_of_qvar v, qexp_of_qatomic vd))) q
  | QOr (v, vd) -> subb (Subst.singletonv v (QExpOr (qexp_of_qvar v, qexp_of_qatomic vd))) q
  | QXor (v, vd) -> subb (Subst.singletonv v (QExpXor (qexp_of_qvar v, qexp_of_qatomic vd))) q
  | QConcatMul (signed, v1, v2, v3, v4) ->
    let c = if signed then cast else ucast in
    let mul = QExpMul (c (qexp_of_qatomic v3) (v1.vsize + v2.vsize), c (qexp_of_qatomic v4) (v1.vsize + v2.vsize)) in
    let e1 = slice mul ((v1.vsize + v2.vsize) - 1) v2.vsize in
    let e2 = slice mul (v2.vsize - 1) 0 in
    subb (Subst.from_listv [(v1, e1); (v2, e2)]) q
  | QAddConcatMul (signed, v1, v2, v3, v4) ->
    let c = if signed then cast else ucast in
    let mul = QExpMul (c (qexp_of_qatomic v3) (v1.vsize + v2.vsize), c (qexp_of_qatomic v4) (v1.vsize + v2.vsize)) in
    let add = QExpAdd (QExpConcat (qexp_of_qvar v1, qexp_of_qvar v2), mul) in
    let e1 = slice add ((v1.vsize + v2.vsize) - 1) v2.vsize in
    let e2 = slice add (v2.vsize - 1) 0 in
    subb (Subst.from_listv [(v1, e1); (v2, e2)]) q
  | QNeg v -> subb (Subst.singletonv v (QExpNeg (qexp_of_qvar v))) q
  | QNot v -> subb (Subst.singletonv v (QExpNot (qexp_of_qvar v))) q
  | QConcatShiftLeft (v1, v2, cv) ->
    let e = QExpSll (QExpConcat (qexp_of_qvar v1, qexp_of_qvar v2), qexp_of_qatomic cv) in
    let upper = slice e ((v1.vsize + v2.vsize) - 1) v2.vsize in
    subb (Subst.singletonv v1 upper) q
  | QShiftLeft (v, cv) -> subb (Subst.singletonv v (QExpSll (qexp_of_qvar v, qexp_of_qatomic cv))) q
  | QConcatShiftRight (v1, v2, cv) ->
    let e = QExpSrl (QExpConcat (qexp_of_qvar v2, qexp_of_qvar v1), qexp_of_qatomic cv) in
    let lower = slice e (v2.vsize - 1) 0 in
    subb (Subst.singletonv v1 lower) q
  | QShiftRight (signed, v, cv) ->
    let f e1 e2 = if signed then QExpSra (e1, e2) else QExpSrl (e1, e2) in
    subb (Subst.singletonv v (f (qexp_of_qvar v) (qexp_of_qatomic cv))) q
  | QInput _ 
  | QCaller _
  | QEnter _
  | QLeave
  | QComment _ -> q
  | QAnnot annot ->
    begin
      match annot with
        QAuxVar (v, None) -> q
      | QAuxVar (v, Some e) -> subb (Subst.singletonv v e) q
      | QConst e -> q
      | QFunction f -> q
      | QPredicate p -> q
      | QInvariant e -> q
      | QAssume e -> QBexpImp (e, q)
      | QAssert e -> QBexpAnd (q, e)
      | QCut e -> e
    end

(** Computes the verification conditions with weakest preconditions. *)
let vc_wp prog =
  (* Eliminate QInvariant first. *)
  let prog = elim_qinvariant (appp prog) in
  let gen (vcs, qop) stmt =
    match qop with
      None ->
        begin
          match stmt.skind with
            QAnnot (QAssert e)
          | QAnnot (QCut e) -> (vcs, Some e)
          | _ -> (vcs, None)
        end
    | Some q ->
      begin
        match stmt.skind with
          QAnnot (QCut e) -> ((QBexpImp (e, q))::vcs, Some e)
        | _ -> (vcs, Some (wp stmt.skind q))
      end in
  let (vcs, qop) = List.fold_left gen ([], None) (List.rev prog) in
  match qop with
    None -> vcs
  | Some q -> q::vcs



(** ========== Atomics in Expressions ========== *)

module QExpSet : Set.S with type elt = qexp = Set.Make(QExpElm)

(** Returns the atomics (except constants) in an expression. *)
let rec atomics_of_qexp e =
  match e with
    QExpConst n -> QExpSet.empty
  | QExpCarry
  | QExpVar _
  | QExpDeref _
  | QExpCoef _ -> QExpSet.singleton e
  | QExpNeg e
  | QExpNot e
  | QExpCast (_, e, _) -> atomics_of_qexp e
  | QExpAdd (e1, e2)
  | QExpSub (e1, e2)
  | QExpMul (e1, e2)
  | QExpAnd (e1, e2)
  | QExpOr (e1, e2)
  | QExpXor (e1, e2)
  | QExpSmod (e1, e2)
  | QExpUmod (e1, e2)
  | QExpPow (e1, e2)
  | QExpConcat (e1, e2)
  | QExpSll(e1, e2)
  | QExpSrl (e1, e2)
  | QExpSra (e1, e2) -> QExpSet.union (atomics_of_qexp e1) (atomics_of_qexp e2)
  | QExpSlice (e, _, _) -> atomics_of_qexp e
  | QExpApp (fd, actuals) ->
    let vars = List.fold_left (fun vars formal -> QExpSet.remove (QExpVar formal) vars) (atomics_of_qexp fd.sexp) fd.sformals in
    List.fold_left (fun vars actual -> QExpSet.union vars (atomics_of_qexp actual)) vars actuals
  | QExpIte (b, e1, e2) -> QExpSet.union (QExpSet.union (atomics_of_qbexp b) (atomics_of_qexp e1)) (atomics_of_qexp e2)

(** Returns the atomics (except constants) in a Boolean expression. *)
and atomics_of_qbexp e =
  match e with
    QBexpTrue -> QExpSet.empty
  | QBexpEq (e1, e2)
  | QBexpNe (e1, e2)
  | QBexpComp (e1, _, e2) -> QExpSet.union (atomics_of_qexp e1) (atomics_of_qexp e2)
  | QBexpNeg e -> atomics_of_qbexp e
  | QBexpAnd (e1, e2)
  | QBexpOr (e1, e2)
  | QBexpImp (e1, e2) -> QExpSet.union (atomics_of_qbexp e1) (atomics_of_qbexp e2)
  | QBexpApp (p, actuals) ->
    let vars = List.fold_left (fun vars formal -> QExpSet.remove (QExpVar formal) vars) (atomics_of_qbexp p.pbexp) p.pformals in
    List.fold_left (fun vars actual -> QExpSet.union vars (atomics_of_qexp actual)) vars actuals



(** ========== Symbolic Memory ========== *)

type mem = qbexp list

let join_mems ms1 ms2 =
  List.flatten (List.map (
    fun m1 ->
      List.map (fun m2 -> m1@m2) ms2
  ) ms1)

let qbexp_of_mem mem = qands mem

let qbexp_of_mems mems = qors (List.map qbexp_of_mem mems)

let string_of_mem mem = string_of_qbexp (qands mem)

let vars_of_mem mem = List.fold_left (fun vars b -> VarSet.union vars (vars_of_qbexp b)) VarSet.empty mem

let rec push_negation e =
  match e with
    QBexpTrue -> QBexpNeg QBexpTrue
  | QBexpEq (e1, e2) -> QBexpNe (e1, e2)
  | QBexpNe (e1, e2) -> QBexpEq (e1, e2)
  | QBexpComp (e1, op, e2) -> QBexpComp (e1, neg_of_cop op, e2)
  | QBexpNeg e' -> e'
  | QBexpAnd (e1, e2) -> QBexpOr (push_negation e1, push_negation e2)
  | QBexpOr (e1, e2) -> QBexpAnd (push_negation e1, push_negation e2)
  | QBexpImp (e1, e2) -> QBexpAnd (e1, push_negation e2)
  | QBexpApp (p, actuals) -> push_negation (apply_b p actuals)

(** Convert a Boolean expression to negation normal form. *)
let rec to_nnf e =
  match e with
    QBexpTrue
  | QBexpEq _
  | QBexpNe _
  | QBexpComp _ -> e
  | QBexpNeg e' -> push_negation (to_nnf e')
  | QBexpAnd (e1, e2) -> QBexpAnd (to_nnf e1, to_nnf e2)
  | QBexpOr (e1, e2) -> QBexpOr (to_nnf e1, to_nnf e2)
  | QBexpImp (e1, e2) -> QBexpOr (push_negation (to_nnf e1), to_nnf e2)
  | QBexpApp (p, actuals) -> to_nnf (apply_b p actuals)

(** Convert a Boolean expression in NNF to DNF. *)
let rec to_dnf e =
  match e with
    QBexpTrue
  | QBexpEq _
  | QBexpNe _
  | QBexpComp _
  | QBexpNeg _ -> e
  | QBexpAnd (e1, e2) ->
    begin
      match to_dnf e1, to_dnf e2 with
        QBexpOr (a, b), QBexpOr (c, d) -> qors [mkand a c; mkand a d; mkand b c; mkand b d]
      | QBexpOr (a, b), c -> qors [mkand a c; mkand b c]
      | a, QBexpOr (b, c) -> qors [mkand a b; mkand a c]
      | a, b -> mkand a b
    end
  | QBexpOr (e1, e2) -> QBexpOr (to_dnf e1, to_dnf e2)
  | QBexpImp (e1, e2) -> QBexpOr (to_dnf (push_negation e1), to_dnf e2)
  | QBexpApp (p, actuals) -> to_dnf (apply_b p actuals)

let to_dnf e =
  let e = to_dnf e in
  List.map split_conj (split_disj e)

let to_mem = split_conj

let to_mems = to_dnf



(** ========== Symbolic Execution ========== *)

let is_primed v =
  try
    String.rindex v.vname '\'' > 0
  with Not_found ->
    false

let new_var var es =
  let max var n e =
    VarSet.fold (
      fun v i ->
        try
          let j = String.rindex v.vname '\'' in
          if String.sub v.vname 0 j = var.vname then
            max i (int_of_string (String.sub v.vname (j + 1) (String.length v.vname - j - 1)))
          else
            i
        with Not_found ->
          i
    ) (vars_of_qbexp e) n in
  let next_index var es =
    (List.fold_left (
      fun i e -> max var i e
     ) 0 es) + 1 in
  let add_index var i =
    {vname = var.vname ^ "'" ^ string_of_int i; vsize = var.vsize; vtype = var.vtype} in
  add_index var (next_index var es)

let advance_var v es =
  let v' = new_var v es in
  let subst = Subst.singletonv v (QExpVar v') in
  (v', subst, List.map (subb subst) es)

let advance_addr a es = 
  let v = addr_base a in
  let v' = new_var v es in
  let subst = Subst.singleton (QExpDeref a) (QExpVar v') in
  (v', subst, List.map (subb subst) es)

let advance_carry es =
  let v = new_var carry_var es in
  let subst = Subst.singleton QExpCarry (QExpVar v) in
  (v, subst, List.map (subb subst) es)

let add_with_carry e1 e2 =
  let e1' = QExpCast (false, e1, !wordsize + 1) in
  let e2' = QExpCast (false, e2, !wordsize + 1) in
  let res = QExpAdd (e1', e2') in
  (QExpSlice (res, !wordsize, !wordsize), QExpSlice (res, !wordsize - 1, 0))

let sub_with_carry e1 e2 =
  let e1' = QExpCast (false, e1, !wordsize + 1) in
  let e2' = QExpCast (false, e2, !wordsize + 1) in
  let res = QExpSub (e1', e2') in
  (QExpSlice (res, !wordsize, !wordsize), QExpSlice (res, !wordsize - 1, 0))

(**
   * Symbolicly execute a statement kind. Return a pair (subst, mems) where
   * (1) subst is a substitution of variables with values changed in the
   * statement kind and (2) mems is a list of symbolic memories after the
   * execution. Note that the substitution of a variable is always a primed
   * variable that may not appear in mems.
*)
let symexe_stmtkind skind p =
  match skind with
    QVar (typ, var) -> (Subst.empty, [p])
  | QLoad (v, typ, addr) ->
    let (_, subst, p') = advance_var v p in
    let q = QBexpEq (QExpVar v, sube subst (QExpDeref addr)) in
    (subst, [q::p'])
  | QStore (typ, addr, atomic) ->
    let (_, subst, p') = advance_addr addr p in
    let q = QBexpEq (QExpDeref addr, (sube subst) @@ qexp_of_qatomic @@ atomic) in
    (subst, [q::p'])
  | QAssign (v, e) ->
    let (_, subst, p') = advance_var v p in
    let q = QBexpEq (QExpVar v, (sube subst) @@ qexp_of_qexpr @@ e) in
    (subst, [q::p'])
  | QAssignIfCarry (v, e, neg) ->
      (* use another encoding to split ite to a disjunction? *)
    let (v', subst, p') = advance_var v p in
    let e' = (sube subst) @@ qexp_of_qexpr @@ e in
    let q =
      if neg then
        QBexpEq (QExpVar v, QExpIte (carryb, QExpVar v', e'))
      else
        QBexpEq (QExpVar v, QExpIte (carryb, e', QExpVar v')) in
    (subst, [q::p'])
  | QAdd (v, e) ->
    let (v', subst, p') = advance_var v p in
    let e' = (sube subst) @@ qexp_of_qaddexpr @@ e in
    let q = QBexpEq (QExpVar v, QExpAdd (QExpVar v', e')) in
    (subst, [q::p'])
  | QAddCarry (v, e) ->
    let (v', subst1, p') = advance_var v p in
    let (carry', subst2, p') = advance_carry p' in
    let e' = (sube subst2) @@ (sube subst1) @@ (qexp_of_qaddexpr e) in
    let (carry, res) = add_with_carry (QExpVar v') e' in
    let q1 = QBexpEq (QExpCarry, carry) in
    let q2 = QBexpEq (QExpVar v, res) in
    (Subst.merge subst1 subst2, [q1::q2::p'])
  | QSub (v, e) ->
    let (v', subst, p') = advance_var v p in
    let e' = (sube subst) @@ qexp_of_qsubexpr @@ e in
    let q = QBexpEq (QExpVar v, QExpSub (QExpVar v', e')) in
    (subst, [q::p'])
  | QSubCarry (v, e) ->
    let (v', subst1, p') = advance_var v p in
    let (carry', subst2, p') = advance_carry p' in
    let e' = (sube subst2) @@ (sube subst1) @@ (qexp_of_qsubexpr e) in
    let (carry, res) = sub_with_carry (QExpVar v') e' in
    let q1 = QBexpEq (QExpCarry, carry) in
    let q2 = QBexpEq (QExpVar v, res) in
    (Subst.merge subst1 subst2, [q1::q2::p'])
  | QMul (v, e) ->
    let (v', subst, p') = advance_var v p in
    let e' = (sube subst) @@ qexp_of_qatomic @@ e in
    let q = QBexpEq (QExpVar v, QExpMul (QExpVar v', e')) in
    (subst, [q::p'])
  | QAnd (v, e) ->
    let (v', subst, p') = advance_var v p in
    let e' = (sube subst) @@ qexp_of_qatomic @@ e in
    let q = QBexpEq (QExpVar v, QExpAnd (QExpVar v', e')) in
    (subst, [q::p'])
  | QOr (v, e) ->
    let (v', subst, p') = advance_var v p in
    let e' = (sube subst) @@ qexp_of_qatomic @@ e in
    let q = QBexpEq (QExpVar v, QExpOr (QExpVar v', e')) in
    (subst, [q::p'])
  | QXor (v, e) ->
    let (v', subst, p') = advance_var v p in
    let e' = (sube subst) @@ qexp_of_qatomic @@ e in
    let q = QBexpEq (QExpVar v, QExpXor (QExpVar v', e')) in
    (subst, [q::p'])
  | QConcatMul (signed, v1, v2, e1, e2) ->
    let (v1', subst1, p') = advance_var v1 p in
    let (v2', subst2, p') = advance_var v2 p' in
    let e1' = (sube subst2) @@ (sube subst1) @@ (qexp_of_qatomic e1) in
    let e2' = (sube subst2) @@ (sube subst1) @@ (qexp_of_qatomic e2) in
    let mul = QExpMul (QExpCast (signed, e1', !wordsize * 2), QExpCast (signed, e2', !wordsize * 2)) in
    let q1 = QBexpEq (QExpVar v1, slice_upper mul) in
    let q2 = QBexpEq (QExpVar v2, slice_lower mul) in
    (Subst.merge subst1 subst2, [q1::q2::p'])
  | QAddConcatMul (signed, v1, v2, e1, e2) ->
    let (v1', subst1, p') = advance_var v1 p in
    let (v2', subst2, p') = advance_var v2 p' in
    let e1' = (sube subst2) @@ (sube subst1) @@ (qexp_of_qatomic e1) in
    let e2' = (sube subst2) @@ (sube subst1) @@ (qexp_of_qatomic e2) in
    let mul = QExpAdd (QExpConcat (QExpVar v1, QExpVar v2), QExpMul (QExpCast (signed, e1', !wordsize * 2), QExpCast (signed, e2', !wordsize * 2))) in
    let q1 = QBexpEq (QExpVar v1, slice_upper mul) in
    let q2 = QBexpEq (QExpVar v2, slice_lower mul) in
    (Subst.merge subst1 subst2, [q1::q2::p'])
  | QNeg v ->
    let (v', subst, p') = advance_var v p in
    let q = QBexpEq (QExpVar v, QExpNeg (QExpVar v')) in
    (subst, [q::p'])
  | QNot v ->
    let (v', subst, p') = advance_var v p in
    let q = QBexpEq (QExpVar v, QExpNot (QExpVar v')) in
    (subst, [q::p'])
  | QConcatShiftLeft (v1, v2, v3) ->
    let (v1', subst, p') = advance_var v1 p in
    let res = QExpSll (QExpConcat (QExpVar v1', sube subst (QExpVar v2)), (sube subst) @@ qexp_of_qatomic @@ v3) in
    let q = QBexpEq (QExpVar v1, slice_upper res) in
    (subst, [q::p'])
  | QShiftLeft (v1, v2) ->
    let (v1', subst, p') = advance_var v1 p in
    let res = QExpSll (QExpVar v1', (sube subst) @@ qexp_of_qatomic @@ v2) in
    let q = QBexpEq (QExpVar v1, res) in
    (subst, [q::p'])
  | QConcatShiftRight (v1, v2, v3) ->
    let (v1', subst, p') = advance_var v1 p in
    let res = QExpSrl (QExpConcat (sube subst (QExpVar v2), QExpVar v1'), (sube subst) @@ qexp_of_qatomic @@ v3) in
    let q = QBexpEq (QExpVar v1, slice_lower res) in
    (subst, [q::p'])
  | QShiftRight (signed, v1, v2) ->
    let (v1', subst, p') = advance_var v1 p in
    let f (e1, e2) = if signed then QExpSra (e1, e2) else QExpSrl (e1, e2) in
    let res = f (QExpVar v1', (sube subst) @@ qexp_of_qatomic @@ v2) in
    let q = QBexpEq (QExpVar v1, res) in
    (subst, [q::p'])
  | QInput _
  | QCaller _
  | QEnter _
  | QLeave
  | QComment _ -> (Subst.empty, [p])
  | QAnnot (QAuxVar (v, eop)) ->
    let (v', subst, p') = advance_var v p in
    begin
      match eop with
        None -> (subst, [p'])
      | Some e ->
        let q = QBexpEq (QExpVar v, sube subst e) in
        (subst, [q::p'])
    end
  | QAnnot (QAssume q) -> (Subst.empty, join_mems [p] (to_mems q))
  | QAnnot (QAssert q) -> (Subst.empty, [p])
  | QAnnot (QCut q) -> (Subst.empty, to_mems q)
  | QAnnot _ -> (Subst.empty, [p])

(** Symbolically execute a statement. *)
let symexe_stmt stmt p = symexe_stmtkind stmt.skind p

(** Remove in a substitution primed variables that do not appear in the specified symbolic memories. *)
let filter_subst subst mems =
  let vars = List.fold_left (fun vs mem -> VarSet.union vs (vars_of_mem mem)) VarSet.empty mems in
  QExpMap.fold (
    fun pvar lvar sub ->
      match lvar with
        QExpVar v ->
          if VarSet.mem v vars then
            Subst.add sub pvar lvar
          else
            sub
      | _ -> assert(false)
  ) subst Subst.empty
  
