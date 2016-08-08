
(** Qhasm. Note that as there is no formal description of Qhasm syntax, we may
    allow some instructions not in Qhasm and omit some instructions in Qhasm. *)

open Big_int

exception InvalidAnnotation of string

(** Allow shorter output of annotations. *)
val shorthand : bool ref

val big_int_of_hex : string -> big_int


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

val size_of_qtype : qtype -> int
val size_of_qtypec : qtypec -> int



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
val mkpvar : string -> qtype -> qvar

(** Makes a general variable with a bit-width. *)
val mkqvar : string -> int -> qvar

(** The 1-bit carry variable. *)
val carry_var : qvar

(**
   addr =
   * base + offset
   * base + index
   * base + index * scale            -- the scale is always 8
   * base + offset + index * scale   -- the scale is always 8
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

val dual_of_cop : cop -> cop

val neg_of_cop : cop -> cop
  
val string_of_cop : cop -> string

val cop_signed : cop -> bool

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
val qands : qbexp list -> qbexp

(** 
 * Returns e1 \/ e2 \/ ... \/ en for a list of expressions [e1; e2; ...; en].
 * Returns (QBexpNeg QBexpTrue) if the list is empty.
 *)
val qors : qbexp list -> qbexp

(**
 * Returns (e1 op1 e) /\ (e op2 e2) for qrange e1 op1 e op2 e2.
 *)
val qrange : qexp -> cop -> qexp -> cop -> qexp -> qbexp

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
val eq_qexp : qexp -> qexp -> bool

(** Check the syntactical equality of two Boolean expressions up to commutativity. *)
val eq_qbexp : qbexp -> qbexp -> bool



(** ========== Architectures ========== *)

(** Supported architecture. *)
type architecture = AMD64 | ARM

(** The target architecture. Always use set_architecture to update the target 
    architecture instead of changing this reference directly. *)
val architecture : architecture ref

val wordsize : int ref

val bytesize : int ref

(** A list of supported architectures. *)
val architectures : architecture list

val string_of_architecture : architecture -> string

val architecture_of_string : string -> architecture option

(** Returns the default variable type in the current architecture. *)
val arch_type : qtype ref

(** Returns the default signed variable type for casting in the current architecture. *)
val arch_typecs : qtypec ref

(** Returns the default unsigned variable type for casting in the current architecture. *)
val arch_typecu : qtypec ref

(** Returns the default signed type for variable multiplication with double wordsizes. *)
val arch_mul_typecs : qtypec ref

(** Returns the default unsigned type for variable multiplication with double wordsizes. *)
val arch_mul_typecu : qtypec ref

val set_architecture : architecture -> unit

val get_architecture : unit -> architecture



(** ========== String Outputs ========== *)

val string_of_qtype : qtype -> string
val string_of_qtypec : qtypec -> string
val string_of_qaddr : qaddr -> string
val string_of_qconst : qconst -> string
val string_of_qatomic : qatomic -> string
val string_of_qexpr : qexpr -> string
val string_of_qaddexpr : qaddexpr -> string
val string_of_qsubexpr : qsubexpr -> string
val string_of_qexp : qexp -> string
val string_of_qbexp : qbexp -> string
val string_of_qannot : qannot -> string
val string_of_qstmtkind : qstmtkind -> string
val string_of_qstmt : qstmt -> string
val string_of_qprog : qprog -> string



(** ========== Conversions from Qhasm Expressions to Annotation Expressions ========== *)

val qexp_of_const : int -> qexp
val qexp_of_qvar : qvar -> qexp
val qexp_of_qconst : qconst -> qexp
val qexp_of_qaddr : qaddr -> qexp
val qexp_of_deref : (qvar * int) -> qexp
val qexp_of_coef : qvar -> qexp
val qexp_of_qatomic : qatomic -> qexp
val qexp_of_qexpr : qexpr -> qexp
val qexp_of_qaddexpr : qaddexpr -> qexp
val qexp_of_qsubexpr : qsubexpr -> qexp



(** ========== Free Variables ========== *)

module VarElm : Set.OrderedType with type t = qvar

module VarSet : Set.S with type elt = VarElm.t

val vars_of_qaddr : qaddr -> VarSet.t
val vars_of_qatomic : qatomic -> VarSet.t
val vars_of_qexpr : qexpr -> VarSet.t
val vars_of_qaddexpr : qaddexpr -> VarSet.t
val vars_of_qsubexpr : qsubexpr -> VarSet.t
(** Returns the variables in an expression. *)
val vars_of_qexp : qexp -> VarSet.t
(** Returns the variables in a Boolean expression. *)
val vars_of_qbexp : qbexp -> VarSet.t
val vars_of_qannot : qannot -> VarSet.t
val vars_of_qstmtkind : qstmtkind -> VarSet.t
val vars_of_qstmt : qstmt -> VarSet.t
val vars_of_qprog : qprog -> VarSet.t

val lvals_of_qstmtkind : qstmtkind -> VarSet.t
val lvals_of_qstmt : qstmt -> VarSet.t



(** ========== Bit-Width ========== *)

(**
   * Returns the estimated size of an expression. The wordsize is always returned
   * for constants and carry.
*)
val size_of_exp : qexp -> int



(** ========== Transformation ========== *)

(** Converts a QInvariant to a QAssume and asserts the invariant in all QCut. *)
val elim_qinvariant : qprog -> qprog

(** Replaces predefined variables by constants. *)
val elim_qexp_coef : (string, string) Hashtbl.t -> qexp -> qexp

(** Replaces predefined variables by constants. *)
val elim_qbexp_coef : (string, string) Hashtbl.t -> qbexp -> qbexp

(**
 * Splits an annotated Qhasm program at every QCut.
 * A QCut will become a QAssert of the former program and will become a QAssume
 * of the latter program. Note that this funcion assumes that there is no
 * QInvariant in the annotated Qhasm program. Also, after splitting, programs
 * may not be well-formed because variables may be used without declarations.
 *)
val elim_qcut : qprog -> qprog list

(** Eliminates functions and predicates. *)
val elim_func_pred : qprog -> qprog
  
(** 
 * Splits an annotated Qhasm program such that a program only has one QAssert.
 * Note that this function assumes that there is no QCut and QInvariant.
 *)
val single_qassert : qprog -> qprog list

(** 
 * Splits conjunctions in every QAssert.
 * Note that this function implies single_qassert and assumes that there is
 * no QCut and QInvariant.
 *)
val split_conjunction : qprog -> qprog list

(** Removes statements after the last assertion. *)
val trim : qprog -> qprog

(** 
    * Removes statements after the last assertion for each program.
    * Empty programs will be discarded.
*)
val trims : qprog list -> qprog list

(** 
    * Over-approximates an annotated program by removing unnecessary assumptions.
    * The input program is assumed to contain neither QCut nor QInvariant.
    * NOTE: If the over-approximated program is verified, the original program
    *       is verified as well.
    * NOTE: If the over-approximated program is not verified, the original
    *       program needs to be verified.
*)
val over_approximate : qprog -> qprog

(** Slices a program and keeps only statements relevant to 
    assertions to be proven. *)
val slice_qprog : qprog -> qprog



(** ========== Others ========== *)

val signed : qtypec -> bool

(** 
    * Returns true if an expression is pure. An expression is pure if it has
    * neither variable, carry, type casting, concatenation, nor slicing.
*)
val pure : qexp -> bool

(** Returns true if a Boolean expression is pure. *)
val bpure : qbexp -> bool

(** Evaluates a pure expression. *)
val eval : qexp -> big_int

(** Evaluates a pure expression as an integer. Raise EvaluationException if the expression cannot be expressed as an integer. *)
val eval_int : qexp -> int

(** Returns the integer value of a qconst. *)
val int_of_qconst : qconst -> int


(** ========== Substitution ========== *)

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

module Subst : Subst_t

val sube : Subst.t -> qexp -> qexp

val subb : Subst.t -> qbexp -> qbexp
  
(** 
    * Returns a functor that takes a list of expressions and returns an
    * expression obtained by substituting the expressions for the specified
    * variables in the specified expression.
*)
val mkfunctor : qexp -> qvar list -> (qexp list -> qexp)

(** 
    * Returns a functor that takes a list of expressions and returns a Boolean
    * expression obtained by substituting the expressions for the specified
    * variables in the specified Boolean expression.
*)
val mkfunctor_b : qbexp -> qvar list -> (qexp list -> qbexp)

  
(** Apply a function to actual parameters. *)
val apply : qfun -> qexp list -> qexp

(** Apply a predicate to actual parameters. *)
val apply_b : qpred -> qexp list -> qbexp

(** Recursively apply functions and predicates. *)
val appe : qexp -> qexp

(** Recursively apply functions and predicates. *)
val appb : qbexp -> qbexp



(** ========== Unification ========== *)

(** Create a unification variable. *)
val uvar : string -> qvar

(** Check if a variable is a unification variable. *)
val is_uvar : qvar -> bool



(** ========== Weakest Precondition ========== *)

(** Computes weakest preconditions assuming that the program has no address alias. *)
val wp : qstmtkind -> qbexp -> qbexp

(** Computes the verification conditions with weakest preconditions. *)
val vc_wp : qprog -> qbexp list


  
(** ========== Symbolic Memory ========== *)

type mem = qbexp list

val string_of_mem : mem -> string

val vars_of_mem : mem -> VarSet.t

val to_mem : qbexp -> mem

val to_mems : qbexp -> mem list


(** ========== Symbolic Execution ========== *)
  
(**
   * Symbolicly execute a statement kind. Return a pair (subst, mems) where
   * (1) subst is a substitution of variables with values changed in the
   * statement kind and (2) mems is a list of symbolic memories after the
   * execution. Note that the substitution of a variable may not appear in
   * mems.
*)
val symexe_stmtkind : qstmtkind -> mem -> Subst.t * mem list

(** Symbolically execute a statement. *)
val symexe_stmt : qstmt -> mem -> Subst.t * mem list

(** Remove in a substitution primed variables that do not appear in the specified symbolic memories. *)
val filter_subst : Subst.t -> mem list -> Subst.t
  
