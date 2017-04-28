
open Big_int
open Num
open Set
open Map
open Unix
open Names

let qfbv () = "qfbv"

let z3_path = "z3"

let boolector_path = "boolector"

let vname = "x"

type solver = Z3 | Boolector

let default_solver = Z3



(* ------------------------------------------------------------------------- *)
(*  Debugging                                                                *)
(* ------------------------------------------------------------------------- *)

let dbgdir = "."

let unix s =
  let r = Unix.system s in
  if r = r then ()
  else ()

let init_trace () =
  unix ("echo \"\" > " ^ dbgdir ^ "/log_qfbv")

let trace s =
  unix ("echo \"" ^ s ^ "\n\" >> " ^ dbgdir ^ "/log_qfbv")

let fail s =
  trace s; failwith s

let pp_constr x = Pp.msg (Printer.pr_constr x)

let print_constr t =
  if Term.isRel t then trace "Rel"
  else if Term.isVar t then trace "Var"
  else if Term.isInd t then trace "Ind"
  else if Term.isEvar t then trace "Evar"
  else if Term.isMeta t then trace "Meta"
  else if Term.isSort t then trace "Sort"
  else if Term.isCast t then trace "Cast"
  else if Term.isApp t then trace "App"
  else if Term.isLambda t then trace "Lambda"
  else if Term.isLetIn t then trace "LetIn"
  else if Term.isProd t then trace "Prod"
  else if Term.isConst t then trace "Const"
  else if Term.isConstruct t then trace "Construct"
  else if Term.isFix t then trace "Fix"
  else if Term.isCoFix t then trace "CoFix"
  else if Term.isCase t then trace "Case"
  else if Term.isProj t then trace "Proj"
  else if Term.is_Prop t then trace "Prop"
  else if Term.is_Set t then trace "Set"
  else if Term.is_Type t then trace "Type"
  else if Term.iskind t then trace "kind"
  else trace ""



(* ------------------------------------------------------------------------- *)
(*  Access Coq terms                                                         *)
(* ------------------------------------------------------------------------- *)

(* The contrib name is used to locate errors when loading constrs *)
let contrib_name = "qf_bv_plugin"

let find_constant contrib dir s =
  Universes.constr_of_global (Coqlib.find_reference contrib dir s)

let init_constant dir s = find_constant contrib_name dir s

let fresh_id_in_env avoid id env =
  (* ids to be avoided *)
  let ids = (avoid@Termops.ids_of_named_context (Environ.named_context env)) in
  (* generate a new id *)
  Namegen.next_ident_away_in_goal id ids

let new_fresh_id avoid id gl =
  fresh_id_in_env avoid id (Proofview.Goal.env gl)



(* ------------------------------------------------------------------------- *)
(*  Pair                                                                     *)
(* ------------------------------------------------------------------------- *)

module CoqDatatypes = struct
    let path = ["Coq"; "Init"; "Datatypes"]
    let _pair : Term.constr lazy_t = lazy (init_constant path "pair")
  end



(* ------------------------------------------------------------------------- *)
(*  Bool                                                                     *)
(* ------------------------------------------------------------------------- *)

module CoqBool = struct
    let path = ["Coq"; "Init"; "Datatypes"]
    let typ : Term.constr lazy_t = lazy (init_constant path "bool")
    let _true : Term.constr lazy_t = lazy (init_constant path "true")
    let _false : Term.constr lazy_t = lazy (init_constant path "false")
  end

(** Constructs a Coq bool from an OCaml bool. *)
let rec cbool_of_obool b : Constr.t =
  if b then Lazy.force CoqBool._true
  else Lazy.force CoqBool._false

(** Constructs an OCaml bool from a Coq bool. *)
let rec obool_of_cbool (n : Constr.t) : bool =
  if Constr.equal n (Lazy.force CoqBool._true) then true
  else if Constr.equal n (Lazy.force CoqBool._false) then false
  else failwith "Not a valid Coq bool."



(* ------------------------------------------------------------------------- *)
(*  Nat                                                                      *)
(* ------------------------------------------------------------------------- *)

module CoqNat = struct
    let path = ["Coq"; "Init"; "Datatypes"]
    let typ : Term.constr lazy_t = lazy (init_constant path "nat")
    let _S : Term.constr lazy_t = lazy (init_constant path "S")
    let _O : Term.constr lazy_t = lazy (init_constant path "O")
  end

(** Constructs a Coq nat from an OCaml int. *)
let rec cnat_of_oint n : Constr.t =
  if n <= 0 then Lazy.force CoqNat._O
  else Constr.mkApp (Lazy.force CoqNat._S, [| cnat_of_oint (n - 1) |])

(** Constructs an OCaml int from a Coq nat. *)
let rec oint_of_cnat (n : Constr.t) : int =
  if Constr.equal n (Lazy.force CoqNat._O) then 0
  else
    try
      let (constructor, args) = Term.destApp n in
      if Constr.equal constructor (Lazy.force CoqNat._S) then 1 + (oint_of_cnat args.(0))
      else failwith "Not a valid Coq nat."
    with destKO -> failwith "Not a valid Coq nat."



(* ------------------------------------------------------------------------- *)
(*  Positive/N/Z                                                             *)
(* ------------------------------------------------------------------------- *)

module CoqBinNums = struct
    let path = ["Coq"; "Numbers"; "BinNums"]
    let typ : Term.constr lazy_t = lazy (init_constant path "positive")
    let _xI : Term.constr lazy_t = lazy (init_constant path "xI")
    let _xO : Term.constr lazy_t = lazy (init_constant path "xO")
    let _xH : Term.constr lazy_t = lazy (init_constant path "xH")
    let _N0 : Term.constr lazy_t = lazy (init_constant path "N0")
    let _Npos : Term.constr lazy_t = lazy (init_constant path "Npos")
    let _Z0 : Term.constr lazy_t = lazy (init_constant path "Z0")
    let _Zpos : Term.constr lazy_t = lazy (init_constant path "Zpos")
    let _Zneg : Term.constr lazy_t = lazy (init_constant path "Zneg")
  end

let num_0 = Int 0
let num_1 = Int 1
let num_2 = Int 2
let num_10 = Int 10

(** Constructs a Coq positive from an OCaml num. *)
let rec cpos_of_onum (n : num) : Constr.t =
  if n </ num_0 then failwith "Not a positive number."
  else if n =/ num_1 then Lazy.force CoqBinNums._xH
  else if mod_num n num_2 =/ num_0 then Constr.mkApp (Lazy.force CoqBinNums._xO, [| cpos_of_onum (quo_num n num_2) |])
  else Constr.mkApp (Lazy.force CoqBinNums._xI, [| cpos_of_onum (quo_num n num_2) |])

(** Constructs an OCaml num from a Coq positive. *)
let rec onum_of_cpos (n : Constr.t) : num =
  if Constr.equal n (Lazy.force CoqBinNums._xH) then num_1
  else
    try
      let (constructor, args) = Term.destApp n in
      if Constr.equal constructor (Lazy.force CoqBinNums._xI) then num_1 +/ (onum_of_cpos args.(0) */ num_2)
      else if Constr.equal constructor (Lazy.force CoqBinNums._xO) then num_0 +/ (onum_of_cpos args.(0) */ num_2)
      else failwith "Not a valid Coq positive."
    with destKO -> failwith "Not a valid Coq positive."

(** Constructs a Coq N from an OCaml num. *)
let rec cn_of_onum (n : num) : Constr.t =
  if n =/ num_0 then Lazy.force CoqBinNums._N0
  else if n >/ num_0 then Constr.mkApp (Lazy.force CoqBinNums._Npos, [| cpos_of_onum n |])
  else fail (string_of_num n ^ " is not a valid Coq N.")

(** Constructs an OCaml num from a Coq N. *)
let onum_of_cn (n : Constr.t) : num =
  if Constr.equal n (Lazy.force CoqBinNums._N0) then num_0
  else
    try
      let (constructor, args) = Term.destApp n in
      if Constr.equal constructor (Lazy.force CoqBinNums._Npos) then onum_of_cpos args.(0)
      else failwith "Not a valid Coq N."
    with destKO -> failwith "Not a valid Coq N."

(** Constructs a Coq Z from an OCaml num. *)
let rec cz_of_onum (n : num) : Constr.t =
  if n =/ num_0 then Lazy.force CoqBinNums._Z0
  else if n >/ num_0 then Constr.mkApp (Lazy.force CoqBinNums._Zpos, [| cpos_of_onum n |])
  else Constr.mkApp (Lazy.force CoqBinNums._Zneg, [| cpos_of_onum (abs_num n) |])

(** Constructs an OCaml num from a Coq Z. *)
let onum_of_cz (n : Constr.t) : num =
  if Constr.equal n (Lazy.force CoqBinNums._Z0) then num_0
  else
    try
      let (constructor, args) = Term.destApp n in
      if Constr.equal constructor (Lazy.force CoqBinNums._Zpos) then onum_of_cpos args.(0)
      else if Constr.equal constructor (Lazy.force CoqBinNums._Zneg) then minus_num (onum_of_cpos args.(0))
      else failwith "Not a valid Coq Z."
    with destKO -> failwith "Not a valid Coq Z."

(** Constructs a Coq positive from a number string in OCaml. *)
let cpos_of_ostring (str : string) : Constr.t =
  cpos_of_onum (num_of_string str)

(** Constructs a number string in OCaml from a Coq positive. *)
let ostring_of_cpos (n : Constr.t) : string =
  string_of_num (onum_of_cpos n)



(* ------------------------------------------------------------------------- *)
(*  Expressions                                                              *)
(* ------------------------------------------------------------------------- *)

module CoqQFBV = struct
    let path = ["mQhasm"; "QFBVSolve"]
    let _sbvVar : Term.constr lazy_t = lazy (init_constant path "sbvVar")
    let _sbvConst : Term.constr lazy_t = lazy (init_constant path "sbvConst")
    let _sbvNot : Term.constr lazy_t = lazy (init_constant path "sbvNot")
    let _sbvAnd : Term.constr lazy_t = lazy (init_constant path "sbvAnd")
    let _sbvOr : Term.constr lazy_t = lazy (init_constant path "sbvOr")
    let _sbvXor : Term.constr lazy_t = lazy (init_constant path "sbvXor")
    let _sbvNeg : Term.constr lazy_t = lazy (init_constant path "sbvNeg")
    let _sbvAdd : Term.constr lazy_t = lazy (init_constant path "sbvAdd")
    let _sbvSub : Term.constr lazy_t = lazy (init_constant path "sbvSub")
    let _sbvMul : Term.constr lazy_t = lazy (init_constant path "sbvMul")
    let _sbvMod : Term.constr lazy_t = lazy (init_constant path "sbvMod")
    let _sbvShl : Term.constr lazy_t = lazy (init_constant path "sbvShl")
    let _sbvShr : Term.constr lazy_t = lazy (init_constant path "sbvShr")
    let _sbvConcat : Term.constr lazy_t = lazy (init_constant path "sbvConcat")
    let _sbvExtract : Term.constr lazy_t = lazy (init_constant path "sbvExtract")
    let _sbvSlice : Term.constr lazy_t = lazy (init_constant path "sbvSlice")
    let _sbvHigh : Term.constr lazy_t = lazy (init_constant path "sbvHigh")
    let _sbvLow : Term.constr lazy_t = lazy (init_constant path "sbvLow")
    let _sbvZeroExtend : Term.constr lazy_t = lazy (init_constant path "sbvZeroExtend")
    let _sbvSignExtend : Term.constr lazy_t = lazy (init_constant path "sbvSignExtend")

    let _sbvTrue : Term.constr lazy_t = lazy (init_constant path "sbvTrue")
    let _sbvUlt : Term.constr lazy_t = lazy (init_constant path "sbvUlt")
    let _sbvUle : Term.constr lazy_t = lazy (init_constant path "sbvUle")
    let _sbvUgt : Term.constr lazy_t = lazy (init_constant path "sbvUgt")
    let _sbvUge : Term.constr lazy_t = lazy (init_constant path "sbvUge")
    let _sbvEq : Term.constr lazy_t = lazy (init_constant path "sbvEq")
    let _sbvAddo : Term.constr lazy_t = lazy (init_constant path "sbvAddo")
    let _sbvSubo : Term.constr lazy_t = lazy (init_constant path "sbvSubo")
    let _sbvMulo : Term.constr lazy_t = lazy (init_constant path "sbvMulo")
    let _sbvLneg : Term.constr lazy_t = lazy (init_constant path "sbvLneg")
    let _sbvConj : Term.constr lazy_t = lazy (init_constant path "sbvConj")

    let _sbvNil : Term.constr lazy_t = lazy (init_constant path "sbvNil")
    let _sbvCons : Term.constr lazy_t = lazy (init_constant path "sbvCons")

    let _Z3 : Term.constr lazy_t = lazy (init_constant path "Z3")
    let _Boolector : Term.constr lazy_t = lazy (init_constant path "Boolector")
  end

type var = (num * num)

type exp =
  | Var of (int * var)
  | Const of (int * num)
  | Not of (int * exp)
  | And of (int * exp * exp)
  | Or of (int * exp * exp)
  | Xor of (int * exp * exp)
  | Neg of (int * exp)
  | Add of (int * exp * exp)
  | Sub of (int * exp * exp)
  | Mul of (int * exp * exp)
  | Mod of (int * exp * exp)
  | Shl of (int * exp * exp)
  | Shr of (int * exp * exp)
  | Concat of (int * int * exp * exp)
  | Extract of (int * int * int * exp)
  | Slice of (int * int * int * exp)
  | High of (int * int * exp)
  | Low of (int * int * exp)
  | ZeroExtend of (int * int * exp)
  | SignExtend of (int * int * exp)

type bexp =
  | True
  | Ult of (int * exp * exp)
  | Ule of (int * exp * exp)
  | Ugt of (int * exp * exp)
  | Uge of (int * exp * exp)
  | Eq of (int * exp * exp)
  | Addo of (int * exp * exp)
  | Subo of (int * exp * exp)
  | Mulo of (int * exp * exp)
  | Lneg of bexp
  | Conj of (bexp * bexp)

let is_atomic t =
  match t with
  | Var _ | Const _ -> true
  | _ -> false

let rec ovar_of_cvar v =
  let _ = Lazy.force CoqDatatypes._pair in
  if Term.isConst v then
    match Global.body_of_constant (Univ.out_punivs (Term.destConst v)) with
      None -> failwith "Failed to find the definition of constant."
    | Some v' -> ovar_of_cvar v'
  else
    try
      let (constructor, args) = Term.destApp v in
      if Constr.equal constructor (Lazy.force CoqDatatypes._pair) then (onum_of_cn args.(2), onum_of_cn args.(3))
      else fail "Not a valid var (2)."
    with destKO -> fail "Not a valid var (1)."

let rec oexp_of_cexp e =
  if Term.isConst e then
    match Global.body_of_constant (Univ.out_punivs (Term.destConst e)) with
      None -> failwith "Failed to find the definition of constant."
    | Some e' -> oexp_of_cexp e'
  else
    try
      let (constructor, args) = Term.destApp e in
      if Constr.equal constructor (Lazy.force CoqQFBV._sbvVar) then Var (oint_of_cnat args.(0), ovar_of_cvar args.(1))
      else if Constr.equal constructor (Lazy.force CoqQFBV._sbvConst) then Const (oint_of_cnat args.(0), onum_of_cz args.(1))
      else if Constr.equal constructor (Lazy.force CoqQFBV._sbvNot) then Not (oint_of_cnat args.(0), oexp_of_cexp args.(1))
      else if Constr.equal constructor (Lazy.force CoqQFBV._sbvAnd) then And (oint_of_cnat args.(0), oexp_of_cexp args.(1), oexp_of_cexp args.(2))
      else if Constr.equal constructor (Lazy.force CoqQFBV._sbvOr) then Or (oint_of_cnat args.(0), oexp_of_cexp args.(1), oexp_of_cexp args.(2))
      else if Constr.equal constructor (Lazy.force CoqQFBV._sbvXor) then Xor (oint_of_cnat args.(0), oexp_of_cexp args.(1), oexp_of_cexp args.(2))
      else if Constr.equal constructor (Lazy.force CoqQFBV._sbvNeg) then Neg (oint_of_cnat args.(0), oexp_of_cexp args.(1))
      else if Constr.equal constructor (Lazy.force CoqQFBV._sbvAdd) then Add (oint_of_cnat args.(0), oexp_of_cexp args.(1), oexp_of_cexp args.(2))
      else if Constr.equal constructor (Lazy.force CoqQFBV._sbvSub) then Sub (oint_of_cnat args.(0), oexp_of_cexp args.(1), oexp_of_cexp args.(2))
      else if Constr.equal constructor (Lazy.force CoqQFBV._sbvMul) then Mul (oint_of_cnat args.(0), oexp_of_cexp args.(1), oexp_of_cexp args.(2))
      else if Constr.equal constructor (Lazy.force CoqQFBV._sbvShl) then Shl (oint_of_cnat args.(0), oexp_of_cexp args.(1), oexp_of_cexp args.(2))
      else if Constr.equal constructor (Lazy.force CoqQFBV._sbvShr) then Shr (oint_of_cnat args.(0), oexp_of_cexp args.(1), oexp_of_cexp args.(2))
      else if Constr.equal constructor (Lazy.force CoqQFBV._sbvConcat) then Concat (oint_of_cnat args.(0), oint_of_cnat args.(1), oexp_of_cexp args.(2), oexp_of_cexp args.(3))
      else if Constr.equal constructor (Lazy.force CoqQFBV._sbvExtract) then Extract (oint_of_cnat args.(0), oint_of_cnat args.(1), oint_of_cnat args.(2), oexp_of_cexp args.(3))
      else if Constr.equal constructor (Lazy.force CoqQFBV._sbvSlice) then Slice (oint_of_cnat args.(0), oint_of_cnat args.(1), oint_of_cnat args.(2), oexp_of_cexp args.(3))
      else if Constr.equal constructor (Lazy.force CoqQFBV._sbvHigh) then High (oint_of_cnat args.(0), oint_of_cnat args.(1), oexp_of_cexp args.(2))
      else if Constr.equal constructor (Lazy.force CoqQFBV._sbvLow) then Low (oint_of_cnat args.(0), oint_of_cnat args.(1), oexp_of_cexp args.(2))
      else if Constr.equal constructor (Lazy.force CoqQFBV._sbvZeroExtend) then ZeroExtend (oint_of_cnat args.(0), oint_of_cnat args.(1), oexp_of_cexp args.(2))
      else if Constr.equal constructor (Lazy.force CoqQFBV._sbvSignExtend) then SignExtend (oint_of_cnat args.(0), oint_of_cnat args.(1), oexp_of_cexp args.(2))
      else fail "Not a valid sexp (2)."
    with destKO -> fail "Not a valid sexp (1)."

let rec obexp_of_cbexp e =
  if Term.isConst e then
    match Global.body_of_constant (Univ.out_punivs (Term.destConst e)) with
      None -> failwith "Failed to find the definition of constant."
    | Some e' -> obexp_of_cbexp e'
  else if Constr.equal e (Lazy.force CoqQFBV._sbvTrue) then True
  else
    try
      let (constructor, args) = Term.destApp e in
      if Constr.equal constructor (Lazy.force CoqQFBV._sbvUlt) then Ult (oint_of_cnat args.(0), oexp_of_cexp args.(1), oexp_of_cexp args.(2))
      else if Constr.equal constructor (Lazy.force CoqQFBV._sbvUle) then Ult (oint_of_cnat args.(0), oexp_of_cexp args.(1), oexp_of_cexp args.(2))
      else if Constr.equal constructor (Lazy.force CoqQFBV._sbvUgt) then Ugt (oint_of_cnat args.(0), oexp_of_cexp args.(1), oexp_of_cexp args.(2))
      else if Constr.equal constructor (Lazy.force CoqQFBV._sbvUge) then Uge (oint_of_cnat args.(0), oexp_of_cexp args.(1), oexp_of_cexp args.(2))
      else if Constr.equal constructor (Lazy.force CoqQFBV._sbvEq) then Eq (oint_of_cnat args.(0), oexp_of_cexp args.(1), oexp_of_cexp args.(2))
      else if Constr.equal constructor (Lazy.force CoqQFBV._sbvAddo) then Addo (oint_of_cnat args.(0), oexp_of_cexp args.(1), oexp_of_cexp args.(2))
      else if Constr.equal constructor (Lazy.force CoqQFBV._sbvSubo) then Subo (oint_of_cnat args.(0), oexp_of_cexp args.(1), oexp_of_cexp args.(2))
      else if Constr.equal constructor (Lazy.force CoqQFBV._sbvMulo) then Mulo (oint_of_cnat args.(0), oexp_of_cexp args.(1), oexp_of_cexp args.(2))
      else if Constr.equal constructor (Lazy.force CoqQFBV._sbvLneg) then Lneg (obexp_of_cbexp args.(0))
      else if Constr.equal constructor (Lazy.force CoqQFBV._sbvConj) then Conj (obexp_of_cbexp args.(0), obexp_of_cbexp args.(1))
      else fail "Not a valid sbexp (2)."
    with destKO -> fail "Not a valid sbexp (1)."

let rec oimp_of_cimp e =
  if Term.isConst e then
    match Global.body_of_constant (Univ.out_punivs (Term.destConst e)) with
      None -> failwith "Failed to find the definition of constant."
    | Some e' -> oimp_of_cimp e'
  else if Constr.equal e (Lazy.force CoqQFBV._sbvNil) then []
  else
    try
      let (constructor, args) = Term.destApp e in
      if Constr.equal constructor (Lazy.force CoqQFBV._sbvCons) then (obexp_of_cbexp args.(0))::(oimp_of_cimp args.(1))
      else fail "Not a valid simp (2)."
    with destKO -> fail "Not a valid simp (1)."

let string_of_var (v : var) : string =
  match v with
  | (v, i) -> vname ^ "_" ^ string_of_num v ^ "_" ^ string_of_num i

let rec string_of_exp (e : exp) : string =
  match e with
  | Var (w, v) -> string_of_var v
  | Const (w, n) -> string_of_num n
  | Not (w, e) -> if is_atomic e then "!" ^ string_of_exp e ^ "" else "!(" ^ string_of_exp e ^ ")"
  | And (w, e1, e2) ->
     (if is_atomic e1 then string_of_exp e1 else "(" ^ string_of_exp e1 ^ ")")
     ^ " & "
     ^ (if is_atomic e2 then string_of_exp e2 else "(" ^ string_of_exp e2 ^ ")")
  | Or (w, e1, e2) ->
     (if is_atomic e1 then string_of_exp e1 else "(" ^ string_of_exp e1 ^ ")")
     ^ " | "
     ^ (if is_atomic e2 then string_of_exp e2 else "(" ^ string_of_exp e2 ^ ")")
  | Xor (w, e1, e2) ->
     (if is_atomic e1 then string_of_exp e1 else "(" ^ string_of_exp e1 ^ ")")
     ^ " ^ "
     ^ (if is_atomic e2 then string_of_exp e2 else "(" ^ string_of_exp e2 ^ ")")
  | Neg (w, e) -> if is_atomic e then "-" ^ string_of_exp e ^ "" else "-(" ^ string_of_exp e ^ ")"
  | Add (w, e1, e2) ->
     (if is_atomic e1 then string_of_exp e1 else "(" ^ string_of_exp e1 ^ ")")
     ^ " + "
     ^ (if is_atomic e2 then string_of_exp e2 else "(" ^ string_of_exp e2 ^ ")")
  | Sub (w, e1, e2) ->
     (if is_atomic e1 then string_of_exp e1 else "(" ^ string_of_exp e1 ^ ")")
     ^ " - "
     ^ (if is_atomic e2 then string_of_exp e2 else "(" ^ string_of_exp e2 ^ ")")
  | Mul (w, e1, e2) ->
     (if is_atomic e1 then string_of_exp e1 else "(" ^ string_of_exp e1 ^ ")")
     ^ " * "
     ^ (if is_atomic e2 then string_of_exp e2 else "(" ^ string_of_exp e2 ^ ")")
  | Mod (w, e1, e2) ->
     (if is_atomic e1 then string_of_exp e1 else "(" ^ string_of_exp e1 ^ ")")
     ^ " % "
     ^ (if is_atomic e2 then string_of_exp e2 else "(" ^ string_of_exp e2 ^ ")")
  | Shl (w, e1, e2) ->
     (if is_atomic e1 then string_of_exp e1 else "(" ^ string_of_exp e1 ^ ")")
     ^ " << "
     ^ (if is_atomic e2 then string_of_exp e2 else "(" ^ string_of_exp e2 ^ ")")
  | Shr (w, e1, e2) ->
     (if is_atomic e1 then string_of_exp e1 else "(" ^ string_of_exp e1 ^ ")")
     ^ " >> "
     ^ (if is_atomic e2 then string_of_exp e2 else "(" ^ string_of_exp e2 ^ ")")
  | Concat (w1, w2, e1, e2) ->
     (if is_atomic e1 then string_of_exp e1 else "(" ^ string_of_exp e1 ^ ")")
     ^ "."
     ^ (if is_atomic e2 then string_of_exp e2 else "(" ^ string_of_exp e2 ^ ")")
  | Extract (w, i, j, e) ->
     (if is_atomic e then string_of_exp e else "(" ^ string_of_exp e ^ ")")
     ^ "[" ^ string_of_int i ^ ", " ^ string_of_int j ^ "]"
  | Slice (w1, w2, w3, e) ->
     (if is_atomic e then string_of_exp e else "(" ^ string_of_exp e ^ ")")
     ^ "{" ^ string_of_int w1 ^ ", " ^ string_of_int w2 ^ ", " ^ string_of_int w3 ^ "}"
  | High (lo, hi, e) ->
     (if is_atomic e then string_of_exp e else "(" ^ string_of_exp e ^ ")")
     ^ "@h" ^ string_of_int hi
  | Low (lo, hi, e) ->
     (if is_atomic e then string_of_exp e else "(" ^ string_of_exp e ^ ")")
     ^ "@l" ^ string_of_int hi
  | ZeroExtend (w, i, e) ->
     (if is_atomic e then string_of_exp e else "(" ^ string_of_exp e ^ ")")
     ^ "@e" ^ string_of_int i
  | SignExtend (w, i, e) ->
     (if is_atomic e then string_of_exp e else "(" ^ string_of_exp e ^ ")")
     ^ "@s" ^ string_of_int i

let rec string_of_bexp e =
  match e with
  | True -> "True"
  | Ult (w, e1, e2) -> string_of_exp e1 ^ " < " ^ string_of_exp e2
  | Ule (w, e1, e2) -> string_of_exp e1 ^ " <= " ^ string_of_exp e2
  | Ugt (w, e1, e2) -> string_of_exp e1 ^ " > " ^ string_of_exp e2
  | Uge (w, e1, e2) -> string_of_exp e1 ^ " >= " ^ string_of_exp e2
  | Eq (w, e1, e2) -> string_of_exp e1 ^ " = " ^ string_of_exp e2
  | Addo (w, e1, e2) -> string_of_exp e1 ^ " +ov " ^ string_of_exp e2
  | Subo (w, e1, e2) -> string_of_exp e1 ^ " -ov " ^ string_of_exp e2
  | Mulo (w, e1, e2) -> string_of_exp e1 ^ " *ov " ^ string_of_exp e2
  | Lneg e -> "~ (" ^ string_of_bexp e ^ ")"
  | Conj (e1, e2) -> string_of_bexp e1 ^ " /\\ " ^ string_of_bexp e2

let rec string_of_imp es = String.concat " -> " (List.map string_of_bexp es)

module VarOrdered : OrderedType with type t = var =
  struct
    type t = var
    let compare v1 v2 =
      match v1, v2 with
      | (x, i), (y, j) ->
         if x </ y then -1
         else if x >/ y then 1
         else if i </ j then -1
         else if i >/ j then 1
         else 0
  end

module VS : Set.S with type elt = var = Set.Make(VarOrdered)
module VM : Map.S with type key = var = Map.Make(VarOrdered)

let mvars v o1 o2 =
  match o1, o2 with
  | Some w1, Some w2 -> if w1 != w2 then
                          fail ("Variable width does not match: "
                                ^ string_of_int w1
                                ^ ", "
                                ^ string_of_int w2)
                        else
                          Some w1
  | Some w, None -> Some w
  | None, Some w -> Some w
  | None, None -> None

let rec vars_exp e =
  match e with
  | Var (w, v) -> VM.singleton v w
  | Const (_, n) -> VM.empty
  | Not (_, e) -> vars_exp e
  | And (_, e1, e2)
  | Or (_, e1, e2)
  | Xor (_, e1, e2) -> VM.merge mvars (vars_exp e1) (vars_exp e2)
  | Neg (_, e) -> vars_exp e
  | Add (_, e1, e2)
  | Sub (_, e1, e2)
  | Mul (_, e1, e2)
  | Mod (_, e1, e2)
  | Shl (_, e1, e2)
  | Shr (_, e1, e2)
  | Concat (_, _, e1, e2) -> VM.merge mvars (vars_exp e1) (vars_exp e2)
  | Extract (_, _, _, e)
  | Slice (_, _, _, e)
  | High (_, _, e)
  | Low (_, _, e)
  | ZeroExtend (_, _, e)
  | SignExtend (_, _, e) -> vars_exp e

let rec vars_bexp e =
  match e with
  | True -> VM.empty
  | Ult (_, e1, e2)
  | Ule (_, e1, e2)
  | Ugt (_, e1, e2)
  | Uge (_, e1, e2)
  | Eq (_, e1, e2)
  | Addo (_, e1, e2)
  | Subo (_, e1, e2)
  | Mulo (_, e1, e2) -> VM.merge mvars (vars_exp e1) (vars_exp e2)
  | Lneg e -> vars_bexp e
  | Conj (e1, e2) -> VM.merge mvars (vars_bexp e1) (vars_bexp e2)

let rec vars_imp es =
  List.fold_left (fun res e -> VM.merge mvars res (vars_bexp e)) VM.empty es



(* ------------------------------------------------------------------------- *)
(*  Solvers                                                                  *)
(* ------------------------------------------------------------------------- *)

let coq_z3 = 1
let coq_boolector = 2

let convert_coq_solver (v : Globnames.global_reference) : solver =
  match v with
  | Globnames.ConstructRef ((ind, _), idx) when Names.MutInd.to_string ind = "mQhasm.QFBVSolve.solver" ->
     if idx = coq_z3 then Z3
     else if idx = coq_boolector then Boolector
     else fail "Unknown solver."
  | Globnames.ConstRef cr ->
     begin
     match Global.body_of_constant cr with
     | None -> fail "Unknown solver."
     | Some c ->
        if Constr.equal c (Lazy.force CoqQFBV._Z3) then Z3
        else if Constr.equal c (Lazy.force CoqQFBV._Boolector) then Boolector
        else fail "Unknown solver."
     end
  | _ -> fail "Solver is not of type mQhasm.QFBVSolve.solver."



(* ------------------------------------------------------------------------- *)
(*  Solve                                                                    *)
(* ------------------------------------------------------------------------- *)

let num_16 = num_of_int 16

let hextbl = ["0"; "1"; "2"; "3"; "4"; "5"; "6"; "7"; "8"; "9"; "A"; "B"; "C"; "D"; "E"; "F"]

let rec hex_of_num w n =
  if w = 0 then ""
  else
    let q = quo_num n num_16 in
    let r = mod_num n num_16 in
    hex_of_num (w - 1) q ^ List.nth hextbl (int_of_num r)

let rec bin_of_num w n =
  if w = 0 then ""
  else
    let q = quo_num n num_2 in
    let r = mod_num n num_2 in
    bin_of_num (w - 1) q ^ (string_of_num r)

let smtlib2_declare_vars vars =
  let decls = VM.fold (
                  fun v w res ->
                  ("(declare-fun "
                   ^ string_of_var v
                   ^ " () (_ BitVec "
                   ^ string_of_int w
                   ^ "))")::res) vars [] in
  String.concat "\n" decls

let bvnot e = "(bvnot " ^ e ^ ")"
let bvand e1 e2 = "(bvand " ^ e1 ^ " " ^ e2 ^ ")"
let bvor e1 e2 = "(bvor " ^ e1 ^ " " ^ e2 ^ ")"
let bvxor e1 e2 = "(bvxor " ^ e1 ^ " " ^ e2 ^ ")"
let bvneg e = "(bvneg " ^ e ^ ")"
let bvadd e1 e2 = "(bvadd " ^ e1 ^ " " ^ e2 ^ ")"
let bvsub e1 e2 = "(bvsub " ^ e1 ^ " " ^ e2 ^ ")"
let bvmul e1 e2 = "(bvmul " ^ e1 ^ " " ^ e2 ^ ")"
let bvmod e1 e2 = "(bvurem " ^ e1 ^ " " ^ e2 ^ ")"
let bvshl e1 e2 = "(bvshl " ^ e1 ^ " " ^ e2 ^ ")"
let bvshr e1 e2 = "(bvlshr " ^ e1 ^ " " ^ e2 ^ ")"
let bvconcat e1 e2 = "(concat " ^ e1 ^ " " ^ e2 ^ ")"
let bvextract i j e = "((_ extract " ^ string_of_int i ^ " " ^ string_of_int j ^ ") " ^ e ^ ")"
let bvslice w1 w2 w3 e = "((_ extract " ^ string_of_int (w1 + w2 - 1) ^ " " ^ string_of_int w1 ^ ") " ^ e ^ ")"
let bvhigh lo hi e = "((_ extract " ^ string_of_int (lo + hi - 1) ^ " " ^ string_of_int lo ^ ") " ^ e ^ ")"
let bvlow lo hi e = "((_ extract " ^ string_of_int (lo - 1) ^ " " ^ string_of_int 0 ^ ") " ^ e ^ ")"
let zero_extend i e = "((_ zero_extend " ^ string_of_int i ^ ") " ^ e ^ ")"
let sign_extend i e = "((_ sign_extend " ^ string_of_int i ^ ") " ^ e ^ ")"
let bvult e1 e2 = "(bvult " ^ e1 ^ " " ^ e2 ^ ")"
let bvule e1 e2 = "(bvule " ^ e1 ^ " " ^ e2 ^ ")"
let bvugt e1 e2 = "(bvugt " ^ e1 ^ " " ^ e2 ^ ")"
let bvuge e1 e2 = "(bvuge " ^ e1 ^ " " ^ e2 ^ ")"
let bveq e1 e2 = "(= " ^ e1 ^ " " ^ e2 ^ ")"
let bvneq e1 e2 = "(not (= " ^ e1 ^ " " ^ e2 ^ "))"
let bvaddo w e1 e2 = bveq (bvhigh w 1 (bvadd (zero_extend 1 e1) (zero_extend 1 e2))) "#b1"
let bvsubo w e1 e2 = bveq (bvhigh w 1 (bvsub (zero_extend 1 e1) (zero_extend 1 e2))) "#b1"
let bvmulo w e1 e2 = bvneq (bvhigh w w (bvmul (zero_extend w e1) (zero_extend w e2))) ("(_ bv0 " ^ string_of_int w ^ ")")

let smtlib2_of_const w n =
  if w / 4 * 4 = w then "#x" ^ hex_of_num (w / 4) n
  else "#b" ^ bin_of_num w n

let rec smtlib2_of_exp e =
  match e with
  | Var (w, v) -> string_of_var v
  | Const (w, n) -> smtlib2_of_const w n
  | Not (w, e) -> bvnot (smtlib2_of_exp e)
  | And (w, e1, e2) -> bvand (smtlib2_of_exp e1) (smtlib2_of_exp e2)
  | Or (w, e1, e2) -> bvor (smtlib2_of_exp e1) (smtlib2_of_exp e2)
  | Xor (w, e1, e2) -> bvxor (smtlib2_of_exp e1) (smtlib2_of_exp e2)
  | Neg (w, e) -> bvneg (smtlib2_of_exp e)
  | Add (w, e1, e2) -> bvadd (smtlib2_of_exp e1) (smtlib2_of_exp e2)
  | Sub (w, e1, e2) -> bvsub (smtlib2_of_exp e1) (smtlib2_of_exp e2)
  | Mul (w, e1, e2) -> bvmul (smtlib2_of_exp e1) (smtlib2_of_exp e2)
  | Mod (w, e1, e2) -> bvmod (smtlib2_of_exp e1) (smtlib2_of_exp e2)
  | Shl (w, e1, e2) -> bvshl (smtlib2_of_exp e1) (smtlib2_of_exp e2)
  | Shr (w, e1, e2) -> bvshr (smtlib2_of_exp e1) (smtlib2_of_exp e2)
  | Concat (w1, w2, e1, e2) -> bvconcat (smtlib2_of_exp e1) (smtlib2_of_exp e2)
  | Extract (w, i, j, e) -> bvextract i j (smtlib2_of_exp e)
  | Slice (w1, w2, w3, e) -> bvslice w1 w2 w3 (smtlib2_of_exp e)
  | High (lo, hi, e) -> bvhigh lo hi (smtlib2_of_exp e)
  | Low (lo, hi, e) -> bvlow lo hi (smtlib2_of_exp e)
  | ZeroExtend (w, i, e) -> zero_extend i (smtlib2_of_exp e)
  | SignExtend (w, i, e) -> sign_extend i (smtlib2_of_exp e)

let rec smtlib2_of_bexp e =
  match e with
  | True -> "true"
  | Ult (w, e1, e2) -> bvult (smtlib2_of_exp e1) (smtlib2_of_exp e2)
  | Ule (w, e1, e2) -> bvule (smtlib2_of_exp e1) (smtlib2_of_exp e2)
  | Ugt (w, e1, e2) -> bvugt (smtlib2_of_exp e1) (smtlib2_of_exp e2)
  | Uge (w, e1, e2) -> bvuge (smtlib2_of_exp e1) (smtlib2_of_exp e2)
  | Eq (w, e1, e2) -> bveq (smtlib2_of_exp e1) (smtlib2_of_exp e2)
  | Addo (w, e1, e2) -> bvaddo w (smtlib2_of_exp e1) (smtlib2_of_exp e2)
  | Subo (w, e1, e2) -> bvsubo w (smtlib2_of_exp e1) (smtlib2_of_exp e2)
  | Mulo (w, e1, e2) -> bvmulo w (smtlib2_of_exp e1) (smtlib2_of_exp e2)
  | Lneg e -> "(not " ^ smtlib2_of_bexp e ^ ")"
  | Conj (e1, e2) -> "(and " ^ smtlib2_of_bexp e1 ^ " " ^ smtlib2_of_bexp e2 ^ ")"

let rec smtlib2_of_imp es =
  let (premises, goal) =
    match List.rev es with
    | g::ps -> (List.rev ps, g)
    | _ -> fail "imp is empty" in
  String.concat "\n" (List.map (fun e -> "(assert " ^ smtlib2_of_bexp e ^ ")") premises)
  ^ "\n"
  ^ "(assert (not " ^ smtlib2_of_bexp goal ^ "))"

let smtlib2_imp_check_sat es =
  "(set-logic QF_BV)\n"
  ^ "(set-info :smt-lib-version 2.0)\n"
  ^ smtlib2_declare_vars (vars_imp es)
  ^ "\n"
  ^ smtlib2_of_imp es
  ^ "\n"
  ^ "(check-sat)\n"
  ^ "(exit)\n"

let smtlib2_write_input file es =
  let input_text = smtlib2_imp_check_sat es in
  let ch = open_out file in
  let _ = output_string ch input_text; close_out ch in
  trace "INPUT IN SMTLIB2 FORMAT:";
  unix ("cat " ^ file ^ " >>  " ^ dbgdir ^ "/log_qfbv");
  trace ""

let run_z3 ifile ofile =
  let t1 = Unix.gettimeofday() in
  unix (z3_path ^ " -smt2 -nw " ^ ifile ^ " 1> " ^ ofile ^ " 2>/dev/null");
  let t2 = Unix.gettimeofday() in
  trace ("Execution time of Z3: " ^ string_of_float (t2 -. t1) ^ " seconds");
  trace "OUTPUT FROM Z3:";
  unix ("cat " ^ ofile ^ " >>  " ^ dbgdir ^ "/log_qfbv");
  trace ""

let run_boolector ifile ofile =
  let t1 = Unix.gettimeofday() in
  unix (boolector_path ^ " --smt2 " ^ ifile ^ " 1> " ^ ofile ^ " 2>/dev/null");
  let t2 = Unix.gettimeofday() in
  trace ("Execution time of Boolector: "
         ^ string_of_float (t2 -. t1) ^ " seconds");
  trace "OUTPUT FROM Boolector:";
  unix ("cat " ^ ofile ^ " >>  " ^ dbgdir ^ "/log_qfbv");
  trace ""

let read_output file =
  (* read the output *)
  let line = ref "" in
  let ch = open_in file in
  let _ =
    try
	  line := input_line ch
    with _ ->
      failwith "Failed to read the output file" in
  let _ = close_in ch in
  (* parse the output *)
  String.trim !line = "unsat"

let solve_simp ?solver:solver f =
  let s =
    match solver with
    | None -> default_solver
    | Some s -> s in
  let ifile = Filename.temp_file "inputqfbv_" "" in
  let ofile = Filename.temp_file "outputqfbv_" "" in
  let g = oimp_of_cimp f in
  let res =
    match s with
    | Z3 ->
       let _ = smtlib2_write_input ifile g in
       let _ = run_z3 ifile ofile in
       read_output ofile
    | Boolector ->
       let _ = smtlib2_write_input ifile g in
       let _ = run_boolector ifile ofile in
       read_output ofile in
  cbool_of_obool res
