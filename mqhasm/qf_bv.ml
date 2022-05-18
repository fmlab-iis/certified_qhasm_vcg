
open Big_int
open Num
open Set
open Map
open Unix
open Names
open Lwt.Infix

let qfbv () = "qfbv"

let z3_path = "z3"

let boolector_path = "boolector"

let vname = "x"

let wordsize = ref 64

let use_btor = ref true

type sat_engine =
  | Lingeling
  | Minisat

let sat_engine = ref Minisat

type solver = Z3 | Boolector

let default_solver = Z3

let split_conj = ref true

let jobs = ref 2

(* ------------------------------------------------------------------------- *)
(*  Debugging                                                                *)
(* ------------------------------------------------------------------------- *)

let dbgdir = "."

let unix s =
  let r = Unix.system s in
  if r = r then ()
  else ()

let unix_lwt cmd =
  Lwt_unix.system cmd

let init_trace () =
  unix ("echo \"\" > " ^ dbgdir ^ "/log_qfbv")

let trace s =
  unix ("echo \"" ^ s ^ "\n\" >> " ^ dbgdir ^ "/log_qfbv")

let trace_lwt s =
  unix_lwt ("echo \"" ^ s ^ "\n\" >> " ^ dbgdir ^ "/log_qfbv")

let fail s =
  trace s; failwith s

let fail_lwt s =
  trace s; failwith s

let mutex = Lwt_mutex.create ()

let lock_log () = Lwt_mutex.lock mutex
let unlock_log () = Lwt_mutex.unlock mutex

let pp_constr fmt x = Pp.pp_with fmt (Printer.pr_constr x)

let print_constr t =
  if Constr.isRel t then trace "Rel"
  else if Constr.isVar t then trace "Var"
  else if Constr.isInd t then trace "Ind"
  else if Constr.isEvar t then trace "Evar"
  else if Constr.isMeta t then trace "Meta"
  else if Constr.isSort t then trace "Sort"
  else if Constr.isCast t then trace "Cast"
  else if Constr.isApp t then trace "App"
  else if Constr.isLambda t then trace "Lambda"
  else if Constr.isLetIn t then trace "LetIn"
  else if Constr.isProd t then trace "Prod"
  else if Constr.isConst t then trace "Const"
  else if Constr.isConstruct t then trace "Construct"
  else if Constr.isFix t then trace "Fix"
  else if Constr.isCoFix t then trace "CoFix"
  else if Constr.isCase t then trace "Case"
  else if Constr.isProj t then trace "Proj"
  else if Constr.is_Prop t then trace "Prop"
  else if Constr.is_Set t then trace "Set"
  else if Constr.is_Type t then trace "Type"
  else if Constr.iskind t then trace "kind"
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
  Namegen.next_ident_away_in_goal id (Names.Id.Set.of_list ids)

let new_fresh_id avoid id gl =
  fresh_id_in_env avoid id (Proofview.Goal.env gl)



(* ------------------------------------------------------------------------- *)
(*  Pair                                                                     *)
(* ------------------------------------------------------------------------- *)

module CoqDatatypes = struct
    let path = ["Coq"; "Init"; "Datatypes"]
    let _pair : Constr.constr lazy_t = lazy (init_constant path "pair")
  end



(* ------------------------------------------------------------------------- *)
(*  Bool                                                                     *)
(* ------------------------------------------------------------------------- *)

module CoqBool = struct
    let path = ["Coq"; "Init"; "Datatypes"]
    let typ : Constr.constr lazy_t = lazy (init_constant path "bool")
    let _true : Constr.constr lazy_t = lazy (init_constant path "true")
    let _false : Constr.constr lazy_t = lazy (init_constant path "false")
  end

(** Constructs a Coq bool from an OCaml bool. *)
let rec cbool_of_obool b : Constr.t =
  if b then Lazy.force CoqBool._true
  else Lazy.force CoqBool._false

(** Constructs an OCaml bool from a Coq bool. *)
let rec obool_of_cbool (n : Constr.t) : bool =
  if Constr.equal n (Lazy.force CoqBool._true) then true
  else if Constr.equal n (Lazy.force CoqBool._false) then false
  else fail "Not a valid Coq bool."



(* ------------------------------------------------------------------------- *)
(*  Nat                                                                      *)
(* ------------------------------------------------------------------------- *)

module CoqNat = struct
    let path = ["Coq"; "Init"; "Datatypes"]
    let typ : Constr.constr lazy_t = lazy (init_constant path "nat")
    let _S : Constr.constr lazy_t = lazy (init_constant path "S")
    let _O : Constr.constr lazy_t = lazy (init_constant path "O")
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
      let (constructor, args) = Constr.destApp n in
      if Constr.equal constructor (Lazy.force CoqNat._S) then 1 + (oint_of_cnat args.(0))
      else fail "Not a valid Coq nat."
    with destKO -> fail "Not a valid Coq nat."



(* ------------------------------------------------------------------------- *)
(*  Positive/N/Z                                                             *)
(* ------------------------------------------------------------------------- *)

module CoqBinNums = struct
    let path = ["Coq"; "Numbers"; "BinNums"]
    let typ : Constr.constr lazy_t = lazy (init_constant path "positive")
    let _xI : Constr.constr lazy_t = lazy (init_constant path "xI")
    let _xO : Constr.constr lazy_t = lazy (init_constant path "xO")
    let _xH : Constr.constr lazy_t = lazy (init_constant path "xH")
    let _N0 : Constr.constr lazy_t = lazy (init_constant path "N0")
    let _Npos : Constr.constr lazy_t = lazy (init_constant path "Npos")
    let _Z0 : Constr.constr lazy_t = lazy (init_constant path "Z0")
    let _Zpos : Constr.constr lazy_t = lazy (init_constant path "Zpos")
    let _Zneg : Constr.constr lazy_t = lazy (init_constant path "Zneg")
  end

let num_0 = Int 0
let num_1 = Int 1
let num_2 = Int 2
let num_10 = Int 10

(** Constructs a Coq positive from an OCaml num. *)
let rec cpos_of_onum (n : num) : Constr.t =
  if n </ num_0 then fail "Not a positive number."
  else if n =/ num_1 then Lazy.force CoqBinNums._xH
  else if mod_num n num_2 =/ num_0 then Constr.mkApp (Lazy.force CoqBinNums._xO, [| cpos_of_onum (quo_num n num_2) |])
  else Constr.mkApp (Lazy.force CoqBinNums._xI, [| cpos_of_onum (quo_num n num_2) |])

(** Constructs an OCaml num from a Coq positive. *)
let rec onum_of_cpos (n : Constr.t) : num =
  if Constr.equal n (Lazy.force CoqBinNums._xH) then num_1
  else
    try
      let (constructor, args) = Constr.destApp n in
      if Constr.equal constructor (Lazy.force CoqBinNums._xI) then num_1 +/ (onum_of_cpos args.(0) */ num_2)
      else if Constr.equal constructor (Lazy.force CoqBinNums._xO) then num_0 +/ (onum_of_cpos args.(0) */ num_2)
      else fail "Not a valid Coq positive."
    with destKO -> fail "Not a valid Coq positive."

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
      let (constructor, args) = Constr.destApp n in
      if Constr.equal constructor (Lazy.force CoqBinNums._Npos) then onum_of_cpos args.(0)
      else fail "Not a valid Coq N."
    with destKO -> fail "Not a valid Coq N."

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
      let (constructor, args) = Constr.destApp n in
      if Constr.equal constructor (Lazy.force CoqBinNums._Zpos) then onum_of_cpos args.(0)
      else if Constr.equal constructor (Lazy.force CoqBinNums._Zneg) then minus_num (onum_of_cpos args.(0))
      else fail "Not a valid Coq Z."
    with destKO -> fail "Not a valid Coq Z."

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
    let _sbvVar : Constr.constr lazy_t = lazy (init_constant path "sbvVar")
    let _sbvConst : Constr.constr lazy_t = lazy (init_constant path "sbvConst")
    let _sbvNot : Constr.constr lazy_t = lazy (init_constant path "sbvNot")
    let _sbvAnd : Constr.constr lazy_t = lazy (init_constant path "sbvAnd")
    let _sbvOr : Constr.constr lazy_t = lazy (init_constant path "sbvOr")
    let _sbvXor : Constr.constr lazy_t = lazy (init_constant path "sbvXor")
    let _sbvNeg : Constr.constr lazy_t = lazy (init_constant path "sbvNeg")
    let _sbvAdd : Constr.constr lazy_t = lazy (init_constant path "sbvAdd")
    let _sbvSub : Constr.constr lazy_t = lazy (init_constant path "sbvSub")
    let _sbvMul : Constr.constr lazy_t = lazy (init_constant path "sbvMul")
    let _sbvMod : Constr.constr lazy_t = lazy (init_constant path "sbvMod")
    let _sbvShl : Constr.constr lazy_t = lazy (init_constant path "sbvShl")
    let _sbvShr : Constr.constr lazy_t = lazy (init_constant path "sbvShr")
    let _sbvConcat : Constr.constr lazy_t = lazy (init_constant path "sbvConcat")
    let _sbvExtract : Constr.constr lazy_t = lazy (init_constant path "sbvExtract")
    let _sbvSlice : Constr.constr lazy_t = lazy (init_constant path "sbvSlice")
    let _sbvHigh : Constr.constr lazy_t = lazy (init_constant path "sbvHigh")
    let _sbvLow : Constr.constr lazy_t = lazy (init_constant path "sbvLow")
    let _sbvZeroExtend : Constr.constr lazy_t = lazy (init_constant path "sbvZeroExtend")
    let _sbvSignExtend : Constr.constr lazy_t = lazy (init_constant path "sbvSignExtend")

    let _sbvFalse : Constr.constr lazy_t = lazy (init_constant path "sbvFalse")
    let _sbvTrue : Constr.constr lazy_t = lazy (init_constant path "sbvTrue")
    let _sbvUlt : Constr.constr lazy_t = lazy (init_constant path "sbvUlt")
    let _sbvUle : Constr.constr lazy_t = lazy (init_constant path "sbvUle")
    let _sbvUgt : Constr.constr lazy_t = lazy (init_constant path "sbvUgt")
    let _sbvUge : Constr.constr lazy_t = lazy (init_constant path "sbvUge")
    let _sbvEq : Constr.constr lazy_t = lazy (init_constant path "sbvEq")
    let _sbvAddo : Constr.constr lazy_t = lazy (init_constant path "sbvAddo")
    let _sbvSubo : Constr.constr lazy_t = lazy (init_constant path "sbvSubo")
    let _sbvMulo : Constr.constr lazy_t = lazy (init_constant path "sbvMulo")
    let _sbvLneg : Constr.constr lazy_t = lazy (init_constant path "sbvLneg")
    let _sbvConj : Constr.constr lazy_t = lazy (init_constant path "sbvConj")
    let _sbvDisj : Constr.constr lazy_t = lazy (init_constant path "sbvDisj")

    let _sbvNil : Constr.constr lazy_t = lazy (init_constant path "sbvNil")
    let _sbvCons : Constr.constr lazy_t = lazy (init_constant path "sbvCons")

    let _Z3 : Constr.constr lazy_t = lazy (init_constant path "Z3")
    let _Boolector : Constr.constr lazy_t = lazy (init_constant path "Boolector")
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
  | False
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
  | Disj of (bexp * bexp)

let is_atomic t =
  match t with
  | Var _ | Const _ -> true
  | _ -> false

let rec ovar_of_cvar v =
  let _ = Lazy.force CoqDatatypes._pair in
  if Constr.isConst v then
    match Global.body_of_constant (Univ.out_punivs (Constr.destConst v)) with
      None -> fail "Failed to find the definition of constant."
    | Some (v', _) -> ovar_of_cvar v'
  else
    try
      let (constructor, args) = Constr.destApp v in
      if Constr.equal constructor (Lazy.force CoqDatatypes._pair) then (onum_of_cn args.(2), onum_of_cn args.(3))
      else fail "Not a valid var (2)."
    with destKO -> fail "Not a valid var (1)."

let rec oexp_of_cexp e =
  if Constr.isConst e then
    match Global.body_of_constant (Univ.out_punivs (Constr.destConst e)) with
      None -> fail "Failed to find the definition of constant."
    | Some (e', _) -> oexp_of_cexp e'
  else
    try
      let (constructor, args) = Constr.destApp e in
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
  if Constr.isConst e then
    match Global.body_of_constant (Univ.out_punivs (Constr.destConst e)) with
      None -> fail "Failed to find the definition of constant."
    | Some (e', _) -> obexp_of_cbexp e'
  else if Constr.equal e (Lazy.force CoqQFBV._sbvFalse) then False
  else if Constr.equal e (Lazy.force CoqQFBV._sbvTrue) then True
  else
    try
      let (constructor, args) = Constr.destApp e in
      if Constr.equal constructor (Lazy.force CoqQFBV._sbvUlt) then Ult (oint_of_cnat args.(0), oexp_of_cexp args.(1), oexp_of_cexp args.(2))
      else if Constr.equal constructor (Lazy.force CoqQFBV._sbvUle) then Ule (oint_of_cnat args.(0), oexp_of_cexp args.(1), oexp_of_cexp args.(2))
      else if Constr.equal constructor (Lazy.force CoqQFBV._sbvUgt) then Ugt (oint_of_cnat args.(0), oexp_of_cexp args.(1), oexp_of_cexp args.(2))
      else if Constr.equal constructor (Lazy.force CoqQFBV._sbvUge) then Uge (oint_of_cnat args.(0), oexp_of_cexp args.(1), oexp_of_cexp args.(2))
      else if Constr.equal constructor (Lazy.force CoqQFBV._sbvEq) then Eq (oint_of_cnat args.(0), oexp_of_cexp args.(1), oexp_of_cexp args.(2))
      else if Constr.equal constructor (Lazy.force CoqQFBV._sbvAddo) then Addo (oint_of_cnat args.(0), oexp_of_cexp args.(1), oexp_of_cexp args.(2))
      else if Constr.equal constructor (Lazy.force CoqQFBV._sbvSubo) then Subo (oint_of_cnat args.(0), oexp_of_cexp args.(1), oexp_of_cexp args.(2))
      else if Constr.equal constructor (Lazy.force CoqQFBV._sbvMulo) then Mulo (oint_of_cnat args.(0), oexp_of_cexp args.(1), oexp_of_cexp args.(2))
      else if Constr.equal constructor (Lazy.force CoqQFBV._sbvLneg) then Lneg (obexp_of_cbexp args.(0))
      else if Constr.equal constructor (Lazy.force CoqQFBV._sbvConj) then Conj (obexp_of_cbexp args.(0), obexp_of_cbexp args.(1))
      else if Constr.equal constructor (Lazy.force CoqQFBV._sbvDisj) then Disj (obexp_of_cbexp args.(0), obexp_of_cbexp args.(1))
      else fail "Not a valid sbexp (2)."
    with destKO -> fail "Not a valid sbexp (1)."

let rec oimp_of_cimp e =
  if Constr.isConst e then
    match Global.body_of_constant (Univ.out_punivs (Constr.destConst e)) with
      None -> fail "Failed to find the definition of constant."
    | Some (e', _) -> oimp_of_cimp e'
  else if Constr.equal e (Lazy.force CoqQFBV._sbvNil) then []
  else
    try
      let (constructor, args) = Constr.destApp e in
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
  | False -> "False"
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
  | Disj (e1, e2) -> string_of_bexp e1 ^ " \\/ " ^ string_of_bexp e2

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
  | False
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
  | Conj (e1, e2)
  | Disj (e1, e2) -> VM.merge mvars (vars_bexp e1) (vars_bexp e2)

let rec vars_imp es =
  List.fold_left (fun res e -> VM.merge mvars res (vars_bexp e)) VM.empty es



(* ------------------------------------------------------------------------- *)
(*  Solvers                                                                  *)
(* ------------------------------------------------------------------------- *)

let coq_z3 = 1
let coq_boolector = 2

let convert_coq_solver (v : Globnames.global_reference) : solver =
  match v with
  | Globnames.ConstructRef ((ind, _), idx)
       when Names.MutInd.to_string ind = "mQhasm.QFBVSolve.solver"
            || Names.MutInd.to_string ind = "Top.solver" ->
     if idx = coq_z3 then Z3
     else if idx = coq_boolector then Boolector
     else fail "Unknown solver."
  | Globnames.ConstructRef ((ind, _), idx) ->
     fail ("Found construct ref: " ^ Names.MutInd.to_string ind)
  | Globnames.ConstRef cr ->
     begin
     match Global.body_of_constant cr with
     | None -> fail "Unknown solver."
     | Some (c, _) ->
        if Constr.equal c (Lazy.force CoqQFBV._Z3) then Z3
        else if Constr.equal c (Lazy.force CoqQFBV._Boolector) then Boolector
        else fail "Unknown solver."
     end
  | _ -> fail "Solver is not of type mQhasm.QFBVSolve.solver."

let rec osolver_of_csolver e : solver =
  if Constr.isConst e then
    match Global.body_of_constant (Univ.out_punivs (Constr.destConst e)) with
      None -> fail "Failed to find the definition of constant."
    | Some (e', _) -> osolver_of_csolver e'
  else if Constr.equal e (Lazy.force CoqQFBV._Boolector) then Boolector
  else if Constr.equal e (Lazy.force CoqQFBV._Z3) then Z3
  else let _ = trace "lala" in fail "lala"
  (*
  else
    try
      let (constructor, args) = Constr.destApp e in
      if Constr.equal constructor (Lazy.force CoqQFBV._sbvUlt) then Ult (oint_of_cnat args.(0), oexp_of_cexp args.(1), oexp_of_cexp args.(2))
      else if Constr.equal constructor (Lazy.force CoqQFBV._sbvUle) then Ule (oint_of_cnat args.(0), oexp_of_cexp args.(1), oexp_of_cexp args.(2))
      else if Constr.equal constructor (Lazy.force CoqQFBV._sbvUgt) then Ugt (oint_of_cnat args.(0), oexp_of_cexp args.(1), oexp_of_cexp args.(2))
      else if Constr.equal constructor (Lazy.force CoqQFBV._sbvUge) then Uge (oint_of_cnat args.(0), oexp_of_cexp args.(1), oexp_of_cexp args.(2))
      else if Constr.equal constructor (Lazy.force CoqQFBV._sbvEq) then Eq (oint_of_cnat args.(0), oexp_of_cexp args.(1), oexp_of_cexp args.(2))
      else if Constr.equal constructor (Lazy.force CoqQFBV._sbvAddo) then Addo (oint_of_cnat args.(0), oexp_of_cexp args.(1), oexp_of_cexp args.(2))
      else if Constr.equal constructor (Lazy.force CoqQFBV._sbvSubo) then Subo (oint_of_cnat args.(0), oexp_of_cexp args.(1), oexp_of_cexp args.(2))
      else if Constr.equal constructor (Lazy.force CoqQFBV._sbvMulo) then Mulo (oint_of_cnat args.(0), oexp_of_cexp args.(1), oexp_of_cexp args.(2))
      else if Constr.equal constructor (Lazy.force CoqQFBV._sbvLneg) then Lneg (obexp_of_cbexp args.(0))
      else if Constr.equal constructor (Lazy.force CoqQFBV._sbvConj) then Conj (obexp_of_cbexp args.(0), obexp_of_cbexp args.(1))
      else if Constr.equal constructor (Lazy.force CoqQFBV._sbvDisj) then Disj (obexp_of_cbexp args.(0), obexp_of_cbexp args.(1))
      else fail "Not a valid sbexp (2)."
    with destKO -> fail "Not a valid sbexp (1)."
   *)


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

(** Returns the log of n (base 2) as an integer. *)
let logi n = int_of_float (log (float_of_int n) /. log 2.0)

module WN : OrderedType with type t = (int * num) =
  struct
    type t = (int * num)
    let compare (w1, n1) (w2, n2) =
      if w1 < w2 then -1
      else if w1 > w2 then 1
      else compare_num n1 n2
  end

module WNMap : Map.S with type key = (int * num) = Map.Make(WN)

class btor_manager (wordsize : int) =
object(self)
  (** the ID of the next Btor variable *)
  val mutable v = 0

  (** a map from a variable to the corresponding Btor variable *)
  val mutable vmap : int VM.t = VM.empty

  (** a map from a bit-width and an integer to the corresponding Btor variable *)
  val mutable cmap : int WNMap.t = WNMap.empty

  val mutable stmts : string list = []

  (** Returns a new ID. *)
  method newvar =
    let _ = v <- v + 1 in
    v

  (** Sets the corresponding Btor variable of a variable. *)
  method setvar v bv = vmap <- VM.add v bv vmap

  method addstmt stmt = stmts <- stmt::stmts

  method getstmts = List.rev stmts

  method mkvar v =
    try
      VM.find v vmap
    with Not_found ->
      let bv = self#newvar in
      let _ = self#addstmt ("; " ^ string_of_var v) in
      let _ = self#addstmt (Printf.sprintf "%d var %d" bv wordsize) in
      let _ = self#setvar v bv in
      bv

  method mkconstd w n =
    try
      WNMap.find (w, n) cmap
    with Not_found ->
      let bv = self#newvar in
      let _ = self#addstmt (Printf.sprintf "%d constd %d" bv w ^ " " ^ string_of_num n) in
      let _ = cmap <- WNMap.add (w, n) bv cmap in
      bv
    | e ->
      fail (Printexc.to_string e)

  method mknot w e =
    let bv = self#newvar in
    let _ = self#addstmt (Printf.sprintf "%d not %d %d" bv w e) in
    bv

  method mkand w e1 e2 =
    let bv = self#newvar in
    let _ = self#addstmt (Printf.sprintf "%d and %d %d %d" bv w e1 e2) in
    bv

  method mkor w e1 e2 =
    let bv = self#newvar in
    let _ = self#addstmt (Printf.sprintf "%d or %d %d %d" bv w e1 e2) in
    bv

  method mkxor w e1 e2 =
    let bv = self#newvar in
    let _ = self#addstmt (Printf.sprintf "%d xor %d %d %d" bv w e1 e2) in
    bv

  method mkneg w e =
    let bv = self#newvar in
    let _ = self#addstmt (Printf.sprintf "%d neg %d %d" bv w e) in
    bv

  method mkadd w e1 e2 =
    let bv = self#newvar in
    let _ = self#addstmt (Printf.sprintf "%d add %d %d %d" bv w e1 e2) in
    bv

  method mksub w e1 e2 =
    let bv = self#newvar in
    let _ = self#addstmt (Printf.sprintf "%d sub %d %d %d" bv w e1 e2) in
    bv

  method mkmul w e1 e2 =
    let bv = self#newvar in
    let _ = self#addstmt (Printf.sprintf "%d mul %d %d %d" bv w e1 e2) in
    bv

  method mkmod w e1 e2 =
    let bv = self#newvar in
    let _ = self#addstmt (Printf.sprintf "%d urem %d %d %d" bv w e1 e2) in
    bv

  method mkshl w e1 e2 =
    let bv = self#newvar in
    let _ = self#addstmt (Printf.sprintf "%d sll %d %d %d" bv w e1 e2) in
    bv

  method mkshr w e1 e2 =
    let bv = self#newvar in
    let _ = self#addstmt (Printf.sprintf "%d srl %d %d %d" bv w e1 e2) in
    bv

  method mkconcat w1 w2 e1 e2 =
    let bv = self#newvar in
    let _ = self#addstmt (Printf.sprintf "%d concat %d %d %d" bv (w1 + w2) e1 e2) in
    bv

  method mkextract w i j e =
    let bv = self#newvar in
    let _ = self#addstmt (Printf.sprintf "%d slice %d %d %d %d" bv (i - j + 1) e i j) in
    bv

  method mkslice w1 w2 w3 e = self#mkextract (w1 + w2 + w3) (w1 + w2 - 1) w1 e

  method mkhigh lo hi e = self#mkextract (lo + hi) (lo + hi - 1) lo e

  method mklow lo hi e = self#mkextract (lo + hi) (lo - 1) 0 e

  method mkzeroextend w i e =
    let bv = self#newvar in
    let c = self#mkconstd i num_0 in
    let _ = self#addstmt (Printf.sprintf "%d concat %d %d %d" bv (w + i) c e) in
    bv

  method mkult e1 e2 =
    let bv = self#newvar in
    let _ = self#addstmt (Printf.sprintf "%d ult 1 %d %d" bv e1 e2) in
    bv

  method mkule e1 e2 =
    let bv = self#newvar in
    let _ = self#addstmt (Printf.sprintf "%d ulte 1 %d %d" bv e1 e2) in
    bv

  method mkugt e1 e2 =
    let bv = self#newvar in
    let _ = self#addstmt (Printf.sprintf "%d ugt 1 %d %d" bv e1 e2) in
    bv

  method mkuge e1 e2 =
    let bv = self#newvar in
    let _ = self#addstmt (Printf.sprintf "%d ugte 1 %d %d" bv e1 e2) in
    bv

  method mkeq e1 e2 =
    let bv = self#newvar in
    let _ = self#addstmt (Printf.sprintf "%d eq 1 %d %d" bv e1 e2) in
    bv

  method mkneq e1 e2 =
    let bv = self#newvar in
    let _ = self#addstmt (Printf.sprintf "%d ne 1 %d %d" bv e1 e2) in
    bv

  method mkaddo e1 e2 =
    let bv = self#newvar in
    let _ = self#addstmt (Printf.sprintf "%d uaddo 1 %d %d" bv e1 e2) in
    bv

  method mksubo e1 e2 =
    let bv = self#newvar in
    let _ = self#addstmt (Printf.sprintf "%d usubo 1 %d %d" bv e1 e2) in
    bv

  method mkmulo e1 e2 =
    let bv = self#newvar in
    let _ = self#addstmt (Printf.sprintf "%d umulo 1 %d %d" bv e1 e2) in
    bv

end

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

let rec btor_of_exp m e =
  match e with
  | Var (w, v) -> m#mkvar v
  | Const (w, n) -> m#mkconstd w n
  | Not (w, e) -> m#mknot w (btor_of_exp m e)
  | And (w, e1, e2) -> m#mkand w (btor_of_exp m e1) (btor_of_exp m e2)
  | Or (w, e1, e2) -> m#mkor w (btor_of_exp m e1) (btor_of_exp m e2)
  | Xor (w, e1, e2) -> m#mkxor w (btor_of_exp m e1) (btor_of_exp m e2)
  | Neg (w, e) -> m#mkneg w (btor_of_exp m e)
  | Add (w, e1, e2) -> m#mkadd w (btor_of_exp m e1) (btor_of_exp m e2)
  | Sub (w, e1, e2) -> m#mksub w (btor_of_exp m e1) (btor_of_exp m e2)
  | Mul (w, e1, e2) -> m#mkmul w (btor_of_exp m e1) (btor_of_exp m e2)
  | Mod (w, e1, e2) -> m#mkmod w (btor_of_exp m e1) (btor_of_exp m e2)
  | Shl (w, e1, Const (_, e2)) -> m#mkshl w (btor_of_exp m e1) (m#mkconstd (logi w) e2)
  | Shl _ -> fail "Shl (_, n) with non-constant n is not supported"
  | Shr (w, e1, Const (_, e2)) -> m#mkshr w (btor_of_exp m e1) (m#mkconstd (logi w) e2)
  | Shr _ -> fail "Shr (_, n) with non-constant n is not supported"
  | Concat (w1, w2, e1, e2) -> m#mkconcat w1 w2 (btor_of_exp m e1) (btor_of_exp m e2)
  | Extract (w, i, j, e) -> m#mkextract w i j (btor_of_exp m e)
  | Slice (w1, w2, w3, e) -> m#mkslice w1 w2 w3 (btor_of_exp m e)
  | High (lo, hi, e) -> m#mkhigh lo hi (btor_of_exp m e)
  | Low (lo, hi, e) -> m#mklow lo hi (btor_of_exp m e)
  | ZeroExtend (w, i, e) -> m#mkzeroextend w i (btor_of_exp m e)
  | SignExtend (w, i, e) -> fail "SignExtend is not supported"

let rec smtlib2_of_bexp e =
  match e with
  | False -> "false"
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
  | Disj (e1, e2) -> "(or " ^ smtlib2_of_bexp e1 ^ " " ^ smtlib2_of_bexp e2 ^ ")"

let rec btor_of_bexp m e =
  match e with
  | False -> m#mkconstd 0 num_0
  | True -> m#mkconstd 1 num_1
  | Ult (w, e1, e2) -> m#mkult (btor_of_exp m e1) (btor_of_exp m e2)
  | Ule (w, e1, e2) -> m#mkule (btor_of_exp m e1) (btor_of_exp m e2)
  | Ugt (w, e1, e2) -> m#mkugt (btor_of_exp m e1) (btor_of_exp m e2)
  | Uge (w, e1, e2) -> m#mkuge (btor_of_exp m e1) (btor_of_exp m e2)
  | Eq (w, e1, e2) -> m#mkeq (btor_of_exp m e1) (btor_of_exp m e2)
  | Addo (w, e1, e2) -> m#mkaddo (btor_of_exp m e1) (btor_of_exp m e2)
  | Subo (w, e1, e2) -> m#mksubo (btor_of_exp m e1) (btor_of_exp m e2)
  | Mulo (w, e1, e2) -> m#mkmulo (btor_of_exp m e1) (btor_of_exp m e2)
  | Lneg e -> m#mknot 1 (btor_of_bexp m e)
  | Conj (e1, e2) -> m#mkand 1 (btor_of_bexp m e1) (btor_of_bexp m e2)
  | Disj (e1, e2) -> m#mkor 1 (btor_of_bexp m e1) (btor_of_bexp m e2)

let rec smtlib2_of_imp es =
  let (premises, goal) =
    match List.rev es with
    | g::ps -> (List.rev ps, g)
    | _ -> fail "imp is empty" in
  String.concat "\n" (List.map (fun e -> "(assert " ^ smtlib2_of_bexp e ^ ")") premises)
  ^ "\n"
  ^ "(assert (not " ^ smtlib2_of_bexp goal ^ "))"

let rec btor_of_imp m es =
  let rec mkconj es =
    match es with
    | [] -> m#mkconstd 1 num_1
    | e1::e2::[] -> m#mkand 1 e1 e2
    | hd::tl -> m#mkand 1 hd (mkconj tl) in
  let (premises, goal) =
    match List.rev es with
    | g::ps -> (List.rev ps, g)
    | _ -> fail "imp is empty" in
  let f = mkconj (List.map (btor_of_bexp m) premises) in
  let g = btor_of_bexp m goal in
  let not_g = m#newvar in
  let r = m#newvar in
  let _ = m#addstmt (Printf.sprintf "%d not 1 %d" not_g g) in
  let _ = m#addstmt (Printf.sprintf "%d and 1 %d %d" r f not_g) in
  r

let smtlib2_declare_vars vars =
  let decls = VM.fold (
                  fun v w res ->
                  ("(declare-fun "
                   ^ string_of_var v
                   ^ " () (_ BitVec "
                   ^ string_of_int w
                   ^ "))")::res) vars [] in
  String.concat "\n" decls

let btor_declare_vars m vars = VM.iter (fun v w -> ignore(m#mkvar v)) vars

let smtlib2_imp_check_sat es =
  "(set-logic QF_BV)\n"
  ^ "(set-info :smt-lib-version 2.0)\n"
  ^ smtlib2_declare_vars (vars_imp es)
  ^ "\n"
  ^ smtlib2_of_imp es
  ^ "\n"
  ^ "(check-sat)\n"
  ^ "(exit)\n"

let btor_imp_check_sat m es =
  let _ = btor_declare_vars m (vars_imp es) in
  let bv = btor_of_imp m es in
  let r = m#newvar in
  (String.concat "\n" m#getstmts)
  ^ "\n"
  ^ (Printf.sprintf "%d root 1 %d" r bv)
  ^ "\n"

let smtlib2_write_input file es =
  let input_text = smtlib2_imp_check_sat es in
  let ch = open_out file in
  let _ = output_string ch input_text; close_out ch in
  trace "INPUT IN SMTLIB2 FORMAT:";
  unix ("cat " ^ file ^ " >>  " ^ dbgdir ^ "/log_qfbv");
  trace ""

let btor_write_input file es =
  let m = new btor_manager !wordsize in
  let input_text = btor_imp_check_sat m es in
  let ch = open_out file in
  let _ = output_string ch input_text; close_out ch in
  trace "INPUT IN BTOR FORMAT:";
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

let run_z3_lwt ifile ofile =
  let t1 = Unix.gettimeofday() in
  let%lwt _ = unix_lwt (z3_path ^ " -smt2 -nw " ^ ifile ^ " 1> " ^ ofile ^ " 2>/dev/null") in
  let t2 = Unix.gettimeofday() in
  let%lwt _ = lock_log () in
  let%lwt _ = trace_lwt ("Execution time of Z3: " ^ string_of_float (t2 -. t1) ^ " seconds") in
  let%lwt _ = trace_lwt "OUTPUT FROM Z3:" in
  let%lwt _ = unix_lwt ("cat " ^ ofile ^ " >>  " ^ dbgdir ^ "/log_qfbv") in
  let%lwt _ = trace_lwt "" in
  let _ = unlock_log () in
  Lwt.return_unit

let string_of_sat_engine e =
  match e with
  | Lingeling -> "lingeling"
  | Minisat -> "minisat"

let string_of_solver e =
  match e with
  | Z3 -> "Z3"
  | Boolector -> "Boolector"

let run_boolector ifile ofile =
  let t1 = Unix.gettimeofday() in
  let _ =
    if !use_btor then
      unix (boolector_path ^ " -SE " ^ string_of_sat_engine !sat_engine ^ " " ^ ifile ^ " 1> " ^ ofile ^ " 2>/dev/null")
    else
      unix (boolector_path ^ " --smt2 -SE " ^ string_of_sat_engine !sat_engine ^ " " ^ ifile ^ " 1> " ^ ofile ^ " 2>/dev/null") in
  let t2 = Unix.gettimeofday() in
  trace ("Execution time of Boolector: "
         ^ string_of_float (t2 -. t1) ^ " seconds");
  trace "OUTPUT FROM Boolector:";
  unix ("cat " ^ ofile ^ " >>  " ^ dbgdir ^ "/log_qfbv");
  trace ""

let run_boolector_lwt ifile ofile =
  let t1 = Unix.gettimeofday() in
  let%lwt _ =
    if !use_btor then
      unix_lwt (boolector_path ^ " -SE " ^ string_of_sat_engine !sat_engine ^ " " ^ ifile ^ " 1> " ^ ofile ^ " 2>/dev/null")
    else
      unix_lwt (boolector_path ^ " --smt2 -SE " ^ string_of_sat_engine !sat_engine ^ " " ^ ifile ^ " 1> " ^ ofile ^ " 2>/dev/null") in
  let t2 = Unix.gettimeofday() in
  let%lwt _ = lock_log () in
  let%lwt _ = trace_lwt ("Execution time of Boolector: " ^ string_of_float (t2 -. t1) ^ " seconds") in
  let%lwt _ = trace_lwt "OUTPUT FROM Boolector:" in
  let%lwt _ = unix_lwt ("cat " ^ ofile ^ " >>  " ^ dbgdir ^ "/log_qfbv") in
  let%lwt _ = trace_lwt "" in
  let _ = unlock_log () in
  Lwt.return_unit

let read_output file =
  (* read the output *)
  let line = ref "" in
  let ch = open_in file in
  let _ =
    try
	  line := input_line ch
    with _ ->
      fail "Failed to read the output file" in
  let _ = close_in ch in
  (* parse the output *)
  String.trim !line = "unsat"

let read_output_lwt file =
  (* read the output *)
  let line = ref "" in
  let%lwt ch = Lwt_io.open_file Lwt_io.input file in
  let%lwt line =
    try%lwt
      Lwt_io.read_line ch
    with _ ->
      fail_lwt "Failed to read the output file" in
  let%lwt _ = Lwt_io.close ch in
  (* parse the output *)
  Lwt.return (String.trim line = "unsat")

let rec bexp_split_conj e =
  match e with
  | False | True
  | Ult _ | Ule _ | Ugt _ | Uge _
  | Eq _
  | Addo _ | Subo _ | Mulo _
  | Lneg _ -> [e]
  | Conj (e1, e2) -> (bexp_split_conj e1)@(bexp_split_conj e2)
  | Disj _ -> [e]

let imp_split_conj es =
  let (premises_rev, goal) =
    match List.rev es with
    | g::ps -> (ps, g)
    | _ -> fail "imp is empty" in
  let gs = bexp_split_conj goal in
  List.map (fun g -> List.rev (g::premises_rev)) gs

let solve_simp_one s f =
  let ifile = Filename.temp_file "inputqfbv_" "" in
  let ofile = Filename.temp_file "outputqfbv_" "" in
  let res =
    match s with
    | Z3 ->
       let _ = smtlib2_write_input ifile f in
       let _ = run_z3 ifile ofile in
       read_output ofile
    | Boolector ->
       let _ =
         if !use_btor then btor_write_input ifile f else smtlib2_write_input ifile f in
       let _ = run_boolector ifile ofile in
       read_output ofile in
  res

let solve_simp_one_lwt s f =
  let ifile = Filename.temp_file "inputqfbv_" "" in
  let ofile = Filename.temp_file "outputqfbv_" "" in
  let res =
    match s with
    | Z3 ->
       let _ = smtlib2_write_input ifile f in
       let%lwt _ = run_z3_lwt ifile ofile in
       let%lwt res = read_output_lwt ofile in
       Lwt.return res
    | Boolector ->
       let _ =
         if !use_btor then btor_write_input ifile f else smtlib2_write_input ifile f in
       let%lwt _ = run_boolector_lwt ifile ofile in
       let%lwt res = read_output_lwt ofile in
       Lwt.return res in
  res

let work_on_pending delivered_helper res pending =
  let (delivered, promised) = Lwt_main.run (Lwt.nchoose_split pending) in
  let res' = List.fold_left delivered_helper res delivered in
  (res', promised)

let rec finish_pending delivered_helper res pending =
  match pending with
  | [] -> res
  | _ -> let (res', pending') = work_on_pending delivered_helper res pending in
         finish_pending delivered_helper res' pending'

let solve_simp_seq s imps =
  List.for_all (fun imp -> solve_simp_one s imp) imps

let solve_simp_lwt s imps =
  let mk_promise imp =
    let solve = solve_simp_one_lwt s imp in
    let%lwt solve_res = solve in
    Lwt.return solve_res in
  let delivered_helper r ret = r && ret in
  let fold_fun (res, pending) imp =
    if res then
      if List.length pending < !jobs then
        let promise = mk_promise imp in
        (res, promise::pending)
      else
        let (res', pending') = work_on_pending delivered_helper res pending in
        let promise = mk_promise imp in
        (res', promise::pending')
    else
      (finish_pending delivered_helper res pending, [])
 in
  let (res, pending) = List.fold_left fold_fun (true, []) imps in
  finish_pending delivered_helper res pending

let solve_simp ?solver:solver imp =
  let s =
    match solver with
    | None -> default_solver
    | Some s -> s in
  let imps =
    if !split_conj then imp_split_conj imp
    else [imp] in
  let res =
    if !jobs > 1 then solve_simp_lwt s imps
    else solve_simp_seq s imps in
  res
