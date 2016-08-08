open Qhasm
       
type pvar = int
       
type mqhasmexp =
  | MQvar of pvar
  | MQconst of string
  | MQNeg of mqhasmexp 
  | MQAdd of mqhasmexp * mqhasmexp
  | MQSub of mqhasmexp * mqhasmexp
  | MQMul of mqhasmexp * mqhasmexp

type mqhasminstr =
  | MQAssign of pvar * mqhasmexp
  | MQSplit of pvar * pvar * mqhasmexp * int

type mqhasm = mqhasminstr list

let qvar_to_mqhasm (qtype, qvar) = []
                          
let qload_to_mqhasm (qvar, qtypec, qaddr) = []

let qstore_to_mqhasm (qtypec, qaddr, qatomic) = []

let qassign_to_mqhasm (qvar, qexpr) = []

let qassignifcarry_to_mqhasm (qvar, qexpr, bool) = []

let qadd_to_mqhasm (qvar, qaddexpr) = []

let qaddcarry_to_mqhasm (qvar, qaddexpr) = []

let qsub_to_mqhasm (qvar, qsubexpr) = []

let qsubcarry_to_mqhasm (qvar, qsubexpr) = []

let qmul_to_mqhasm (qvar, qatomic) = []

let qand_to_mqhasm (qvar, qatomic) = []

let qor_to_mqhasm (qvar, qatomic) = []

let qxor_to_mqhasm (qvar, qatomic) = []
                                       
let qconcatmul_to_mqhasm (b, qvar, qvar', qatomic, qatomic') = []

let qaddconcatmul_to_mqhasm (b, qvar, qvar', qatomic, qatomic') = []

let qneg_to_mqhasm qvar = []

let qnot_to_mqhasm qvar = []

let qconcatshiftleft_to_mqhasm (qvar, qvar', qatomic) = []

let qshiftleft_to_mqhasm (qvar, qatomic) = []
                                             
let qconcatshiftright_to_mqhasm (qvar, qvar', qatomic) = []
                                                
let qshiftright_to_mqhasm (b, qvar, qatomic) = []

let qinput_to_mqhasm qvar = []

let qcaller_to_mqhasm qvar = []

let qenter_to_mqhasm qvar = []

let qleave_to_mqhasm = []
                         
let qcomment_to_mqhasm str = []

let qannot_to_mqhasm qannot = []
                                       
let mqhasm_from_qstmtkind skind =
  match skind with
  | QVar (qtype, qvar) ->
     qvar_to_mqhasm (qtype, qvar)
  | QLoad (qvar, qtypec, qaddr) ->
     qload_to_mqhasm (qvar, qtypec, qaddr)
  | QStore (qtypec, qaddr, qatomic) ->
     qstore_to_mqhasm (qtypec, qaddr, qatomic)
  | QAssign (qvar, qexpr) ->
     qassign_to_mqhasm (qvar, qexpr)
  | QAssignIfCarry (qvar, qexpr, b) ->
     qassignifcarry_to_mqhasm (qvar, qexpr, b)
  | QAdd (qvar, qaddexpr) ->
     qadd_to_mqhasm (qvar, qaddexpr)
  | QAddCarry (qvar, qaddexpr) ->
     qaddcarry_to_mqhasm (qvar, qaddexpr)
  | QSub (qvar, qsubexpr) ->
     qsub_to_mqhasm (qvar, qsubexpr)
  | QSubCarry (qvar, qsubexpr) ->
     qsubcarry_to_mqhasm (qvar, qsubexpr)
  | QMul (qvar, qatomic) ->
     qmul_to_mqhasm (qvar, qatomic)
  | QAnd (qvar, qatomic) ->
     qand_to_mqhasm (qvar, qatomic)
  | QOr (qvar, qatomic) ->
     qor_to_mqhasm (qvar, qatomic)
  | QXor (qvar, qatomic) ->
     qxor_to_mqhasm (qvar, qatomic)
  | QConcatMul (b, qvar, qvar', qatomic, qatomic') ->
     qconcatmul_to_mqhasm (b, qvar, qvar', qatomic, qatomic')
  | QAddConcatMul (b, qvar, qvar', qatomic, qatomic') ->
     qaddconcatmul_to_mqhasm (b, qvar, qvar', qatomic, qatomic')
  | QNeg qvar ->
     qneg_to_mqhasm qvar
  | QNot qvar ->
     qnot_to_mqhasm qvar
  | QConcatShiftLeft (qvar, qvar', qatomic) ->
     qconcatshiftleft_to_mqhasm (qvar, qvar', qatomic)
  | QShiftLeft (qvar, qatomic) ->
     qshiftleft_to_mqhasm (qvar, qatomic)
  | QConcatShiftRight (qvar, qvar', qatomic) ->
     qconcatshiftright_to_mqhasm (qvar, qvar, qatomic)
  | QShiftRight (b, qvar, qatomic) ->
     qshiftright_to_mqhasm (b, qvar, qatomic)
  | QInput qvar ->
     qinput_to_mqhasm qvar
  | QCaller qvar ->
     qcaller_to_mqhasm qvar
  | QEnter qvar ->
     qenter_to_mqhasm qvar
  | QLeave ->
     qleave_to_mqhasm
  | QComment str ->
     qcomment_to_mqhasm str
  | QAnnot qannot ->
     qannot_to_mqhasm qannot
                          
let mqhasm_from_qfile qfile =
  []

let string_of_mqhasm mqhasm =
  ""
