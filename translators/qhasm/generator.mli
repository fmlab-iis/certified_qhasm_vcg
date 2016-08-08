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
       
val mqhasm_from_qfile : qfile -> mqhasm
val string_of_mqhasm : mqhasm -> string
                                   
