A variable identifier <var id> is an integer.

An expression <exp> is of the form:
* QVar (PVar <var id>)     - a variable
* QConst <an integer>      - a constant
* QUnop QNeg <exp>         - negation of <exp>
* QBinop QAdd <exp> <exp>  - <exp> + <exp>
* QBinop QSub <exp> <exp>  - <exp> - <exp>
* QBinop QMul <exp> <exp>  - <exp> * <exp>

Two kinds of instructions <instr> are available:
* QAssign (PVar <var id>) <exp>  - assign <exp> to variable <var id>
* QSplit (PVar <var id>) (PVar <var id>) <exp> <a positive integer>
                                 - split <exp> and assign to two variables

For instance, x0 := x2 * 5 is represented by

QAssign (PVar 0) (QBinop QMul (QVar (PVar 2)) (QConst 5%Z)

Similarly, we can split a big constant into two variables by

QSplit (PVar 1) (PVar 2) (QConst 12345678901234567890%Z) (31%positive)

We have x1 * 2^(31) + x2 := 12345678901234567890 .

A program is a sequence of instructions:
* [:: <instr>; <instr>; ...; <instr> ]

For instance, swapping x0 and x1 is represented by

[:: QAssign (PVar 2) (PVar 1);
    QAssign (PVar 1) (PVar 0);
    QAssign (PVar 0) (PVar 2) ]
