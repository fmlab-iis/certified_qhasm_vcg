A variable is represented by an integer <var id>, its identifier.

An expression <exp> is of the form:
* zVar <var id>            - a variable
* zConst <an integer>      - a constant
* zUnop zNeg <exp>         - negation of <exp>
* zBinop zAdd <exp> <exp>  - <exp> + <exp>
* zBinop zSub <exp> <exp>  - <exp> - <exp>
* zBinop zMul <exp> <exp>  - <exp> * <exp>
* zBinop zPow <exp> <nat> - <exp> ** <nat>

Two kinds of instructions <instr> are available:
* zAssign <var id> <exp>  - assign <exp> to variable <var id>
* zSplit <var id> <var id> <exp> <a natural number>
                          - split <exp> and assign to two variables

For instance, x0 := x2 * 5 is represented by

zAssign 0 (zBinop zMul (zVar 2) (zConst 5%Z)

Similarly, we can split a big constant into two variables by

zSplit 1 2 (zConst 12345678901234567890%Z) (31%nat)

We have x1 * 2^(31) + x2 := 12345678901234567890 .

A program is a sequence of instructions:
* [:: <instr>; <instr>; ...; <instr> ]

For instance, swapping x0 and x1 by a temporary variable x2 is represented by

[:: zAssign 2 1;
    zAssign 1 0;
    zAssign 0 2 ]
