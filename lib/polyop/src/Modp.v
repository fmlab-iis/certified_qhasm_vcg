
From Coq Require Import List.
From Coq Require Import ZArith.
From PolyOp Require Import PolyOp.

Open Scope Z_scope.



(********************************************)
(* Test for positive constant in Z          *)
(********************************************)

Ltac NCst t :=
  match t with
  | O => constr:(1%positive)
  | Zpos ?t1 => t1
  | _ => constr:false
  end.

(********************************************)
(* Belonging in a list for Z                *)
(********************************************)

Ltac rIN a l :=
  match l with
  | (cons a ?l) => constr:true
  | (cons _ ?l) => rIN a l
  | _ => constr:false
  end.

(********************************************)
(* Adding a variable in a list for Z        *)
(********************************************)

Ltac rAddFv a l :=
  match (rIN a l) with
  | true => constr:l
  | _ => constr:(cons a l)
  end.

(********************************************)
(* Adding a variable in a list for Z        *)
(********************************************)

Ltac rFind_at a l :=
  match l with
  | (cons a _) => constr:xH
  | (cons _ ?l) =>
    let p := rFind_at a l in
    let v := constr:(Psucc p) in
    let v1 := eval compute in v in
    v1
  | _ => constr:xH
 end.

(********************************************)
(* Computing the list of variables for Z    *)
(********************************************)

Ltac variables t :=
  let rec aux t fv :=
  match t with
  | 0 => fv
  | 1 => fv
  | Zpos _ => fv
  | Zneg _ => fv
  | False  => fv
  | ?t1 -> ?g1 =>
    let fv1  := aux t1 fv in
    let fv2  := aux g1 fv1 in constr: fv2
  | (_ <= ?t1) => aux t1 fv
  | (_ < ?t1) => aux t1 fv
  | (?t1 = _) => aux t1 fv
  | (?t1 + ?t2) =>
    let fv1  := aux t1 fv in
    let fv2  := aux t2 fv1 in constr: fv2
  | (?t1 * ?t2) =>
    let fv1  := aux t1 fv in
    let fv2  := aux t2 fv1 in constr: fv2
  | (?t1 - ?t2) =>
    let fv1  := aux t1 fv in
    let fv2  := aux t2 fv1 in constr: fv2
  | (-?t1) =>
    let fv1  := aux t1 fv in fv1
  | (?t1 ^ ?t2) =>
    let fv1  := aux t1 fv in
    match NCst t2 with
    | false => let fv1 := rAddFv t fv in constr:fv1
    | _ => fv1
    end
  | _ => let fv1 := rAddFv t fv in constr:fv1
  end
  in aux t (@nil Z).

(********************************************)
(* Syntaxification tactic for Z             *)
(********************************************)

Ltac abstrait t fv :=
  let rec aux t :=
  match t with
  | 0 => constr:(Const 0 1)
  | 1 => constr:(Const 1 1)
  | 2 => constr:(Const 2 1)
  | Zpos _ => constr:(Const t 1)
  | Zneg _ => constr:(Const t 1)
  | (?t1 + ?t2) =>
    let v1  := aux t1 in
    let v2  := aux t2 in constr:(Add v1 v2)
  | (?t1 * ?t2) =>
    let v1  := aux t1 in
    let v2  := aux t2 in constr:(Mul v1 v2)
  | (?t1 - ?t2) =>
    let v1  := aux t1 in
    let v2  := aux t2 in constr:(Sub v1 v2)
  | (?t1 ^ 0) =>
    constr:(Const 1 1)
  | (?t1 ^ ?n) =>
    match NCst n with
    | false => let p := rFind_at t fv in constr:(Var p)
    | ?n1 => let v1  := aux t1 in constr:(Pow v1 n1)
    end
  | (- ?t1) =>
    let v1  := aux t1 in constr:(Opp v1)
  | _ =>
    let p := rFind_at t fv in constr:(Var p)
  end
  in aux t.

(********************************************)
(* Unsyntaxification for Z                  *)
(********************************************)

Fixpoint interpret t fv {struct t} : Z :=
  match t with
  | (Add t1 t2) =>
    let v1  := interpret t1 fv in
    let v2  := interpret t2 fv in (v1 + v2)
  | (Mul t1 t2) =>
    let v1  := interpret t1 fv in
    let v2  := interpret t2 fv in (v1 * v2)
  | (Sub t1 t2) =>
    let v1  := interpret t1 fv in
    let v2  := interpret t2 fv in (v1 - v2)
  | (Opp t1) =>
    let v1  := interpret t1 fv in (-v1)
  | (Pow t1 t2) =>
    let v1  := interpret t1 fv in v1 ^ (Zpos t2)
  | (Const t1 t2) =>  t1
  | (Var n) => nth (pred (nat_of_P n)) fv 0
  | Zero => 0
  end.

Ltac simplZ :=
  cbv beta iota zeta delta -[Zmult Zplus Zpower Z.pow_pos Zminus Zopp Zdiv Zmod].

Ltac modp_find_witness :=
  match goal with
  | |- exists k : Z, ?p = k * ?c =>
    let l := variables p in
    let ap := abstrait p l in
    let ac := abstrait c l in
    pdiv ap ac ltac:(fun w =>
      let w := constr:(interpret w l) in
      idtac "Witness:" w;
      exists w; simplZ; ring
    )
  end.

Close Scope Z_scope.