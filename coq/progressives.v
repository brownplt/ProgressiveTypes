Require Export Arith.EqNat.
Require Export List.

Inductive id : Type :=
  | Id : nat -> id
.

Definition beq_id X1 X2 :=
  match (X1, X2) with
    (Id n1, Id n2) => beq_nat n1 n2
  end.

Inductive w : Type :=
  | div_0 : w
  | div_lam : w
  | add_lam : w
  | app_n : w
  | app_0 : w
.

Inductive c : Type :=
  | div : c
  | add : c
.

Inductive expr : Type :=
  | ENum : nat -> expr
  | ELam : id -> expr -> expr
  | EVar : id -> expr
  | EErr : w -> expr
  | EApp : expr -> expr -> expr
  | EPrim : c -> expr -> expr
.

Inductive aval : expr -> Prop :=
  | av_num : forall n, aval (ENum n)
  | av_lam : forall id expr, aval (ELam id expr)
.


Inductive cxt : Type :=
  | EHole : cxt
  | EAppFun : cxt -> expr -> cxt
  | EAppArg : expr -> cxt -> cxt
  | EPrimArg : c -> cxt -> cxt
.

Inductive ActExp : expr -> Prop :=
  | ActPrim : forall c e, aval e -> ActExp (EPrim c e)
  | ActApp : forall e1 e2, aval e1 -> aval e2 -> ActExp (EApp e1 e2)
.

Inductive EDecomp : expr -> cxt -> expr -> Prop :=
  | CxtHole : forall ae, ActExp ae -> EDecomp ae EHole ae
  | CxtAppFun : forall EC efun earg ae,
                   EDecomp efun EC ae -> 
                   EDecomp (EApp efun earg) (EAppFun EC earg) ae
  | CxtAppArg : forall EC efun earg ae,
                   aval efun ->
                   EDecomp earg EC ae ->
                   EDecomp (EApp efun earg) (EAppArg efun EC) ae
  | CxtPrimArg : forall EC c earg ae,
                   EDecomp earg EC ae ->
                   EDecomp (EPrim c earg) (EPrimArg c EC) ae
.

Fixpoint e_plug (c: cxt) (e: expr) : expr :=
  match c with    
    | EHole => e
    | EAppFun c2 e2 => EApp (e_plug c2 e) e2
    | EAppArg e2 c2 => EApp e2 (e_plug c2 e)
    | EPrimArg op c2 => EPrim op (e_plug c2 e)
  end
.

Fixpoint subst (x: id) (s: expr) (t: expr) : expr :=
  match t with
    | ENum n => ENum n
    | ELam x2 e => if (beq_id x x2) then (t) else (ELam x2 (subst x s e)) 
    | EVar x2 => if (beq_id x x2) then s else t
    | EErr err_w => EErr err_w
    | EApp e1 e2 =>EApp (subst x s e1) (subst x s e2)
    | EPrim op_c e => EPrim op_c (subst x s e)
    end
.

(*
(** 6. Finally, define the small-step relation.  Just one case
   suffices for all valid decompositions of expressions! *)
Reserved Notation " t '/' st '==>a' t' " (at level 40, st at level 39).
Inductive astep : state -> aexp -> aexp -> Prop :=
  | A_step : forall st a E aact a', 
    Adecompose a E aact ->
      aact / st ==>a a' ->
      a / st ==>a (aexp_plug E a')

  | AS_Id : forall st i, 
      AId i / st ==>a ANum (st i)
  | AS_Plus : forall st n1 n2,
      APlus (ANum n1) (ANum n2) / st ==>a ANum (n1 + n2)
  | AS_Minus : forall st n1 n2,
      (AMinus (ANum n1) (ANum n2)) / st ==>a (ANum (minus n1 n2))
  | AS_Mult : forall st n1 n2,
      (AMult (ANum n1) (ANum n2)) / st ==>a (ANum (mult n1 n2))

    where " t '/' st '==>a' t' " := (astep st t t').
*)

(* thatsthejoke.jpg *)
Fixpoint int_reciprocal (n : nat) := 0.

Inductive delt : c -> expr -> expr -> Prop :=
 | DDivZero : delt div (ENum 0) (EErr div_0)
 | DDivN :
   forall n, beq_nat n 0 = false ->
   delt div (ENum n) (ENum (int_reciprocal n))
 | DDivLam :
   forall x e,
   delt div (ELam x e) (EErr div_lam)

 | DAddN :
   forall n,
   delt add (ENum n) (ENum (S n))
 | DAddLam :
   forall x e,
   delt add (ELam x e) (EErr add_lam)
.

Inductive step : expr -> expr -> Prop :=
 | StepCxt : forall e E ae ae',
   EDecomp e E ae ->
   step ae ae' ->
   step e (e_plug E ae')

 | StepErr : forall e E w,
   EDecomp e E (EErr w) ->
   step e (EErr w)

 | StepApp : forall x eb ea,
   aval ea ->
   step (EApp (ELam x eb) ea) (subst x ea eb)
 | StepAppNum : forall n ea,
   aval ea -> beq_nat n 0 = false ->
   step (EApp (ENum n) ea) (EErr app_n)
 | StepApp0 : forall ea,
   aval ea ->
   step (EApp (ENum 0) ea) (EErr app_0)

 | StepPrim : forall c ea ea',
   aval ea ->
   delt c ea ea' ->
   step (EPrim c ea) ea'
.

Example step1 :
  step (EPrim div (ENum 22)) (ENum 0)
.
Proof.
  apply StepPrim. apply av_num. apply DDivN. reflexivity.
Qed.

