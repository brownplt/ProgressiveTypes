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

Inductive expr : Type :=
  | ENum : nat -> expr
  | ELam : id -> expr -> expr
  | EVar : id -> expr
  | EErr : w -> expr
  | EApp : expr -> expr -> expr
  | EDiv : expr -> expr
  | EAdd : expr -> expr
.

Inductive aval : expr -> Prop :=
  | av_num : forall n, aval (ENum n)
  | av_lam : forall id expr, aval (ELam id expr)
.


Inductive cxt : Type :=
  | EHole : cxt
  | EAppFun : cxt -> expr -> cxt
  | EAppArg : expr -> cxt -> cxt
  | EDivArg : cxt -> cxt
  | EAddArg : cxt -> cxt
.

Inductive ActExp : expr -> Prop :=
  | ActDiv : forall n, ActExp (EDiv (ENum n))
  | ActAdd : forall n, ActExp (EAdd (ENum n))
  | ActApp : forall e1 e2, ActExp (EApp e1 e2)
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
  | CxtDivArg : forall EC earg ae,
                   EDecomp earg EC ae ->
                   EDecomp (EDiv earg) (EDivArg EC) ae
  | CxtAddArg : forall EC earg ae,
                   EDecomp earg EC ae ->
                   EDecomp (EAdd earg) (EAddArg EC) ae
.

Fixpoint e_plug (c: cxt) (e: expr) : expr :=
  match c with    
    | EHole => e
    | EAppFun c2 e2 => EApp (e_plug c2 e) e2
    | EAppArg e2 c2 => EApp e2 (e_plug c2 e)
    | EDivArg c2 => EDiv (e_plug c2 e)
    | EAddArg c2 => EAdd (e_plug c2 e)
  end
.

Fixpoint subst (x: id) (s: expr) (t: expr) : expr :=
  match t with
    | ENum n => ENum n
    | ELam x2 e => if (beq_id x x2) then (t) else (ELam x2 (subst x s e)) 
    | EVar x2 => if (beq_id x x2) then s else t
    | EErr w => EErr w
    | EApp e1 e2 =>EApp (subst x s e1) (subst x s e2)
    | EDiv e => EDiv (subst x s e)
    | EAdd e => EAdd (subst x s e)
    end
.

Inductive step : expr -> expr-> Prop :=
.