

Inductive id : Type :=
  | Id : nat -> id
.

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
  | EVal : value -> expr
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
  | EAppArg : value  -> expr -> cxt -> cxt
  | EDivArg : cxt -> cxt
  | EAddArg : cxt -> cxt
.

Inductive ActExp : expr -> Prop :=
  | ActDiv : forall n, ActExp (EDiv (EVal (VNum n)))
  | ActAdd : forall n, ActExp (EAdd (EVal (VNum n)))
  | ActApp : forall v1 v2, ActExp (EApp (EVal v1) (EVal v2))
.

(*Not Finished*)
Inductive EDecomp : expr -> cxt -> expr -> Prop :=
  | CxtHole : forall ae, ActExp ae -> EDecomp ae EHole ae
  | CxtAppFun : forall EC efun earg ae,
                   EDecomp efun EC ae -> 
                   EDecomp (EApp efun earg) (EAppFun EC earg) ae
. 
(*Not Finished*)

 