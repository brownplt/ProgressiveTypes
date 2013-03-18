
Inductive id : Type :=
  | Id : nat -> Id
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
  | EVar : id -> expr
  | EErr : w -> expr
  | EApp : expr -> expr -> expr
  | EDiv : expr -> expr
  | EAdd : expr -> expr
.



