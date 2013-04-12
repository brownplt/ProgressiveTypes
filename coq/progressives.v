Require Export Arith.EqNat.
Require Export QArith.
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

Fixpoint beq_w w w' :=
  match w, w' with
    | div_0, div_0 => true
    | div_lam, div_lam => true
    | add_lam, add_lam => true
    | app_n, app_n => true
    | app_0, app_0 => true
    | _, _ => false
end
.

Inductive c : Type :=
  | div : c
  | add : c
.

Inductive typ : Type :=
  | TBot
  | TZero : typ
  | TNum : typ
  | TUnion : typ -> typ -> typ
  | TArrow : typ -> list w -> typ -> typ
(* Come back to these *)
(*| TRec : id -> typ -> typ
  | TId : id -> typ *)
.

Inductive expr : Type :=
  | ENum : Q -> expr
  | ELam : id -> typ -> list w -> expr -> expr
  | EVar : id -> expr
  | EErr : w -> expr
  | EApp : expr -> expr -> expr
  | EPrim : c -> expr -> expr
.

Inductive aval : expr -> Prop :=
  | av_num : forall n, aval (ENum n)
  | av_lam : forall id typ ws expr, aval (ELam id typ ws expr)
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
    | ELam x2 typ ws e =>
      if (beq_id x x2) then (t) else (ELam x2 typ ws (subst x s e)) 
    | EVar x2 => if (beq_id x x2) then s else t
    | EErr err_w => EErr err_w
    | EApp e1 e2 =>EApp (subst x s e1) (subst x s e2)
    | EPrim op_c e => EPrim op_c (subst x s e)
    end
.

Inductive delt : c -> expr -> expr -> Prop :=
 | DDivZero : delt div (ENum 0) (EErr div_0)
 | DDivN :
   forall n, not (Qeq n 0) ->
   delt div (ENum n) (ENum (Qinv n))
 | DDivLam :
   forall x typ ws e,
   delt div (ELam x typ ws e) (EErr div_lam)

 | DAddN :
   forall n,
   delt add (ENum n) (ENum (Qplus n 1))
 | DAddLam :
   forall x typ ws e,
   delt add (ELam x typ ws  e) (EErr add_lam)
.

Inductive step : expr -> expr -> Prop :=
 | StepCxt : forall e E ae ae' e',
   EDecomp e E ae ->
   step ae ae' ->
   e' = (e_plug E ae') ->
   step e e'

 | StepErr : forall e E w,
   EDecomp e E (EErr w) ->
   step e (EErr w)

 | StepApp : forall x typ ws eb ea,
   aval ea ->
   step (EApp (ELam x typ ws eb) ea) (subst x ea eb)
 | StepAppNum : forall n ea,
   aval ea -> not (Qeq n 0) ->
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
  step (EPrim div (ENum 1)) (ENum 1)
.
Proof.
  apply StepPrim. apply av_num. apply DDivN.
  unfold not. intros. inversion H.
Qed.

Example bigger_num :
  step (EPrim div (ENum (Qmake 22 1))) (ENum (Qmake 1 22))
.
Proof.
  apply StepPrim. apply av_num. apply DDivN.
  unfold not. intros. inversion H.
Qed.

Definition relation (X: Type) := X->X->Prop.

Inductive refl_step_closure {X:Type} (R: relation X) 
                            : X -> X -> Prop :=
  | rsc_refl  : forall (x : X),
                 refl_step_closure R x x
  | rsc_step : forall (x y z : X),
                    R x y ->
                    refl_step_closure R y z ->
                    refl_step_closure R x z.

Definition stepmany := refl_step_closure step.


Example decomp1 :
  EDecomp (EPrim div (EPrim add (ENum 1)))
          (EPrimArg div EHole)
          (EPrim add (ENum 1))
.
Proof.
  apply CxtPrimArg. apply CxtHole. apply ActPrim. apply av_num.
Qed.
          

Example step2 :
  stepmany (EPrim div (EPrim add (ENum 1))) (ENum (Qmake 1 2))
.
Proof.
  apply rsc_step with (EPrim div (ENum (Qmake 2 1))).
  apply StepCxt with (E := EPrimArg div EHole)
                     (ae := EPrim add (ENum 1))
                     (ae' := ENum (Qmake 2 1)).
  apply CxtPrimArg. apply CxtHole. apply ActPrim. apply av_num.

  apply StepPrim. apply av_num. apply DAddN.
reflexivity.

  apply rsc_step with (ENum (Qmake 1 2)).
  apply StepPrim. apply av_num. apply DDivN. 
  unfold not. intros. inversion H.
  apply rsc_refl.
Qed.

Fixpoint has_error (test_w: w) (lw: list w) : bool :=
  match lw with
    | nil => false
    | hd :: tl =>
      if beq_w test_w hd then true else has_error test_w tl
  end
.
      

Inductive delta_t : c -> typ -> list w -> typ -> Prop :=
  | dt_bottom : forall c lw,
    delta_t c TBot lw TBot
  | dt_union : forall c t1 t2 lw t_left t_right,
    delta_t c t1 lw t_left ->
    delta_t c t2 lw t_right ->
    delta_t c (TUnion t1 t2) lw (TUnion t_left t_right)

  | dt_divN : forall lw,
    delta_t div TNum lw TNum
  | dt_div0 : forall lw,
    has_error div_0 lw = true ->
    delta_t div TZero lw TBot
  | dt_divLam : forall t1 lw1 t2 lw2 typ_arrow,
    has_error div_lam lw2 = true ->
    typ_arrow = (TArrow t1 lw1 t2) ->
    delta_t div typ_arrow lw2 TBot

  | dt_addN : forall lw,
    delta_t add TNum lw (TUnion TNum TZero)
  | dt_add0 : forall lw,
    delta_t add TZero lw TNum
  | dt_addLam : forall t1 lw1 t2 lw2 typ_arrow,
    has_error add_lam lw2 = true ->
    typ_arrow = (TArrow t1 lw1 t2) ->
    delta_t add typ_arrow lw2 TBot
.

Example divide_by_0 :
  delta_t div TZero (div_0 :: nil) TBot
.
  apply dt_div0. reflexivity.
Qed.

Example divide_by_lam :
  delta_t div (TArrow TNum nil TZero) (div_0 :: (div_lam :: nil)) TBot
.
  apply dt_divLam with (t1 := TNum) (lw1 := nil) (t2 := TZero);
  reflexivity.
Qed.

Example divide_by_union :
  delta_t add (TUnion (TArrow TNum nil TZero) TNum) (add_lam :: nil)
     (TUnion TBot (TUnion TNum TZero)).
Proof.
  apply dt_union.
  apply dt_addLam with (t1 := TNum) (lw1 := nil) (t2 := TZero);  reflexivity.
  apply dt_addN.
Qed.


