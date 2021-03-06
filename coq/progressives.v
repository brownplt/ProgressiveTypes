(*Require Export Arith.EqNat.*)
Require Export Arith.
Require Export QArith.
Require Export List.
Require Export SfLib.

Ltac break_ands :=
  repeat match goal with
           [ H : _ /\ _ |- _ ] => inversion H; clear H
         end.

Hint Extern 2 =>
  match goal with
    [ H : _ /\ _ |- _ ] => inversion H; clear H
  end.

Definition beq_id X1 X2 :=
  match (X1, X2) with
    (Id n1, Id n2) => beq_nat n1 n2
  end.

Theorem beq_id_refl : forall i,
  true = beq_id i i.
Proof.
  intros. destruct i.
  apply beq_nat_refl. Qed.

Theorem beq_id_eq : forall i i',
  beq_id i i' = true -> i = i'.
Proof.
  intros. unfold beq_id in H. destruct i; destruct i'.
  f_equal.
  apply beq_nat_eq. auto.
Qed.

  
Inductive w : Type :=
  | div_0 : w
  | div_lam : w
  | add_lam : w
  | app_n : w
  | app_0 : w
.

Hint Constructors w.

Definition W := list w.

Hint Unfold W.

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

Hint Constructors c.

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

Hint Extern 4 =>
  match goal with 
    | [ H : TBot = ?t |- _ ] => inversion H
    | [ H : TZero = ?t |- _ ] => inversion H
    | [ H : TNum = ?t |- _ ] => inversion H
    | [ H : TUnion _ _ = ?t |- _ ] => inversion H
    | [ H : TArrow _ _ _ = ?t |- _ ] => inversion H
  end.


Hint Constructors typ.

Fixpoint beq_list_w lw lw' :=
  match lw, lw' with
    | nil, nil => true
    | w :: tail, w' :: tail' =>
      andb (beq_w w w') (beq_list_w tail tail')
    | _, _ => false
  end
.

Fixpoint bcontains_list_w lw lw' :=
  match lw, lw' with
    | nil, nil => true
    | nil, nonempty => true
    | w :: tail, w' :: tail' =>
      andb (beq_w w w') (bcontains_list_w tail tail')
    | nonempty, nil => false
  end
.

Lemma beq_w_eq : forall w w', beq_w w w' = true <-> w = w'.
Proof.
 intros. 
 split; destruct w0; destruct w'; try (simpl in H); try (discriminate); auto.
Qed.


Lemma bcontains_list_trans: forall l1 l2 l3,
  bcontains_list_w l1 l2 = true -> 
  bcontains_list_w l2 l3 = true ->
  bcontains_list_w l1 l3 = true.
Proof.
  intros. generalize dependent l2. generalize dependent l3. induction l1; intros.
  destruct l3; reflexivity.
  simpl in *. destruct l2. inversion H.
  apply andb_true_iff in H. break_ands.
  apply beq_w_eq in H1. subst.
  simpl in H0. destruct l3; auto. rewrite andb_true_iff in *. break_ands; split; eauto.
Qed.

Lemma bcontains_list_refl: forall l,
  bcontains_list_w l l = true.
Proof.
  induction l; auto.
  simpl. rewrite andb_true_iff. split; auto.
  destruct a; auto.
Qed.

Hint Resolve bcontains_list_refl.
Hint Resolve bcontains_list_trans.
Hint Rewrite beq_w_eq.

Fixpoint beq_typ t t' :=
  match t, t' with
    | TBot, TBot => true
    | TZero, TZero => true
    | TNum, TNum => true
    | TUnion t1 t2, TUnion t1' t2' =>
      andb (beq_typ t1 t1') (beq_typ t2 t2')
    | TArrow t1 lw t2, TArrow t1' lw' t2' =>
      andb (beq_typ t1 t1')
           (andb (beq_typ t2 t2') (beq_list_w lw lw'))
    | _, _ => false
  end.

Inductive expr : Type :=
  | ENum : Q -> expr
  | ELam : id -> typ -> list w -> expr -> expr
  | EVar : id -> expr
  | EErr : w -> expr
  | EApp : expr -> expr -> expr
  | EPrim : c -> expr -> expr
.

Hint Extern 4 =>
  match goal with 
    | [ H : ENum _ = ?t |- _ ] => inversion H
    | [ H : ELam _ _ _ _ = ?t |- _ ] => inversion H
    | [ H : EVar _ = ?t |- _ ] => inversion H
    | [ H : EErr _ = ?t |- _ ] => inversion H
    | [ H : EApp _ _ = ?t |- _ ] => inversion H
    | [ H : EPrim _ _ = ?t |- _ ] => inversion H
  end.


Hint Constructors expr.

Inductive aval : expr -> Prop :=
  | av_num : forall n, aval (ENum n)
  | av_lam : forall id typ ws expr, aval (ELam id typ ws expr)
.

Hint Constructors aval.

Inductive cxt : Type :=
  | EHole : cxt
  | EAppFun : cxt -> expr -> cxt
  | EAppArg : expr -> cxt -> cxt
  | EPrimArg : c -> cxt -> cxt
.

Hint Constructors cxt.

Inductive ActExp : expr -> Prop :=
  | ActPrim : forall c e, aval e -> ActExp (EPrim c e)
  | ActApp : forall e1 e2, aval e1 -> aval e2 -> ActExp (EApp e1 e2)
.

Hint Constructors ActExp.

Inductive HoleFiller : expr -> Prop :=
  | HFErr : forall w, HoleFiller (EErr w)
  | HFAct : forall e, ActExp e -> HoleFiller e
.

Hint Constructors HoleFiller.

Inductive EDecomp : expr -> cxt -> expr -> Prop :=
  | CxtHole : forall ae, HoleFiller ae -> EDecomp ae EHole ae
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

Hint Constructors EDecomp.

Fixpoint e_plug (c: cxt) (e: expr) : expr :=
  match c with    
    | EHole => e
    | EAppFun c2 e2 => EApp (e_plug c2 e) e2
    | EAppArg e2 c2 => EApp e2 (e_plug c2 e)
    | EPrimArg op c2 => EPrim op (e_plug c2 e)
  end
.
Definition Env := partial_map typ.

Inductive closed : Env -> expr -> Prop :=
  | closed_var : forall env x t,
      env x = Some t ->
      closed env (EVar x)
  | closed_num : forall env n, closed env (ENum n)
  | closed_err : forall env w, closed env (EErr w)
  | closed_lam : forall env x W t e,
      closed (extend env x t) e ->
      closed env (ELam x t W e)
  | closed_app : forall env e1 e2,
      closed env e1 -> closed env e2 -> closed env (EApp e1 e2)
  | closed_prim : forall env c e,
      closed env e -> closed env (EPrim c e)
.

Hint Constructors closed.

Lemma decomp_expr: forall e,
  closed empty e ->
  (exists E ae, HoleFiller ae /\ EDecomp e E ae) \/ aval e.
Proof with eauto.
  intros.
  induction e; auto; inversion H.
  Case "Var". discriminate.
  Case "Err".
    left. exists EHole. exists (EErr w0)...
  Case "App".
    left. apply IHe1 in H3.
    inversion H3.
    SCase "e1 decomposed".
      elim H5. intros E' H'. elim H'. intro ae.
      intros.
      exists (EAppFun E' e2).
      exists ae...
    SCase "e1 was a value".
      inversion H. subst.  apply IHe2 in H4. inversion H4.
      SSCase "e2 decomposed".
        elim H0. intros E' H'. elim H'. intro ae. intros.
        exists (EAppArg e1 E').
        exists ae...
      SSCase "e2 was a value".
        exists EHole. exists (EApp e1 e2).
        split...

  Case "Prim".
    left. apply IHe in H2. inversion H2.
    SCase "e decomposed".
      elim H4. intros E' H'. elim H'. intro ae. intros.
      exists (EPrimArg c0 E').
      exists ae...
    SCase "e was a value".
      exists EHole. exists (EPrim c0 e).
      split...
Qed.

Hint Resolve decomp_expr.

Fixpoint e_subst (x: id) (s: expr) (t: expr) : expr :=
  match t with
    | ENum n => ENum n
    | ELam x2 typ ws e =>
      if (beq_id x x2) then (t) else (ELam x2 typ ws (e_subst x s e)) 
    | EVar x2 => if (beq_id x x2) then s else t
    | EErr err_w => EErr err_w
    | EApp e1 e2 =>EApp (e_subst x s e1) (e_subst x s e2)
    | EPrim op_c e => EPrim op_c (e_subst x s e)
    end
.

Inductive delt : c -> expr -> expr -> Prop :=
 | DDivZero :
   forall n, Qeq n 0 ->
   delt div (ENum n) (EErr div_0)
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

Hint Constructors delt.

Inductive cxt_step : expr -> expr -> Prop :=
 | CStepApp : forall x typ ws eb ea,
   aval ea ->
   cxt_step (EApp (ELam x typ ws eb) ea) (e_subst x ea eb)
 | CStepAppNum : forall n ea,
   aval ea -> not (Qeq n 0) ->
   cxt_step (EApp (ENum n) ea) (EErr app_n)
 | CStepApp0 : forall n ea,
   aval ea -> Qeq n 0 ->
   cxt_step (EApp (ENum n) ea) (EErr app_0)

 | CStepPrim : forall c ea ea',
   aval ea ->
   delt c ea ea' ->
   cxt_step (EPrim c ea) ea'
.

Hint Constructors cxt_step.

Inductive step : expr -> expr -> Prop :=
 | StepCxt : forall e E ae ae' e',
   EDecomp e E ae ->
   ActExp ae ->
   cxt_step ae ae' ->
   e' = (e_plug E ae') ->
   step e e'

 | StepErr : forall e E w,
   EDecomp e E (EErr w) ->
   step e (EErr w)
.

Hint Constructors step.

Example step1 :
  cxt_step (EPrim div (ENum 1)) (ENum 1)
.
Proof.
  apply CStepPrim. apply av_num. apply DDivN.
  unfold not. intros. inversion H.
Qed.

Example bigger_num :
  cxt_step (EPrim div (ENum (Qmake 22 1))) (ENum (Qmake 1 22))
.
Proof.
  apply CStepPrim. apply av_num. apply DDivN.
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

Hint Unfold stepmany.
Hint Constructors refl_step_closure.

Example decomp1 :
  EDecomp (EPrim div (EPrim add (ENum 1)))
          (EPrimArg div EHole)
          (EPrim add (ENum 1))
.
Proof.
  apply CxtPrimArg. apply CxtHole. constructor. apply ActPrim. apply av_num.
Qed.
          

Example step2 :
  stepmany (EPrim div (EPrim add (ENum 1))) (ENum (Qmake 1 2))
.
Proof.
  apply rsc_step with (EPrim div (ENum (Qmake 2 1))).
  apply StepCxt with (E := EPrimArg div EHole)
                     (ae := EPrim add (ENum 1))
                     (ae' := ENum (Qmake 2 1)).
  apply CxtPrimArg. apply CxtHole. constructor. apply ActPrim. apply av_num.
  constructor. constructor.
  apply CStepPrim. apply av_num. apply DAddN.
  reflexivity.

  apply rsc_step with (ENum (Qmake 1 2)).
  apply StepCxt with (E := EHole)
                     (ae := EPrim div (ENum (2 # 1)))
                     (ae' := ENum (1 # 2)).
  apply CxtHole. constructor. apply ActPrim. apply av_num.
  constructor. constructor. apply CStepPrim. apply av_num. apply DDivN. 
  unfold not. intros. inversion H. reflexivity.
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

Hint Constructors delta_t.

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

Lemma beq_list_eq : forall lw lw', beq_list_w lw lw' = true -> lw = lw'.
Proof.
  induction lw; destruct lw'; simpl; auto; intros; try (discriminate).
  apply andb_true_iff in H.
  break_ands.
  f_equal; auto.
  destruct a; destruct w0; simpl in H0; solve [auto | discriminate].
Qed.

Lemma beq_typ_eq : forall s t, beq_typ s t = true -> s = t.
Proof.
  induction s; destruct t; simpl; intros; try solve [auto | tauto | discriminate];
  apply andb_true_iff in H; f_equal; auto.
  break_ands.
  apply andb_true_iff in H1. break_ands.
  apply beq_list_eq in H2. assumption.
  break_ands.
  apply andb_true_iff in H1. break_ands. auto.
Qed.


Inductive apply_t : typ -> typ -> list w -> typ -> Prop :=
  | at_bot1 : forall t lw, apply_t t TBot lw TBot
  | at_bot2 : forall t lw, apply_t TBot t lw TBot

  | at_zero : forall t lw,
    ~ (t = TBot) ->
    has_error app_0 lw = true ->
    apply_t TZero t lw TBot
  | at_num : forall t lw,
    ~ (t = TBot) ->
    has_error app_n lw = true ->
    apply_t TNum t lw TBot

  | at_app : forall t1 lw1 t2 t' lw2 arrow_typ,
    ~ (t' = TBot) ->
    beq_typ t1 t' = true ->
    bcontains_list_w lw1 lw2 = true ->
    arrow_typ = (TArrow t1 lw1 t2) ->
    apply_t arrow_typ t' lw2 t2

  | at_union : forall t1 t2 t' lw left_typ right_typ union_typ result_typ,
    ~ (t' = TBot) ->
    apply_t t1 t' lw left_typ ->
    apply_t t2 t' lw right_typ ->
    union_typ = (TUnion t1 t2) ->
    result_typ = (TUnion left_typ right_typ) ->
    apply_t union_typ t' lw result_typ
.

Hint Constructors apply_t.

Example app_union :
  apply_t (TUnion (TArrow TNum nil TZero) TNum) TNum (app_n :: nil)
          (TUnion TZero TBot)
.
  apply at_union with (t1 := (TArrow TNum nil TZero))
                      (t2 := TNum)
                      (left_typ := TZero)
                      (right_typ := TBot); try solve [discriminate].
  apply at_app with (t1 := TNum) (lw1 := nil); try solve [discriminate];
  reflexivity.

  apply at_num; try solve [discriminate]; reflexivity.

  reflexivity.
  reflexivity.
Qed.

Example app_div :
  apply_t (TArrow TNum nil TNum) TNum nil
          TNum
.
  apply at_app with (t1 := TNum) (lw1 := nil); try solve [discriminate]; reflexivity.
Qed.

Inductive subtype : typ -> typ -> Prop :=
  | SBot : forall T, subtype TBot T
  | SRefl : forall T, subtype T T
  | SUnionL : forall S T1 T2,
      subtype S T1 ->
      subtype S (TUnion T1 T2)
  | SUnionR : forall S T1 T2,
      subtype S T2 ->
      subtype S (TUnion T1 T2)
  | SUnionJoin : forall S1 S2 T,
      subtype S1 T ->
      subtype S2 T ->
      subtype (TUnion S1 S2) T
  | SArrow : forall A1 W1 R1 A2 W2 R2,
      subtype A2 A1 ->
      subtype R1 R2 ->
      bcontains_list_w W1 W2 = true ->
      subtype (TArrow A1 W1 R1) (TArrow A2 W2 R2)
.

Hint Constructors subtype.

Definition partial_map (A:Type) := id -> option A.

Definition empty {A:Type} : partial_map A := (fun _ => None). 

(** Informally, we'll write [Gamma, x:T] for "extend the partial
    function [Gamma] to also map [x] to [T]."  Formally, we use the
    function [extend] to add a binding to a partial map. *)

Definition extend {A:Type} (Gamma : partial_map A) (x:id) (T : A) :=
  fun x' => if beq_id x x' then Some T else Gamma x'.

Lemma extend_eq : forall A (ctxt: partial_map A) x T,
  (extend ctxt x T) x = Some T.
Proof.
  intros. unfold extend. rewrite <- beq_id_refl. auto.
Qed.

Lemma extend_neq : forall A (ctxt: partial_map A) x1 T x2,
  beq_id x2 x1 = false ->
  (extend ctxt x2 T) x1 = ctxt x1.
Proof.
  intros. unfold extend. rewrite H. auto.
Qed.


Definition context := partial_map typ.

Inductive has_type : W -> context -> expr -> typ -> Prop :=
  | HTVar : forall W Gamma x t,
      Gamma x = Some t ->
      has_type W Gamma (EVar x) t
  | HTLam : forall W Gamma x targ W2 e tres,
      has_type W2 (extend Gamma x targ) e tres ->
      has_type W Gamma (ELam x targ W2 e) (TArrow targ W2 tres)
  | HTZero :  forall W Gamma n,
      Qeq n 0 ->
      has_type W Gamma (ENum n) TZero
  | HTNum : forall W Gamma n,
      not (Qeq n 0) ->
      has_type W Gamma (ENum n) TNum
  | HTErr : forall W Gamma w T,
      has_error w W = true ->
      has_type W Gamma (EErr w) T
  | HTApp : forall W Gamma e1 e2 t1 t2 t,
      has_type W Gamma e1 t1 ->
      has_type W Gamma e2 t2 ->
      apply_t t1 t2 W t ->
      has_type W Gamma (EApp e1 e2) t
  | HTPrim : forall W Gamma c e t1 t,
      has_type W Gamma e t1 ->
      delta_t c t1 W t ->
      has_type W Gamma (EPrim c e) t
  | HTSub : forall W Gamma e s t,
      has_type W Gamma e s ->
      subtype s t ->
      has_type W Gamma e t
.

Hint Constructors has_type.


Example ht_lam :
  has_type nil empty (ELam (Id 0) TNum nil (EVar (Id 0))) 
           (TArrow TNum nil TNum)
.
  eauto.
Qed.

Example ht_div0 :
  has_type nil empty (ELam (Id 0) TZero (div_0 :: nil) (EPrim div (EVar (Id 0))))
           (TArrow TZero (div_0 :: nil) TBot)
.
 apply HTLam. apply HTPrim with (t1 := TZero). 
   apply HTVar. reflexivity.
   apply dt_div0. reflexivity.
Qed.

Lemma typing_used_w : forall W G e E w T,
  has_type W G e T ->
  EDecomp e E (EErr w) ->
  has_error w W = true.
Proof.
  intros.
  generalize dependent E.
  induction H; intros; try solve [inversion H0]; 
    match goal with
      [ H : EDecomp _ _ _ |- _ ] => inversion H
    end;
    subst; eauto.
Qed.

Hint Resolve typing_used_w.

Lemma delta_injective : forall c t lw t' t'',
  delta_t c t lw t' ->
  delta_t c t lw t'' ->
  t' = t''.
Proof.
  intros. generalize dependent t''.
  induction H; intros; try solve [
    match goal with
      [ H : delta_t _ _ _ _ |- _ ] => inversion H
    end; solve [auto | subst; discriminate]].
    inversion H1; subst; auto. f_equal; auto.
Qed.
    

Lemma delta_subtype : forall t1 t2 t' t'' c W,
  subtype t1 t2 ->
  delta_t c t1 W t' ->
  delta_t c t2 W t'' ->
  subtype t' t''.
Proof.
  intros.
  generalize dependent t'. generalize dependent t''.
  induction H; intros.
    inversion H0; constructor. assert (t' = t''). eapply delta_injective; eauto. subst. auto.
    inversion H1; subst; auto.
    inversion H1; subst; auto.
    inversion H2; subst; auto.
    inversion H2; subst; inversion H3; subst; auto.
Qed.


(*
Lemma canonical_forms : forall W G e T,
  has_type W G (ENum 0) T -> subtype TZero T
  and
  forall n, n == 0 has_type W G (ENum n) T -> 
*)
Lemma inv_nonzero : forall q, ~ (/ q == 0) -> ~ (q == 0).
Proof. 
  intros. intro. apply H. destruct q. unfold Qinv in *. simpl in *.
  destruct (Z.eq_dec Qnum 0%Z); subst. reflexivity. inversion H0; omega.
Qed.

Lemma inv_zeronon : forall q, ~ q == 0 -> ~ / q == 0.
Proof.
  intros. intro. apply H. destruct q. unfold Qinv in *. simpl in *.
  destruct (Z.eq_dec Qnum 0%Z); subst. reflexivity.
  destruct Qnum; simpl in *. contradiction. inversion H0. inversion H0.
Qed.

Hint Resolve inv_nonzero.
Hint Resolve inv_zeronon.

Lemma delta_inv_div_0 : forall t1 W,
  subtype TZero t1 ->
  forall t, delta_t div t1 W t ->
  has_error div_0 W = true.
Proof.
  intros t1 W H.
  remember TZero as t_sub.
  induction H; subst; intros; try (inversion Heqt_sub);
    match goal with
      [ H : delta_t _ _ _ _ |- _ ] => inversion H
    end; try (discriminate); eauto.
Qed.

Lemma delta_inv_div_lam : forall s W' u t1 W,
  subtype (TArrow s W' u) t1 ->
  forall t, delta_t div t1 W t ->
  has_error div_lam W = true.
Proof.
  intros s W' u t1 W H.
  remember (TArrow s W' u) as t_sub.
  induction H; subst; intros; try (inversion Heqt_sub);
    match goal with
      [ H : delta_t _ _ _ _ |- _ ] => inversion H
    end; try (discriminate); eauto.
Qed.

Lemma delta_inv_add_lam : forall s W' u t1 W,
  subtype (TArrow s W' u) t1 ->
  forall t, delta_t add t1 W t ->
  has_error add_lam W = true.
Proof.
  intros s W' u t1 W H.
  remember (TArrow s W' u) as t_sub.
  induction H; subst; intros; try (inversion Heqt_sub);
    match goal with
      [ H : delta_t _ _ _ _ |- _ ] => inversion H
    end; try (discriminate); eauto.
Qed.

Lemma app_inv_0 : forall t1 targ W,
  subtype TZero t1 ->
  forall tres, apply_t t1 targ W tres ->
  ~ (subtype targ TBot) ->
  has_error app_0 W = true.
Proof.
  intros t1 targ W H.
  remember TZero as t_sub.
  induction H; subst; intros; try (inversion Heqt_sub);
    match goal with
      [ H : apply_t _ _ _ _ |- _ ] => inversion H
    end; try (discriminate); try (inversion H5); subst; eauto.
Qed.

Lemma app_inv_n : forall t1 targ W,
  subtype TNum t1 ->
  forall tres, apply_t t1 targ W tres ->
  ~ (subtype targ TBot) ->
  has_error app_n W = true.
Proof.
  intros t1 targ W H.
  remember TNum as t_sub.
  induction H; subst; intros; try (inversion Heqt_sub);
    match goal with
      [ H : apply_t _ _ _ _ |- _ ] => inversion H
    end; try (discriminate); try (inversion H5); subst; eauto.
Qed.

Hint Resolve delta_inv_div_0.
Hint Resolve delta_inv_div_lam. 
Hint Resolve delta_inv_add_lam.
Hint Resolve app_inv_0.
Hint Resolve app_inv_n.

Fixpoint type_size t : nat :=
  match t with
    | TBot => 1%nat
    | TZero => 1%nat
    | TNum => 1%nat
    | TUnion t1 t2 => S (type_size t1 + type_size t2)
    | TArrow t1 _ t2 => S (type_size t1 + type_size t2)
  end.

Lemma union_incl_1 : forall t1 t2 t3, 
  subtype (TUnion t1 t2) t3 -> subtype t1 t3.
Proof.
  intros. remember (TUnion t1 t2) as t_union. induction H; eauto.
  subst. eauto.
  inversion Heqt_union. subst. assumption.
Qed.

Lemma union_incl_2 : forall t1 t2 t3, 
  subtype (TUnion t1 t2) t3 -> subtype t2 t3.           
Proof.
  intros. remember (TUnion t1 t2) as t_union. induction H; eauto.
  subst. eauto.
  inversion Heqt_union. subst. assumption.
Qed.

Hint Resolve union_incl_1.
Hint Resolve union_incl_2.
    
Lemma subtype_transitive : forall s t u,
  subtype s t -> subtype t u -> subtype s u.
Proof.
  intros.
  remember (type_size t) as n.
  assert (type_size t <= n)%nat by omega. clear Heqn. generalize dependent u; generalize dependent s; generalize dependent t.
  induction n; intros.
  Case "n = 0".
    destruct t; inversion H1.
  Case "n > 0".
    generalize dependent t; generalize dependent u.
    induction s; intros; inversion H; subst; try (discriminate); eauto;
      inversion H1; eauto;
      try solve [
        apply IHn with (t := T1); eauto; rewrite <- H4; apply le_plus_l
      ];
      try solve [
        apply IHn with (t := T2); eauto; rewrite <- H4; apply le_plus_r
      ].
    SCase "s = TArrow; t = TArrow".
      remember (TArrow A2 W2 R2) as middle.
      induction H0; try solve [inversion H]; inversion Heqmiddle; subst; eauto.
      SSCase "u = TArrow".
        apply SArrow; eauto.
        apply IHn with (t := A2); auto. simpl in H1. omega.
        apply IHn with (t := R2); auto. simpl in H1. omega.
Qed.

Hint Resolve subtype_transitive.

Lemma apply_subtype : forall targ1 W1 tres1 tfun targ2 W2 tres2,
  subtype (TArrow targ1 W1 tres1) tfun ->
  apply_t tfun targ2 W2 tres2 ->
  ~ (subtype targ2 TBot) ->
  (subtype tres1 tres2) /\ (subtype targ2 targ1) /\ (bcontains_list_w W1 W2 = true).
Proof.
  intros.
  remember (TArrow targ1 W1 tres1) as arr_typ.
  remember targ1 as arg_typ.
  generalize dependent tres2.
  induction H; try solve [intros; subst; discriminate].
  intros.
  induction H0; try solve [discriminate].
    contradict H1. auto.
    subst. inversion H3. split; auto. split; auto. apply beq_typ_eq in H0. subst; auto.
    subst. inversion H0.
    
    intros. inversion H0; subst; try solve [discriminate].
      contradict H1. constructor. inversion H5. subst.
        split. apply subtype_transitive with (t := left_typ). apply IHsubtype; auto. auto.
        assert (subtype tres1 left_typ /\ subtype targ2 targ1 /\ bcontains_list_w W1 W2 = true).
        apply IHsubtype; auto. split; break_ands; auto.
    intros. inversion H0; subst; try solve [discriminate].
      contradict H1. constructor. inversion H5. subst.
        split. apply subtype_transitive with (t := right_typ). apply IHsubtype; auto. auto.
        assert (subtype tres1 right_typ /\ subtype targ2 targ1 /\ bcontains_list_w W1 W2 = true).
        apply IHsubtype; auto. split; break_ands; auto.
      
    intros. inversion Heqarr_typ. subst.
    inversion H3; subst. contradict H1. constructor.
    inversion H7. subst. repeat split; auto. apply beq_typ_eq in H5. subst. assumption.
    eauto.
    inversion H7.
Qed.


Lemma apply_subtype_res : forall targ1 W1 tres1 tfun targ2 W2 tres2,
  subtype (TArrow targ1 W1 tres1) tfun ->
  ~ (subtype targ2 TBot) ->
  apply_t tfun targ2 W2 tres2 ->
  subtype tres1 tres2.
Proof.
  intros.
  assert (ans := apply_subtype _ _ _ _ _ _ _ H H1 H0). auto.
Qed.
Lemma apply_subtype_arg : forall targ1 W1 tres1 tfun targ2 W2 tres2,
  subtype (TArrow targ1 W1 tres1) tfun ->
  ~ (subtype targ2 TBot) ->
  apply_t tfun targ2 W2 tres2 ->
  subtype targ2 targ1.
Proof.
  intros.
  assert (ans := apply_subtype _ _ _ _ _ _ _ H H1 H0). auto.
Qed.

Lemma apply_subtype_W : forall targ1 W1 tres1 tfun targ2 W2 tres2,
  subtype (TArrow targ1 W1 tres1) tfun ->
  ~ (subtype targ2 TBot) ->
  apply_t tfun targ2 W2 tres2 ->
  bcontains_list_w W1 W2 = true.
Proof.
  intros.
  assert (ans := apply_subtype _ _ _ _ _ _ _ H H1 H0). auto.
Qed.

Hint Resolve apply_subtype_res.
Hint Resolve apply_subtype_arg.
Hint Resolve apply_subtype_W.
Hint Resolve apply_subtype.

Lemma invert_lam : forall x t w e W G t1 t2,
  has_type W G (ELam x t w e) t1 ->
  subtype t1 t2 ->
  exists tres ,
    (has_type W G (ELam x t w e) (TArrow t w tres) /\
    has_type w (extend G x t) e tres /\
    subtype (TArrow t w tres) t2).
Proof.
  intros.
  remember (ELam x t w0 e) as elam.
  induction H; inversion Heqelam; subst; eauto.
Qed.

Lemma invert_lam_arrow : forall x t w e W G t1 t2,
  has_type W G (ELam x t w e) t1 ->
  subtype t1 t2 ->
  exists tres ,
    has_type W G (ELam x t w e) (TArrow t w tres).
Proof.
  intros.
  assert (H_new := invert_lam _ _ _ _ _ _ _ t1 H (SRefl t1)).
  elim H_new. intros. exists x0. break_ands. assumption.
Qed.
  

Lemma invert_lam_res : forall x t w e W G t1 t2,
  has_type W G (ELam x t w e) t1 ->
  subtype t1 t2 ->
  exists tres ,
     has_type w (extend G x t) e tres.
 Proof.
  intros.
  assert (H_new := invert_lam _ _ _ _ _ _ _ t1 H (SRefl t1)).
  elim H_new. intros. exists x0. break_ands. assumption.
Qed.

Lemma invert_lam_sub : forall x t w e W G t1 t2,
  has_type W G (ELam x t w e) t1 ->
  subtype t1 t2 ->
  exists tres ,
    subtype (TArrow t w tres) t2.
Proof.
  intros.
  assert (H_new := invert_lam _ _ _ _ _ _ _ t1 H (SRefl t1)).
  elim H_new. intros. exists x0. break_ands. eauto.
Qed.

Hint Resolve invert_lam_arrow.
Hint Resolve invert_lam_res.
Hint Resolve invert_lam_sub.

Lemma invert_num : forall n t1 t2 W G,
  ~ (n == 0) ->
  has_type W G (ENum n) t1 ->
  subtype t1 t2 ->
  subtype TNum t2.
Proof.
  intros.
  remember (ENum n) as num.
  induction H0; inversion Heqnum; subst. contradiction.
  eauto. eauto.
Qed.

Lemma invert_0 : forall n t1 t2 W G,
  Qeq n 0 ->
  has_type W G (ENum n) t1 ->
  subtype t1 t2 ->
  subtype TZero t2.
Proof.
  intros.
  remember (ENum n) as num.
  induction H0; inversion Heqnum. assumption.  assert (n == 0). assumption. subst. contradiction. apply IHhas_type. assumption. subst. apply subtype_transitive with (t := t); assumption.
Qed.

Hint Resolve invert_num.
Hint Resolve invert_0.

Lemma val_not_bottom : forall e W G t,
  has_type W G e t ->
  aval e ->
  ~ (subtype t TBot).
Proof.
  intros.
  induction H; try solve [inversion H0];
      try solve [unfold not; intro; inversion H1].
    unfold not. intro. apply IHhas_type. assumption.
      apply subtype_transitive with (t := t); assumption.
Qed.

Hint Resolve val_not_bottom.

Definition map_contains G G' := 
  forall (x : id) (T : typ),
    G x = Some T -> G' x = Some T.

Definition all_same (G1 G2 : Env) :=
  forall (x : id), G1 x = G2 x.

Lemma double_extend_contains : forall G x x' (t t' : typ),
  beq_id x x' = true ->
  map_contains (extend (extend G x t) x' t') (extend G x' t').
Proof.
  intros. unfold map_contains.
  intros. unfold extend in *.
  remember (beq_id x' x0) as id.
  destruct id. assumption.
  apply beq_id_eq in H; subst.
  symmetry in Heqid. rewrite Heqid in H0.
  assumption.
Qed.

Lemma commute_extend_contains : forall G x x' (t t' : typ),
  beq_id x x' = false ->
  map_contains (extend (extend G x t) x' t') (extend (extend G x' t') x t).
Proof.
  intros. unfold map_contains.
  intros. unfold extend in *.
  remember (beq_id x' x0) as id.
  destruct id.
  symmetry in Heqid. apply beq_id_eq in Heqid; subst.
  rewrite H; assumption.
  assumption.
Qed.

Hint Resolve double_extend_contains.
Hint Resolve commute_extend_contains.

Lemma other_extend_eq1 : forall G x x' (t t' :typ),
  beq_id x' x = false ->
  G x = Some t ->
  (extend G x' t') x = Some t.
Proof.
  intros.
  unfold extend.
  rewrite H. assumption.
Qed.

Lemma other_extend_eq2 : forall G x x' (t t' :typ),
  beq_id x' x = false ->
  (extend G x' t') x = Some t ->
  G x = Some t.
Proof.
  intros.
  unfold extend in H0.
  rewrite H in H0. assumption.
Qed.

Lemma extend_then_get : forall G x (T T' : typ),
  (extend G x T) x = Some T' ->
  T = T'.
Proof.
  intros. unfold extend in H.
  remember (beq_id x x) as id.
  destruct id; simpl in H.
  inversion H; auto.
  rewrite <- beq_id_refl in Heqid.
  inversion Heqid.
Qed.

Hint Resolve other_extend_eq1.
Hint Resolve other_extend_eq2.
Hint Resolve extend_then_get.

Lemma contains_w_trans : forall w W1 W2,
  bcontains_list_w W1 W2 = true ->
  has_error w W1 = true ->
  has_error w W2 = true.
Proof.
  intros.
  generalize dependent W2.
  induction W1.
  intros.
  inversion H0.
  intros.
  destruct W2.
  inversion H.
  destruct w0; destruct a; destruct w1; auto; simpl; auto; inversion H.
Qed.

Hint Resolve contains_w_trans.
    

Lemma weaken_W : forall W1 W2 G e t,
  has_type W1 G e t ->
  bcontains_list_w W1 W2 = true ->
  has_type W2 G e t.
Proof.
  intros.
  induction H; subst; try solve [constructor; assumption]; eauto.
  Case "HTApp".
    apply HTApp with (t1 := t1) (t2 := t2); auto.
    clear H H1 IHhas_type1 IHhas_type2.
    induction H2; subst; eauto.
  Case "HTPrim".
    apply HTPrim with (t1 := t1); eauto.
    clear H IHhas_type.
    induction H1; eauto.
Qed.

Lemma map_empty_contained : forall G,
  map_contains empty G.
Proof.
  intros.
  unfold map_contains.
  intros.
  inversion H.
Qed.

Lemma map_extend_contained : forall G x t,
  G x = None ->
  map_contains G (extend G x t).
Proof.
  intros.
  unfold map_contains.
  intros.
  remember (beq_id x x0) as xb.
  destruct xb.
  symmetry in Heqxb.
  apply beq_id_eq in Heqxb. subst. rewrite H0 in H. inversion H.
  symmetry in Heqxb.
  apply other_extend_eq1. assumption. assumption.
Qed.

Lemma map_contains_ext : forall G G' x t,
  map_contains G G' -> 
  map_contains (extend G x t) (extend G' x t).
Proof.
  intros. unfold map_contains in *.
  unfold extend. intros.
  remember (beq_id x x0) as id.
  destruct id. assumption.
  apply H; assumption.
Qed.

Hint Resolve map_empty_contained.
Hint Resolve map_extend_contained.
Hint Resolve map_contains_ext.

Lemma weaken_G : forall W G G' v t,
  map_contains G G' ->
  has_type W G v t ->
  has_type W G' v t.
Proof.
  intros. generalize dependent G'.
  induction H0; intros; eauto.
Qed.
  
Lemma weaken_W_apply : forall W W' t t' t'',
  apply_t t t' W t'' ->
  bcontains_list_w W W' = true ->
  apply_t t t' W' t''.
Proof.
  intros. induction H; subst; eauto.
Qed.

Lemma weaken_W_delta : forall W W' c t tres,
  delta_t c t W tres ->
  bcontains_list_w W W' = true ->
  delta_t c t W' tres.
Proof.
  intros. induction H; subst; eauto.
Qed.

Hint Resolve weaken_W.
Hint Resolve weaken_G.
Hint Resolve weaken_W_apply.
Hint Resolve weaken_W_delta.

Lemma subst_type : forall e x v G T W1 W2 Tx,
  has_type W1 (extend G x Tx) e T ->
  aval v ->
  bcontains_list_w W1 W2 = true ->
  has_type nil empty v Tx ->
  has_type W2 G (e_subst x v e) T.
Proof.
  intros. 
  generalize dependent T. generalize dependent W1. generalize dependent G. generalize dependent W2.
  induction e; intros.
  Case "Num".
    remember (ENum q) as e_num.
    remember (extend G x Tx) as G1.
    induction H; simpl; eauto.
  Case "Lam".
    simpl.
    remember (ELam i t l e) as e_lam.
    remember (extend G x Tx) as G1.
    induction H; try solve [inversion Heqe_lam]; subst; eauto. inversion Heqe_lam; subst.
    SCase "Arrow". subst. simpl.
      remember (beq_id x i) as H_x.
      destruct H_x; eauto.
      SSCase "x = i".
        apply HTLam.
        apply weaken_G with (G := (extend (extend G x Tx) i t)).
        apply double_extend_contains; auto.
        assumption.
  Case "Var".
    simpl.
    remember (beq_id x i) as H_x.
    destruct H_x.
    SCase "actually substing".
      remember (EVar i) as e_var.
      remember (extend G x Tx) as g_ext.
      induction H; eauto.
        inversion Heqe_var. subst.
        symmetry in HeqH_x.
        apply beq_id_eq in HeqH_x. subst.
        apply extend_then_get in H. subst.
        apply weaken_W with (W1 := []).
        apply weaken_G with (G := empty).
        apply map_empty_contained. assumption. simpl. destruct W2; auto.
    SCase "not actually substing".
      remember (EVar i) as e_var.
      remember (extend G x Tx) as g_ext.
      induction H; eauto.
        apply HTVar. subst. apply other_extend_eq2 with (x' := x) (t' := Tx).
        inversion Heqe_var. auto. auto.
  Case "Err".
    remember (EErr w0) as e_err.
    induction H; simpl; eauto.
  Case "EApp".
    remember (EApp e1 e2) as e_app.
    remember (extend G x Tx) as g_ext.
    induction H; eauto.
    apply HTApp with (t1 := t1) (t2 := t2).
    fold e_subst. inversion Heqe_app. subst. apply IHe1 with (W1 := W0); auto.
    fold e_subst. inversion Heqe_app. subst. apply IHe2 with (W1 := W0); auto.
    apply weaken_W_apply with (W := W0); auto.
  Case "EPrim".
    remember (EPrim c0 e) as e_prim.
    remember (extend G x Tx) as g_ext.
    induction H; eauto.
    apply HTPrim with (t1 := t1).
    fold e_subst. inversion Heqe_prim. subst. apply IHe with (W1 := W0); auto.
    apply weaken_W_delta with (W := W0); auto.
Qed.

Lemma values_no_errors : forall W G v t,
  aval v ->
  has_type W G v t ->
  has_type [] G v t.
Proof.
  intros; induction H0; subst; inversion H; subst; eauto.
Qed.

Hint Resolve values_no_errors.

Hint Extern 4 =>
  match goal with
    [ H : has_type _ _ (ELam _ _ _ _) ?s,
      H_sub : subtype ?s _
      |- _ ] =>
    let H_new := fresh "H_new" in
      assert (H_new := invert_lam _ _ _ _ _ _ _ _ H H_sub)
  | [
      H_sub : subtype ?s _,
      H : has_type _ _ (ELam _ _ _ _) ?s
      |- _ ] =>
    let H_new := fresh "H_new" in
      assert (H_new := invert_lam _ _ _ _ _ _ _ _ H H_sub)

  end.



Theorem preservation : forall e e' W T,
     has_type W empty e T  ->
     step e e'  ->
     has_type W empty e' T.
Proof.
  intros.
  generalize dependent e'.
  remember (empty) as mt.
  induction H; intros;
    try solve [
      inversion H0; try solve [
        inversion H1 |
        subst; inversion H1; subst; inversion H3 |
        apply HTErr; inversion H1; subst; auto
      ]]; subst; eauto.
  Case "HTApp".
   inversion H2; subst; eauto.
    SCase "Decomp".
     inversion H3; subst; simpl in *; eauto.
     SSCase "Active".
        inversion H5; subst; eauto.
        SSSCase "EApp".
          apply subst_type with (W1 := ws) (Tx := typ0); auto; try solve [
            assert (H_new := invert_lam _ _ _ _ _ _ _ t1 H (SRefl t1));
              elim H_new; intros; break_ands; clear H_new;
                assert (~ (subtype t2 TBot)) by
                  (apply val_not_bottom with (e := e2) (W := W0) (G := empty); assumption);
                  eauto
          ].
  Case "HTPrim".
  inversion H1; subst; eauto.
    SCase "Decomp".
    inversion H2; subst; simpl in *; eauto.
    SSCase "Active". 
      inversion H4. subst.
      inversion H10; subst; auto; eauto. 
      SSSCase "DivN".
        inversion H; subst.
        SSSSCase "Zero : TNum". contradiction.
        SSSSCase "Num : TNum".
          inversion H0; subst; eauto.
        SSSSCase "Num : s <= t". simpl in *.
          induction H7; subst; try solve [inversion H10]; eauto. 
          SSSSSCase "Zero is not non-zero". inversion H10. contradiction. 
          SSSSSCase "Num". apply HTSub with (s := TNum); auto.
            SSSSSSCase "delta/subtyping commute".
              apply delta_subtype with (t1 := TNum) (t2 := t1) (c := div) (W := W0); auto.
      SSSCase "DivLam".
        inversion H; subst; eauto.
        SSSSCase "Num : s <= t". simpl in *.
        induction H6; subst; try solve [inversion H10]; eauto.
      SSSCase "AddNumOrZero".
        inversion H; subst.
        SSSSCase "Zero : TZero".
          simpl.
          inversion H0; subst; auto.
          SSSSSCase "0 + 1 is a number".
          apply HTNum. rewrite H11. simpl_relation.
        SSSSCase "Num : TNum".
          simpl.
          inversion H0; subst; auto.
          SSSSSCase "n + 1 is zero or a number".
            destruct (n + 1).
              destruct Qnum; solve [
                apply HTSub with (s := TZero); 
                  [constructor; simpl_relation | apply SUnionR; apply SRefl]
                | apply HTSub with (s := TNum); 
                  [constructor; simpl_relation | apply SUnionL; apply SRefl]].
        SSSSCase "Num : s <= t"; simpl in *.
          remember (ENum n) as e_n.
          induction H6; inversion Heqe_n; subst; try solve [inversion H10]; eauto.
          SSSSSCase "Zero".
            apply HTSub with (s := TNum). apply HTNum. rewrite H6. simpl_relation. 
            apply delta_subtype with (t1 := TZero) (t2 := t1) (c := add) (W := W0); auto.
          SSSSSCase "Num". 
            apply HTSub with (s := (TUnion TNum TZero)).
            destruct (Qeq_dec n (Qmake (-1) 1)).
              apply HTSub with (s := TZero). apply HTZero. rewrite q. simpl_relation. apply SUnionR. apply SRefl.
              apply HTSub with (s := TNum). apply HTNum. intro. apply n0.
                rewrite <- Qplus_inj_r. rewrite H9.  simpl_relation.
              apply SUnionL. apply SRefl.
              apply delta_subtype with (t1 := TNum) (t2 := t1) (c := add) (W := W0); auto.
      SSSCase "AddLambda".
        inversion H; subst.
        inversion H0. subst. simpl. apply HTErr. assumption.
        SSSSCase "Num : s <= t". simpl in *.
          induction H6; subst; try solve [inversion H10]; eauto.
Qed.
   
Inductive is_error: expr -> Prop :=
  | err : forall w, is_error (EErr w).
   

Hint Constructors aval.

Lemma has_type_closed : forall e W G t,
  has_type W G e t ->
  closed G e.
Proof.
  induction e; intros; auto; 
    match goal with
      | [ H : has_type _ _ ?e _ |- _ ] => let e' := fresh "e'" in
        remember e as e'; induction H; inversion Heqe'; subst
    end; try solve [apply IHhas_type; eauto | econstructor; eauto].
Qed.

Hint Resolve has_type_closed.

Lemma progress : forall W e t,
  has_type W empty e t ->
  aval e \/
  (~ (is_error e) /\ exists e', step e e') \/
  (is_error e /\ exists w, (e = EErr w) /\ has_error w W = true).
Proof.
  intros.
  assert ((exists E ae, HoleFiller ae /\ EDecomp e E ae) \/ aval e).
  apply decomp_expr. eauto.
  inversion H0; try solve [left; assumption].
  Case "Decomp".
    elim H1. intros E H2'. elim H2'. intros ae H2''. break_ands.
    destruct ae; try solve [inversion H2; inversion H4].
    SCase "EErr".
      remember E as e_before_the_fall.
      destruct E;
        try solve [
          right; left; split;
          try solve [unfold not; intro; inversion H4; subst; inversion H3 |
                     exists (EErr w0); apply StepErr with (E := e_before_the_fall); assumption]
        ].
      SSCase "Hole". subst. inversion H3. subst. right. right. split.
        constructor. exists w0. split; eauto.
    SCase "EApp".
      inversion H2. inversion H4. subst.
      right. left. split.
        unfold not. intro. inversion H5. subst. inversion H3.
        destruct ae1; try solve [inversion H8]; try (destruct (Qeq_dec q 0)); eauto.
    SCase "EPrim".
      inversion H2. inversion H4. subst.
      right. left. split.
        unfold not. intro. inversion H5. subst. inversion H3.
        destruct ae; try solve [inversion H7]; destruct c0; eauto.
          destruct (Qeq_dec q 0); eauto.
Qed.

Theorem soundness : forall W e e' t, 
  has_type W empty e t ->
  stepmany e e' ->
  aval e' \/
  (~ (is_error e') /\ exists e'', step e' e'') \/
  (is_error e' /\ exists w, (e' = EErr w) /\ has_error w W = true).
Proof.
  intros.
  induction H0.
  Case "Refl". eapply progress; eauto.
  Case "Step". apply IHrefl_step_closure. apply preservation with x; auto.
Qed.
