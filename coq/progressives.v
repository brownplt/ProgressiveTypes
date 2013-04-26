Require Export Arith.EqNat.
Require Export QArith.
Require Export List.
Require Export SfLib.

Inductive id : Type :=
  | Id : nat -> id
.

Definition beq_id X1 X2 :=
  match (X1, X2) with
    (Id n1, Id n2) => beq_nat n1 n2
  end.

Theorem beq_id_refl : forall i,
  true = beq_id i i.
Proof.
  intros. destruct i.
  apply beq_nat_refl. Qed.

Inductive w : Type :=
  | div_0 : w
  | div_lam : w
  | add_lam : w
  | app_n : w
  | app_0 : w
.

Definition W := list w.

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

Lemma bcontains_list_trans: forall l1 l2 l3,
  bcontains_list_w l1 l2 = true -> 
  bcontains_list_w l2 l3 = true ->
  bcontains_list_w l1 l3 = true.
Proof.
Admitted.
(*
  intros. generalize dependent l2. generalize dependent l3. induction l1; intros.
  destruct l3; reflexivity.
  intros. simpl. destruct l2. inversion H.
  inversion H.
  destruct l3. inversion H0.
  inversion H0. rewrite H2.
  assert (bcontains_list_w l1 l3 = true). apply IHl1 with (l2 := l2).
  destruct H2.
*)  


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

Inductive cxt_step : expr -> expr -> Prop :=
 | CStepApp : forall x typ ws eb ea,
   aval ea ->
   cxt_step (EApp (ELam x typ ws eb) ea) (e_subst x ea eb)
 | CStepAppNum : forall n ea,
   aval ea -> not (Qeq n 0) ->
   cxt_step (EApp (ENum n) ea) (EErr app_n)
 | CStepApp0 : forall ea,
   aval ea ->
   cxt_step (EApp (ENum 0) ea) (EErr app_0)

 | CStepPrim : forall c ea ea',
   aval ea ->
   delt c ea ea' ->
   cxt_step (EPrim c ea) ea'
.

Inductive step : expr -> expr -> Prop :=
 | StepCxt : forall e E ae ae' e',
   EDecomp e E ae ->
   cxt_step ae ae' ->
   e' = (e_plug E ae') ->
   step e e'

 | StepErr : forall e E w,
   EDecomp e E (EErr w) ->
   step e (EErr w)
.

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
  apply CStepPrim. apply av_num. apply DAddN.
  reflexivity.

  apply rsc_step with (ENum (Qmake 1 2)).
  apply StepCxt with (E := EHole)
                     (ae := EPrim div (ENum (2 # 1)))
                     (ae' := ENum (1 # 2)).
  apply CxtHole. apply ActPrim. apply av_num.
  apply CStepPrim. apply av_num. apply DDivN. 
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

Inductive apply_t : typ -> typ -> list w -> typ -> Prop :=
  | at_bot1 : forall t lw, apply_t TBot t lw TBot
  | at_bot2 : forall t lw, apply_t t TBot lw TBot

  | at_zero : forall t lw,
    has_error app_0 lw = true ->
    apply_t TZero t lw TBot
  | at_num : forall t lw,
    has_error app_n lw = true ->
    apply_t TNum t lw TBot

  | at_app : forall t1 lw1 t2 t' lw2 arrow_typ,
    beq_typ t1 t' = true ->
    bcontains_list_w lw1 lw2 = true ->
    arrow_typ = (TArrow t1 lw1 t2) ->
    apply_t arrow_typ t' lw2 t2

  | at_union : forall t1 t2 t' lw left_typ right_typ union_typ result_typ,
    apply_t t1 t' lw left_typ ->
    apply_t t2 t' lw right_typ ->
    union_typ = (TUnion t1 t2) ->
    result_typ = (TUnion left_typ right_typ) ->
    apply_t union_typ t' lw result_typ
.

Example app_union :
  apply_t (TUnion (TArrow TNum nil TZero) TNum) TNum (app_n :: nil)
          (TUnion TZero TBot)
.
  apply at_union with (t1 := (TArrow TNum nil TZero))
                      (t2 := TNum)
                      (left_typ := TZero)
                      (right_typ := TBot).
  apply at_app with (t1 := TNum) (lw1 := nil);
  reflexivity.

  apply at_num; reflexivity.

  reflexivity.
  reflexivity.
Qed.

Example app_div :
  apply_t (TArrow TNum nil TNum) TNum nil
          TNum
.
  apply at_app with (t1 := TNum) (lw1 := nil); reflexivity.
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

Example ht_lam :
  has_type nil empty (ELam (Id 0) TNum nil (EVar (Id 0))) 
           (TArrow TNum nil TNum)
.
  apply HTLam. apply HTVar. reflexivity.
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
  induction H; intros; try solve [inversion H0]; subst.
  Case "Error". inversion H0. subst. assumption.
  Case "App".
    inversion H2; subst.
    SCase "AppFun". apply IHhas_type1 in H7. assumption.
    SCase "AppArg". apply IHhas_type2 in H8. assumption.
  Case "Prim".
    inversion H1; subst.
    SCase "PrimArg". apply IHhas_type in H6. assumption.
  Case "Subtype".
    apply IHhas_type in H1. assumption.
Qed.

Lemma delta_subtype : forall t1 t2 t' t'' c W,
  subtype t1 t2 ->
  delta_t c t1 W t' ->
  delta_t c t2 W t'' ->
  subtype t' t''.
Proof. Admitted.

(*
Lemma canonical_forms : forall W G e T,
  has_type W G (ENum 0) T -> subtype TZero T
  and
  forall n, n == 0 has_type W G (ENum n) T -> 
*)
Lemma inv_nonzero : forall q, ~ (/ q == 0) -> ~ (q == 0).
Proof. admit.
(*  intros. intro. apply H. destruct q. unfold Qinv in *. simpl in *.
  destruct (Z.eq_dec Qnum 0%Z); subst. reflexivity. inversion H0; omega.*)
Qed.

Lemma inv_zeronon : forall q, ~ q == 0 -> ~ / q == 0.
Proof. admit.
(*  intros. intro. apply H. destruct q. unfold Qinv in *. simpl in *.
  destruct (Z.eq_dec Qnum 0%Z); subst. reflexivity.
  destruct Qnum; simpl in *. contradiction. inversion H0. inversion H0. *)
Qed.

Lemma delta_inv_div_0 : forall t1 W t,
  subtype TZero t1 ->
  delta_t div t1 W t ->
  has_error div_0 W = true.
Proof.
  intros t1 W t H H1.
  generalize dependent t.
  remember TZero as t_sub.
  induction H; subst; intros; try solve [inversion Heqt_sub].
    Case "TRefl". inversion H1.
      SCase "TZero". assumption.
      SCase "TLam". inversion H0.
    Case "TUnionL".
      inversion H1; subst.
      SCase "TUnion". apply IHsubtype with (t := t_left). reflexivity. assumption.
      SCase "TArrow". inversion H2.
    Case "TUnionR".
      inversion H1; subst.
      SCase "TUnion". apply IHsubtype with (t := t_right). reflexivity. assumption.
      SCase "TArrow". inversion H2.
Qed.

Lemma delta_inv_div_lam : forall s W' u t1 W t,
  subtype (TArrow s W' u) t1 ->
  delta_t div t1 W t ->
  has_error div_lam W = true.
Proof.
  intros s W' u t1 W t H H1.
  generalize dependent t.
  remember (TArrow s W' u) as t_sub.
  induction H; subst; intros; try solve [inversion Heqt_sub].
    Case "TRefl". inversion H1.
      SCase "TLam". assumption.
    Case "TUnionL".
      inversion H1; subst.
      SCase "TUnion". apply IHsubtype with (t := t_left). reflexivity. assumption.
      SCase "TArrow". inversion H2.
    Case "TUnionR".
      inversion H1; subst.
      SCase "TUnion". apply IHsubtype with (t := t_right). reflexivity. assumption.
      SCase "TArrow". assumption. inversion H2. subst. assumption.
Qed.


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
  Admitted.

Lemma union_incl_2 : forall t1 t2 t3, 
  subtype (TUnion t1 t2) t3 -> subtype t2 t3.           
Proof.
  Admitted.
    
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
    induction s; intros; inversion H; try solve [constructor]; subst; try solve [assumption].
    SCase "s = TZero; t = TUnion: Left".
      inversion H1.
      assert ((type_size T1 <= n)%nat). rewrite <- H4. apply le_plus_l.
      apply IHn with (t := T1); auto. simpl in H1. apply union_incl_1 with (t2 := T2). assumption.
      apply IHn with (t := (TUnion T1 T2)); assumption.
    SCase "s = TZero; t = TUnion: Right".
      inversion H1.
      assert ((type_size T2 <= n)%nat). rewrite <- H4. apply le_plus_r.
      apply IHn with (t := T2); auto. simpl in H1. apply union_incl_2 with (t1 := T1). assumption.
      apply IHn with (t := (TUnion T1 T2)); assumption.
   SCase "s = TNum; t = TUnion: Left".
      inversion H1.
      assert ((type_size T1 <= n)%nat). rewrite <- H4. apply le_plus_l.
      apply IHn with (t := T1); auto. simpl in H1. apply union_incl_1 with (t2 := T2). assumption.
      apply IHn with (t := (TUnion T1 T2)); assumption.
    SCase "s = TNum; t = TUnion: Right".
      inversion H1.
      assert ((type_size T2 <= n)%nat). rewrite <- H4. apply le_plus_r.
      apply IHn with (t := T2); auto. simpl in H1. apply union_incl_2 with (t1 := T1). assumption.
      apply IHn with (t := (TUnion T1 T2)); assumption.
    SCase "s = TUnion; t = TUnion: Left".
      inversion H1.
      assert ((type_size T1 <= n)%nat). rewrite <- H4. apply le_plus_l.
      apply IHn with (t := T1); auto. simpl in H1. apply union_incl_1 with (t2 := T2). assumption.
      apply IHn with (t := (TUnion T1 T2)); assumption.
    SCase "s = TUnion; t = TUnion: Right".
      inversion H1.
      assert ((type_size T2 <= n)%nat). rewrite <- H4. apply le_plus_r.
      apply IHn with (t := T2); auto. simpl in H1. apply union_incl_2 with (t1 := T1). assumption.
      apply IHn with (t := (TUnion T1 T2)); assumption.
    SCase "s = TUnion; t = t: Join".
      apply SUnionJoin. 
      apply IHs1 with (t := t); assumption.
      apply IHs2 with (t := t); assumption.
    SCase "s = TArrow; t = TUnion: Left".
      inversion H1.
      assert ((type_size T1 <= n)%nat). rewrite <- H4. apply le_plus_l.
      apply IHn with (t := T1); auto. simpl in H1. apply union_incl_1 with (t2 := T2). assumption.
      apply IHn with (t := (TUnion T1 T2)); assumption.
    SCase "s = TArrow; t = TUnion: Right".
      inversion H1.
      assert ((type_size T2 <= n)%nat). rewrite <- H4. apply le_plus_r.
      apply IHn with (t := T2); auto. simpl in H1. apply union_incl_2 with (t1 := T1). assumption.
      apply IHn with (t := (TUnion T1 T2)); assumption.
    SCase "s = TArrow; t = TArrow".
      remember (TArrow A2 W2 R2) as middle.
      induction H0; try solve [inversion H]; try solve [assumption]; try solve [inversion Heqmiddle].
      SSCase "u = TUnion: Left".
        apply SUnionL. apply IHsubtype; assumption.
      SSCase "u = TUnion: Right".
        apply SUnionR. apply IHsubtype; assumption.
      SSCase "u = TArrow".
        inversion Heqmiddle; subst.
        apply SArrow. 
        apply IHn with (t := A2); auto. simpl in H1. omega.
        apply IHn with (t := R2); auto. simpl in H1. omega.
        apply bcontains_list_trans with (l2 := W2); assumption.
Qed.

Ltac break_ands :=
  repeat match goal with
           [ H : _ /\ _ |- _ ] => inversion H; clear H
         end.

Lemma apply_subtype_res : forall targ1 W1 tres1 tfun targ2 W2 tres2,
  subtype (TArrow targ1 W1 tres1) tfun ->
  apply_t tfun targ2 W2 tres2 ->
  subtype tres1 tres2.
Proof.
Admitted.

Lemma apply_subtype_arg : forall targ1 W1 tres1 tfun targ2 W2 tres2,
  subtype (TArrow targ1 W1 tres1) tfun ->
  apply_t tfun targ2 W2 tres2 ->
  subtype targ2 targ1.
Proof.
Admitted.

Lemma apply_subtype_W : forall targ1 W1 tres1 tfun targ2 W2 tres2,
  subtype (TArrow targ1 W1 tres1) tfun ->
  apply_t tfun targ2 W2 tres2 ->
  bcontains_list_w W1 W2 = true.
Proof.
Admitted.


Lemma apply_subtype : forall targ1 W1 tres1 tfun targ2 W2 tres2,
  subtype (TArrow targ1 W1 tres1) tfun ->
  apply_t tfun targ2 W2 tres2 ->
  (subtype tres1 tres2) /\ (subtype targ2 targ1) /\ (bcontains_list_w W1 W2 = true).
Proof.
Admitted.



Lemma subst_type : forall e x v G T W1 W2 Tx,
  has_type W1 (extend G x Tx) e T ->
  aval v ->
  G x = Some Tx ->
  bcontains_list_w W1 W2 = true ->
  has_type W2 G v Tx ->
  has_type W2 G (e_subst x v e) T.
Proof.
Admitted.

Theorem preservation : forall e e' W T,
     has_type W empty e T  ->
     step e e'  ->
     has_type W empty e' T.
Proof.
  intros.
  generalize dependent e'.
  induction H; intros.
  Case "HTVar".
  inversion H0.
    SCase "Decomp".
      subst. inversion H1. subst. inversion H3.
    SCase "Err". inversion H1.
  Case "HTLam".
  inversion H0.
    SCase "Decomp".
      subst. inversion H1. subst. inversion H3.
    SCase "Err". inversion H1.
  Case "HTZero".
  inversion H0.
    SCase "Decomp".
      subst. inversion H1. inversion H3.
    SCase "Err". inversion H1.
  Case "HTNum".
  inversion H0.
    SCase "Decomp".
      subst. inversion H1. inversion H3.
    SCase "Err". inversion H1.
  Case "HTErr".
  inversion H0; subst.
    SCase "Decomp".
    inversion H1. subst. inversion H3.
    SCase "Err".
    apply HTErr. inversion H1. subst. apply H.
  Case "HTApp".
   inversion H2; subst.
    SCase "Decomp".
     inversion H3; subst; simpl in *.
     SSCase "Active".
        inversion H4; subst.
        SSSCase "EApp".
          apply subst_type with (W1 := ws) (Tx := typ0).
          
          remember (ELam x typ0 ws eb) as elam.
          induction H; subst; try solve [inversion Heqelam]; subst.
            SSSSCase "HTLam".
              apply HTSub with (s := tres). inversion Heqelam. subst. assumption.
              assert (subtype (TArrow targ W2 tres) (TArrow targ W2 tres)).
              apply SRefl.
              assert (foo := apply_subtype targ W2 tres (TArrow targ W2 tres) t2 W0 t H6 H1).
              break_ands. assumption.
            SSSSCase "HTSub".
              apply IHhas_type; try solve [assumption].
              
apply_subtype
     : forall (targ1 : typ) (W1 : list w) (tres1 tfun targ2 : typ)
         (W2 : list w) (tres2 : typ),
       subtype (TArrow targ1 W1 tres1) tfun ->
       apply_t tfun targ2 W2 tres2 ->
       subtype tres1 tres2 /\
       subtype targ2 targ1 /\ bcontains_list_w W1 W2 = true

        SSSCase "AppN".
          admit.
        SSSCase "App0".
          admit.
     SSCase "EApp Fun".
       admit.
     SSCase "EApp Arg".
       admit.
   SCase "Error".
      apply HTErr.
      apply typing_used_w with (G := Gamma)
                               (E := E)
                               (e := EApp e1 e2)
                               (T := t).
      apply HTApp with (t1 := t1) (t2 := t2); assumption. assumption.
  Case "HTPrim".
  inversion H1; subst.
    SCase "Decomp".
    inversion H2; subst.
    SSCase "Active". inversion H4. subst.
    inversion H3. subst.
    inversion H10; subst. 
      SSSCase "Div0".
      inversion H; subst.
        SSSSCase "Zero : TZero". 
        inversion H0; subst.
          SSSSSCase "Div0 : TBot".
          simpl.
          apply HTErr. assumption.
          SSSSSCase "DivLam : TBot".
          discriminate.
        SSSSCase "Num : TZero". contradiction.
        SSSSCase "Num : s <= t". simpl in *.
        induction H7; subst; try solve [inversion H10].
          SSSSSCase "HTZero". apply HTErr. apply delta_inv_div_0 with (t1 := t1) (t := t); assumption.
          SSSSSCase "HTNum". inversion H10. contradiction.
          SSSSSCase "HTSub". apply IHhas_type0; try solve [assumption].
            apply subtype_transitive with (t := t0); assumption.
      SSSCase "DivN".
        inversion H; subst.
        SSSSCase "Zero : TNum". contradiction.
        SSSSCase "Num : TNum".
          inversion H0; subst.
          SSSSSCase "DivNum : TNum".
          simpl. apply HTNum. apply inv_zeronon. assumption.
          SSSSSCase "DivLam : TBot". inversion H9.
          SSSSCase "Num : s <= t". simpl in *.
            induction H7; subst; try solve [inversion H10].
            SSSSSCase "Zero is not non-zero". inversion H10. contradiction.
            SSSSSCase "Num". apply HTSub with (s := TNum).
              SSSSSSCase "Numbers are numbers". apply HTNum. apply inv_zeronon. assumption.
              SSSSSSCase "delta/subtyping commute".
                apply delta_subtype with (t1 := TNum) (t2 := t1) (c := div) (W := W0).
                assumption. apply dt_divN. assumption.
            SSSSSCase "HTSub". apply IHhas_type0; try solve [assumption].
            apply subtype_transitive with (t := t0); assumption.
      SSSCase "DivLam".
        inversion H; subst.
        inversion H0. subst. simpl. apply HTErr. assumption.
        SSSSCase "Num : s <= t". simpl in *.
        induction H5; subst; try solve [inversion H10].
          SSSSSCase "HTLam". apply HTErr.
            apply delta_inv_div_lam with (s := targ) (W' := W2) (u := tres) (t1 := t1) (t := t); assumption.
          SSSSSCase "HTSub". apply IHhas_type0; try solve [assumption].
            apply subtype_transitive with (t := t0); assumption.
      SSSCase "AddNumOrZero".
        inversion H; subst.
        SSSSCase "Zero : TZero".
          simpl.
          inversion H0; subst.
          SSSSSCase "0 + 1 is a number".
          apply HTNum. rewrite H11. rewrite Qplus_0_l. unfold not. intros. inversion H5.
          SSSSSCase "Zero is not a lambda". inversion H7.
        SSSSCase "Num : TNum".
          simpl.
          inversion H0; subst.
          SSSSSCase "n + 1 is zero or a number".
            destruct (n + 1).
              destruct Qnum.
                apply HTSub with (s := TZero). constructor. simpl_relation. (* TODO(joe): lookup/remember this *)
                apply SUnionR. apply SRefl.
                apply HTSub with (s := TNum). constructor. simpl_relation.
                apply SUnionL. apply SRefl.
                apply HTSub with (s := TNum). constructor. simpl_relation.
                apply SUnionL. apply SRefl.
          SSSSSCase "Numbers are not lambdas". inversion H7.
        SSSSCase "Num : s <= t"; simpl in *.
          remember (ENum n) as e_n.
          induction H5; inversion Heqe_n; subst; try solve [inversion H10].
          SSSSSCase "Zero".
            apply HTSub with (s := TNum). apply HTNum. rewrite H5. rewrite Qplus_0_l. simpl_relation.
            apply delta_subtype with (t1 := TZero) (t2 := t1) (c := add) (W := W0); auto. constructor.
          SSSSSCase "Num". 
            apply HTSub with (s := (TUnion TNum TZero)).
            destruct (Qeq_dec n (Qmake (-1) 1)).
              apply HTSub with (s := TZero). apply HTZero. rewrite q. simpl_relation. apply SUnionR. apply SRefl.
              apply HTSub with (s := TNum). apply HTNum. simpl_relation. apply n0. rewrite <- Qplus_inj_r. rewrite H9.  simpl_relation.
              apply SUnionL. apply SRefl.
              apply delta_subtype with (t1 := TNum) (t2 := t1) (c := add) (W := W0); auto. constructor.
          SSSSSCase "Inductive". apply IHhas_type0; try auto. apply subtype_transitive with (t := t0); auto.
      SSSCase "AddLambda".
        inversion H; subst.
        inversion H0. subst. simpl. apply HTErr. assumption.
        SSSSCase "Num : s <= t". simpl in *. admit. (* Need a stupid lemma (see todo.txt) *)
    SSCase "NonActive".
      simpl in *.
      assert (step e (e_plug EC ae')).
      apply StepCxt with (E := EC)
                         (ae := ae)
                         (ae' := ae').
      assumption. assumption. reflexivity.
      apply IHhas_type in H4.
      apply HTPrim with (t1 := t1). assumption. assumption.
    SSCase "Error".
      apply HTErr.
      apply typing_used_w with (G := Gamma)
                               (E := E)
                               (e := EPrim c0 e)
                               (T := t).
      apply HTPrim with (t1 := t1); assumption. assumption.
  Case "Subtype".
   apply IHhas_type in H1. apply HTSub with (s := s); assumption.
Qed.      
      
