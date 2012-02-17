:- module(types0, [
  type/4,
  subtype/2
]).

isType(nzInt).
isType(nzniFlt).
isType(zero).
isType(∪(S,T)) :- isType(S), isType(T).
isType(arrow(S,T)) :- isType(S), isType(T).

type(_, _, nzIntConst, nzInt).
type(_, _, nzFltConst, nzniFlt).
type(_, _, zeroConst, zero).
type(Ω, Γ, if(Test, Then, Else), Tau) :-
  type(Ω, Γ, Test, nzInt),
  type(Ω, Γ, Then, Tau),
  type(Ω, Γ, Else, Tau).

type(Ω, Env, subsume(E, T), T) :-
  type(Ω, Env, E, S),
  subtype(S, T).

type(_ , [bind(V,T)|_ ], var(V), T).
type(Ω, [bind(_,_)|Γ], var(V), T) :-
  type(Ω, Γ, var(V), T).

type(Ω, Γ, λ(X, S, Body), arrow(S, T)) :-
  type(Ω, [bind(X, S)|Γ], Body, T).

type(Ω, Γ, app(Fun, Arg), TR) :-
  type(Ω, Γ, Fun, TF),
  type(Ω, Γ, Arg, TA),
  apply(TF, TA, Ω, TR).

type(Ω, Γ, op(Op, E1, E2), T) :-
  type(Ω, Γ, E1, T1),
  type(Ω, Γ, E2, T2),
  δ(Op, T1, T2, Ω, T).

notBottom(zero).
notBottom(nzInt).
notBottom(nzniFlt).
notBottom(∪(S, _)) :- notBottom(S).
notBottom(∪(_, T)) :- notBottom(T).
notBottom(arrow(_, _)).

apply(⊥,_,_,⊥).
apply(_,⊥,_,⊥).

apply(∪(S, T), U, Ω, ∪(SR, TR)) :-
  apply(S, U, Ω, SR), apply(T, U, Ω, TR).

% We are careful to only accept non-⊥ args here. It is interesting that
% we can enumerate these...  If we did not have explicit subsumption,
% this could be significantly more complicated.
apply(arrow(T, S), T, _, S) :- notBottom(T).

apply(zero, T, Ω, ⊥) :- notBottom(T), member(errBadApp, Ω).
apply(nzInt, T, Ω, ⊥) :- notBottom(T), member(errBadApp, Ω).
apply(nzniFlt, T, Ω, ⊥) :- notBottom(T), member(errBadApp, Ω).

wftype(T) :- safe_canonical(T,T).

safe_canonical(S, T) :- canonical(S,T).
%  call_with_depth_limit(canonical(S, T), 3, R),
%  not(=(R, depth_limit_exceeded)).

canonical(nzInt, nzInt).
canonical(nzniFlt, nzniFlt).
canonical(zero, zero).

canonical(∪(S1, T1), ∪(S2, T2)) :-
  canonical(S1, S2), canonical(T1, T2),
  not(subtype(S1, T1)), not(subtype(T1, S1)).

canonical(Tc, ∪(S, T)) :- 
  canonical(Sc, S),
  canonical(Tc, T),
  subtype(Sc, Tc).

canonical(Sc, ∪(S, T)) :- 
  canonical(Sc, S),
  canonical(Tc, T),
  subtype(Tc, Sc).

canonical(arrow(S1, T1), arrow(S2, T2)) :-
  canonical(S1, S2), canonical(T1, T2).

subtype(T, T).
subtype(⊥, _).
subtype(T, ∪(S, _)) :- subtype(T, S).
subtype(T, ∪(_, U)) :- subtype(T, U).
subtype(∪(S, T), U) :- (subtype(S, U), subtype(T, U)).
subtype(arrow(S1, T1), arrow(S2, T2)) :-
  (subtype(S2, S1), subtype(T1, T2)).

% Delta distributes over ∪
δ(Op, ∪(S1, S2), T2, Ω, ∪(TS1, TS2)) :-
  δ(Op, S1, T2, Ω, TS1),
  δ(Op, S2, T2, Ω, TS2).

δ(Op, T2, ∪(S1, S2), Ω, ∪(TS1, TS2)) :-
  δ(Op, T2, S1, Ω, TS1),
  δ(Op, T2, S2, Ω, TS2).

δ(_, ⊥, _, _, ⊥).
δ(_, _, ⊥, _, ⊥).

δ(plus, zero, zero, _, zero).
δ(plus, zero, nzniFlt, _, nzniFlt).
δ(plus, zero, nzInt, _, nzInt).
δ(plus, nzniFlt, zero, _, nzniFlt).
δ(plus, nzniFlt, nzniFlt, _, ∪(nzInt, nzFloat)).
δ(plus, nzniFlt, nzInt, _, nzniFlt).
δ(plus, nzInt, zero, _, nzInt).
δ(plus, nzInt, nzniFlt, _, nzniFlt).
δ(plus, nzInt, nzInt, _, nzInt).

δ(plus, arrow(_, _), _, Ω, ⊥ ) :-
  member(errPlusLambdaLeft, Ω).
δ(plus, T, arrow(_, _), Ω, ⊥ ) :-
  member(errPlusLambdaRight, Ω),
  subtype(T, ∪(nzInt, nzniFlt, zero)).

δ(iplus, zero, zero, _, zero).
δ(iplus, zero, nzniFlt, Ω, ⊥) :-
  member(errIPlusRightFloatWithZeroLeft, Ω).
δ(iplus, zero, nzInt, _, nzInt).
δ(iplus, nzniFlt, zero, Ω, ⊥) :-
  member(errIPlusLeftFloatWithZeroRight, Ω).
δ(iplus, nzniFlt, nzniFlt, Ω, ⊥) :-
  member(errIPlusBothFloat, Ω).
δ(iplus, nzniFlt, nzInt, Ω, ⊥) :-
  member(errIPlusLeftFloatWithIntright, Ω).
δ(iplus, nzInt, zero, _, nzInt).
δ(iplus, nzInt, nzniFlt, Ω, ⊥) :-
  member(errIPlusRightFloatWithIntLeft, Ω).
δ(iplus, nzInt, nzInt, _, nzInt).

δ(iplus, arrow(_, _), _, Ω, errIPlusLambdaLeft) :-
  member(errIPlusLambdaLeft, Ω).
δ(iplus, T, arrow(_, _), Ω, errIPlusLambdaRight) :-
  member(errIPlusLambdaRight, Ω),
  subtype(T, ∪(nzInt, zero)).

δ(div, zero, zero, Ω, ⊥) :-
  member(errDivByZeroWithZeroNumerator, Ω).
δ(div, zero, nzniFlt, _, zero).
δ(div, zero, nzInt, _, zero).
δ(div, nzniFlt, zero, Ω, ⊥) :-
  member(errDivByZeroWithFloatNumerator, Ω).
δ(div, nzniFlt, nzniFlt, _, ∪(nzInt, nzniFlt)).
δ(div, nzniFlt, nzInt, _, nzniFlt).
δ(div, nzInt, zero, Ω, ⊥) :-
  member(errDivByZeroWithIntNumerator, Ω).
δ(div, nzInt, nzniFlt, _, ∪(nzniFlt, nzInt)).
δ(div, nzInt, nzInt, _, ∪(nzniFlt, nzInt)).

δ(div, arrow(_, _), _, errIPlusLambdaLeft).
δ(div, T, arrow(_, _), errIPlusLambdaRight) :-
  subtype(T, ∪(nzInt, ∪(nzniFlt, zero))).

