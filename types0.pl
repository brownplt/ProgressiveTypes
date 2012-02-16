:- module(types0, [
  type/4
]).

isType(nzInt).
isType(nzniFlt).
isType(zero).
isType(union(S,T)) :- isType(S), isType(T).
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

type(_, [bind(V,T)|_], var(V), T).
type(Ω, [bind(_,_)|Γ], var(V), T) :-
  type(Ω, Γ, var(V), T).

type(Ω, Γ, λ(X, S, Body), arrow(S, T)) :-
  type(Ω, [bind(X, S)|Γ], Body, T).

type(Ω, Γ, app(Fun, Arg), T2) :-
  type(Ω, Γ, Fun, arrow(T1, T2)),
  type(Ω, Γ, Arg, T1).

type(Ω, Γ, op(Op, E1, E2), T) :-
  type(Ω, Γ, E1, T1),
  type(Ω, Γ, E2, T2),
  delta(Op, T1, T2, Ω, T).

wftype(T) :- safe_canonical(T,T).

safe_canonical(S, T) :- canonical(S,T).
%  call_with_depth_limit(canonical(S, T), 3, R),
%  not(=(R, depth_limit_exceeded)).

canonical(nzInt, nzInt).
canonical(nzniFlt, nzniFlt).
canonical(zero, zero).

canonical(union(S1, T1), union(S2, T2)) :-
  canonical(S1, S2), canonical(T1, T2),
  not(subtype(S1, T1)), not(subtype(T1, S1)).

canonical(Tc, union(S, T)) :- 
  canonical(Sc, S),
  canonical(Tc, T),
  subtype(Sc, Tc).

canonical(Sc, union(S, T)) :- 
  canonical(Sc, S),
  canonical(Tc, T),
  subtype(Tc, Sc).

canonical(arrow(S1, T1), arrow(S2, T2)) :-
  canonical(S1, S2), canonical(T1, T2).

subtype(T, T).
subtype(T, union(S, U)) :- (subtype(T, S); subtype(T, U)).
subtype(union(S, T), U) :- (subtype(S, U), subtype(T, U)).
subtype(arrow(S1, T1), arrow(S2, T2)) :-
  (subtype(S2, S1), subtype(T1, T2)).

% Delta distributes over unions
delta(Op, union(S1, S2), T2, Ω, union(TS1, TS2)) :-
  delta(Op, S1, T2, Ω, TS1),
  delta(Op, S2, T2, Ω, TS2).

delta(Op, T2, union(S1, S2), Ω, union(TS1, TS2)) :-
  delta(Op, T2, S1, Ω, TS1),
  delta(Op, T2, S2, Ω, TS2).

delta(_, ⊥ , _, _, ⊥ ).
delta(_, _, ⊥ , _, ⊥ ).

delta(plus, zero, zero, _, zero).
delta(plus, zero, nzniFlt, _, nzniFlt).
delta(plus, zero, nzInt, _, nzInt).
delta(plus, nzniFlt, zero, _, nzniFlt).
delta(plus, nzniFlt, nzniFlt, _, union(nzInt, nzFloat)).
delta(plus, nzniFlt, nzInt, _, nzniFlt).
delta(plus, nzInt, zero, _, nzInt).
delta(plus, nzInt, nzniFlt, _, nzniFlt).
delta(plus, nzInt, nzInt, _, nzInt).

delta(plus, arrow(_, _), _, Ω, ⊥ ) :-
  member(errPlusLambdaLeft, Ω).
delta(plus, T, arrow(_, _), Ω, ⊥ ) :-
  member(errPlusLambdaRight, Ω),
  subtype(T, union(nzInt, nzniFlt, zero)).

delta(iplus, zero, zero, _, zero).
delta(iplus, zero, nzniFlt, Ω, ⊥ ) :-
  member(errIPlusRightFloatWithZeroLeft, Ω).
delta(iplus, zero, nzInt, _, nzInt).
delta(iplus, nzniFlt, zero, Ω, ⊥ ) :-
  member(errIPlusLeftFloatWithZeroRight, Ω).
delta(iplus, nzniFlt, nzniFlt, Ω, ⊥ ) :-
  member(errIPlusBothFloat, Ω).
delta(iplus, nzniFlt, nzInt, Ω, ⊥ ) :-
  member(errIPlusLeftFloatWithIntright, Ω).
delta(iplus, nzInt, zero, _, nzInt).
delta(iplus, nzInt, nzniFlt, Ω, ⊥ ) :-
  member(errIPlusRightFloatWithIntLeft, Ω).
delta(iplus, nzInt, nzInt, _, nzInt).

delta(iplus, arrow(_, _), _, Ω, errIPlusLambdaLeft) :-
  member(errIPlusLambdaLeft, Ω).
delta(iplus, T, arrow(_, _), Ω, errIPlusLambdaRight) :-
  member(errIPlusLambdaRight, Ω),
  subtype(T, union(nzInt, zero)).

delta(div, zero, zero, Ω, ⊥ ) :-
  member(errDivByZeroWithZeroNumerator, Ω).
delta(div, zero, nzniFlt, _, zero).
delta(div, zero, nzInt, _, zero).
delta(div, nzniFlt, zero, Ω, ⊥ ) :-
  member(errDivByZeroWithFloatNumerator, Ω).
delta(div, nzniFlt, nzniFlt, _, union(nzInt, nzniFlt)).
delta(div, nzniFlt, nzInt, _, nzniFlt).
delta(div, nzInt, zero, Ω, ⊥ ) :-
  member(errDivByZeroWithIntNumerator, Ω).
delta(div, nzInt, nzniFlt, _, union(nzniFlt, nzInt)).
delta(div, nzInt, nzInt, _, union(nzniFlt, nzInt)).

delta(div, arrow(_, _), _, errIPlusLambdaLeft).
delta(div, T, arrow(_, _), errIPlusLambdaRight) :-
  subtype(T, union(nzInt, nzniFlt, zero)).


