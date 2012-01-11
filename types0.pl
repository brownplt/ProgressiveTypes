
isType(nzInt).
isType(nzniFlt).
isType(zero).
isType(union(S,T)) :- isType(S), isType(T).
isType(arrow(S,T)) :- isType(S), isType(T).

allowed(T) :- isType(T).
allowed(erriplusrightfloat).
allowed(erriplusleftfloat).

type(_, nzIntConst, nzInt).
type(_, nzFltConst, nzniFlt).
type(_, zeroConst, zero).
type(TEnv, if(Test, Then, Else), Tau) :-
  type(TEnv,Test,int),
  type(TEnv,Then,Tau),
  type(TEnv,Else,Tau).

type([bind(V,T)|_], var(V), T).
type([bind(_,_)|TEnvRest], var(V), T) :-
  type(TEnvRest, var(V), T).

type(TEnv, fun(Arg, Body), arrow(T1, T2)) :-
  type([bind(Arg, T1)|TEnv], Body, T2).

type(TEnv, app(Fun, Arg), T2) :-
  type(TEnv, Fun, arrow(T1, T2)),
  type(TEnv, Arg, T1).

type(TEnv, op(Op, E1, E2), T) :-
  type(TEnv, E1, T1),
  type(TEnv, E2, T2),
  delta(Op, T1, T2, T),
  allowed(T).

% No subsumption for now.  It causes some issues with
% inferring crazy unbounded unions.
%type(TEnv, Expr, T) :-
%  type(TEnv, Expr, S),
%  subtype(S, T).

%canonical(T, union(U, T)) :- subtype(canonical(U, T).
%canonical(U, union(U, T)) :- subtype(T, U).
%canonical(S, union(U, T)) :-
  
canonical(arrow(S1, T1), arrow(S2, T2)) :-
  canonical(S1, S2), canonical(T1, T2).

subtype(T, T).
subtype(T, union(S, U)) :- (subtype(T, S); subtype(T, U)).
subtype(union(S, T), U) :- (subtype(S, U), subtype(T, U)).
subtype(arrow(S1, T1), arrow(S2, T2)) :-
  (subtype(S2, S1), subtype(T1, T2)).

% Delta distributes over unions using subtyping
delta(Op, union(S1, S2), T2, union(TS1, TS2)) :-
  delta(Op, S1, T2, TS1),
  delta(Op, S2, T2, TS2).

delta(Op, T2, union(S1, S2), union(TS1, TS2)) :-
  delta(Op, T2, S1, TS1),
  delta(Op, T2, S2, TS2).

delta(plus, zero, zero, zero).
delta(plus, zero, nzniFlt, nzniFlt).
delta(plus, zero, nzInt, nzInt).
delta(plus, nzniFlt, zero, nzniFlt).
delta(plus, nzniFlt, nzniFlt, union(nzInt, nzFloat)).
delta(plus, nzniFlt, nzInt, nzniFlt).
delta(plus, nzInt, zero, nzInt).
delta(plus, nzInt, nzniFlt, nzniFlt).
delta(plus, nzInt, nzInt, nzInt).

delta(plus, arrow(_, _), _, errPlusLambdaLeft).
delta(plus, T, arrow(_, _), errPlusLambdaRight) :-
  subtype(T, union(nzInt, nzniFlt, zero)).

delta(iplus, zero, zero, zero).
delta(iplus, zero, nzniFlt, errIPlusRightFloatWithZeroLeft).
delta(iplus, zero, nzInt, nzInt).
delta(iplus, nzniFlt, zero, errIPlusLeftFloatWithZeroRight).
delta(iplus, nzniFlt, nzniFlt, errIPlusBothFloat).
delta(iplus, nzniFlt, nzInt, errIPlusLeftFloatWithIntright).
delta(iplus, nzInt, zero, nzInt).
delta(iplus, nzInt, nzniFlt, errIPlusRightFloatWithIntLeft).
delta(iplus, nzInt, nzInt, nzInt).

delta(iplus, arrow(_, _), _, errIPlusLambdaLeft).
delta(iplus, T, arrow(_, _), errIPlusLambdaRight) :-
  subtype(T, union(nzInt, zero).

delta(div, zero, zero, errDivByZeroWithZeroNumerator).
delta(div, zero, nzniFlt, zero).
delta(div, zero, nzInt, zero).
delta(div, nzniFlt, zero, errDivByZeroWithFloatNumerator).
delta(div, nzniFlt, nzniFlt, union(nzInt, nzniFlt)).
delta(div, nzniFlt, nzInt, nzniFlt).
delta(div, nzInt, zero, errDivByZeroWithFloatNumerator).
delta(div, nzInt, nzniFlt, union(nzniFlt, nzInt)).
delta(div, nzInt, nzInt, union(nzniFlt, nzInt)).

delta(div, arrow(_, _), _, errIPlusLambdaLeft).
delta(div, T, arrow(_, _), errIPlusLambdaRight) :-
  subtype(T, union(nzInt, nzniFlt, zero).


