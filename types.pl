
isType(int).
isType(flt).
isType(union(S,T)) :- isType(S), isType(T).
isType(arrow(S,T)) :- isType(S), isType(T).

allowed(T) :- isType(T).
allowed(erriplusrightfloat).
allowed(erriplusleftfloat).

type(_, intConst, int).
type(_, fltConst, flt).
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

subtype(T, T).
subtype(T, union(S, U)) :- (subtype(T, S); subtype(T, U)).
subtype(union(S, T), U) :- (subtype(S, U), subtype(T, U)).
subtype(arrow(S1, T1), arrow(S2, T2)) :-
  (subtype(S2, S1), subtype(T1, T2)).

% Delta distributes over unions using subtyping
delta(Op, union(S1, S2), T2, TResult) :-
  delta(Op, S1, T2, TS1),
  delta(Op, S2, T2, TS2),
  subtype(TS1, TResult),
  subtype(TS2, TResult).

%TODO: division

delta(plus, flt, flt, flt).
delta(plus, int, flt, flt).
delta(plus, flt, int, flt).
delta(plus, int, int, int).
delta(plus, arrow(_, _), _, errlambdaleftplus).
delta(plus, T, arrow(_, _), errlambdarightplus) :-
  subtype(T, union(int, flt)).

delta(iplus, int, int, int).
delta(iplus, int, flt, erriplusrightfloat).
delta(iplus, flt, _, erriplusleftfloat).
delta(iplus, arrow(_, _), _, errlambdaleftiplus).
delta(iplus, int, arrow(_, _), errlambdarightiplus).

