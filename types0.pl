:- module(types0, [
  type/4,
  subtype/2,
  typ_subst/4,
  typ_equal/2
]).

isType(nzInt).
isType(nzniFlt).
isType(zero).
isType(∪(S,T)) :- isType(S), isType(T).
isType(arrow(S,T)) :- isType(S), isType(T).
isType(μ(_,T)) :- isType(T).
isType(tvar(_)).

type(_, _, nzIntConst, nzInt).
type(_, _, nzFltConst, nzniFlt).
type(_, _, zeroConst, zero).

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

% typ_subst :: X: identifier, S: type, T: type, U: type
% Substitutes instances of tvar(X) for S in T, outputs on U
% *Only* ground terms should be used for type variables.  The use of not
% makes it dangerous to abstract over them with logic variables.  E.g.,
% consider:
%
% typ_subst(X, zero, μ(Y, tvar(X)), ???)
%
% If X and Y are unified, then the substitution won't happen.  If they
% get unified to different values, it will.
typ_subst(_, _, zero, zero).
typ_subst(_, _, nzInt, nzInt).
typ_subst(_, _, nzniFlt, nzniFlt).
typ_subst(X, S, tvar(X), S).
typ_subst(X, _, tvar(Y), tvar(Y)) :- not(X = Y).
typ_subst(X, S, ∪(T1, T2), ∪(U1, U2)) :-
  typ_subst(X, S, T1, U1), typ_subst(X, S, T2, U2).
typ_subst(X, S, arrow(T1, T2), arrow(U1, U2)) :-
  typ_subst(X, S, T1, U1), typ_subst(X, S, T2, U2).
typ_subst(X, S, μ(Y, T), μ(Y, U)) :-
  not(X = Y), typ_subst(X, S, T, U). 
typ_subst(X, _, μ(X, T), μ(X, T)). % Variable is shadowed

% typ_equal :: S: type, T: type 
% Checks equality, correctly handling binding of μ-types.  Note that in
% the case of μ, we don't check that the variables are non-equal before
% recurring with substitution.  This is quite non-deterministic, and can
% find several ways to determine that two types are equal.
typ_equal(T, T).
typ_equal(μ(X, S), μ(X, T)) :- typ_equal(S, T).
typ_equal(μ(X, S), μ(Y, T)) :-
  typ_subst(X, tvar(Y), S, S2),
  typ_equal(S2, T).
typ_equal(arrow(S1, T1), arrow(S2, T2)) :-
  typ_equal(S1, S2), typ_equal(T1, T2).
typ_equal(∪(S1, T1), ∪(S2, T2)) :-
  typ_equal(S1, S2), typ_equal(T1, T2).


subtype(T, S) :- rec_subtype([], T, S).

rec_subtype(_, S, T) :- typ_equal(S, T).
rec_subtype(_, ⊥, _).
rec_subtype(Cache, S, T) :-
  member(seen_it(S, T), Cache).

rec_subtype(Cache, μ(X, S), T) :-
  typ_subst(x, μ(X, S), S, S2),
  rec_subtype([seen_it(μ(X, S), T)|Cache], S2, T).
rec_subtype(Cache, S, μ(X, T)) :-
  typ_subst(X, μ(X, T), T, T2),
  rec_subtype([seen_it(S, μ(X, T))|Cache], S, T2).

rec_subtype(Cache, T, ∪(S, U)) :-
  rec_subtype([seen_it(T, ∪(S, U))|Cache], T, S).
rec_subtype(Cache, T, ∪(S, U)) :-
  rec_subtype([seen_it(T, ∪(S, U))|Cache], T, U).
rec_subtype(Cache, ∪(S, T), U) :- 
  NewCache = [seen_it(∪(S, T), U)|Cache],
  rec_subtype(NewCache, S, U), rec_subtype(NewCache, T, U).

rec_subtype(Cache, arrow(S1, T1), arrow(S2, T2)) :-
  NewCache = [seen_it(arrow(S1, T1), arrow(S2, T2))|Cache],
  rec_subtype(NewCache, S2, S1), rec_subtype(NewCache, T1, T2).

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

