:- begin_tests(types0).
:- use_module('types0', except([])).

test(divZero, [nondet]) :-
  type([errDivByZeroWithIntNumerator], [], op(div, nzIntConst, zeroConst), ⊥ ).

test(divZero, [fail]) :-
  type([], [], op(div, nzIntConst, zeroConst), ⊥ ).

test(divInt, [nondet]) :-
  type([], [], op(div, nzIntConst, nzIntConst), ∪(nzniFlt, nzInt)).

test(divFlt, [nondet]) :-
  type([], [], op(div, nzIntConst, nzFltConst), ∪(nzniFlt, nzInt)).

test(divZeroTop, [nondet]) :-
  type([], [], op(div, zeroConst, nzIntConst), zero).

test(iplusIZ, [nondet]) :-
  type([], [], op(iplus, nzIntConst, zeroConst), nzInt).

test(plusIZ, [nondet]) :-
  type([], [], op(plus, nzIntConst, zeroConst), nzInt).

test(plusFZ, [nondet]) :-
  type([], [], op(plus, nzFltConst, zeroConst), nzniFlt).

test(plusZI, [nondet]) :-
  type([], [], op(iplus, zeroConst, nzIntConst), nzInt).

test(funDivIX, [nondet]) :-
  type([], [], λ(x, ∪(nzInt, nzniFlt), op(div, nzIntConst, var(x))), 
       arrow(∪(nzInt, nzniFlt),
             ∪(∪(nzniFlt, nzInt),
                   ∪(nzniFlt, nzInt)))).

test(funDiv0X, [nondet]) :-
  type([
    errDivByZeroWithIntNumerator,
    errDivByZeroWithFloatNumerator
  ], [], λ(x, ∪(nzInt, nzniFlt), op(div, var(x), zeroConst)),
  arrow(∪(nzInt, nzniFlt), ∪(⊥ , ⊥ ))).

test(plusBot, [nondet]) :-
  type(
    [errDivByZeroWithIntNumerator],
    [],
    op(plus, op(div, nzIntConst, zeroConst), zeroConst),
    ⊥
  ).

% Simple union subsumption
test(sub1, [nondet]) :-
  type([], [],
    subsume(nzIntConst, ∪(nzInt, zero)), ∪(nzInt, zero)
  ).

% Bottom should subsume to unions of arrows and other things
test(sub2, [nondet]) :-
  type([errDivByZeroWithZeroNumerator], [],
    subsume(
      op(div, zeroConst, zeroConst),
      ∪(arrow(nzInt, zero), nzniFlt)
    ),
    ∪(arrow(nzInt, zero), nzniFlt)
  ).

% Shouldn't be able to subsume to bottom, even including a bottom
test(sub3, [fail]) :-
  type([errDivByZeroWithZeroNumerator], [bind(x, ∪(nzInt, zero))],
    subsume(
      op(div, zeroConst, var(x)),
      ⊥
    ),
    _
  ).

% Subtyping unions shouldn't care about order
test(sub4, [nondet]) :-
  subtype(∪(nzInt, nzniFlt), ∪(nzniFlt, nzInt)).

test(sub5, [nondet]) :-
  subtype(∪(⊥,⊥), ⊥).

test(apply, [nondet]) :-
  type(
    [], [],
    λ(f, arrow(∪(zero, ∪(nzInt, nzniFlt)), ∪(nzInt, nzniFlt)),
      λ(x, ∪(zero, ∪(nzInt, nzniFlt)), app(var(f), var(x)))),
    arrow(arrow(∪(zero, ∪(nzInt, nzniFlt)), ∪(nzInt, nzniFlt)),
          arrow(∪(zero, ∪(nzInt, nzniFlt)), ∪(nzInt, nzniFlt)))
  ).

test(badapp, [fail]) :-
  type([], [], app(nzIntConst, zeroConst), _).

test(badappallowed, [nondet]) :-
  type([errBadApp], [], app(nzIntConst, zeroConst), ⊥).

test(badappallowedtyp, [nondet]) :-
  type(
    [errBadApp],
    [bind(f, ∪(arrow(zero, zero), nzInt))],
    app(var(f), zeroConst),
    ∪(zero, ⊥)
  ).

test(badappunion, [fail]) :-
  type(
    [],
    [bind(f, ∪(arrow(zero, zero), nzInt))],
    app(var(f), zeroConst),
    _
  ).

test(appfunion, all(X == [∪(zero, nzInt)])) :-
  type(
    [],
    [bind(f, ∪(arrow(zero, zero), arrow(zero, nzInt)))],
    app(var(f), zeroConst),
    X
  ).

test(tsubst1, all(X == [nzInt])) :-
  typ_subst(x, nzInt, tvar(x), X).

test(tsubst2, all(X == [∪(nzInt, zero)])) :-
  typ_subst(x, nzInt, ∪(tvar(x), zero), X).

test(tsubst3, all(X == [μ(x, tvar(x))])) :-
  typ_subst(x, zero, μ(x, tvar(x)), X).

test(tsubst4, all(X == [μ(y, zero)])) :-
  typ_subst(x, zero, μ(y, tvar(x)), X).

test(tsubst5, all(X == [tvar(y)])) :-
  typ_subst(x, zero, tvar(y), X).

test(tsubst6, all(X == [μ(y, μ(z, zero))])) :-
  typ_subst(x, zero, μ(y, μ(z, tvar(x))), X).

test(tsubst7, all(X == [zero])) :-
  typ_subst(x, _, zero, X).

test(tsubst8, all(X == [arrow(μ(y, zero), nzInt)])) :-
  typ_subst(x, zero, arrow(μ(y, tvar(x)), nzInt), X).


test(tequal1, set(X == [∪(tvar(x), nzInt)])) :-
  typ_equal(μ(y, ∪(tvar(y), nzInt)), μ(x, X)).

test(tequal_union, set(X == [∪(tvar(x), nzInt)])) :-
  typ_equal(∪(tvar(x), nzInt), X).

test(tequal_simpl_union, set(X == [∪(zero, nzInt)])) :-
  typ_equal(∪(zero, nzInt), X).

test(tequal2, [fail]) :-
  typ_equal(tvar(x), tvar(y)).

test(tequal3, [fail]) :-
  typ_equal(μ(x, μ(y, ∪(zero, tvar(x)))),
            μ(x, μ(y, ∪(zero, tvar(y))))).

test(tequal3, set(X == [∪(tvar(x), tvar(y))])) :-
  typ_equal(μ(x, μ(y, ∪(tvar(x), tvar(y)))),
            μ(x, μ(y, X))).

test(μ1, [nondet]) :-
  subtype(
    μ(x, ∪(tvar(x), nzInt)),
    ∪(μ(x, ∪(tvar(x), nzInt)), nzInt)
  ).

test(μ2, [nondet]) :-
  subtype(
    μ(x, arrow(tvar(x), tvar(x))),
    arrow(μ(x, arrow(tvar(x), tvar(x))), μ(x, arrow(tvar(x), tvar(x))))
  ).

test(μ3, [nondet]) :-
  subtype(
    arrow(
      μ(x, arrow(tvar(x), tvar(x))),
      μ(y, arrow(tvar(y), tvar(y)))
    ),
    μ(x, arrow(tvar(x), tvar(x)))
  ).

test(hungry, [nondet]) :-
  subtype(
    arrow(nzInt,
      arrow(nzInt,
        arrow(nzInt,
          μ(z, arrow(nzInt, tvar(z)))))),
    μ(z, arrow(nzInt, tvar(z)))
  ).

test(fμ, [nondet]) :-
  univ(T),
  subtype(
    arrow(T, nzInt),
    T
  ).

test(fμ_simpl, [nondet]) :-
  T = μ(z, ∪(nzInt, ∪(nzniFlt, arrow(tvar(z), tvar(z))))),
  subtype(
    arrow(T, nzInt),
    T
  ).


test(progtyp, [nondet]) :-
  univ(T),
  ω_all(Ω),
  type(Ω, [],
    λ(f, T,
      λ(x, T,
        subsume(app(var(f),
          subsume(op(iplus, var(x), nzIntConst), T)), T))),
    _).

test(op_univ, [nondet]) :-
  univ(T),
  ω_all(Ω),
  type(Ω, [bind(x, T)],
    op(iplus, var(x), nzIntConst),
    _).

test(ω_all_simpl, [nondet]) :-
  ω_all(Ω),
  type(Ω, [], op(iplus, nzFltConst, nzIntConst), ⊥).

test(ω_app, [nondet]) :-
  univ(T),
  ω_all(Ω),
  type(Ω, [bind(f, T)], app(var(f), subsume(nzFltConst, T)), _).

test(univ_subtyp, [nondet]) :-
  univ(T),
  type([], [], subsume(nzFltConst, T), T).

test(univ_subtyp_direct, [nondet]) :-
  univ(T),
  type([], [bind(f, arrow(T, T)), bind(x, T)],
    app(var(f), var(x)), T).

test(univ_subtyp2, [nondet]) :-
  univ(T),
  type([], [bind(f, arrow(T, T))],
    app(var(f), subsume(nzFltConst, T)), T).


% Regression tests for missing a case in notBottom
test(tenv, [nondet]) :-
  univ(T),
  type([errBadApp], [bind(f, arrow(T, T))],
    var(f), arrow(T, T)).

test(apply_univ, [nondet]) :-
  univ(T),
  apply(arrow(T, T), T, [], T).


:- end_tests(types0).

:- run_tests.
:- halt.

