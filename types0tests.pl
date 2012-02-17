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

test(appfunion, [nondet]) :-
  type(
    [],
    [bind(f, ∪(arrow(zero, zero), arrow(zero, nzInt)))],
    app(var(f), zeroConst),
    ∪(zero, nzInt)
  ).


:- end_tests(types0).

:- run_tests.
:- halt.

