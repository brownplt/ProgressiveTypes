:- begin_tests(types0).
:- use_module('types0', except([])).

test(divZero, [nondet]) :-
  type([errDivByZeroWithIntNumerator], [], op(div, nzIntConst, zeroConst), ⊥ ).

test(divZero, [fail]) :-
  type([], [], op(div, nzIntConst, zeroConst), ⊥ ).

test(divInt, [nondet]) :-
  type([], [], op(div, nzIntConst, nzIntConst), union(nzniFlt, nzInt)).

test(divFlt, [nondet]) :-
  type([], [], op(div, nzIntConst, nzFltConst), union(nzniFlt, nzInt)).

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
  type([], [], λ(x, union(nzInt, nzniFlt), op(div, nzIntConst, var(x))), 
       arrow(union(nzInt, nzniFlt),
             union(union(nzniFlt, nzInt),
                   union(nzniFlt, nzInt)))).

test(funDiv0X, [nondet]) :-
  type([
    errDivByZeroWithIntNumerator,
    errDivByZeroWithFloatNumerator
  ], [], λ(x, union(nzInt, nzniFlt), op(div, var(x), zeroConst)),
  arrow(union(nzInt, nzniFlt), union(⊥ , ⊥ ))).

test(plusBot, [nondet]) :-
  type(
    [errDivByZeroWithIntNumerator],
    [],
    op(plus, op(div, nzIntConst, zeroConst), zeroConst),
    ⊥
  ).


:- end_tests(types0).

:- run_tests.
:- halt.
