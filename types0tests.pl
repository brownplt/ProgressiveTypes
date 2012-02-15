:- begin_tests(types0).
:- use_module('types0', except([])).

test(divZero, [nondet]) :-
  type([], op(div, nzIntConst, zeroConst), errDivByZeroWithIntNumerator).

test(divInt, [nondet]) :-
  type([], op(div, nzIntConst, nzIntConst), union(nzniFlt, nzInt)).

test(divFlt, [nondet]) :-
  type([], op(div, nzIntConst, nzFltConst), union(nzniFlt, nzInt)).

test(divZeroTop, [nondet]) :-
  type([], op(div, zeroConst, nzIntConst), zero).

test(iplusIZ, [nondet]) :-
  type([], op(iplus, nzIntConst, zeroConst), nzInt).

test(plusIZ, [nondet]) :-
  type([], op(plus, nzIntConst, zeroConst), nzInt).

test(plusFZ, [nondet]) :-
  type([], op(plus, nzFltConst, zeroConst), nzniFlt).

test(plusZI, [nondet]) :-
  type([], op(iplus, zeroConst, nzIntConst), nzInt).

test(funDivIX, [nondet]) :-
  type([], fun(x, union(nzInt, nzniFlt), op(div, nzIntConst, var(x))), 
       arrow(union(nzInt, nzniFlt),
             union(union(nzniFlt, nzInt),
                   union(nzniFlt, nzInt)))).

test(funDiv0X, [nondet]) :-
  type([], fun(x, union(nzInt, nzniFlt), op(div, var(x), zeroConst)),
       T).

%       arrow(union(nzInt, nzniFlt),
%             union(errDivByZeroWithIntNumerator,
%                   errDivByZeroWithFloatNumerator))).

:- end_tests(types0).

:- run_tests.
:- halt.
