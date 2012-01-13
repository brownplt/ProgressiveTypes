
canonical(nzInt, union(nzInt, nzInt)).

canonical(nzInt, union(nzInt, union(nzInt, nzInt))).

canonical(union(nzInt, nzniFlt), union(nzInt, union(nzniFlt, nzniFlt))).

canonical(union(nzInt, nzniFlt), union(union(nzInt, nzniFlt), union(nzniFlt, nzniFlt))).

not(canonical(union(nzInt, nzInt), union(nzInt, union(nzInt, nzInt)))).

canonical(arrow(nzInt, nzniFlt), arrow(union(nzInt, nzInt), union(nzniFlt, nzniFlt))).

type([], op(div, nzIntConst, zeroConst), T).

type([], op(div, nzIntConst, nzIntConst), T).

type([], op(div, nzIntConst, nzFltConst), T).

type([], op(div, zeroConst, nzIntConst), T).

type([], op(iplus, nzIntConst, zeroConst), T).

type([], op(plus, nzIntConst, zeroConst), T).

type([], op(plus, nzFltConst, zeroConst), T).

type([], op(iplus, zeroConst, nzIntConst), T).

type([], fun(x, union(nzInt, nzniFlt), op(div, nzIntConst, var(x))), T).

type([], fun(x, union(nzInt, nzniFlt), op(div, nzIntConst, var(x))), arrow(T1, T2)).

type([], fun(x, union(nzInt, nzniFlt),
         op(div, nzIntConst, var(x))),
         arrow(union(T11, T12), T2)).

type([], fun(x, T, var(x)), S).


type([], fun(x, union(nzInt, nzniFlt), op(div, var(x), zeroConst)), T).

% type([(x, arrow(nzInt, bottom)|[]], app(var(x), nzIntConst), bottom, errunion(... some errors ...)))

