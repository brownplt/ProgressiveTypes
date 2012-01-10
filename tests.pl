
type([], intConst, int).

type([bind(x, int)|[bind(y, flt)|[]]], var(x), int).

type([bind(x, int)|[bind(y, flt)|[]]], var(y), flt).

type([], fun(x, var(x)), arrow(int, T)).

type(E, fun(x, var(y)), arrow(int, flt)).

subtype(int, union(int, flt)).

subtype(union(int,int), int).

subtype(union(int, union(int, flt)), union(flt, int)).

not(subtype(int, flt)).

subtype(union(int,flt), union(flt, int)).

subtype(arrow(int, int), arrow(int, int)).

subtype(arrow(union(int, flt), flt), arrow(flt, flt)).

subtype(flt, union(int, flt)).

subtype(arrow(flt, flt), arrow(flt, union(flt, int))).

type([], op(iplus, intConst, fltConst), T).

