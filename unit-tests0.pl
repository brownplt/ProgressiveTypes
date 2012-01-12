:- begin_tests(types0).

test(canonical) :-
  canonical(nzInt, union(nzInt, nzInt)).

test(canonical) :-
  canonical(nzInt, union(nzInt, union(nzInt, nzInt))).

:- end_tests(types0).
