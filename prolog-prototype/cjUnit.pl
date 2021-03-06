:- begin_tests(classicjava).
:- use_module('classicjava.pl', except([])).

% Well-formedness tests

test(wfe) :-
  wellFormedExpr(new(ponies)).

test(wfc) :-
  wellFormedClass(class(billy, billysDad, [], [])).

test(wfa) :-
  wellFormedArg(arg(argName, aClass)).

test(wfm) :-
  wellFormedMethod(method(foo, arg(a, aClass),
    new(aClass), aClass, [])).

test(wff) :-
  wellFormedField(field(fieldName, className)).

isAClass(class(aClass, aParent, 
  [ field(f, aClass) ],
  [ method(aMethod, arg(argName, aClass),
           var(aClass), aClass, [])|[]
  ]
)).

test(wfc2) :-
  isAClass(X), wellFormedClass(X).

isAnExpr(invoke(new(aClass), aMethod, getfield(new(aClass),z))).
isAnExpr2(getfield(invoke(new(aClass), aMethod,
            getfield(new(aClass),z)), y)).

test(wfe2) :-
  isAnExpr(Y), wellFormedExpr(Y).

test(wfe3) :-
  isAnExpr2(Y), wellFormedExpr(Y).

test(wfp) :-
  isAClass(X), isAnExpr(Y), wellFormedProg([X], Y).

% Cyclic tests

parent(class(parentClass, childClass, [], [])).

child(class(childClass, parentClass, [], [])).

test(badcyclic, [fail]) :-
  parent(P), child(C), classListTreeCheck([P, C], _).

test(goodcyclic) :-
  A = class(a, object, [], []),
  B = class(b, a, [], []),
  classListTreeCheck([A, B], [parent(b,a), parent(a,object)]), !.

test(methods1) :-
  C = class(aClass, object, [], [
    method(getb, arg(b, bClass), var(b), bClass, [])
  ]),
  M = [signature(aClass, getb, arg(b, bClass), bClass, [])],
  classesMethodDescriptions([C], M), !.

test(methods2) :-
  A = class(aClass, object, [], [
    method(getb, arg(b, bClass), var(b), bClass, [])
  ]),
  B = class(bClass, object, [], [
    method(geta, arg(a, aClass), var(a), aClass, [])
  ]),
  M = [signature(aClass, getb, arg(b, bClass), bClass, []),
       signature(bClass, geta, arg(a, aClass), aClass, [])],
  classesMethodDescriptions([A,B],M), !.

% Getting the right signature

parentWithFoo(class(parentClass, object, [
  field(x, object)
], [
  method(foo, arg(p, parentClass), new(parentClass), parentClass, [])
])).

goodChildWithFoo(class(goodChild, parentClass, [], [
    method(foo, arg(p, parentClass), var(p), parentClass, [])
])).

goodChildWithX(class(goodFieldChild, parentClass, [
  field(x, object)
], [])).

badChildWithFoo(class(badChild, parentClass, [], [
  method(foo, arg(p, badChild), var(p), badChild, [])
])).

badChildWithX(class(badFieldChild, parentclass, [
  field(x, parentClass)
], [])).

childWithoutFoo(class(noFooChild, parentClass, [], [
    method(noop, arg(p, parentClass), new(noFooChild), noFooChild, [])
])).

noMethodsChild(class(noMethods, parentClass, [], [])).

goodFooGrandchild(class(goodFooGC, noMethods, [], [
  method(foo, arg(p, parentClass), new(parentClass), parentClass, [])
])).

goodGrandchildX(class(goodFooGC, noMethods, [
  field(x, object)
], [])).

badFooGrandchild(class(badFooGC, noMethods, [], [
  method(foo, arg(p, parentClass), new(noMethods), noMethods, [])
])).

noMethodsParent(class(noMethodsP, object, [], [])).

fooChildNoMethodsParent(class(fooChild, noMethodsP, [], [
    method(foo, arg(p, parentClass), var(p), parentClass, [])
])).

test(parent_fields, [nondet]) :-
  parentWithFoo(P),
  F = [
    fieldsig(parentClass, x, object)
  ],
  classesFieldDescriptions([P], F).

test(good_child_fields, [nondet]) :-
  parentWithFoo(P), goodChildWithX(C),
  F = [
    fieldsig(parentClass, x, object),
    fieldsig(goodFieldChild, x, object)
  ],
  classesFieldDescriptions([P,C], F).

test(goodchilddescs, [nondet]) :-
  parentWithFoo(P), goodChildWithFoo(C),
  M = [
    signature(parentClass, foo, arg(p, parentClass), parentClass, []),
    signature(goodChild, foo, arg(p, parentClass), parentClass, [])
  ],
  classesMethodDescriptions([P,C],M).

test(goodchildsig, [nondet]) :-
  parentWithFoo(P), goodChildWithFoo(C),
  classListTreeCheck([P,C], Parents),
  classesMethodDescriptions([P,C], Methods),
  Sig = signature(goodChild, foo, arg(p, parentClass), parentClass, []),
  getSignature(Parents, goodChild, foo, Methods, Sig).

test(checkinheritsingle, [nondet]) :-
  parentWithFoo(P), checkInheritance([P]).

test(checkinheritfield, [nondet]) :-
  parentWithFoo(P), goodChildWithX(C), checkInheritance([P, C]).

test(checkinheritbadfield, [fail]) :-
  parentWithFoo(P), badChildWithX(C), checkInheritance([P, C]).

test(checkinheritskipfield, [nondet]) :-
  parentWithFoo(P), noMethodsChild(C), goodGrandchildX(GC),
  checkInheritance([P, C, GC]).

test(checkinheritgood, [nondet]) :-
  parentWithFoo(P), goodChildWithFoo(C), checkInheritance([P,C]).

test(checkinheritbad, [fail]) :-
  parentWithFoo(P), badChildWithFoo(C), checkInheritance([P,C]).

test(checkinheritomit, [nondet]) :-
  parentWithFoo(P), childWithoutFoo(C), checkInheritance([P,C]).

test(checkshadow, [nondet]) :-
  noMethodsParent(P), fooChildNoMethodsParent(C),
  checkInheritance([P, C]).

test(checkskipchild, [nondet]) :-
  parentWithFoo(P), noMethodsChild(C), goodFooGrandchild(GC),
  checkInheritance([P, C, GC]).

test(checkskipbad, [fail]) :-
  parentWithFoo(P), noMethodsChild(C), badFooGrandchild(GC),
  checkInheritance([P, C, GC]).

test(typeinvoke, [nondet]) :-
  T = parentClass,
  parentWithFoo(P), typecheck([P],
    invoke(new(parentClass),foo,new(parentClass)), T, []).

test(badinvoke, [fail]) :-
  parentWithFoo(P), typecheck([P],
    invoke(new(parentClass),foo,new(object)), _, _).

test(badmethod, [fail]) :-
  typecheck([class(aClass, object, [], [
    method(foo, arg(p, object), new(aClass), object)
  ])], new(object), _, _).

test(badmethod2, [fail]) :-
  typecheck([class(aClass, object, [], [
    method(foo, arg(p, object), new(aClass), aClass, []),
    method(foo, arg(p, object), new(aClass), object, [])
  ])], new(object), _, _).

test(id, [nondet]) :-
  typecheck([class(bClass, object, [], [
    method(foo, arg(p, object), var(p), object, []),
    method(bar, arg(p, bClass), var(p), bClass, [])
  ])], new(object), _, _).

% Cast examples
intClass(class(integer, object, [], [])).
colorClass(class(color, object, [], [])).

pointClass(class(point, object, [
  field(x, integer)
], [
  method(getX, arg(p, object), new(integer), integer, [])
])).

pointClass2(class(point2d, point, [
  field(y, integer)
], [
  method(getY, arg(unused, object), new(integer), integer, [])
])).

pointClassC(class(pointC, point, [], [
  method(getC, arg(unused, object), new(color), color, [])
])).

shapeClass(class(shape, object, [], [])).

exampleList(L) :-
  intClass(I),
  colorClass(C),
  pointClass(PC),
  pointClass2(PC2),
  pointClassC(PCC),
  shapeClass(SC),
  L = [I, C, PC, PC2, PCC, SC].

test(get_x, [nondet]) :-
  exampleList(CS), typecheck(CS, getfield(new(point), x), integer, []).
test(get_x2, [nondet]) :-
  exampleList(CS), typecheck(CS, getfield(new(point2d), x), integer, []).
test(get_y, [nondet]) :-
  exampleList(CS), typecheck(CS, getfield(new(point2d), y), integer, []).
test(get_zbad, [nondet]) :-
  exampleList(CS), typecheck(CS, getfield(new(point), z), bottom,
    [errfieldnotfound]).

test(invoke_bad, [nondet]) :-
  exampleList(CS), typecheck(CS, invoke(new(point), notmethod, new(object)),
    bottom, [errmethodnotfound]).

test(point_to_object, [nondet]) :-
  exampleList(CS), typecheck(CS, cast(new(point), object), object, []).
test(point_to_point, [nondet]) :-
  exampleList(CS), typecheck(CS, cast(new(point), point), point, []).
test(point_to_shape, [nondet]) :-
  exampleList(CS), typecheck(CS, cast(new(point), shape), bottom, [errcrosscast]).
test(point_to_point2d, [nondet]) :-
  exampleList(CS), typecheck(CS, cast(new(point), point2d), point2d, [errdowncast]).
test(point_to_pointc, [nondet]) :-
  exampleList(CS), typecheck(CS, cast(new(point), pointC), pointC, [errdowncast]).
test(point2d_object, [nondet]) :-
  exampleList(CS), typecheck(CS, cast(new(point2d), object), object, []).

badCastingClass(class(badcast, object, [], [
  method(foo, arg(c, integer), cast(var(c), color), bottom, [errcrosscast])
])).

test(badcast, [nondet]) :-
  badCastingClass(B), intClass(I), colorClass(C),
  typecheck([I,C,B], invoke(cast(new(integer), badcast), foo,
    new(integer)), _, [errcrosscast]).

badDeclaringClass(class(baddecl, object, [], [
  method(throwsalot, arg(t, object), cast(var(t), integer), bottom, [])
])).

test(baddecl, [fail]) :-
  badDeclaringClass(B), intClass(I),
    typecheck([I,B], new(object), _, _).

nullLookupClass(class(nullLookup, object, [
  field(f, object)
], [
  method(getF, arg(o, union(null, nullLookup)),
          getfield(o, f), object, [errnullptrfield])
])).

:- end_tests(classicjava).

:- run_tests.
:- halt.

