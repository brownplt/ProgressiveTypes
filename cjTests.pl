wellFormedExpr(new(ponies)).

wellFormedClass(class(billy, bilysDad, [])).

wellFormedArg(arg(argName, aClass)).

wellFormedClass(class(aClass, aParent, [method(aMethod, 
			arg(argName, aClass), var(aClass), aClass)|[]])).

wellFormedMethod(method(aMethod, 
			arg(argName, aClass), var(aClass), aClass)).

assert(isAClass(class(aClass, aParent, [method(aMethod, 
			arg(argName, aClass), var(aClass), aClass)|[]]))).

isAClass(X), wellFormedClass(X).

assert(isAnExpr(invoke(new(aClass), aMethod, new(aClass)))).

isAnExpr(Y), wellFormedExpr(Y).

isAClass(X), isAnExpr(Y), wellFormedProg([X|[]], Y).

assert(parent(class(parentClass, childClass, []))).

assert(child(class(childClass, parentClass, []))).

write('Starting cyclic output, next should fail').

parent(P), child(C), classListTreeCheck([P, C], Outlist).	

assert(classA(class(a, object, []))).

assert(classB(class(b, a, []))).

write('Starting good tree output, next should succeed.').

classA(A), classB(B), classListTreeCheck([A, B], Outlist2).

write('\nMethod list tests').

assert(methodExample1(class(aClass, object, [
    method(getb, arg(b, bClass), var(b), bClass)
  ]))).

methodExample1(C), classesMethodDescriptions([C], M),
M = [signature(aClass, getb, arg(b, bClass), bClass)].

assert(methodExample2(class(bClass, object, [
    method(geta, arg(a, aClass), var(a), aClass)
  ]))).

methodExample1(A), methodExample2(B), classesMethodDescriptions([A,B],M),
M = [signature(aClass, getb, arg(b, bClass), bClass),
     signature(bClass, geta, arg(a, aClass), aClass)].


write('\nGetting the right signature').

assert(parentWithFoo(class(parentClass, object, [
    method(foo, arg(p, parentClass), new(parentClass), parentClass)
  ]))).

assert(goodChildWithFoo(class(goodChild, parentClass, [
    method(foo, arg(p, parentClass), var(p), parentClass)
  ]))).

assert(badChildWithFoo(class(badChild, parentClass, [
    method(foo, arg(p, badChild), var(p), badChild)
  ]))).

assert(childWithoutFoo(class(noFooChild, parentClass, [
    method(noop, arg(p, parentClass), new(noFooChild), noFooChild)
  ]))).


assert(noMethodsChild(class(noMethods, parentClass, []))).

assert(goodFooGrandchild(class(goodFooGC, noMethods, [
  method(foo, arg(p, parentClass), new(parentClass), parentClass)
]))).

assert(badFooGrandchild(class(badFooGC, noMethods, [
  method(foo, arg(p, parentClass), new(noMethods), noMethods)
]))).

write('\n\nShould have interesting results for sig:').

parentWithFoo(P), goodChildWithFoo(C),
classListTreeCheck([P,C], Parents),
classesMethodDescriptions([P,C], Methods),
getSignature(Parents, goodChild, foo, Methods, Sig).

write('\n\nShould have interesting results for methods:').

parentWithFoo(P), goodChildWithFoo(C),
classesMethodDescriptions([P,C], Methods).

write('Just one class should work for checkInheritance:').

parentWithFoo(P4), checkInheritance([P4]).

write('Next should succeed.').

parentWithFoo(P1), goodChildWithFoo(C1), checkInheritance([P1,C1]).

write('Next should fail:').

parentWithFoo(P2), badChildWithFoo(C2), checkInheritance([P2,C2]).

write('Next should succeed.').

parentWithFoo(P3), childWithoutFoo(C3), checkInheritance([P3,C3]).

write('Child with no methods should succeed.').

parentWithFoo(P5), noMethodsChild(C5), checkInheritance([P5,C5]).

assert(noMethodsParent(class(noMethodsP, object, []))).

assert(fooChildNoMethodsParent(class(fooChild, noMethodsP, [
    method(foo, arg(p, parentClass), var(p), parentClass)
  ]))).

write('Child with methods and no parent methods should succeed.').

noMethodsParent(P6), fooChildNoMethodsParent(C6), checkInheritance([P6,C6]).

write('Should succeed when grandchild is good:').

parentWithFoo(P7), noMethodsChild(C7), goodFooGrandchild(GC7),
checkInheritance([P7, C7, GC7]).

write('Should fail when grandchild is bad:').

parentWithFoo(P8), noMethodsChild(C8), badFooGrandchild(GC8),
checkInheritance([P8, C8, GC8]).

write('Should succeed with T=parentClass when invoked correctly:').

parentWithFoo(P9), typecheck([P9],
  invoke(new(parentClass),foo,new(parentClass)), T).

write('Should fail when invoked incorrectly:').

parentWithFoo(P10), typecheck([P10],
  invoke(new(parentClass),foo,new(object)), T).

write('End.').

parentWithFoo(P11), classesMethodDescriptions([P11],D),
classListTreeCheck([P11], Par),
getSignature(Par, parentClass, foo, D, Sig).

