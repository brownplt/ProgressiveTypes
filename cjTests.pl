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

write('Starting cyclic output').

assert(parent(class(parentClass, childClass, []))).

assert(child(class(childClass, parentClass, []))).

parent(P), child(C), classListTreeCheck([P, C], Outlist).	

assert(classA(class(a, object, []))).

assert(classB(class(b, a, []))).

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

write('\n\nShould have interesting results for sig:').

parentWithFoo(P), goodChildWithFoo(C),
classListTreeCheck([P,C], Parents),
classesMethodDescriptions([P,C], Methods),
getSignature(Parents, goodChild, foo, Methods, Sig).

write('\n\nShould have interesting results for methods:').

parentWithFoo(P), goodChildWithFoo(C),
classesMethodDescriptions([P,C], Methods).

%parentWithFoo(P), goodChildWithFoo(C), checkInheritance([P,C]).

write('Next should fail:').

%parentWithFoo(P), badChildWithFoo(C), checkInheritance([P,C]).

%parentWithFoo(P), childWithoutFoo(C), checkInheritance([P,C]).




