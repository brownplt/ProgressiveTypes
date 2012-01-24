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


