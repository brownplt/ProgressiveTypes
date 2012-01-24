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

