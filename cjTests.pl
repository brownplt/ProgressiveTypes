wellFormedExpr(new(ponies)).

wellFormedClass(class(billy, bilysDad, [], [])).

wellFormedArg(arg(argName, aClass)).

wellFormedClass(class(aClass, aParent, [], [method(aMethod, 
			arg(argName, aClass), var(aClass), aClass)|[]])).

wellFormedMethod(method(aMethod, 
			arg(argName, aClass), var(aClass), aClass)).

assert(isAClass(class(aClass, aParent, [], [method(aMethod, 
			arg(argName, aClass), var(aClass), aClass)|[]]))).

isAClass(X), wellFormedClass(X).

assert(isAnExpr(invoke(new(aClass), aMethod, new(aClass)))).

isAnExpr(Y), wellFormedExpr(Y).

isAClass(X), isAnExpr(Y), wellFormedProg([X|[]], Y).
