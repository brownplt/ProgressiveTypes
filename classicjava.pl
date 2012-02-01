
wellFormedProg([Cd1|Rest], Expr):-
  wellFormedClass(Cd1),
  wellFormedProg(Rest, Expr).

wellFormedProg([], Expr):-
  wellFormedExpr(Expr).

wellFormedClass(class(Name, Parent, Methods)):-
  wellFormedMethods(Methods).

wellFormedMethods([Method1|Rest]):-
  wellFormedMethod(Method1),
  wellFormedMethods(Rest).

wellFormedMethods([]).

wellFormedMethod(method(Name, Arg, BodyExpr, Res)):-
  wellFormedArg(Arg),
  wellFormedExpr(BodyExpr).

wellFormedArg(arg(Name, Class)).

wellFormedExpr(new(ClassName)).

wellFormedExpr(cast(Expr, ClassName)):-
  wellFormedExpr(Expr).

wellFormedExpr(invoke(ObjExpr, MethodName, ArgExpr)):-
  wellFormedExpr(ArgExpr),
  wellFormedExpr(ObjExpr).

wellFormedExpr(var(VarName)).

classListTreeCheck(List, Outlist):-
  classListTreeCheck2(List, [parent(object, object)], Outlist).

classListTreeCheck2([], Classes, Outlist) :- Outlist=Classes.

% a parent is:
% parent(childClassName, parentClassName)

% classListTreeCheck2 : List(class), List(parent), List(parent)
classListTreeCheck2([class(CName, PName, _)|Rest], Classes, Outlist):-
  member(parent(PName, _), Classes),
  classListTreeCheck2(Rest, [parent(CName, PName)|Classes], Outlist).


% an arg is:
% arg(argName, argType)

% a signature is:
% signature(className, methodName, arg, returnType)

classesMethodDescriptions([], Methods) :- Methods = [].
classesMethodDescriptions([class(ClassName, _, CMethods)|Rest], Methods) :-
  classMethodDescriptions(ClassName, CMethods, TheseMethods),
  classesMethodDescriptions(Rest, RestMethods),
  append([TheseMethods, RestMethods], Methods).

classMethodDescriptions(_, [], Methods) :- Methods = [].
classMethodDescriptions(ClassName, [method(Name, Arg, _, Return)|Rest], Methods) :-
  Methods = [signature(ClassName, Name, Arg, Return)|RestMethods],
  classMethodDescriptions(ClassName, Rest, RestMethods).

% isAncestor : List(parent), className, className
isAncestor(Parents, ChildName, Ancestor) :-
  member(parent(ChildName, Ancestor), Parents).
isAncestor(Parents, ChildName, Ancestor) :-
  member(parent(ChildName, TransitionParent), Parents),
  isAncestor(Parents, TransitionParent, Ancestor).

% getSignature : List(parent), className, methodName, methodDescriptions, signature
getSignature(Parents, Class, Method, Descs, Sig) :-
  isAncestor(Parents, Class, ParentClass),
  wellFormedArg(Arg),
  member(signature(ParentClass, Method, Arg, Return), Descs),
  Sig = signature(ParentClass, Method, Arg, Return).

findClass(Name, Classes, OutClass) :-
  member(class(Name, P, M), Classes),
  OutClass = class(Name, P, M).
findSignature(CName, MName, Methods, OutSig) :-
  member(signature(CName, MName, Arg, Return), Methods),
  OutSig = signature(CName, MName, Arg, Return).

% checkInheritance : List(class)
checkInheritance(Classes) :-
  classListTreeCheck(Classes, Parents),
  checkInheritanceAncestors(Parents, Classes, Classes).

% checkInheritanceAncestors : List(parent), List(class), List(class)
checkInheritanceAncestors(_, _, []).
checkInheritanceAncestors(Parents, AllClasses,
    [class(CName, CParent, CMethods)|RestClasses]) :-
  checkChildMethods(Parents, AllClasses, CParent, class(CName, CParent, CMethods)),
  checkInheritanceAncestors(Parents, AllClasses, RestClasses).

% checkChildMethods : List(parent), List(class), className, class
checkChildMethods(Parents, Classes, object, Child).
checkChildMethods(Parents, Classes, AncestorName,
    class(CName, CParent, CMethods)) :-
  findClass(AncestorName, Classes, class(AncestorName, AParent, AMethods)),
  classesMethodDescriptions(Classes, MethodDescs),
  checkMethods(MethodDescs, AncestorName, CName, AMethods, CMethods),
  checkChildMethods(Parents, Classes, AParent,
    class(CName, CParent, CMethods)).
  
checkMethods(MethodDescs, PName, CName, PMethods, []).
checkMethods(MethodDescs, PName, CName, PMethods,
  [method(MName, _, _, _)|RestMethods]) :-
  not(member(signature(PName, MName, _, _), MethodDescs)),
  checkMethods(MethodDescs, PName, CName, PMethods, RestMethods).
checkMethods(MethodDescs, PName, CName, PMethods,
  [method(MName, _, _, _)|RestMethods]) :-
  member(signature(CName, MName, Arg, Return), MethodDescs),
  member(signature(PName, MName, Arg, Return), MethodDescs),
  checkMethods(MethodDescs, PName, CName, PMethods, RestMethods).
checkMethods(MethodDescs, PName, CName, PMethods,
  [method(MName, _, _, _)|RestMethods]) :-
  member(signature(CName, MName, CArg, CReturn), MethodDescs),
  member(signature(PName, MName, PArg, PReturn), MethodDescs),
  CArg /= PArg, !, fail.
checkMethods(MethodDescs, PName, CName, PMethods,
  [method(MName, _, _, _)|RestMethods]) :-
  member(signature(CName, MName, CArg, CReturn), MethodDescs),
  member(signature(PName, MName, PArg, PReturn), MethodDescs),
  CReturn /= PReturn, !, fail.

