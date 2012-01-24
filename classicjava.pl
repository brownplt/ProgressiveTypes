
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

% checkInheritance : List(class)

