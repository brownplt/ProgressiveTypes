:- module(classicjava, [
  wellFormedProg/2,
  wellFormedClass/1,
  wellFormedMethods/1,
  wellFormedMethod/1,
  wellFormedArg/1,
  wellFormedExpr/1,
  classListTreeCheck/2,
  classesMethodDescriptions/2,
  getSignature/5,
  checkInheritance/1,
  typecheck/4
]).

wellFormedProg([Cd1|Rest], Expr):-
  wellFormedClass(Cd1),
  wellFormedProg(Rest, Expr).

wellFormedProg([], Expr):-
  wellFormedExpr(Expr).

wellFormedClass(class(_, _, Methods)):-
  wellFormedMethods(Methods).

wellFormedMethods([Method1|Rest]):-
  wellFormedMethod(Method1),
  wellFormedMethods(Rest).

wellFormedMethods([]).

wellFormedMethod(method(_, Arg, BodyExpr, _, _)):-
  wellFormedArg(Arg),
  wellFormedExpr(BodyExpr).

wellFormedArg(arg(_, _)).

wellFormedExpr(new(_)).

wellFormedExpr(cast(Expr, _)):-
  wellFormedExpr(Expr).

wellFormedExpr(invoke(ObjExpr, _, ArgExpr)):-
  wellFormedExpr(ArgExpr),
  wellFormedExpr(ObjExpr).

wellFormedExpr(var(_)).

classListTreeCheck(List, Outlist):-
  classListTreeCheck2(List, [], Outlist).

% a parent is:
% parent(childClassName, parentClassName)

% classListTreeCheck2 : List(class), List(parent), List(parent)
classListTreeCheck2([], Classes, Outlist) :- Classes=Outlist.
classListTreeCheck2([class(CName, object, _)|Rest], Classes, Outlist):-
  classListTreeCheck2(Rest, [parent(CName, object)|Classes], Outlist).
classListTreeCheck2([class(CName, PName, _)|Rest], Classes, Outlist):-
  classListTreeCheck2(Rest, [parent(CName, PName)|Classes], Outlist),
  member(parent(PName, _), Classes).

% an arg is:
% arg(argName, argType)

% a signature is:
% signature(className, methodName, arg, returnType, errors)

classesMethodDescriptions([], Methods) :- Methods = [].
classesMethodDescriptions([class(ClassName, _, CMethods)|Rest], Methods) :-
  classMethodDescriptions(ClassName, CMethods, TheseMethods),
  classesMethodDescriptions(Rest, RestMethods),
  append([TheseMethods, RestMethods], Methods).

classMethodDescriptions(_, [], Methods) :- Methods = [].
classMethodDescriptions(ClassName, [method(Name, Arg, _, Return, Errors)|Rest], Methods) :-
  Methods = [signature(ClassName, Name, Arg, Return, Errors)|RestMethods],
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
  member(signature(ParentClass, Method, Arg, Return, Errors), Descs),
  Sig = signature(ParentClass, Method, Arg, Return, Errors).
getSignature(_, Class, Method, Descs, Sig) :-
  member(signature(Class, Method, Arg, Return, Errors), Descs),
  Sig = signature(Class, Method, Arg, Return, Errors).

findClass(Name, Classes, OutClass) :-
  member(class(Name, P, M), Classes),
  OutClass = class(Name, P, M).
findSignature(CName, MName, Methods, OutSig) :-
  member(signature(CName, MName, Arg, Return, Errors), Methods),
  OutSig = signature(CName, MName, Arg, Return, Errors).

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
checkChildMethods(_, _, object, _).
checkChildMethods(Parents, Classes, AncestorName,
    class(CName, CParent, CMethods)) :-
  findClass(AncestorName, Classes, class(AncestorName, AParent, AMethods)),
  classesMethodDescriptions(Classes, MethodDescs),
  checkMethods(MethodDescs, AncestorName, CName, AMethods, CMethods),
  checkChildMethods(Parents, Classes, AParent,
    class(CName, CParent, CMethods)).
  
checkMethods(_, _, _, _, []).
checkMethods(MethodDescs, PName, CName, PMethods,
  [method(MName, _, _, _, _)|RestMethods]) :-
  not(member(signature(PName, MName, _, _, _), MethodDescs)),
  checkMethods(MethodDescs, PName, CName, PMethods, RestMethods).
checkMethods(MethodDescs, PName, CName, PMethods,
  [method(MName, _, _, _, _)|RestMethods]) :-
  member(signature(CName, MName, Arg, Return, Errors), MethodDescs),
  member(signature(PName, MName, Arg, Return, Errors), MethodDescs),
  checkMethods(MethodDescs, PName, CName, PMethods, RestMethods).
checkMethods(MethodDescs, PName, CName, _,
  [method(MName, _, _, _, _)|_]) :-
  member(signature(CName, MName, CArg, _, _), MethodDescs),
  member(signature(PName, MName, PArg, _, _), MethodDescs),
  not(CArg = PArg), !, fail.
checkMethods(MethodDescs, PName, CName, _,
  [method(MName, _, _, _, _)|_]) :-
  member(signature(CName, MName, _, CReturn, _), MethodDescs),
  member(signature(PName, MName, _, PReturn, _), MethodDescs),
  not(CReturn = PReturn), !, fail.
checkMethods(MethodDescs, PName, CName, _,
  [method(MName, _, _, _, _)|_]) :-
  member(signature(CName, MName, _, _, CErrors), MethodDescs),
  member(signature(PName, MName, _, _, PErrors), MethodDescs),
  not(CErrors = PErrors), !, fail.

% typecheck : List(class), expr, className, List(error)
typecheck(Classes, Expr, T, Errors) :-
  classListTreeCheck(Classes, Parents),
  classesMethodDescriptions(Classes, Methods),
  typecheckClasses(Parents, Methods, Classes),
  type(Methods, Parents, _, Expr, T, Errors).

typecheckClasses(_, _, []).
typecheckClasses(Parents, Methods, [Class|Classes]) :-
  typecheckClass(Parents, Methods, Class),
  typecheckClasses(Parents, Methods, Classes).

typecheckClass(Parents, Methods, class(_, _, CMethods)) :-
  typecheckMethods(Parents, Methods, CMethods).

typecheckMethods(_, _, []).
typecheckMethods(Parents, Methods, [CMethod|CMethods]) :-
  typecheckMethod(Parents, Methods, CMethod),
  typecheckMethods(Parents, Methods, CMethods).

typecheckMethod(Parents, Methods, method(_, Arg, Body, Result, Errors)) :-
  type(Methods, Parents, Arg, Body, Result, Errors).

% type : list(Signature), List(parent), arg, expr, className, List(error)
type(_, Parents, _, new(ClassName), ClassName, _) :-
  member(parent(ClassName, _), Parents).
type(_, _, _, new(object), object, _).

type(Sigs, Parents, A, invoke(ObjExpr, MethodName, ArgExpr), Result, Errors):-
  type(Sigs, Parents, A, ObjExpr, ObjClass, OErrors),
  type(Sigs, Parents, A, ArgExpr, ArgClass, AErrors),
  getSignature(Parents, ObjClass, MethodName, Sigs,
    signature(_, MethodName, arg(_, ArgClass), Result, SErrors)),
  append([OErrors, AErrors, SErrors], Errors).
type(Sigs, Parents, A, invoke(ObjExpr, _, ArgExpr), Result, Errors):-
  type(Sigs, Parents, A, ObjExpr, ObjClass, OErrors),
  type(Sigs, Parents, A, ArgExpr, ArgClass, AErrors),
  (ObjClass = bottom; ArgClass = bottom),
  Result = bottom, append([OErrors, AErrors], Errors).

type(_, _, arg(VarName, Result), var(VarName), Result, _).

type(Sigs, Parents, A, cast(Expr, ClassName), ClassName, Errors):-
  type(Sigs, Parents, A, Expr, ClassName, Errors).
type(Sigs, Parents, A, cast(Expr, ParentClassName), ParentClassName, Errors):-
  type(Sigs, Parents, A, Expr, EClassName, Errors),
  isAncestor(Parents, EClassName, ParentClassName).
type(Sigs, Parents, A, cast(Expr, ChildClassName), ChildClassName, Errors):-
  type(Sigs, Parents, A, Expr, EClassName, EErrors),
  isAncestor(Parents, ChildClassName, EClassName),
  Errors = [errdowncast|EErrors].
type(Sigs, Parents, A, cast(Expr, OtherClassName), bottom, Errors):-
  type(Sigs, Parents, A, Expr, EClassName, EErrors),
  not(EClassName = OtherClassName),
  not(isAncestor(Parents, EClassName, OtherClassName)),
  not(isAncestor(Parents, OtherClassName, EClassName)),
  Errors = [errcrosscast|EErrors].

