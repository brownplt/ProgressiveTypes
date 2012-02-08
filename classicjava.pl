:- module(classicjava, [
  wellFormedProg/2,
  wellFormedClass/1,
  wellFormedMethods/1,
  wellFormedMethod/1,
  wellFormedField/1,
  wellFormedArg/1,
  wellFormedExpr/1,
  classListTreeCheck/2,
  classesMethodDescriptions/2,
  classesFieldDescriptions/2,
  getSignature/5,
  checkInheritance/1,
  typecheck/4
]).

wellFormedProg([Cd1|Rest], Expr):-
  wellFormedClass(Cd1),
  wellFormedProg(Rest, Expr).

wellFormedProg([], Expr):-
  wellFormedExpr(Expr).

wellFormedClass(class(_, _, Fields, Methods)) :-
  wellFormedFields(Fields),
  wellFormedMethods(Methods).

wellFormedFields([]).
wellFormedFields([Field1|Rest]) :-
  wellFormedField(Field1),
  wellFormedFields(Rest).

wellFormedField(field(_, _)).

wellFormedMethods([]).
wellFormedMethods([Method1|Rest]):-
  wellFormedMethod(Method1),
  wellFormedMethods(Rest).

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

wellFormedExpr(getfield(ObjExpr, _)) :-
  wellFormedExpr(ObjExpr).

classListTreeCheck(List, Outlist):-
  classListTreeCheck2(List, [], Outlist).

% a parent is:
% parent(childClassName, parentClassName)

% classListTreeCheck2 : List(class), List(parent), List(parent)
classListTreeCheck2([], Classes, Outlist) :- Classes=Outlist.
classListTreeCheck2([class(CName, object, _, _)|Rest], Classes, Outlist):-
  classListTreeCheck2(Rest, [parent(CName, object)|Classes], Outlist).
classListTreeCheck2([class(CName, PName, _, _)|Rest], Classes, Outlist):-
  classListTreeCheck2(Rest, [parent(CName, PName)|Classes], Outlist),
  member(parent(PName, _), Classes).

% an arg is:
% arg(argName, argType)

classesFieldDescriptions([], Fields) :- Fields = [].
classesFieldDescriptions([class(ClassName, _, CFields, _)|Rest], Fields) :-
  classFieldDescriptions(ClassName, CFields, TheseFields),
  classesFieldDescriptions(Rest, RestFields),
  append([TheseFields, RestFields], Fields).

classFieldDescriptions(_, [], Fields) :- Fields = [].
classFieldDescriptions(ClassName, [field(Name, Type)|Rest], Fields) :-
  Fields = [fieldsig(ClassName, Name, Type)|RestFields],
  classFieldDescriptions(ClassName, Rest, RestFields).

% a signature is:
% signature(className, methodName, arg, returnType, errors)

classesMethodDescriptions([], Methods) :- Methods = [].
classesMethodDescriptions([class(ClassName, _, _, CMethods)|Rest], Methods) :-
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

% getField : List(parent), className, methodName, fieldDescriptions, fieldsig
getField(Parents, Class, FName, Descs, Sig) :-
  isAncestor(Parents, Class, ParentClass),
  member(fieldsig(ParentClass, FName, FType), Descs),
  Sig = fieldsig(ParentClass, FName, FType).
getField(_, Class, FName, Descs, Sig) :-
  member(fieldsig(Class, FName, FType), Descs),
  Sig = fieldsig(Class, FName, FType).

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
  member(class(Name, P, F, M), Classes),
  OutClass = class(Name, P, F, M).
findSignature(CName, MName, Methods, OutSig) :-
  member(signature(CName, MName, Arg, Return, Errors), Methods),
  OutSig = signature(CName, MName, Arg, Return, Errors).

% a context is
% context(List(parent), List(fieldDesc), List(methodDesc))

% getContext : List(class), context
getContext(Classes, context(Parents, FieldDescs, MethodDescs)) :-
  classListTreeCheck(Classes, Parents),
  classesFieldDescriptions(Classes, FieldDescs),
  classesMethodDescriptions(Classes, MethodDescs).

contextParents(context(Parents, _, _), Parents).
contextFieldDescs(context(_, FieldDescs, _), FieldDescs).
contextMethodDescs(context(_, _, MethodDescs), MethodDescs).

% checkInheritance : List(class)
checkInheritance(Classes) :-
  getContext(Classes, Context),
  checkInheritanceAncestors(Context, Classes, Classes).

% checkInheritanceAncestors : List(parent), List(class), List(class)
checkInheritanceAncestors(_, _, []).
checkInheritanceAncestors(Context, AllClasses,
    [class(CName, CParent, CFields, CMethods)|RestClasses]) :-
  contextMethodDescs(Context, MethodDescs),
  contextFieldDescs(Context, FieldDescs),
  checkChildMethods(MethodDescs, AllClasses, CParent,
                    class(CName, CParent, CFields, CMethods)),
  checkChildFields(FieldDescs, AllClasses, CParent,
                   class(CName, CParent, CFields, CMethods)),
  checkInheritanceAncestors(Context, AllClasses, RestClasses).

checkChildFields(_, _, object, _).
checkChildFields(FieldDescs, Classes, AncestorName,
    class(CName, CParent, CFields, CMethods)) :-
  findClass(AncestorName, Classes,
            class(AncestorName, AParent, AFields, _)),
  checkFields(FieldDescs, AncestorName, CName, AFields, CFields),
  checkChildFields(FieldDescs, Classes, AParent,
    class(CName, CParent, CFields, CMethods)).

checkFields(_, _, _, _, []).
checkFields(FieldDescs, PName, CName, PFields,
  [field(FName, _)|RestFields]) :-
  not(member(fieldsig(PName, FName, _), FieldDescs)),
  checkFields(FieldDescs, PName, CName, PFields, RestFields).
checkFields(FieldDescs, PName, CName, PFields,
  [field(FName, _)|RestFields]) :-
  member(fieldsig(CName, FName, CType), FieldDescs),
  member(fieldsig(PName, FName, CType), FieldDescs),
  checkMethods(FieldDescs, PName, CName, PFields, RestFields).
checkFields(FieldDescs, PName, CName, _,
  [field(FName, _)|_]) :-
  member(fieldsig(CName, FName, CType), FieldDescs),
  member(fieldsig(PName, FName, PType), FieldDescs),
  not(CType=PType), !, fail.

% checkChildMethods : List(parent), List(class), className, class
checkChildMethods(_, _, object, _).
checkChildMethods(MethodDescs, Classes, AncestorName,
    class(CName, CParent, CFields, CMethods)) :-
  findClass(AncestorName, Classes,
            class(AncestorName, AParent, _, AMethods)),
  checkMethods(MethodDescs, AncestorName, CName, AMethods, CMethods),
  checkChildMethods(MethodDescs, Classes, AParent,
    class(CName, CParent, CFields, CMethods)).
  
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
  getContext(Classes, Context),
  typecheckClasses(Context, Classes),
  type(Context, _, Expr, T, Errors).

typecheckClasses(_, []).
typecheckClasses(Context, [Class|Classes]) :-
  typecheckClass(Context, Class),
  typecheckClasses(Context, Classes).

typecheckClass(Context, class(_, _, _, CMethods)) :-
  typecheckMethods(Context, CMethods).

typecheckMethods(_, []).
typecheckMethods(Context, [CMethod|CMethods]) :-
  typecheckMethod(Context, CMethod),
  typecheckMethods(Context, CMethods).

typecheckMethod(Context, method(_, Arg, Body, Result, Errors)) :-
  type(Context, Arg, Body, Result, Errors).

% type : list(fieldsig), list(Signature), List(parent), arg, expr, className, List(error)
type(context(Parents, _, _), _, new(ClassName), ClassName, _) :-
  member(parent(ClassName, _), Parents).
type(_, _, new(object), object, _).

type(Context, A, invoke(ObjExpr, MethodName, ArgExpr), Result, Errors):-
  contextParents(Context, Parents),
  contextMethodDescs(Context, Sigs),
  type(Context, A, ObjExpr, ObjClass, OErrors),
  type(Context, A, ArgExpr, ArgClass, AErrors),
  getSignature(Parents, ObjClass, MethodName, Sigs,
    signature(_, MethodName, arg(_, ArgClass), Result, SErrors)),
  append([OErrors, AErrors, SErrors], Errors).
type(Context, A, invoke(ObjExpr, MethodName, ArgExpr), bottom, Errors):-
  contextParents(Context, Parents),
  contextMethodDescs(Context, Sigs),
  type(Context, A, ObjExpr, ObjClass, OErrors),
  type(Context, A, ArgExpr, _, AErrors),
  not(getSignature(Parents, ObjClass, MethodName, Sigs,
    signature(_, MethodName, _, _, _))),
  append([[errmethodnotfound], OErrors, AErrors], Errors).
type(Context, A, invoke(ObjExpr, _, ArgExpr), Result, Errors):-
  type(Context, A, ObjExpr, ObjClass, OErrors),
  type(Context, A, ArgExpr, ArgClass, AErrors),
  (ObjClass = bottom; ArgClass = bottom),
  Result = bottom, append([OErrors, AErrors], Errors).

type(Context, A, getfield(ObjExpr, FName), FType, Errors):-
  contextParents(Context, Parents),
  contextFieldDescs(Context, Fields),
  type(Context, A, ObjExpr, ObjClass, Errors),
  getField(Parents, ObjClass, FName, Fields, fieldsig(_, FName, FType)).
type(Context, A, getfield(ObjExpr, FName), bottom, Errors):-
  contextParents(Context, Parents),
  contextFieldDescs(Context, Fields),
  type(Context, A, ObjExpr, ObjClass, OErrors),
  not(getField(Parents, ObjClass, FName, Fields, fieldsig(_, FName, _))),
  Errors = [errfieldnotfound|OErrors].

type(_, arg(VarName, Result), var(VarName), Result, _).

type(Context, A, cast(Expr, ClassName), ClassName, Errors):-
  type(Context, A, Expr, ClassName, Errors).
type(Context, A, cast(Expr, ParentClassName), ParentClassName, Errors):-
  contextParents(Context, Parents),
  type(Context, A, Expr, EClassName, Errors),
  isAncestor(Parents, EClassName, ParentClassName).
type(Context, A, cast(Expr, ChildClassName), ChildClassName, Errors):-
  contextParents(Context, Parents),
  type(Context, A, Expr, EClassName, EErrors),
  isAncestor(Parents, ChildClassName, EClassName),
  Errors = [errdowncast|EErrors].
type(Context, A, cast(Expr, OtherClassName), bottom, Errors):-
  contextParents(Context, Parents),
  type(Context, A, Expr, EClassName, EErrors),
  not(EClassName = OtherClassName),
  not(isAncestor(Parents, EClassName, OtherClassName)),
  not(isAncestor(Parents, OtherClassName, EClassName)),
  Errors = [errcrosscast|EErrors].

