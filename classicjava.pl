
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

classListTreeCheck2([], Classes, Outlist):-Outlist=Classes.

% a parent is:
% parent(childClassName, parentClassName)


% classListTreeCheck2 : List(class), List(parent), List(parent)
classListTreeCheck2([class(CName, PName, _)|Rest], Classes, Outlist):-
  member(parent(PName, _), Classes),
  classListTreeCheck2(Rest, [parent(CName, PName)|Classes], Outlist).



