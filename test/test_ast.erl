-module(test_ast).

% @doc This file defines the λ_erl AST.
% It is used to generate types for testing.

-compile(nowarn_export_all).
-compile(export_all).


-type ty() ::
    ty_atom() 
  | ty_union() | ty_intersection() | ty_negation()
  | ty_tuple().
  % | ty_fun() | ty_var()
  % | ty_mu() 
  % | ty_bottom() | ty_any() .
   
-type ty_atom() :: {atom, atom()} | {any_atom}.

% polymorphic calculus with type variables
-type ty_var()     :: {var, ty_varname()}.
-type ty_varname() :: atom().

% recursive type
-type ty_mu()        :: {mu, ty_var(), ty()}.

-type ty_bottom() :: none.
-type ty_any() :: any.
-type ty_tuple()  :: {tuple, [ty()]}.
-type ty_fun()    :: {'fun', [ty()], ty()}.

-type ty_union()        :: {union, ty(), ty()}.
-type ty_intersection() :: {intersection, ty(), ty()}.
-type ty_negation()     :: {negation, ty()}.

atom() -> {any_atom}.
atom(Atom) -> {'atom', Atom}.

t([X, Y]) -> {'tuple', [X, Y]}.

% type constructors
f(X, Y) when is_list(X) -> error(not_yet_supported); %{'fun', X, Y};
f(X, Y) -> {'fun', [X], Y}.

v(VariableName) -> {var, VariableName}.


mu(Var, Ty) -> {mu, Var, Ty}.

any() -> any.
none() -> none.

u(X, Y) -> {union, X, Y}.
u([]) -> none();
u([X]) -> X;
u([X,Y | T]) -> {union, X, u([Y | T])}.

i(X, Y) -> {intersection, X, Y}.
i([]) -> any();
i([X]) -> X;
i([X,Y | T]) -> {intersection, X, i([Y | T])}.

n(X) -> {negation, X}.
d(X, Y) -> {difference, X, Y}.