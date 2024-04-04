-module(minsem).
-compile(nowarn_export_all).
-compile(export_all).

% This module implements a minimal but full implementation for the semantic subtyping framework for the limited type algebra 
% 
% t = true | {t, t} | !t | t & t
% 
% There are different ways of allowing t to be an infinite regular tree.
% In a strict language, lazy equations or an explicit type constructor for type unfolding could be used.
% We use lazy equations.
% The Any type is an equation fulfilling:  Any = true | {Any, Any}.
% There is no bottom symbol. 
% A syntactical shortcut for the negation of true is: false := !true
% Bottom is defined in terms of Any and negation: Bottom := !Any
% A valid corecursive non-empty example type would be: X := true | {true, {true, X & X2}} with X2 := true | {X2, X2}
% In general, a type t consisits of an corecursive equation system with i equations:
%   X1 = ...
%   X2 = ...
%   ...
%   Xi = ...
% One way of producing an empty (corecursive) type could be: X := {X, X}

% A type is either a lazy reference represented as a function to be evaluated
% or a disjoint union of flags and products.
% The flag and product types are represented as a two-layered DNF.
% The outer layer contains type variables, the inner layer contains the DNF of the type at hand.
% These disjoint unions will be denoted by 'U.' instead of the regular union 'U' to 
% highlight that negations in one union will not leak into the other union,
% e.g. true ∉ !{true, true}.
% Alternatively, it could be viewed as each component is always intersected implicitly with its top type,
% e.g true ∉ !{true, true} & {Any, Any}.
%
% The generic interface is defined by the top-level record ty() and its atom component types product() and flag().
-type ty() :: ty_ref() | ty_rec().
-type product() :: {ty_ref(), ty_ref()}.
-type flag() :: true.

% ty_ref, ty_rec are implementation specific
-record(ty, {flag :: dnf(flag()), product :: dnf(product())}).
-type ty_ref () :: fun(() -> ty()).
-type ty_rec () :: #ty{}.

% Since Erlang does not support memoization natively, we need to track visiting left-hand side equation references manually in a set
-type memo() :: #{}.

% A DNF<X> is a disjunction represented as a list of coclauses.
% A coclause is represented as a pair of positive and negative Xs components in two lists.
% An example DNF of products: [{[{true*, true*}], []}, {[], [{false*, true*}]}] == {true, true} | !{false, true}
% Note that inside the products, true* and false* are actually ty_ref() again and unfold to a full ty_rec().
-type dnf(Atom) :: [{[Atom], [Atom]}]. 

% Constructors for flags and products at the DNF level
-spec flag() -> dnf(true).
flag() -> [{[true], []}].

-spec negated_flag() -> dnf(true).
negated_flag() -> [{[], [true]}].

-spec product(ty(), ty()) -> dnf(product()).
product(A, B) -> [{[{A, B}], []}].

-spec product(product()) -> dnf(product()).
product(P) -> [{[P], []}].

-spec negated_product(product()) -> dnf(product()).
negated_product(P) -> [{[], [P]}].

% We can now define the corecursive Top type:
% Any = true U. {Any, Any}
-spec any() -> ty().
any() -> fun Any() -> #ty{
    % Notice that we introduce the equation name 'Any' (the constant function reference) and 
    % use it in the right-hand side of the equation in the product constructor
    % The return type of this function is strictly speaking a new equation
    % Luckily, erlang hashes the (AST) same closures to the same hash value
    % so it won't happen that a type equation is created when an "old" type equation already memoized is expected
    % e.g. X = {true, true} & {true, true} -> should be hashed as X = {true, true}, and not a new X2 = {true, true} & {true, true} with X2 /= X
    % Otherwise, we would need to implement hashing module alpha renaming ourselves
    flag = flag(),
    product = product(Any, Any)
  } end.

% To define the empty type, 
% we need to define the corecursive operator: negation.
% !Any = false U. !{Any, Any}
-spec empty() -> ty().
empty() -> neg(any()).

% A corecursive function consists of both a regular definition
% and its codefinition.
% A codefinition is always applied 
% when the left-hand side of an equation is encountered the second time.
% The codefinition describes the corecursive case.
% Since the Erlang runtime does not support corecursive functions,
% we need to track function calls explicitly in a memoization set.
% The Erlang manual mentions that a maps-backed set 
% is the most efficient set implementation up to date for our use case.
-spec neg(ty_ref()) -> ty_ref().
neg(Ty) -> 
  neg(Ty, #{}).

-spec neg
(ty_ref(), memo()) -> ty_ref(); % this branch is similar for all corecursive functions TODO abstract?
(ty_rec(), memo()) -> ty_rec().
% if Ty is a reference, memoization needs to be checked
neg(Ty, Memo) when is_function(Ty) -> 
  case Memo of
    % given a memoized type, use the codefinition; in this case the new equation left-hand side
    % note: depending on the datastructure this branch will never be taken
    % e.g. in our dnf implementation, a type A is negated by 
    % just changing its position from {[A], []} to {[], [A]} in a coclause.
    % If negation is not again applied on A, the corecursive case is never triggered
    % As we are using a map anyway, we add the corecursive case to the memoization set for convenience
    #{Ty := NewTy} -> NewTy;
    _ -> 
      % Wrap the new negated type in a new reference,
      % 'unfold' the type, memoize, and negate.
      % This new reference NewTy is a neq corecursive equation.
      % Every function in general that handles a ty() is corecursive.
      % Will this new reference always result in a new equation? No. (see comment on the any() function)
      fun NewTy() -> neg(Ty(), Memo#{Ty => NewTy}) end
  end;
% negation delegates the operation onto its components
% since the components are made of a two layered DNF structure, 
% we use a generic vdnf traversal and specific dnf traverals for flags and products
% the variable negation function is supplied with a function which knows how to negate its components
neg(#ty{flag = F, product = Prod}, M) -> 
  FlagDnf = negate_flag_dnf(F, M),
  ProductDnf = negate_product_dnf(Prod, M),
  #ty{flag = FlagDnf, product = ProductDnf}.


-spec negate_flag_dnf(dnf(flag()), memo()) -> dnf(flag()).
negate_flag_dnf(Dnf, _Memo) -> % memo not needed as signs are flipped
  % similar to the variable case, for each coclause (Pvars, Nvars), we flip the atom signs
  % for two flipped coclauses, we intersect them
  dnf(Dnf, {fun(P, N) -> 
      [X | Xs] = [negated_flag() || true <- P] ++ [flag() || true <- N],
      lists:foldl(fun(E, Acc) -> union_dnf(E, Acc) end, X, Xs)
    end, fun(Dnf1, Dnf2) -> intersect_dnf(Dnf1(), Dnf2()) end}).

-spec negate_product_dnf(dnf(product()), memo()) -> dnf(product()).
negate_product_dnf(Dnf, _Memo) -> % memo not needed as signs are flipped
  dnf(Dnf, {fun(P, N) -> 
      [X | Xs] = [negated_product(T) || T <- P] ++ [product(T) || T <- N],
      lists:foldl(fun(E, Acc) -> union_dnf(E, Acc) end, X, Xs)
    end, fun(Dnf1, Dnf2) -> intersect_dnf(Dnf1(), Dnf2()) end}).

% intersection and union for ty, corecursive
% Here, we have two operands for memoization. 
% We memoize the intersection operation Ty & Ty2 as {Ty, Ty2}
% and the result equation as NewTy
% Whenever the intersection operation on Ty & Ty2 is encountered
% we return the memoized result NewTy
% In our implementation, the corecursive case is never triggered
intersect(Ty, Ty2) -> intersect(Ty, Ty2, #{}).
union(Ty, Ty2) -> union(Ty, Ty2, #{}).

intersect(Ty, Ty2, Memo) when is_function(Ty), is_function(Ty2) -> 
  case Memo of #{Ty := NewTy} -> error(todo),NewTy;
    _ -> fun NewTy() -> intersect(Ty(), Ty2(), Memo#{{Ty, Ty2} => NewTy}) end
  end;
intersect(#ty{flag = F1, product = P1}, #ty{flag = F2, product = P2}, _Memo) ->
  #ty{flag = intersect_dnf(F1, F2), product = intersect_dnf(P1, P2)}.

union(Ty, Ty2, Memo) when is_function(Ty) -> 
  case Memo of #{Ty := NewTy} -> error(todo), NewTy;
    _ -> fun NewTy() -> union(Ty(), Ty2(), Memo#{{Ty, Ty2} => NewTy}) end
  end;
union(#ty{flag = F1, product = P1}, #ty{flag = F2, product = P2}, _Memo) ->
  #ty{flag = union_dnf(F1, F2), product = union_dnf(P1, P2)}.


% lists:uniq is very important here
% equations which differ produce a new type which is not memoized, yet equivalent to a previously memoized type
% e.g. (Any, Any) & (Any, Any) should be represented as (Any, Any)
% Erlang is then able to hash two closures to the same value
union_dnf(A, B) -> lists:uniq(A ++ B). 
intersect_dnf(A, B) -> [{lists:uniq(P1 ++ P2), lists:uniq(N1 ++ N2)} || {P1, N1} <- A, {P2, N2} <- B].

% flag/product dnf line
dnf([{Pos, Neg}], {Process, _Combine}) ->
  Process(Pos, Neg);
dnf([{Pos, Neg} | Cs], F = {Process, Combine}) ->
  Res1 = fun() -> Process(Pos, Neg) end,
  Res2 = fun() -> dnf(Cs, F) end,
  Combine(Res1, Res2).

% now for the main part, emptyness checking
is_empty(Ty) -> 
  is_empty(Ty, #{}).

is_empty(Ty, Memo) when is_function(Ty) -> 
  case Memo of
    % use the codefinition for a memoized type: it is assumed to be empty
    #{Ty := true} -> true;
    _ -> 
      is_empty(Ty(), Memo#{Ty => true})
  end;
is_empty(#ty{flag = FlagDnf, product = ProdDnf}, Memo) ->
  is_empty_flag(FlagDnf, Memo)
  and is_empty_prod(ProdDnf, Memo).

% flag emptyness, empty iff:
%  * (variable occurs in both pos and neg position) or (true in N)
% We can ignore variables for emptyness checks (after pos neg elimination) because t & alpha empty iff t empty
is_empty_flag(FlagDnf, _Memo) -> % memo not needed, no corecursive components
  dnf(FlagDnf, {fun(_Pos, Neg) -> not sets:is_empty(sets:from_list(Neg)) end, fun(R1, R2) -> R1() and R2() end}).

% product emptyness, empty iff:
%  * (variable occurs in both pos and neg position) or product dnf empty
is_empty_prod(Dnf, Memo) ->
  dnf(Dnf, {
    fun(Pos, Neg) -> 
      BigP = big_intersect(Pos),
      phi(pi1(BigP), pi2(BigP), Neg, Memo)
    end, 
    fun(R1, R2) -> R1() and R2() end
  }).

pi1({Ty, _}) -> Ty.
pi2({_, Ty}) -> Ty.

big_intersect([]) -> {any(), any()};
big_intersect([X]) -> X;
big_intersect([{Ty1, Ty2}, {Ty3, Ty4} | Xs]) -> 
  NewL = intersect(Ty1, Ty3),
  NewR = intersect(Ty2, Ty4),
  big_intersect([{NewL, NewR} | Xs]).

% Φ(S1 , S2 , ∅ , T1 , T2) = (S1<:T1) or (S2<:T2)
% Φ(S1 , S2 , N ∪ {T1, T2} , Left , Right) = Φ(S1 , S2 , N , Left | T1 , Right) and Φ(S1 , S2 , N , Left , Right | T2)
phi(S1, S2, N, Memo) -> 
  phi(S1, S2, N, empty(), empty(), Memo).
phi(S1, S2, [], T1, T2, Memo) ->
  Int1 = intersect(S1, neg(T1)),
  Res1 = is_empty(Int1, Memo),
  Res2 = is_empty(intersect(S2, neg(T2)), Memo),
  Res1 or Res2;
phi(S1, S2, [Ty | N], Left, Right, Memo) ->
  T1 = pi1(Ty),
  T2 = pi2(Ty),
  U = union(Left, T1),
  Res = (phi(S1, S2, N, U, Right, Memo)),
  Res2 = (phi(S1, S2, N , Left, union(Right,T2), Memo)),
  Res and Res2.
  



-ifdef(TEST).
-include_lib("eunit/include/eunit.hrl").

usage_test() ->
  A = any(),
  io:format(user,"Any: ~p (~p) ~n~p~n", [A, erlang:phash2(A), A()]),
  
  % negation:
  Aneg = neg(A),
  io:format(user,"Empty: ~p~n", [Aneg]),
  io:format(user,"Empty unfolded: ~p~n", [Aneg()]),

  %intersection of same recursive equations
  Ai = intersect(A, A),
  io:format(user,"Any & Any: ~p~n", [{Ai, Ai()}]),

  % % double negation
  Anegneg = neg(neg(A)),
  io:format(user,"Any: ~p~n", [Anegneg]),
  io:format(user,"Any unfolded: ~p~n", [Anegneg()]),

  % % We cannot trust the name generated for the corecursive equations (Erlang funs):
  F1 = io_lib:format("~p", [Aneg]),
  F2 = io_lib:format("~p", [Anegneg]),
  true = (F1 =:= F2),
  false = (Aneg =:= Anegneg),

  % is_empty
  io:format(user,"Any is empty: ~p~n", [is_empty(A)]),
  false = is_empty(A),
  io:format(user,"Empty is empty: ~p~n", [is_empty(Aneg)]),
  true = is_empty(Aneg),

  % define a custom any type
  X = fun Z() -> #ty{
                    flag = flag(), 
                    product = product(Z, Z)
  } end,
  % it's different from the any equation return by any()
  true = X /= any(),
  io:format(user,"Any (custom) is empty: ~p~n", [is_empty(X)]),
  false = is_empty(X),
  ok.

-endif.
