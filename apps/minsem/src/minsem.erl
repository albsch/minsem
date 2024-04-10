-module(minsem).
-compile(nowarn_export_all).
-compile(export_all).

% This module implements a minimal but full implementation for the semantic subtyping framework for
% the limited type algebra
%
% t = true | {t, t} | !t | t & t
%
% There are different ways of allowing t to be an infinite regular tree.
% In a strict language, lazy equations or an explicit type constructor for type unfolding could be used.
% We use lazy equations.
%
% The Any type is an equation fulfilling:  Any = true | {Any, Any}.
% There is no bottom symbol.
% A syntactical shortcut for the negation of true is: false := !true
% Bottom is defined in terms of Any and negation: Bottom := !Any
%
% A valid corecursive non-empty example type would be:
%
% X := true | {true, {true, X & X2}} with X2 := true | {X2, X2}
%
% In general, a type t consisits of an corecursive equation system with i equations:
%   X1 = ...
%   X2 = ...
%   ...
%   Xi = ...
% One way of producing an empty (corecursive) type could be: X := {X, X}
%
% A type is either a lazy reference represented as a function to be evaluated
% or a disjoint union of flags and products.
% The flag and product types are represented as a DNF.
% These disjoint unions will be denoted by 'U.' instead of the regular union 'U' to
% highlight that negations in one union will not leak into the other union,
% e.g. true ∉ !{true, true}.
% Alternatively, it could be viewed as each component is always intersected implicitly with its top type,
% e.g true ∉ !{true, true} & {Any, Any}.
%
% ??? Where is the U. in the examples above? What does it mean for a negation to leak into the union.
%
% The generic interface is defined by the top-level record ty() and its atom component types product() and flag().
-type ty() :: ty_ref() | ty_rec().
-type product() :: {ty_ref(), ty_ref()}. % ??? I would expect this to be {ty(), ty()}
-type flag() :: true.

% ty_ref, ty_rec are implementation specific
-record(ty, {flag = negated_flag() :: dnf(flag()), product :: dnf(product())}). % by default, flag is set to empty
-type ty_ref () :: fun(() -> ty()).  % ??? does it make sense to return another ty_ref() here?
-type ty_rec () :: #ty{}.

-record(ty_, {flag = negated_flag() :: dnf(flag_()), product :: dnf(product_())}).
-type ty_() :: fun(() -> ty_rec_()).
-type ty_rec_ () :: #ty_{}.
-type product_() :: {ty_(), ty_()}.
-type flag_() :: true.


% Since Erlang does not support memoization natively, we need to track visiting left-hand side
% equation references manually in a set
-type memo() :: #{}.

% A DNF<X> is a disjunction represented as a list of lines.
% A line is represented as a pair of positive and negative Xs components in two lists.
% An example DNF of products: [{[{true*, true*}], []}, {[], [{false*, true*}]}] == {true, true} | !{false, true}
% Note that inside the products, true* and false* are actually ty_ref() again and unfold to a full ty_rec().
% It is important for termination to choose the DNF representation appropriately. ??? termination of what?
% Termination is valid only modulo or up-to alpha-equivalence and type equivalency up to boolean
% tautologies (e.g. t and t&t)
%
% ??? what alpha-equivalence? there are no variables so far. From below, I think you mean
% "equivalence of function references"
%
% Alpha-equivalence is handled by the hashing mechanism of Erlang for Erlang funs.
% Boolean tautology equivalence is handled by the DNF representation.
% To ensure termination, the representation should share (some) tautologically equivalent boolean
% combinations.
% It seems sufficient for termination to model the positive and negative parts of the DNF as a set
% instead of a list.
-type dnf(Atom) :: [{[Atom], [Atom]}].

% Constructors for flags and products at the DNF level
-spec flag() -> dnf(true).
flag() -> [{[true], []}].

-spec negated_flag() -> dnf(true).
negated_flag() -> [{[], [true]}].

-spec product(ty(), ty()) -> dnf(product()). % According to the definition of product, {ty(), ty()} is not a valid product
product(A, B) -> [{[{A, B}], []}].

-spec product(product()) -> dnf(product()).
product(P) -> [{[P], []}].

-spec negated_product(product()) -> dnf(product()).
negated_product(P) -> [{[], [P]}].

-spec ty(dnf(flag()), dnf(product())) -> ty_rec().
ty(Flag, Product) -> #ty{flag = Flag, product = Product}.

-spec ty_flag(dnf(flag())) -> ty_rec().
ty_flag(Flag) -> #ty{flag = Flag, product = product(empty(), empty())}.

-spec ty_product(dnf(product())) -> ty_rec().
ty_product(Product) -> #ty{flag = negated_flag(), product = Product}.

% We can now define the corecursive Top type:
% Any = true U. {Any, Any}
-spec any() -> ty().
any() -> fun Any() -> #ty{
    % Notice that we introduce the equation name 'Any' (the function reference) and
    % use it in the right-hand side of the equation in the product constructor
    % The return value of this function is strictly speaking a new equation (a frfesh function reference)
    % Luckily, erlang hashes the same closures (AST with its bound values) to the same hash value
    % ??? should this be the free values of the closure that are hashed together with the AST?
    % so it won't happen that a type equation is created when an "old" type equation already memoized is expected
    % e.g. X = {true, true} & {X, X} should be hashed to the same value as another equation X' = {true, true} & {X', X'}.
    % Otherwise, the algorithm does not terminate and we would need to implement hashing ourselves,
    % to capture alpha-equivalency in the hash
    flag = flag(),
    product = product(Any, Any)
  } end.

% To define the empty type,
% we need to define the corecursive operator: negation.
% !Any = false U. !{Any, Any}
-spec empty() -> ty().
empty() -> negate(any()).

% A corecursive function consists of both a regular definition
% and its codefinition.
% A codefinition is always applied
% when the left-hand side of an equation is encountered the second time.
% The codefinition describes the corecursive case.
% Since the Erlang runtime does not support corecursive functions,
% we need to track function calls explicitly in a memoization set.
% The Erlang manual mentions that a maps-backed set
% is the most efficient set implementation up to date for our use case.
% We use a generic function 'corec_ref/3' for corecursive function application.
% This definition is used to initiate a corecursive negation
-spec negate(ty_ref()) -> ty_ref().
negate(Ty) -> corec_ref(Ty, #{}, fun negate/2).

% we define two corecursive helper operators:
% one that introduces new equations and one for constant term memoizations
corec_ref(Corec, Memo, Continue) -> corec(Corec, Memo, Continue, reference).
corec_const(Corec, Memo, Continue, Const) -> corec(Corec, Memo, Continue, {const, Const}).

% A generic corecursion operator for type operators negation/union/intersection
% and other constant corecursive functions (is_empty)
% We track the codefinition inside the memoization map
% If a corecursive call is encountered, use the mapped codefinition in the map
% The operator provides two ways of specifying memoization:
% a constant term memoization (used for e.g. is_empty, Boolean return)
% and a new equation reference memoization (used for e.g. type operators)
-spec corec
([ty_ref()], memo(), fun(([ty_rec()], memo()) -> ty_rec()), reference) -> ty_ref();
( ty_ref() , memo(), fun(( ty_rec() , memo()) -> ty_rec()), reference) -> ty_ref();
([ty_ref()], memo(), fun(([ty_rec()], memo()) -> ty_rec()), {const, Const}) -> Const;
( ty_ref() , memo(), fun(( ty_rec() , memo()) -> ty_rec()), {const, Const}) -> Const.
corec(Corec, Memo, Continue, Type) ->
  case Memo of
    % given a memoized type, use the codefinition; in this case the new equation left-hand side
    % note: depending on the datastructure this branch will never be taken
    % e.g. in our dnf implementation, a type A is negated by
    % just changing its position from {[A], []} to {[], [A]} in a line.
    % If the operation is not again applied on A, the corecursive case is never triggered
    % As we are using a map anyway, we add the corecursive case to the memoization set for convenience
    #{Corec := Codefinition} -> Codefinition;
    _ ->
      % to allow for multiple arguments, Corec can be supplied as a list of references to unfold
      % ??? where is this needed?
      UnfoldMaybeList = fun(L) when is_list(L) -> [T() || T <- L]; (L) -> L() end,
      case Type of
        % 'unfold' the input(s), memoize, and apply Continue.
        % This new reference NewRef is a new corecursive equation.
        % Every function in general that handles a ty() is corecursive.
        % Will this new reference always result in a new equation? No. (see comment on the any() function)
        reference -> fun NewRef() -> Continue(UnfoldMaybeList(Corec), Memo#{Corec => NewRef}) end;
        % 'unfold' the input(s), memoize the constant term, and apply Continue.
        {const, Const} -> Continue(UnfoldMaybeList(Corec), Memo#{Corec => Const})
      end
  end.


-spec negate(ty_ref(), memo()) -> ty_ref(); (ty_rec(), memo()) -> ty_rec().
% This definition is used to continue a (nested) corecursive negation
negate(Ty, Memo) when is_function(Ty) -> corec_ref(Ty, Memo, fun negate/2);
% Negation delegates the operation onto its components.
% Since the components are made of a DNF structure,
% we use a generic dnf traversal for flags and products
negate(#ty{flag = F, product = Prod}, M) ->
  FlagDnf = negate_flag_dnf(F, M),
  ProductDnf = negate_product_dnf(Prod, M),
  #ty{flag = FlagDnf, product = ProductDnf}.

-spec negate_flag_dnf(dnf(flag()), memo()) -> dnf(flag()).
negate_flag_dnf(Dnf, _Memo) -> % memo not needed as signs are flipped
  % for each line (Pos, Neg), we flip the atom signs
  % for two flipped lines, we intersect them
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
% In our implementation, the corecursive case is never triggered ??? why
-spec intersect(ty_ref(), ty_ref()) -> ty_ref().
intersect(Ty, Ty2) -> corec_ref([Ty, Ty2], #{}, fun cintersect/2).
-spec union(ty_ref(), ty_ref()) -> ty_ref().
union(Ty, Ty2) -> corec_ref([Ty, Ty2], #{}, fun cunion/2).

% wrapper functions for single argument type operators
-spec cintersect ([ty_ref()], memo()) -> ty_ref(); ([ty_rec()], memo()) -> ty_rec().
cintersect([Ty, Ty2], Memo) when is_function(Ty), is_function(Ty2) -> corec_ref([Ty, Ty2], Memo, fun cintersect/2);
cintersect([#ty{flag = F1, product = P1}, #ty{flag = F2, product = P2}], _Memo) ->
  #ty{flag = intersect_dnf(F1, F2), product = intersect_dnf(P1, P2)}.

-spec cunion ([ty_ref()], memo()) -> ty_ref(); ([ty_rec()], memo()) -> ty_rec().
cunion([Ty, Ty2], Memo) when is_function(Ty), is_function(Ty2) -> corec_ref([Ty, Ty2], Memo, fun cunion/2);
cunion([#ty{flag = F1, product = P1}, #ty{flag = F2, product = P2}], _Memo) ->
  #ty{flag = union_dnf(F1, F2), product = union_dnf(P1, P2)}.

% lists:uniq is very important here
% equations which differ produce a new type which is not memoized, yet equivalent to a previously memoized type
% e.g. (Any, Any) & (Any, Any) should be represented as (Any, Any)
% Erlang is then able to hash two closures to the same value
-spec union_dnf(dnf(Ty), dnf(Ty)) -> dnf(Ty).
union_dnf(A, B) -> lists:uniq(A ++ B).
-spec intersect_dnf(dnf(Ty), dnf(Ty)) -> dnf(Ty).
intersect_dnf(A, B) -> [{lists:uniq(P1 ++ P2), lists:uniq(N1 ++ N2)} || {P1, N1} <- A, {P2, N2} <- B].

% flag/product dnf line
-spec dnf(dnf(Atom), {fun(([Atom], [Atom]) -> Result), fun((fun(() -> Result), fun(() -> Result)) -> Result)}) -> Result.
dnf([{Pos, Neg}], {Process, _Combine}) -> Process(Pos, Neg);
dnf([{Pos, Neg} | Cs], F = {Process, Combine}) ->
  Res1 = fun() -> Process(Pos, Neg) end,
  Res2 = fun() -> dnf(Cs, F) end,
  Combine(Res1, Res2).

% now for the main part, emptyness checking
-spec is_empty(ty_ref()) -> boolean().
is_empty(Ty) ->
  corec_const(Ty, #{}, fun is_empty/2, true).

-spec is_empty(ty_ref(), memo()) -> boolean(); (ty_rec(), memo()) -> boolean().
is_empty(Ty, Memo) when is_function(Ty) -> corec_const(Ty, Memo, fun is_empty/2, true);
is_empty(#ty{flag = FlagDnf, product = ProdDnf}, Memo) ->
  % 'and' does not short-circuit. ??? why don't you use andalso?
  % Usually, if non-emptyness arises from a non-empty flag, we don't need to descend into the
  % corecursive product part.
  % Algorithm still terminates because of memoization (Erlang-specific hashing of fun values)
  % and appropriate DNF representation.
  is_empty_flag(FlagDnf, Memo) and is_empty_prod(ProdDnf, Memo).

-spec is_empty_flag(dnf(flag()), memo()) -> boolean().
% flag emptyness, empty iff: (true in N)
is_empty_flag(FlagDnf, _Memo) -> % memo not needed, no corecursive components
  dnf(FlagDnf, {fun(_Pos, Neg) -> not sets:is_empty(sets:from_list(Neg)) end, fun(R1, R2) -> R1() and R2() end}).

-spec is_empty_prod(dnf(product()), memo()) -> boolean().
% product emptyness, empty iff: product dnf empty
is_empty_prod(Dnf, Memo) ->
  dnf(Dnf, {
    fun(Pos, Neg) ->
      % intersect all positive products, and execute full tree exploration phi
      {Ty1, Ty2} = big_intersect(Pos),
      phi(Ty1, Ty2, Neg, Memo)
    end,
    fun(R1, R2) -> R1() and R2() end
  }).

-spec big_intersect([product()]) -> product().
big_intersect([]) -> {any(), any()};
big_intersect([X]) -> X;
big_intersect([{Ty1, Ty2}, {Ty3, Ty4} | Xs]) ->
  big_intersect([{intersect(Ty1, Ty3), intersect(Ty2, Ty4)} | Xs]).

% Φ(S1 , S2 , ∅ , T1 , T2) = (S1<:T1) or (S2<:T2)
% Φ(S1 , S2 , N ∪ {T1, T2} , Left , Right) = Φ(S1 , S2 , N , Left | T1 , Right) and Φ(S1 , S2 , N , Left , Right | T2)
-spec phi(ty_ref(), ty_ref(), [ty_ref()], memo()) -> boolean().
phi(S1, S2, N, Memo) -> phi(S1, S2, N, empty(), empty(), Memo).

-spec phi(ty_ref(), ty_ref(), [ty_ref()], ty_ref(), ty_ref(), memo()) -> boolean().
phi(S1, S2, [], T1, T2, Memo) ->
  is_empty(intersect(S1, negate(T1)), Memo) or is_empty(intersect(S2, negate(T2)), Memo);
phi(S1, S2, [{T1, T2} | N], Left, Right, Memo) ->
  phi(S1, S2, N, union(Left, T1), Right, Memo) and phi(S1, S2, N , Left, union(Right,T2), Memo).




-ifdef(TEST).
-include_lib("eunit/include/eunit.hrl").

usage_test() ->
  A = any(),
  io:format(user,"Any: ~p (~p) ~n~p~n", [A, erlang:phash2(A), A()]),

  % negation:
  Aneg = negate(A),
  io:format(user,"Empty: ~p~n", [Aneg]),
  io:format(user,"Empty unfolded: ~p~n", [Aneg()]),

  %intersection of same recursive equations
  Ai = intersect(A, A),
  io:format(user,"Any & Any: ~p~n", [{Ai, Ai()}]),

  % % double negation
  Anegneg = negate(negate(A)),
  io:format(user,"Any: ~p~n", [Anegneg]),
  io:format(user,"Any unfolded: ~p~n", [Anegneg()]),

  % % We cannot trust the name generated for the corecursive equations (Erlang funs):
  io:format(user,"Refs Aneg vs Anegneg: ~p vs ~p~nHashes Aneg vs Anegeg: ~p vs ~p~n", [Aneg, Anegneg, erlang:phash2(Aneg), erlang:phash2(Anegneg)]),
  F1 = io_lib:format("~p", [Aneg]),
  F2 = io_lib:format("~p", [Anegneg]),
  true = (F1 =:= F2),
  false = (Aneg =:= Anegneg),
  false = (erlang:phash2(Aneg) =:= erlang:phash2(Anegneg)),

  % is_empty
  io:format(user,"Any is empty: ~p~n", [is_empty(A)]),
  false = is_empty(A),
  io:format(user,"Empty is empty: ~p~n", [is_empty(Aneg)]),
  true = is_empty(Aneg),

  % define a custom any type
  X = fun Z() -> ty(flag(), product(Z, Z)) end,
  % it's different from the any equation return by any()
  true = X /= any(),
  io:format(user,"Any (custom) is empty: ~p~n", [is_empty(X)]),
  false = is_empty(X),

  % (X, (X, true)) where X = (X, true) | (true, true)
  JustTrue = fun() -> ty_flag(flag()) end,
  false = is_empty(JustTrue),
  RX = fun XX() -> ty_product( union_dnf(product(XX, JustTrue), product(JustTrue, JustTrue)) ) end,
  false = is_empty(RX),
  RXX = fun() ->
    InnerProd = fun() -> ty_product(product(RX, JustTrue)) end,
    ty_product(product(RX, InnerProd))
  end,
  false = is_empty(RXX),

  % interleaving corecursion
  % (true, A) where
  % A = (B, true) | (true, true)
  % B = (true, A)
  Ty = fun() ->
    fun A() ->
      TyB = fun B() -> ty_product(product(JustTrue, A)) end,
      ty_product( union_dnf(product(TyB, JustTrue), product(JustTrue, JustTrue)))
    end
  end,
  false = is_empty(Ty),

  % (true, A) where
  % A = (B, true)
  % B = (true, A)
  Ty2 = fun() ->
    fun A() ->
      TyB = fun B() -> ty_product(product(JustTrue, A)) end,
      ty_product( product(TyB, JustTrue) )
    end
  end,
  true = is_empty(Ty2),

  ok.

-endif.
