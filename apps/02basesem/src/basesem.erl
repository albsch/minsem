-module(basesem).
-compile(nowarn_export_all).
-compile(export_all).

% This module implements a base implementation for the semantic subtyping framework for the limited type algebra 
% 
% t = true | alpha | t -> t | {t, t} | !t | t & t
% 
% In addition to the minimal grammar, type variables and arrows are now allowed.
% 
% The generic interface is defined by the top-level record ty() and its atom component types product() and flag().
-type ty() :: ty_ref() | ty_rec().
-type product() :: {ty_ref(), ty_ref()}.
-type flag() :: true.

% arrows are now included in the type record
-type arrow() :: {arrow, ty_ref(), ty_ref()}.
-record(ty, {flag = negated_flag() :: dnf(flag()), product :: dnf(product()), arrow :: dnf(arrow())}). 
-type ty_ref () :: fun(() -> ty()).
-type ty_rec () :: #ty{}.
-type memo() :: #{}.

% dnf representation stays the same
-type dnf(Atom) :: [{[Atom], [Atom]}]. 

-spec flag() -> dnf(true).
flag() -> [{[true], []}].

-spec negated_flag() -> dnf(true).
negated_flag() -> [{[], [true]}].

-spec product(ty_ref(), ty_ref()) -> dnf(product()).
product(A, B) -> [{[{A, B}], []}].

% additional constructors for arrows
-spec arrow(ty(), ty()) -> dnf(arrow()).
arrow(A, B) -> [{[{arrow, A, B}], []}].

-spec arrow(arrow()) -> dnf(arrow()).
arrow(P) -> [{[P], []}].

-spec negated_arrow(arrow()) -> dnf(arrow()).
negated_arrow(P) -> [{[], [P]}].

-spec product(product()) -> dnf(product()).
product(P) -> [{[P], []}].

-spec negated_product(product()) -> dnf(product()).
negated_product(P) -> [{[], [P]}].

-spec ty(dnf(flag()), dnf(product()), dnf(arrow())) -> ty_rec().
ty(Flag, Product, Arrow) -> #ty{flag = Flag, product = Product, arrow = Arrow}.

% since we introduced arrows, we need to be able to define a type union with an empty arrow part
% a single arrow type (s -> t) is never empty. 
% The arrow which accepts any input and diverges (1 -> 0) is subset of any other arrow.
% We do not yet want to introduce neutral elements for any and empty kinds, so we need to 
% construct this "empty arrow part" ourselves with the appropriate line (arrow a intersected with its negation !a).
-spec ty_flag(dnf(flag())) -> ty_rec().
ty_flag(Flag) -> #ty{flag = Flag, product = product(empty(), empty()), arrow = empty_arrow()}.

% define the empty arrow DNF with an arrow S and its negation !S in the same line
-spec empty_arrow() -> dnf(arrow()).
empty_arrow() ->
  AnyArrowAtom = {arrow, empty(), any()},
  [{[AnyArrowAtom], [AnyArrowAtom]}].

-spec ty_product(dnf(product())) -> ty_rec().
ty_product(Product) -> #ty{flag = negated_flag(), product = Product, arrow = empty_arrow()}.

-spec ty_arrow(dnf(arrow())) -> ty_rec().
ty_arrow(A) -> #ty{flag = negated_flag(), product = product(empty(), empty()), arrow = A}.

% The top type is extended with the Any arrow:
% Any = true U. {Any, Any} U. (!Any -> Any)
% Any other arrow is included in the top arrow type (Empty -> t) for any t
-spec any() -> ty().
any() -> fun Any() -> #ty{
    flag = flag(),
    product = product(Any, Any),
    arrow = arrow(negate(Any), Any)
  } end.

% !Any = false U. !{Any, Any} U. !(!Any -> Any)
-spec empty() -> ty().
empty() -> negate(any()).

-spec negate(ty_ref()) -> ty_ref().
negate(Ty) -> corec_ref(Ty, #{}, fun negate/2).

corec_ref(Corec, Memo, Continue) -> corec(Corec, Memo, Continue, reference).
corec_const(Corec, Memo, Continue, Const) -> corec(Corec, Memo, Continue, {const, Const}).

-spec corec
([ty_ref()], memo(), fun(([ty_rec()], memo()) -> ty_rec()), reference) -> ty_ref();
( ty_ref() , memo(), fun(( ty_rec() , memo()) -> ty_rec()), reference) -> ty_ref();
([ty_ref()], memo(), fun(([ty_rec()], memo()) -> ty_rec()), {const, Const}) -> Const;
( ty_ref() , memo(), fun(( ty_rec() , memo()) -> ty_rec()), {const, Const}) -> Const.
corec(Corec, Memo, Continue, Type) ->
  case Memo of
    #{Corec := Codefinition} -> Codefinition;
    _ -> 
      UnfoldMaybeList = fun(L) when is_list(L) -> [T() || T <- L]; (L) -> L() end,
      case Type of 
        reference -> fun NewRef() -> Continue(UnfoldMaybeList(Corec), Memo#{Corec => NewRef}) end;
        {const, Const} -> Continue(UnfoldMaybeList(Corec), Memo#{Corec => Const})
      end
  end.


-spec negate(ty_ref(), memo()) -> ty_ref(); (ty_rec(), memo()) -> ty_rec().
negate(Ty, Memo) when is_function(Ty) -> corec_ref(Ty, Memo, fun negate/2);
negate(#ty{flag = F, product = Prod, arrow = Arrow}, M) -> 
  FlagDnf = negate_flag_dnf(F, M),
  ProductDnf = negate_product_dnf(Prod, M),
  ArrowDnf = negate_arrow_dnf(Arrow, M),
  #ty{flag = FlagDnf, product = ProductDnf, arrow = ArrowDnf}.

-spec negate_flag_dnf(dnf(flag()), memo()) -> dnf(flag()).
negate_flag_dnf(Dnf, _Memo) ->
  dnf(Dnf, {fun(P, N) -> 
      [X | Xs] = [negated_flag() || true <- P] ++ [flag() || true <- N],
      lists:foldl(fun(E, Acc) -> union_dnf(E, Acc) end, X, Xs)
    end, fun(Dnf1, Dnf2) -> intersect_dnf(Dnf1, Dnf2) end}).

-spec negate_product_dnf(dnf(product()), memo()) -> dnf(product()).
negate_product_dnf(Dnf, _Memo) -> 
  dnf(Dnf, {fun(P, N) -> 
      [X | Xs] = [negated_product(T) || T <- P] ++ [product(T) || T <- N],
      lists:foldl(fun(E, Acc) -> union_dnf(E, Acc) end, X, Xs)
    end, fun(Dnf1, Dnf2) -> intersect_dnf(Dnf1, Dnf2) end}).

% arrow dnf negation is similar to product dnf negation
-spec negate_arrow_dnf(dnf(arrow()), memo()) -> dnf(arrow()).
negate_arrow_dnf(Dnf, _Memo) -> 
  dnf(Dnf, {fun(P, N) -> 
      [X | Xs] = [negated_arrow(T) || T <- P] ++ [arrow(T) || T <- N],
      lists:foldl(fun(E, Acc) -> union_dnf(E, Acc) end, X, Xs)
    end, fun(Dnf1, Dnf2) -> intersect_dnf(Dnf1, Dnf2) end}).

-spec intersect(ty_ref(), ty_ref()) -> ty_ref().
intersect(Ty, Ty2) -> corec_ref([Ty, Ty2], #{}, fun cintersect/2).
-spec union(ty_ref(), ty_ref()) -> ty_ref().
union(Ty, Ty2) -> corec_ref([Ty, Ty2], #{}, fun cunion/2).

% component-wise arrow intersection and union
-spec cintersect ([ty_ref()], memo()) -> ty_ref(); ([ty_rec()], memo()) -> ty_rec().
cintersect([Ty, Ty2], Memo) when is_function(Ty), is_function(Ty2) -> corec_ref([Ty, Ty2], Memo, fun cintersect/2);
cintersect([#ty{flag = F1, product = P1, arrow = A1}, #ty{flag = F2, product = P2, arrow = A2}], _Memo) ->
  #ty{flag = intersect_dnf(F1, F2), product = intersect_dnf(P1, P2), arrow = intersect_dnf(A1, A2)}.

-spec cunion ([ty_ref()], memo()) -> ty_ref(); ([ty_rec()], memo()) -> ty_rec().
cunion([Ty, Ty2], Memo) when is_function(Ty), is_function(Ty2) -> corec_ref([Ty, Ty2], Memo, fun cunion/2);
cunion([#ty{flag = F1, product = P1, arrow = A1}, #ty{flag = F2, product = P2, arrow = A2}], _Memo) ->
  #ty{flag = union_dnf(F1, F2), product = union_dnf(P1, P2), arrow = union_dnf(A1, A2)}.

-spec union_dnf(dnf(Ty), dnf(Ty)) -> dnf(Ty).
union_dnf(A, B) -> lists:uniq(A ++ B). 
-spec intersect_dnf(dnf(Ty), dnf(Ty)) -> dnf(Ty).
intersect_dnf(A, B) -> [{lists:uniq(P1 ++ P2), lists:uniq(N1 ++ N2)} || {P1, N1} <- A, {P2, N2} <- B].

% flag/product/arrow dnf line
-spec dnf(dnf(Atom), {fun(([Atom], [Atom]) -> Result), fun((Result, Result) -> Result)}) -> Result.
dnf([{Pos, Neg}], {Process, _Combine}) -> Process(Pos, Neg);
dnf([{Pos, Neg} | Cs], F = {Process, Combine}) ->
  Res1 = Process(Pos, Neg),
  Res2 = dnf(Cs, F),
  Combine(Res1, Res2).

-spec is_empty(ty_ref()) -> boolean().
is_empty(Ty) -> 
  R = corec_const(Ty, #{}, fun is_empty/2, true),
  io:format(user,"Checking emptyness... ~p: ~p ~n", [erlang:phash2(Ty), R]),
  R.

-spec is_empty(ty_ref(), memo()) -> boolean(); (ty_rec(), memo()) -> boolean().
is_empty(Ty, Memo) when is_function(Ty) -> corec_const(Ty, Memo, fun is_empty/2, true);
is_empty(#ty{flag = FlagDnf, product = ProdDnf, arrow = ArrowDnf}, Memo) ->
  % add arrow emptyness check
  is_empty_flag(FlagDnf, Memo) and is_empty_prod(ProdDnf, Memo) and is_empty_arrow(ArrowDnf, Memo). 

-spec is_empty_flag(dnf(flag()), memo()) -> boolean().
is_empty_flag(FlagDnf, _Memo) ->
  dnf(FlagDnf, {fun(_Pos, Neg) -> not sets:is_empty(sets:from_list(Neg)) end, fun(R1, R2) -> R1 and R2 end}).

-spec is_empty_prod(dnf(product()), memo()) -> boolean().
is_empty_prod(Dnf, Memo) ->
  dnf(Dnf, {
    fun(Pos, Neg) -> 
      {Ty1, Ty2} = big_intersect(Pos),
      phi(Ty1, Ty2, Neg, Memo)
    end, 
    fun(R1, R2) -> R1 and R2 end
  }).

-spec is_empty_arrow(dnf(arrow()), memo()) -> boolean().
is_empty_arrow(Dnf, Memo) ->
  dnf(Dnf, {fun
      (Pos, Neg) -> 
        BigSTuple = lists:foldl(fun({arrow, S, _T}, Domain) -> union(S, Domain) end, empty(), Pos),
        is_empty_arrow_cont(BigSTuple, Pos, Neg, Memo)
    end, 
    fun(R1, R2) -> R1 and R2 end
  }).

is_empty_arrow_cont(_, _, [], _Memo) -> false;
is_empty_arrow_cont(BigS, Pos, [{arrow, Ts, T2} | N], Memo) ->
  (
    %% ∃ Ts-->T2 ∈ N s.t.
    %%    Ts is in the domain of the function
    %%    BigS is the union of all domains of the positive function intersections
    is_empty(intersect(Ts, negate(BigS)), Memo)
      and
      phi_arrow(Ts, negate(T2), Pos, Memo)
  )
  %% Continue searching for another arrow ∈ N
    or
    is_empty_arrow_cont(BigS, Pos, N, Memo).

-spec big_intersect([product()]) -> product().
big_intersect([]) -> {any(), any()};
big_intersect([X]) -> X;
big_intersect([{Ty1, Ty2}, {Ty3, Ty4} | Xs]) -> 
  big_intersect([{intersect(Ty1, Ty3), intersect(Ty2, Ty4)} | Xs]).

-spec phi(ty_ref(), ty_ref(), [ty_ref()], memo()) -> boolean().
phi(S1, S2, N, Memo) -> phi(S1, S2, N, empty(), empty(), Memo).

-spec phi(ty_ref(), ty_ref(), [ty_ref()], ty_ref(), ty_ref(), memo()) -> boolean().
phi(S1, S2, [], T1, T2, Memo) ->
  is_empty(intersect(S1, negate(T1)), Memo) or is_empty(intersect(S2, negate(T2)), Memo);
phi(S1, S2, [{T1, T2} | N], Left, Right, Memo) ->
  phi(S1, S2, N, union(Left, T1), Right, Memo) and phi(S1, S2, N , Left, union(Right,T2), Memo).

% phi from paper covariance and contravariance
% phi(T1, T2, P0, P+, P-)
phi_arrow(T1, T2, P, Memo) -> phi_arrow(T1, T2, P, empty(), any(), Memo).
phi_arrow(T1, T2, [], D , C, Memo) ->
  % (T1 <: D) or (C <: T2)
  is_empty(intersect(T1, negate(D)), Memo) or is_empty(intersect(C, negate(T2)));
% phi(T1, T2, P U {S1 --> S2}, D, C)
phi_arrow(T1, T2, [{arrow, S1, S2} | P], D, C, Memo) ->
  % phi(T1, T2, P, D, C&S2)
  phi_arrow(T1, T2, P, D, intersect(C, S2), Memo)
    and
    % phi(T1, T2, P, D|S1, C)
    phi_arrow(T1, T2, P, union(D, S1), C, Memo).


-ifdef(TEST).
-include_lib("eunit/include/eunit.hrl").

% usage_test() ->
%   A = any(),
%   io:format(user,"Any: ~p (~p) ~n~p~n", [A, erlang:phash2(A), A()]),
  
%   % negation:
%   Aneg = negate(A),
%   io:format(user,"Empty: ~p~n", [Aneg]),
%   io:format(user,"Empty unfolded: ~p~n", [Aneg()]),

%   %intersection of same recursive equations
%   Ai = intersect(A, A),
%   io:format(user,"Any & Any: ~p~n", [{Ai, Ai()}]),

%   % % double negation
%   Anegneg = negate(negate(A)),
%   io:format(user,"Any: ~p~n", [Anegneg]),
%   io:format(user,"Any unfolded: ~p~n", [Anegneg()]),

%   % % We cannot trust the name generated for the corecursive equations (Erlang funs):
%   io:format(user,"Refs Aneg vs Anegneg: ~p vs ~p~nHashes Aneg vs Anegeg: ~p vs ~p~n", [Aneg, Anegneg, erlang:phash2(Aneg), erlang:phash2(Anegneg)]),
%   F1 = io_lib:format("~p", [Aneg]),
%   F2 = io_lib:format("~p", [Anegneg]),
%   true = (F1 =:= F2),
%   false = (Aneg =:= Anegneg),
%   false = (erlang:phash2(Aneg) =:= erlang:phash2(Anegneg)),

%   % is_empty
%   io:format(user,"Any is empty: ~p~n", [is_empty(A)]),
%   false = is_empty(A),
%   io:format(user,"Empty is empty: ~p~n", [is_empty(Aneg)]),
%   true = is_empty(Aneg),

%   % define a custom any type
%   X = fun Z() -> ty(flag(), product(Z, Z), arrow(negate(Z), Z)) end,
%   % it's different from the any equation return by any()
%   true = X /= any(),
%   io:format(user,"Any (custom) is empty: ~p~n", [is_empty(X)]),
%   false = is_empty(X),

%   % (X, (X, true)) where X = (X, true) | (true, true)
%   JustTrue = fun() -> ty_flag(flag()) end,
%   false = is_empty(JustTrue),
%   RX = fun XX() -> ty_product( union_dnf(product(XX, JustTrue), product(JustTrue, JustTrue)) ) end,
%   false = is_empty(RX),
%   RXX = fun() -> 
%     InnerProd = fun() -> ty_product(product(RX, JustTrue)) end,
%     ty_product(product(RX, InnerProd))
%   end,
%   false = is_empty(RXX),

%   % interleaving corecursion
%   % (true, A) where 
%   % A = (B, true) | (true, true)
%   % B = (true, A)
%   Ty = fun() -> 
%     fun TyA() ->
%       TyB = fun() -> ty_product(product(JustTrue, TyA)) end,
%       ty_product( union_dnf(product(TyB, JustTrue), product(JustTrue, JustTrue)))
%     end
%   end,
%   false = is_empty(Ty),

%   % (true, A) where 
%   % A = (B, true)
%   % B = (true, A)
%   Ty2 = fun() -> 
%     fun TyA() ->
%       TyB = fun() -> ty_product(product(JustTrue, TyA)) end,
%       ty_product( product(TyB, JustTrue) )
%     end
%   end,
%   true = is_empty(Ty2),
%   ok.

arrow_test() ->
  True = fun() -> ty_flag(flag()) end,
  S = fun() -> ty_product(product(True, True)) end,
  T = fun() -> ty_product(product(True, fun() -> ty_product(product(True, True)) end)) end,
  U = fun() -> ty_product(product(fun() -> ty_product(product(True, True)) end, fun() -> ty_product(product(True, True)) end)) end,
  V = fun() -> ty_product(product(fun() -> ty_product(product(True, True)) end, True)) end,
  % [false = is_empty(intersect(T1, negate(T2))) || T1 <- [S, T, U, V], T2 <- [S, T, U, V], T1 /= T2],

  % (S-->T)&(S-->U) <: S-->T&U
  % true = is_empty(intersect(
  %     intersect(fun() -> ty_arrow(arrow(S, T)) end, fun() -> ty_arrow(arrow(S, U)) end), 
  %     negate(fun() -> ty_arrow(arrow(S, intersect(T, U))) end))
  % ),
  % (S-->U)&(T-->U) <: S|T-->U
  Left = intersect(fun() -> ty_arrow(arrow(S, U)) end, fun() -> ty_arrow(arrow(T, U)) end), 
  false = is_empty(Left),
  Right = fun() -> ty_arrow(arrow(union(S, T), U)) end,
  false = is_empty(Right),
  false = is_empty(negate(Right)),
  Ty = intersect(Left, negate(Right)),

  io:format(user,"===============~n", []),
  io:format(user,"Right: ~n~s~n", [print(negate(Right))]),
  % io:format(user,"~s~n", [print(Ty)]),
  % true = is_empty(Ty),
  % (S | T) --> (U | V)  <:> ( S -> U | V ) & ( T -> U | V )
  % (S | T) --> (U)  <:> ( S -> U ) & ( T -> U )
  % (S | T) --> (U | V)  <:> ( S -> U | V ) & ( T -> U | V )

  ok.



format_dnf_flag(Flag) -> 
  utils:sep_by(prettypr:text(" |"),
  [
    utils:sep_by(prettypr:text(" &"), 
      [ prettypr:text("flag") || P <- Pos] 
        ++
      [ prettypr:text("!flag") || N <- Neg] 
    )
    || {Pos, Neg} <- Flag]
).
format_dnf_product(Product, M) -> 
  FormattedProductsAndNext = [ {[ format_product(P, M) || P <- Pos] , [ format_product(N, M) || N <- Neg]} || {Pos, Neg} <- Product],
  
  ProductsStr = 
    utils:sep_by(prettypr:text(" |"),
    [
      utils:sep_by(prettypr:text(" &"), 
        [ P || {_, P} <- Pos] 
          ++
        [ prettypr:beside(prettypr:text("!"), N) || {_, N} <- Neg] 
      )
      || {Pos, Neg} <- FormattedProductsAndNext]
  ),
  Todo = [ [ T || {T, _} <- Pos] ++ [  T || {T, _} <- Neg] || {Pos, Neg} <- FormattedProductsAndNext],

  {lists:uniq(lists:flatten(Todo)), ProductsStr}.

format_dnf_arrow(Arrow, M) -> 
  FormattedArrowsAndNext = [ {[ format_arrow(P, M) || P <- Pos] , [ format_arrow(N, M) || N <- Neg]} || {Pos, Neg} <- Arrow],
  
  ArrowsStr = 
    utils:sep_by(prettypr:text(" |"),
    [
      utils:sep_by(prettypr:text(" &"), 
        [ P || {_, P} <- Pos] 
          ++
        [ prettypr:beside(prettypr:text("!"), N) || {_, N} <- Neg] 
      )
      || {Pos, Neg} <- FormattedArrowsAndNext]
  ),
  Todo = [ [ T || {T, _} <- Pos] ++ [  T || {T, _} <- Neg] || {Pos, Neg} <- FormattedArrowsAndNext],

  {lists:uniq(lists:flatten(Todo)), ArrowsStr}.

format_product({Ref1, Ref2}, M) ->
  {[Ref1, Ref2], utils:beside([prettypr:text("{"), prettypr:text(integer_to_list(erlang:phash2(Ref1))), prettypr:text(","), prettypr:text(integer_to_list(erlang:phash2(Ref2))), prettypr:text("}")])}.

format_arrow({arrow, Ref1, Ref2}, M) ->
  {[Ref1, Ref2], utils:beside([prettypr:text("("), prettypr:text(integer_to_list(erlang:phash2(Ref1))), prettypr:text(" -> "), prettypr:text(integer_to_list(erlang:phash2(Ref2))), prettypr:text(")")])}.

print(Ty) ->
  Str = format([], [Ty], #{}),
  prettypr:format(Str, 200).

format(Txt, [], M) -> 
  lists:foldl(fun(E, Acc) -> prettypr:beside(prettypr:break(E), Acc) end, prettypr:empty(), (Txt));
format(Txt, [R | Tys], M) ->
  case M of
    #{R := _} -> format(Txt, Tys, M);
    _ -> 
    #ty{flag = A, product = Product,arrow = Arrow} = R(),
    FlagStr = format_dnf_flag(A),
    {TxtP, ProductStr} = format_dnf_product(Product, M#{R => ok}),
    {TxtP2, ArrowStr} = format_dnf_arrow(Arrow, M#{R => ok}),
    
    NextTys = lists:uniq(Tys ++ TxtP ++ TxtP2),

    NewTy = utils:beside([
    prettypr:text(integer_to_list(erlang:phash2(R))),
    prettypr:break(prettypr:text(" := ")),
    prettypr:text("("),
    utils:sep_by(prettypr:text(" |"), 
      [
        utils:beside([prettypr:text("(flag & "), FlagStr, prettypr:text(")")]),
        utils:beside([prettypr:text("({Any, Any} & "), ProductStr, prettypr:text(")")]),
        utils:beside([prettypr:text("((Empty -> Any) & "), ArrowStr, prettypr:text(")")])
    ]),
    prettypr:text(")")
    ]),
    format([NewTy | Txt], NextTys, M#{R => ok})
  end.


variable_test() ->
  ok.
  % variable tests
  % (α × t) ∧ α !≤ ((1 × 1) × t)
  % α ∧ (α × t) ≤ α
  % (α → γ) ∧ (β → γ) ∼ (α∨β) → γ
  % ((α∨β) × γ) ∼ (α×γ) ∨ (β×γ)
  % (α×γ → δ1 ) ∧ (β×γ → δ2 ) ≤ ((α∨β) × γ) → δ1 ∨ δ2
  % 1 → 0 ≤ α → β ≤ 0 → 1
  % 1 ≤ ((α ⇒ β) ⇒ α) ⇒ α
  % nil × α ≤! (nil × ¬nil) ∨ (α × nil)
  % α1 → β1 ≤ ((α1 ∧α2 )→(β1 ∧β2 )) ∨ ¬(α2 →(β2 ∧¬β1 ))
  % µx.(α×(α×x)) ∨ nil  ≤ µx.(α×x)     ∨ nil
  % µx.(α×x)     ∨ nil !≤ µx.(α×(α×x)) ∨ nil
  % µx.(α×(α×x)) ∨ (α×nil)  ≤ µx.(α×x)     ∨ nil
  % µx.(α×x)     ∨ (α×nil) !≤ µx.(α×(α×x)) ∨ nil
  % µx.(α×x) ∨ nil ∼ (µx.(α×(α×x))∨nil) ∨ (µx.(α×(α×x))∨(α×nil))
  % (µx.(α×(α×x))∨nil) <!> (µx.(α×(α×x))∨(α×nil))


-endif.
