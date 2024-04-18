-module(sharesem).
-compile(nowarn_export_all).
-compile(export_all).

-type ty() ::       ty_ref() | ty_rec().
-type product() :: {ty_ref(), ty_ref()}.
-type flag() :: true.


% a ty_ref is now a pointer
-type ty_ref ():: {ty_ref, integer()}.

% Now a type record has its own ID and needs to be closed/defined manually
% The ID can be anything, it's usually a monotonically increasing counter
-record(ty, {
          id = open :: integer() | open, 
          flag      :: dnf(flag()), 
          product   :: dnf(product())
         }). 
-type ty_rec () :: #ty{}.

% We need to manually track the id to type record mapping.
% We'll first implement a pure version.
% We have three options for hash tables in Erlang that are pure and efficient:
% (Big) maps (HAMT), custom hash table (Erlang), custom hash table (C Nif).
% 
% Whereas implemeting a custom hash table in C would be the most efficient,
% it's unfeasible and likely premature optimization.
% A custom hash table in Erlang is much slower than maps 
% in Erlang which are implemented in C and implement the fast hash array mapped tries.

% memo stays the same
-type memo() :: #{}.

-type dnf(Atom) :: [{[Atom], [Atom]}]. 
-spec flag() -> dnf(true).
flag() -> [{[true], []}].
-spec negated_flag() -> dnf(true).
negated_flag() -> [{[], [true]}].
-spec product(ty_ref(), ty_ref()) -> dnf(product()).
product(A, B) -> [{[{A, B}], []}].
-spec product(product()) -> dnf(product()).
product(P) -> [{[P], []}].
-spec negated_product(product()) -> dnf(product()).
negated_product(P) -> [{[], [P]}].

% The state is now explicit and can be modified by any function
% The state keeps track of:
% * The next unused ID for a new type
% * The type map, mapping type pointers to type records
% * The hash table for type records to enable structure sharing
-record(s, {id = 0, ty = #{}, htbl = #{}}).
-type s() :: #s{}.

% A fresh context consists of a counter and an empty map for types and an empty hash table for type records.
% This context is added to the input of every function that handle types.
% We statically define the recursive type Any type and assign it the ID 0.
% In our implementation, every new corecursive type gets a new ID, cannot be distinguished and is not shared.
% To ensure termination, at least the Any type needs to be shared.
% Otherwise, many equations alpha-equivalent to Any are created,
% this can't be detected and the algorithm does not terminate.
-spec ctx() -> s().
ctx() ->
  Any = {ty_ref, 0},
  % we define the corecursive type and close it at the same time.
  AnyRec = #ty{id = 0, flag = (F = flag()), product = (P = product(Any, Any))},
  % we also add the hash of the Any function to the hash table, 
  % even though it will never be accessed again in our implementation;
  % any new corecursive type gets its own unique ID, 
  % there will never be a corecursive type that matches the hash 
  % TODO explain hash collisions
  #s{id = 1, ty = #{Any => AnyRec}, htbl = #{ hash(AnyRec) => [Any] }}.

hash(#ty{flag = _Flag, product = _Product}) ->
  % algorithm should work for bad hash functions, too
  % erlang:phash2({_Flag, _Product}).
  17.


id(S = #s{id = Id}) ->
  {Id, S#s{id = Id + 1}}.

% preconditions: 
% id = open
% id of product ty refs: defined (and therefore tracked in state)
store(NewId, Ty = #ty{id = open, flag = F, product = P}, S = #s{id = Id, htbl = Htbl, ty = Tys}) ->
  H = hash(Ty),
  case Htbl of
    #{H := Refs} -> 
      % a good hash function should produce a lot of share hits and less collisions
      case [X || X <- Refs, begin #{X := #ty{flag = FTy, product = PTy}} = Tys, {FTy, PTy} =:= {F, P} end] of
        [Ref] -> 
          % io:format(user, "Share hit for ~p!~n", [Ref]),
          {Ref, S#s{id = Id - 1}};
        _ -> 
          NewTy = Ty#ty{id = NewId},
          % io:format(user, "Store ~p:= (collision)~n~p~n", [NewId, NewTy]),
          {{ty_ref, NewId}, S#s{htbl = Htbl#{H => Refs ++ [{ty_ref, NewId}]}, ty = Tys#{{ty_ref, NewId} => NewTy }}}
        end;
    _ ->
      NewTy = Ty#ty{id = NewId},
      % io:format(user, "Store ~p:~n~p~n", [NewId, NewTy]),
      {{ty_ref, NewId}, S#s{htbl = Htbl#{H => [{ty_ref, NewId}]}, ty = Tys#{{ty_ref, NewId} => NewTy }}}
    end.


% Defining the top type
% Any = true U. {Any, Any}
% references the statically created type in the state.
-spec any() -> ty_ref().
any() -> {ty_ref, 0}.

% the constructors do not change
-spec ty(dnf(flag()), dnf(product())) -> ty_rec().
ty(Flag, Product) -> #ty{flag = Flag, product = Product}.
-spec ty_flag(dnf(flag()), s()) -> {ty_rec(), s()}.
ty_flag(Flag, S) -> 
  {E1, S0} = empty(S),
  {E2, S1} = empty(S0),
  {#ty{flag = Flag, product = product(E1, E2)}, S1}.
-spec ty_product(dnf(product())) -> ty_rec().
ty_product(Product) -> #ty{flag = negated_flag(), product = Product}.


% The Empty type is still defined in terms of Any; this time, 
% we store and share every newly created type in the context.
-spec empty(s()) -> {ty_ref(), s()}.
empty(S) -> negate(any(), S).

% Each corecursive function has access to the state 
-spec negate(ty_ref(), s()) -> {ty_ref(), s()}.
negate(Ty, S) -> corec_ref(Ty, #{}, fun negate/3, S).

% we define two corecursive helper operators: 
% one that introduces new equations and one for constant term memoizations
corec_ref(Corec, Memo, Continue, S) -> corec(Corec, Memo, Continue, reference, S).
corec_const(Corec, Memo, Continue, Const, S) -> corec(Corec, Memo, Continue, {const, Const}, S).

% A generic corecursion operator for type operators negation/union/intersection 
% and other constant corecursive functions (is_empty)
% We track the codefinition inside the memoization map
% If a corecursive call is encountered, use the mapped codefinition in the map
% The operator provides two ways of specifying memoization: 
% a constant term memoization (used for e.g. is_empty, Boolean return) 
% and a new equation reference memoization (used for e.g. type operators)
-spec corec
([ty_ref()], memo(), fun(([ty_rec()], memo(), s()) -> {ty_rec(), s()}), reference,      s()) -> {ty_ref(), s()};
( ty_ref() , memo(), fun(( ty_rec() , memo(), s()) -> {ty_rec(), s()}), reference,      s()) -> {ty_ref(), s()};
([ty_ref()], memo(), fun(([ty_rec()], memo(), s()) -> {ty_rec(), s()}), {const, Const}, s()) -> {Const, s()};
( ty_ref() , memo(), fun(( ty_rec() , memo(), s()) -> {ty_rec(), s()}), {const, Const}, s()) -> {Const, s()}.
corec(Corec, Memo, Continue, Type, S = #s{ty = Tys}) ->
 case Memo of
  % memoization of a {ty_ref, integer()} tuple
   #{Corec := Codefinition} -> {Codefinition, S};
   _ -> 
     UnfoldMaybeList = fun
      (L) when is_list(L) -> [begin #{T := Ty} = Tys, Ty end || T <- L]; 
      (L) -> begin 
        #{L := Ty} = Tys, 
        Ty 
      end 
    end,
     case Type of 
       reference -> 
        {NewId, S0} = id(S),
        NewMemo =  Memo#{Corec => NewId},
        Unfolded = UnfoldMaybeList(Corec),

        TyRec = Continue(Unfolded,NewMemo, S0),
        % smart constructor
        {Ref, S1} = store(NewId, TyRec, S0),
        {Ref, S1};
       % 'unfold' the input(s), memoize the constant term, and apply Continue.
       {const, Const} -> 
        Continue(UnfoldMaybeList(Corec), Memo#{Corec => Const}, S)
     end
 end.


-spec negate(ty_ref(), memo(), s()) -> {ty_ref(), s()}; (ty_rec(), memo(), s()) -> {ty_rec(), s()}.
% This definition is used to continue a (nested) corecursive negation
negate(Ty, Memo, S) when is_function(Ty) -> corec_ref(Ty, Memo, fun negate/3, S);
% Negation delegates the operation onto its components.
% Since the components are made of a DNF structure, 
% we use a generic dnf traversal for flags and products
negate(#ty{flag = F, product = Prod}, M, _S) -> 
  % io:format(user,"Negating: ~p~n~p~n", [F, M]),
 FlagDnf = negate_flag_dnf(F, M),
 ProductDnf = negate_product_dnf(Prod, M),
 #ty{flag = FlagDnf, product = ProductDnf}.

-spec negate_flag_dnf(dnf(flag()), memo()) -> dnf(flag()).
negate_flag_dnf(Dnf, _Memo) -> 
 {Flag, _} = dnf(Dnf, {fun(P, N, S) -> 
     [X | Xs] = [negated_flag() || true <- P] ++ [flag() || true <- N],
     {lists:foldl(fun(E, Acc) -> union_dnf(E, Acc) end, X, Xs), S}
   end, fun(Dnf1, Dnf2, S) -> {intersect_dnf(Dnf1, Dnf2), S} end}, ctx()),
  Flag.

-spec negate_product_dnf(dnf(product()), memo()) -> dnf(product()).
negate_product_dnf(Dnf, _Memo) -> % memo not needed as signs are flipped
 {Prod, _} = dnf(Dnf, {fun(P, N, S) -> 
     [X | Xs] = [negated_product(T) || T <- P] ++ [product(T) || T <- N],
     {lists:foldl(fun(E, Acc) -> union_dnf(E, Acc) end, X, Xs), S}
   end, fun(Dnf1, Dnf2, S) -> {intersect_dnf(Dnf1, Dnf2), S} end}, ctx()),
  Prod.

% flag/product dnf line
-spec dnf(dnf(Atom), {
  fun(([Atom], [Atom], s()) -> {Result, s()}), 
  fun((Result, Result, s()) -> {Result, s()})
}, s()) -> {Result, s()}.
dnf([{Pos, Neg}], {Process, _Combine}, S) -> Process(Pos, Neg, S);
dnf([{Pos, Neg} | Cs], F = {Process, Combine}, S) ->
 {Res1, S0} = Process(Pos, Neg, S),
 {Res2, S1} = dnf(Cs, F, S0),
 Combine(Res1, Res2, S1).

% lists:uniq is very important here
% equations which differ produce a new type which is not memoized, yet equivalent to a previously memoized type
% e.g. (Any, Any) & (Any, Any) should be represented as (Any, Any)
% Erlang is then able to hash two closures to the same value
-spec union_dnf(dnf(Ty), dnf(Ty)) -> dnf(Ty).
union_dnf(A, B) -> lists:uniq(A ++ B). 
-spec intersect_dnf(dnf(Ty), dnf(Ty)) -> dnf(Ty).
intersect_dnf(A, B) -> [{lists:uniq(P1 ++ P2), lists:uniq(N1 ++ N2)} || {P1, N1} <- A, {P2, N2} <- B].

% intersection and union for ty, corecursive
% Here, we have two operands for memoization. 
% We memoize the intersection operation Ty & Ty2 as {Ty, Ty2}
% and the result equation as NewTy
% Whenever the intersection operation on Ty & Ty2 is encountered
% we return the memoized result NewTy
% In our implementation, the corecursive case is never triggered,
% as intersection and negation only moves the atoms in the lines around.
% It does not recurse into an atom in a line.
-spec intersect(ty_ref(), ty_ref(), s()) -> {ty_ref(), s()}.
intersect(Ty, Ty2, S) -> corec_ref([Ty, Ty2], #{}, fun cintersect/3, S).
-spec union(ty_ref(), ty_ref(), s()) -> {ty_ref(), s()}.
union(Ty, Ty2, S) -> corec_ref([Ty, Ty2], #{}, fun cunion/3, S).

% wrapper functions for single argument type operators
-spec cintersect ([ty_ref()], memo(), s()) -> {ty_ref(), s()}; ([ty_rec()], memo(), s()) -> {ty_rec(), s()}.
cintersect([Ty1 = {ty_ref, _}, Ty2 = {ty_ref, _}], Memo, S) -> corec_ref([Ty1, Ty2], Memo, fun cintersect/3, S);
cintersect([#ty{flag = F1, product = P1}, #ty{flag = F2, product = P2}], _Memo, S) ->
 #ty{flag = intersect_dnf(F1, F2), product = intersect_dnf(P1, P2)}.

-spec cunion ([ty_ref()], memo(), s()) -> {ty_ref(), s()}; ([ty_rec()], memo(), s()) -> {ty_rec(), s()}.
cunion([Ty1 = {ty_ref, _}, Ty2 = {ty_ref, _}], Memo, S) -> corec_ref([Ty1, Ty2], Memo, fun cunion/3, S);
cunion([#ty{flag = F1, product = P1}, #ty{flag = F2, product = P2}], _Memo, S) ->
 #ty{flag = union_dnf(F1, F2), product = union_dnf(P1, P2)}.



% now for the main part, emptyness checking
-spec is_empty(ty_ref(), s()) -> {boolean(), s()}.
is_empty(Ty, S) -> 
 corec_const(Ty, #{}, fun is_empty/3, true, S).

-spec is_empty(ty_ref(), memo(), s()) -> {boolean(), s()}; (ty_rec(), memo(), s()) -> {boolean(), s()}.
is_empty(Ty = {ty_ref, _}, Memo, S) -> corec_const(Ty, Memo, fun is_empty/3, true, S);
is_empty(#ty{flag = FlagDnf, product = ProdDnf}, Memo, S) ->
  ResFlag = is_empty_flag(FlagDnf, Memo),
  {ResProd, S0} = is_empty_prod(ProdDnf, Memo, S),
  {ResFlag and ResProd, S0}.

-spec is_empty_flag(dnf(flag()), memo()) -> boolean().
% flag emptyness, empty iff: (true in N)
is_empty_flag(FlagDnf, _Memo) -> % memo not needed, no corecursive components
 {Res,_} = dnf(FlagDnf, {fun(_Pos, Neg, S) -> {not sets:is_empty(sets:from_list(Neg)), S} end, fun(R1, R2, S) -> {R1 and R2, S} end}, ctx()),
 Res.

-spec is_empty_prod(dnf(product()), memo(), s()) -> {boolean(), s()}.
% product emptyness, empty iff: product dnf empty
is_empty_prod(Dnf, Memo, S) ->
 dnf(Dnf, {
   fun(Pos, Neg, Si) -> 
     % intersect all positive products, and execute full tree exploration phi
     {{Ty1, Ty2}, S0} = big_intersect(Pos, Si),
     phi(Ty1, Ty2, Neg, Memo, S0)
   end, 
   fun(R1, R2, Si) -> 
    {R1 and R2, Si} end
 }, S).

-spec big_intersect([product()], s()) -> {product(), s()}.
big_intersect([], S) -> {{any(), any()}, S};
big_intersect([X], S) -> {X, S};
big_intersect([{Ty1, Ty2}, {Ty3, Ty4} | Xs], S) -> 
  {TyL, S0} = intersect(Ty1, Ty3, S),
  {TyR, S1} = intersect(Ty2, Ty4, S0),
  big_intersect([{TyL, TyR} | Xs], S1).

% Φ(S1 , S2 , ∅ , T1 , T2) = (S1<:T1) or (S2<:T2)
% Φ(S1 , S2 , N ∪ {T1, T2} , Left , Right) = Φ(S1 , S2 , N , Left | T1 , Right) and Φ(S1 , S2 , N , Left , Right | T2)
-spec phi(ty_ref(), ty_ref(), [ty_ref()], memo(), s()) -> {boolean(), s()}.
phi(S1, S2, N, Memo, S) -> 
  % io:format(user,"========~n", []),
  {Empty, S0} = empty(S),
  phi(S1, S2, N, Empty, Empty, Memo, S0).

-spec phi(ty_ref(), ty_ref(), [ty_ref()], ty_ref(), ty_ref(), memo(), s()) -> {boolean(), s()}.
phi(TS1, TS2, [], T1, T2, Memo, S) ->
  {N1, S00} = negate(T1, S),
  {L, S0} = intersect(TS1, N1, S00),
  {Res1, S1} = is_empty(L, Memo, S0),
  {N2, S22} = negate(T2, S1),
  {R, S2} = intersect(TS2, N2, S22),
  {Res2, S3} = is_empty(R, Memo, S2),
  {Res1 or Res2, S3};
phi(TS1, TS2, [{T1, T2} | N], Left, Right, Memo, S) ->
 {Tl, S0} = union(Left, T1, S),
 {Res1, S1} = phi(TS1, TS2, N, Tl, Right, Memo, S0),
 {Tr, S2} = union(Right,T2, S1),
 {Res2, S3} = phi(TS1, TS2, N , Left, Tr , Memo, S2),
 {Res1 and Res2, S3}.



%% Exercises:
%% - Implement hashing modulo alpha-equivalence (PLDI'21)

-ifdef(TEST).
-include_lib("eunit/include/eunit.hrl").
usage_test_() -> {
timeout, 10000, fun usage_teste/0
}.

usage_teste() ->
  Any = any(),
  
  io:format(user,"Any: ~p (~p) ~n", [Any, erlang:phash2(Any)]),
  S = ctx(),
  {Empty, S0} = negate(Any, S),
  io:format(user, "New empty: ~p ~n", [Empty]),

  % state does not change, sharing of types
  Res = negate(Any, S0),
  io:format(user,"Res: ~p~n", [Res]),
  % {Empty2, S0} = negate(Any, S0),
  % {Any2, S0} = negate(Empty, S0),

   %intersection of same recursive equations
   {Ai, S1} = intersect(Any, Any, S0),

   io:format(user,"Ai: ~n", []),
   % is_empty
   {false, _} = is_empty(Any, S1),
   io:format(user,"done: ~n", []),
   {true, _} = is_empty(Empty, S1),

  io:format(user,"Custom: ~p~n", [S1]),

   % define a custom any type
   % get new ID
   {FreeId, S2} = id(S1),
   % create an open type record
   NewAnyRec = ty(flag(), product({ty_ref, FreeId}, {ty_ref, FreeId})),
   % close the type record by storing
   {NewAny, S3} = store(FreeId, NewAnyRec, S2),
   % it's different from the any equation return by any()
   % with hashing modulo alpha equivalence they would be the same
   true = NewAny /= any(),
   {false, _} = is_empty(NewAny, S3),

   % (X, (X, true)) where X = (X, true) | (true, true)
   {IdTrue, S4} = id(S3),
   {JustTrueR, S5} = ty_flag(flag(), S4),
   {JustTrue, S6} = store(IdTrue, JustTrueR, S5),
   {false, _} = is_empty(JustTrue, S6),

   {IdXX, S7} = id(S6),
   XX = {ty_ref, IdXX},
   RXR = ty_product( union_dnf(product(XX, JustTrue), product(JustTrue, JustTrue)) ),
   {RX, S8} = store(IdXX, RXR, S7),
   {false, _} = is_empty(RX, S8),

   {IdInnerProd, S9} = id(S8),
   InnerProdR = ty_product(product(RX, JustTrue)),
   {InnerProd, S10} = store(IdInnerProd, InnerProdR, S9),

   {IdRXX, S11} = id(S10),
   RXXR = ty_product(product(RX, InnerProd)),
   {RXX, S12} = store(IdRXX, RXXR, S11),
   {false, _} = is_empty(RXX, S12),

 % interleaving corecursion
 % (true, A) where 
 % A = (B, true) | (true, true)
 % B = (true, A)
 fun() ->
 {IdA, S13} = id(S12),
 {IdB, S14} = id(S13),
 BR = ty_product(product(JustTrue, {ty_ref, IdA})),
 {B, S15} = store(IdB, BR, S14),
 AR = ty_product( union_dnf(product(B, JustTrue), product(JustTrue, JustTrue))),
 {A, S16} = store(IdA, AR, S15),
 {false, _} = is_empty(A, S16)
 end(),

 % (true, A) where 
 % A = (B, true)
 % B = (true, A)
 {IdA, S13} = id(S12),
 {IdB, S14} = id(S13),
 BR = ty_product(product(JustTrue, {ty_ref, IdA})),
 {B, S15} = store(IdB, BR, S14),
 AR = ty_product( product(B, JustTrue)),
 {A, S16} = store(IdA, AR, S15),
 {true, _} = is_empty(A, S16),

  ok.

-endif.
