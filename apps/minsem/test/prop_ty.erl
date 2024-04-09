-module(prop_ty).

-include_lib("proper/include/proper.hrl").
-include_lib("eunit/include/eunit.hrl").

-compile(export_all).

-import(test_ast, [u/2, i/2, d/2, n/1]).

type_operations_ast(Size, F) -> [
    {1, ?LAZY(?LET({A, B}, {F(Size div 2), F(Size div 2)}, u(A, B))) },
    {1, ?LAZY(?LET({A, B}, {F(Size div 2), F(Size div 2)}, i(A, B))) },
    {1, ?LAZY(?LET({A, B}, {F(Size div 2), F(Size div 2)}, d(A, B))) },
    {1, ?LAZY(?LET(Compound, F(Size - 1), n(Compound))) }
  ].

gen_ty_ast() -> ?SIZED(Size, gen_ty_ast(Size)).

gen_ty_ast(Size) when Size =< 1 ->
frequency([
    {1, ?LAZY(test_ast:any())},
    {1, ?LAZY(test_ast:none())}
]);
gen_ty_ast(Size) ->
frequency([
    {25, ?LAZY(test_ast:atom(true))},
    {10, ?LAZY(?LET(P, prop_dnf_product:gen_dnf_product_ast(Size), P))}
  ] ++ type_operations_ast(Size, fun(Siz) -> gen_ty_ast(Siz) end)).

ast_to_dnf(any) -> minsem:any();
ast_to_dnf(none) -> minsem:empty();
ast_to_dnf({intersection, A, B}) -> minsem:intersect(ast_to_dnf(A), ast_to_dnf(B));
ast_to_dnf({union, A, B}) -> minsem:union(ast_to_dnf(A), ast_to_dnf(B));
ast_to_dnf({negation, A}) -> minsem:negate(ast_to_dnf(A));
ast_to_dnf({difference, A, B}) -> minsem:intersect(ast_to_dnf(A), minsem:negate(ast_to_dnf(B)));
ast_to_dnf({atom, true}) -> fun() -> minsem:ty_flag(minsem:flag()) end;
ast_to_dnf(T = {tuple, [_, _]}) -> fun() -> minsem:ty_product(prop_dnf_product:ast_to_dnf(T)) end.


prop_empty_termination() ->
  ?FORALL(X, gen_ty_ast(), begin Res = minsem:is_empty(ast_to_dnf(X)), true = (Res =:= true orelse Res =:= false) end).

prop_generator_ast_quality() ->
  ?FORALL(Ast, gen_ty_ast(),
    begin
      % io:format(user, "~p~n", [Ast]),
      X = ast_to_dnf(Ast),
      % io:format(user, "~p~n", [X]),
      collect(
        case { minsem:is_empty(X), minsem:is_empty(minsem:intersect(minsem:any(), minsem:negate(X))) } of
          {true, false} -> empty;
          {false, true} -> any;
          _ -> non_trivial
        end, true)
    end
  ).