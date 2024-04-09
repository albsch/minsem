-module(prop_dnf_product).

-include_lib("proper/include/proper.hrl").
-include_lib("eunit/include/eunit.hrl").

-compile(export_all).

gen_dnf_product_ast() -> ?SIZED(Size, gen_dnf_product_ast(Size)).
gen_dnf_product_ast(Size) when Size =< 1 ->
frequency([
    {1, ?LAZY(test_ast:t([test_ast:any(), test_ast:any()]))},
    {1, ?LAZY(test_ast:t([test_ast:none(), test_ast:none()]))}
]);
gen_dnf_product_ast(Size) ->
frequency([
    {20, ?LAZY(?LET(A, prop_product:gen_product_ast(Size), A))}
  ] ++ prop_ty:type_operations_ast(Size, fun(Siz) -> gen_dnf_product_ast(Siz) end)).

ast_to_dnf({intersection, A, B}) -> minsem:intersect_dnf(ast_to_dnf(A), ast_to_dnf(B));
ast_to_dnf({union, A, B}) -> minsem:union_dnf(ast_to_dnf(A), ast_to_dnf(B));
ast_to_dnf({negation, A}) -> minsem:negate_product_dnf(ast_to_dnf(A), #{});
ast_to_dnf({difference, A, B}) -> minsem:intersect_dnf(ast_to_dnf(A), minsem:negate_product_dnf(ast_to_dnf(B), #{}));
ast_to_dnf(T = {tuple, [_, _]}) -> minsem:product(prop_product:ast_to_dnf(T)).