-module(prop_product).

-include_lib("proper/include/proper.hrl").
-include_lib("eunit/include/eunit.hrl").

-compile(nowarn_export_all).
-compile(export_all).
      
gen_product_ast() -> ?SIZED(Size, gen_product_ast(Size)).

gen_product_ast(Size) -> ?LAZY(?LET({A, B}, 
   {prop_ty:gen_ty_ast(Size div 2), prop_ty:gen_ty_ast(Size div 2)},
   test_ast:t([A, B])
  )).

ast_to_dnf({tuple, [A, B]}) -> {prop_ty:ast_to_dnf(A), prop_ty:ast_to_dnf(B)}.