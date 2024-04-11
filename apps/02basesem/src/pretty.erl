-module(pretty).

-record(ty, {flag, product, arrow}). 

-compile(nowarn_export_all).
-compile(export_all).

format(Txt, [], _) -> 
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


format_dnf_flag(Flag) -> 
  utils:sep_by(prettypr:text(" |"),
  [
    utils:sep_by(prettypr:text(" &"), 
      [ prettypr:text("flag") || _ <- Pos] 
        ++
      [ prettypr:text("!flag") || _ <- Neg] 
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

format_product({Ref1, Ref2}, _) ->
  {[Ref1, Ref2], utils:beside([prettypr:text("{"), prettypr:text(integer_to_list(erlang:phash2(Ref1))), prettypr:text(","), prettypr:text(integer_to_list(erlang:phash2(Ref2))), prettypr:text("}")])}.

format_arrow({arrow, Ref1, Ref2}, _) ->
  {[Ref1, Ref2], utils:beside([prettypr:text("("), prettypr:text(integer_to_list(erlang:phash2(Ref1))), prettypr:text(" -> "), prettypr:text(integer_to_list(erlang:phash2(Ref2))), prettypr:text(")")])}.
