-module(utils).

-export([parens/1, beside/1, sep_by/2, pnegate/1]).
-export([compare/2]).

compare(I, I) -> 0;
compare(I1, I2) when I1 > I2 -> 1;
compare(_, _) -> -1.

% PRETTY PRINTING UTILS
pnegate(D) ->
    utils:beside([prettypr:text("not"), utils:parens(D)]).

parens(D) -> prettypr:beside(prettypr:text("("), prettypr:beside(D, prettypr:text(")"))).

sep_by(_Sep, []) -> prettypr:text("");
sep_by(_Sep, [D]) ->D;
sep_by(Sep, Docs) ->
    WithSep =
        lists:foldr(
          fun(D, Acc) ->
                  case Acc of
                      [] -> [D]; % last without trailing sep
                      _ -> [beside([D, Sep]) | Acc]
                  end
          end,
          [],
          Docs),
    Res = prettypr:sep(WithSep),
    Res.

beside([]) -> error(todo);
beside([X]) -> X;
beside([X | Rest]) -> prettypr:beside(X, beside(Rest)).