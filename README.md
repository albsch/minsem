Mini semantic subtyping framework
=====

Execute test cases via `rebar3`:

```
./rebar3 eunit -m minsem
===> Verifying dependencies...
===> Analyzing applications...
===> Compiling minsem
===> Performing EUnit tests...
Any: #Fun<minsem.0.133147983> (36237324) 
{ty,[{[true],[]}],
    [{[{#Fun<minsem.0.133147983>,#Fun<minsem.0.133147983>}],[]}]}
Empty: #Fun<minsem.1.133147983>
Empty unfolded: {ty,[{[],[true]}],
                    [{[],
                      [{#Fun<minsem.0.133147983>,#Fun<minsem.0.133147983>}]}]}
Any & Any: {#Fun<minsem.6.133147983>,
            {ty,[{[true],[]}],
                [{[{#Fun<minsem.0.133147983>,#Fun<minsem.0.133147983>}],[]}]}}
Any: #Fun<minsem.1.133147983>
Any unfolded: {ty,[{[true],[]}],
                  [{[{#Fun<minsem.0.133147983>,#Fun<minsem.0.133147983>}],
                    []}]}
Any is empty: false
Empty is empty: true
Any (custom) is empty: false
.
Finished in 0.012 seconds
1 tests, 0 failures
```
