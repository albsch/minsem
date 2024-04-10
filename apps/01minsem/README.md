Minimal semantic subtyping framework
=====

* Subtype relation
* Corecursion & Termination
* Type grammar: t = true | (t, t) | t & t | !t


Execute unit test cases via `rebar3`:

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

Execute property-basec test cases via `rebar3`:

```
./rebar3 proper -n 1000
===> Verifying dependencies...
===> Analyzing applications...
===> Compiling minsem
===> Analyzing applications...
===> Compiling extra_test
===> Testing prop_ty:prop_empty_termination()
OK: Passed 1000 test(s).
===> Testing prop_ty:prop_generator_ast_quality()
OK: Passed 1000 test(s).

85.20% non_trivial
12.70% empty
 2.10% any
===> 
2/2 properties passed
```
