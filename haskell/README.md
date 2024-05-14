Haskell implementation of a somewhat minimal type language
for semantic subtyping.

Run the tests:

```
stack run
```

To re-generate the test cases or to generate more test cases
verified by cduce, use this command (`cduce` has to be in the `PATH`):

```
stack run genTests cduce_test_cases.txt 100 100
```

This generates 100 types that are expected to be empty and
another hundred that are expected to be non-empty. If you re-run
the test generation, the new test cases are appended to the file
`cduce_test_cases.txt`.


