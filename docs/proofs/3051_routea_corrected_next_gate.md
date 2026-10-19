# Route A corrected next gate (record 3051)

The earlier 3050 contract is an interface description, not a request to
regenerate all four channels. Existing evidence already contains the full
numerical inputs:

- record 2668: repaired-owner four-channel full-grid replay over 776611 nodes;
- record 2670: continuous-box price over 8192 cells, with total below the
  committed knownError2109 budget;
- records 2676-2683: Lean bridges for representative cell/channel rectangles;
- records 2684-2687: exact finite-grid arithmetic for the sampled ledger.

The binding proof gap is now the evaluator-to-Lean bridge:

```text
2242 interval hull operations
        -> continuous cell rectangle theorem
        -> all 8192 cell instances
        -> exact rational charge sum
        -> live chargeRest identity
        -> signed infinite-xi tail
```

Do not start a new four-channel numerical replay unless a named evaluator
change invalidates 2668/2670. The next concrete proof target is one generic
parameterized theorem for the 2242 rectangle evaluator, followed by a generated
8192-cell arithmetic import. The 3047 baseM0 certificate remains an independent
cross-check and is not the binding producer path.
