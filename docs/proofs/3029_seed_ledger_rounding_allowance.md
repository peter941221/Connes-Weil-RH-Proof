# 3029 Seed ledger rounding allowance

Using the same imported legacy evaluator context as the 2804 generator, the
canonical charge excess over the exported ledger was priced across all 8192
cells.

```text
order 4 total excess = 2.3618571359789742487e-36
order 7 total excess = 2.5857306688451114276e-30

order 4 budget margin = 99.34914688075490618
order 7 budget margin = 1407294745.9561314875
```

Both allowance checks pass. The context load is intentional: importing the
legacy evaluator before setting interval precision reproduces the generator's
rounding class. The result remains numerical evidence; evaluator-to-Lean
soundness is still open.
