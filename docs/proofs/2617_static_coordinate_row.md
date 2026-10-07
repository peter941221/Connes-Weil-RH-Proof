# Record 2617: direct coordinate bounds for static defect row zero

Status: ROW00-STATIC-COMPARISON-PASS. All thirty entry bounds and the original
row theorem compile; thirty cell audits and the row audit report exactly
`[propext, Classical.choice, Quot.sound]`. Full 2600 verification remains open.

## Obligation and method

The target is row zero of record 2600: thirty upper bounds for the interval
matrix defect. The candidate inverse, analytic matrix rectangles, and entry
upper bounds are unchanged. This does not prove that the matrix rectangles
contain the actual analytic integrals.

A complex rectangle stores four real endpoints. Its L1 upper is the maximum
absolute real endpoint plus the maximum absolute imaginary endpoint. If both
real endpoints have absolute value at most `realBound`, both imaginary
endpoints have absolute value at most `imagBound`, and their sum is at most
the committed upper, that upper bounds the rectangle directly.

`rectL1Upper2598_le_of_coordinate_bounds2617` proves this implication without
constructing an equality between two whole rectangles. The generated leaves
first prove the four complete coordinate sums, then rewrite the corresponding
defect coordinates, and finally apply the implication. Off-diagonal leaves
prove the finite indices are different explicitly before removing the
diagonal identity contribution.

```text
[Row-zero product cache: 900 product equations]
                     |
                     v
[Six five-term blocks per entry and coordinate]
                     |
                     v
[Four complete coordinate sums per entry]
                     |
                     v
[Direct entry upper: no whole-rectangle equality]
                     |
                     v
[Thirty original cell names + original row theorem]
```

The row facade preserves the existing theorem names and the row theorem's
`j` argument. It imports checked leaves instead of normalizing all thirty
entries in one process. Other rows are untouched.

## Reproduction

The existing upstream library and row-zero product cache are prerequisites.
Use the pinned Lean toolchain and place the build and dependency libraries on
the Linux-native filesystem when measuring execution time. The certificate
runner compiles modules serially and honors the repository resource locks.

Generate the row source:

    python3 scripts/generate_static_coordinate_bounds_2617.py --all-columns

Run the focused arithmetic, generation, and negative-control tests:

    python3 scripts/static_coordinate_bounds_selftest_2617.py

Compile and validate all row leaves and audits:

    python3 scripts/validate_static_coordinate_bounds_2617.py --compile

The runner refreshes 2598 before its consumers. It records source and compiled
object fingerprints, rejects unsuccessful or interrupted logs, and requires
the exact standard three axioms for every cell audit and the row audit. A
compiled file's existence alone is insufficient evidence of source freshness.

The primary 2600 generator also regenerates this row facade and its leaves;
it does not restore the superseded row-zero proof shape. The legacy
product-cache rewrite is not needed for this facade. The block generator
declares the generic six-block sum theorem
only in column zero; later columns import it instead of defining it again.

## Scope and next obligations

The fingerprinted control compiles 214 modules serially with Lean 4.30.0.
Their measured compiler wall times sum to 311.39 seconds; the maximum
per-process resident memory is 3.919 GiB. This excludes generation, cache
copying, and construction of the reused upstream library and product cache.
Seventeen focused tests pass, including primary-generator reproduction in a
temporary directory, all thirty independent coordinate comparisons, and
rejection of stale fingerprints, interrupted logs, and forbidden axioms.
All twenty-two record-2271 Linux integration tests also pass. No source in
that replay manifest was changed.

The earlier whole-rectangle payload consumer was also run against the refreshed
2598 interface on the Linux-native libraries. GNU time recorded 166.75 seconds
and 5.797 GiB before an explicit interrupt; no object was produced. The new
first-cell coordinate sums plus direct upper compiled in 6.59 seconds in the
fingerprinted control. Both shapes reuse the existing product/block cache;
this is a bounded proof-engineering comparison, not a completed baseline
timing or a clean-build speedup claim.

```text
+----------------------+-------------------+------------------------------+
| Control              | Checked scope     | Outcome                      |
+----------------------+-------------------+------------------------------+
| Whole rectangle      | one final entry   | interrupted; no proof object |
| Coordinate leaves    | all 30 row entries| compiler and axiom gates pass|
| Full static matrix   | 900 entries       | not yet Lean verified        |
| Analytic containment | actual integrals  | remains an explicit premise  |
+----------------------+-------------------+------------------------------+
```

Passing this record closes one complete static row, not the full 900-entry
comparison. The independent Fraction engine also replays the existing 2351
certificate, but that external replay is not a Lean integral-containment proof.

The remaining work is the other twenty-nine static rows, actual analytic
matrix containment, actual coefficient membership, full-grid integration
certificates, and the selected detector's signed budget. Interpolation alone
does not establish coefficient membership. No producer GO or RH is claimed.

Evidence: `results/2617_static_coordinate_bound_validation.json`,
`C1RouteACorrectionCoordinateBound2617.lean`, the generated row-zero leaves,
and `C1RouteACorrectionStaticDefectCoordinate2617Row00Audit.lean`.
