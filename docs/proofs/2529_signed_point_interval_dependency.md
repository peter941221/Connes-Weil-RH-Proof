# Record 2529 — direct point rectangles still overpay

Date: 2026-10-03.

A directed-MPFR replay was run for the 2528 point-node idea at 2560 cells.
The implementation kept each 2338 coefficient rectangle, point bump interval,
and point phase interval, multiplied them as complex rectangles, summed the 30
rectangles, and only then took the final rectangle norm.

The result was:

```text
sigma = -1/2    node sum = 3.357380101378732
sigma = +1/2    node sum = 3.342538523716836
```

The corresponding 2528 center-plus-error diagnostic was about `2.6868874`
and `2.6752115`. The gap is interval dependency inflation: tiny independent
phase and coefficient widths are carried through repeated rectangle products,
so the final box is much wider than the actual signed sum. This is an
implementation obstruction to the direct rectangle version of the new route,
not a no-go for signed pointwise cancellation.

Decision:

```text
freeze: per-family complex rectangle -> sum -> final norm
keep:   center complex sum -> norm + scalar coefficient/rounding error
```

The next certificate representation must make the center sum the primary
object and charge coefficient, phase, bump, and floating-point uncertainty as
separate scalar errors. The 2529 artifact is not a Lean certificate and makes
no producer-GO, SourceRH, or RH claim.

Evidence:

- `scripts/routea_owner_signed_point_node_mpfr_2529.py`
- `results/2529_signed_point_node_mpfr.json`
- `docs/proofs/2528_signed_pointwise_cancellation.md`
