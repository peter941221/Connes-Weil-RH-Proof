# Record 3204: concrete-owner Taylor-6 diagnostic

The 3187 Taylor-6 evaluator was repriced with the exact binary64 values from
Lean's `record2680CorrectionCoefficient`. The coefficient error term is zero
because these are fixed owner values, not an ideal-box center approximation.
The captured modulation values and support radii are unchanged.

At 40960 cells and 192-bit Arb precision, the diagnostic result is:

```text
owner-window diagnostic upper ~= -3.51105083244727867065463511235e-9
sixth-order remainder is positive and included
```

The result remains external numerical evidence. It does not prove the
per-cell derivative bounds in Lean, import JSONL, include the full-line tail,
or establish a producer certificate.

Evidence: `scripts/routea_concrete_owner_taylor6_3204.py` and
`results/3204_concrete_owner_taylor6.json`.