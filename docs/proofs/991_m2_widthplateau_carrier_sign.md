# 991 - same width is not the same carrier (SUPERSEDED carrier-sign claim corrected)

Date: 2026-08-12. Status: numeric object-identity audit. RH NOT claimed.
Companions: `docs/proofs/991_m2_widthplateau_carrier_sign.py` and
`ConnesWeilRH/Dev/M2WidthPlateau.lean`.

## Result first

The earlier statement that the script computed the signs of Lean's `narrowC`
and `wideC` was false. The script computes smooth finite-vanishing residuals
whose support widths are `2.4` and `3.0`; Lean's carriers are plain scaled
plateau bumps. Equal support width is not object equality.

Under the corrected complete functional, both numerical residual families are
positive and resolution-stable:

```text
+--------------------+-------+-----------+-----------+-----------+-------------+
| numeric residual   | N     | arch      | pole      | primes    | QW          |
+--------------------+-------+-----------+-----------+-----------+-------------+
| width 2.4          | 10001 | +0.18608  | ~0        | -0.19253  | +0.006443   |
| width 2.4          | 20001 | +0.18608  | ~0        | -0.19253  | +0.006444   |
| width 2.4          | 40001 | +0.18608  | ~0        | -0.19253  | +0.006444   |
+--------------------+-------+-----------+-----------+-----------+-------------+
| width 3.0          | 10001 | +0.41524  | ~0        | -0.41834  | +0.003105   |
| width 3.0          | 20001 | +0.41524  | ~0        | -0.41835  | +0.003106   |
| width 3.0          | 40001 | +0.41524  | ~0        | -0.41835  | +0.003106   |
+--------------------+-------+-----------+-----------+-----------+-------------+
```

The sampled vanishing residuals are around `1e-16` to `1e-15`, and
`F(0)=||g||_2^2=1` is asserted by the evaluator.

## What Lean actually owns

`M2WidthPlateau.lean` defines:

```lean
noncomputable def wideC : CompactLogTest := wideTest (3 / 2) wideW_pos
noncomputable def narrowC : CompactLogTest := wideTest (6 / 5) narrowW_pos

noncomputable def widePsi : Real := C1WeilExplicit.healthyQw wideC
noncomputable def narrowPsi : Real := C1WeilExplicit.healthyQw narrowC
```

These definitions make the complete expressions stateable. They do not prove
their signs and they do not give either plain plateau the three required
Mellin vanishings.

The same-owner sign bridge is closed exactly:

```lean
theorem healthyQw_eq_neg_weilLocalSum (c : CompactLogTest) :
  C1WeilExplicit.healthyQw c =
    -C1.healthyCC20TestSpace.weilLocalSum
      (C1.healthyCC20TestSpace.starConvolution c)
```

This proves `source QW = -CC20 local sum` for the same `c`; it does not transfer
a number from a different numeric residual.

## Verdict

No counterexample or Lean carrier sign has been produced. The corrected script
only shows positive complete-QW values for two residual families with matching
support widths. A formal numerical sign would require constructing that exact
residual in Lean and certifying its integrals; the main RH route instead needs
the universal all-test sign theorem. RH NOT claimed.
