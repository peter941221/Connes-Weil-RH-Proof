# Rational D4/D7 jet boxes fit a larger row allowance (record 3070)

Date: 2026-10-19.

Status: all-cell mpmath interval routing diagnostic. D4 means the fourth
derivative integral and D7 the seventh derivative integral of
`Real.smoothTransition`. This record prices the comparison between the proved
Lean rational jet family from theorem 2738 and the exported 3040 cell rows. It
does not prove that comparison in Lean.

## Method

For each of the 8192 cells `B_i` from record 2809, the diagnostic sets
`m_i = max(1, ceil(-P_i.lo))`, where `P_i` is the exact-real phase interval
computed by the 2734 interval recurrence. This makes the Taylor argument
`-P_i.lo/m_i` at most one, as required by the 2736 rational exponential box.
It then evaluates the 2738 rational transition-jet recurrence at derivative
orders 4 and 7 using mpmath interval arithmetic and prices

```text
cellCharge(i,k) = 4 * (2047/33554432) * endpointAbsMax(jetBox(i,k)).
```

The exported 3040 row already contains its endpoint-majorant share. Therefore
the comparison is against `rowHead3040(i,k) = row3040(i,k) -
endpointShare(k)/8192`, without charging the endpoint share twice. The script
uses the existing rational rows and does not generate or alter Lean proof data.

## All-cell result

```text
+--------+-------+----------------------+------------------+---------------------+
| order  | cells | max excess           | worst cell       | allowance decision |
+--------+-------+----------------------+------------------+---------------------+
| D4     | 8192  | 1.54629285734e-17   | 2010             | below 2e-10         |
| D7     | 8192  | 1.28208440447e-10   | 1249             | below 2e-10         |
+--------+-------+----------------------+------------------+---------------------+
```

A uniform `2e-10` allowance per row costs `8192 * 2e-10 = 1.6384e-6` in the
aggregate. This is negligible relative to the D4 and D7 thresholds 1500 and
2,000,000,000 and the exact aggregate row sums proved in 3042.

The diagnostic is not a theorem. It establishes the right target and a
plausible rational margin: formally prove, for every `i < 8192`,
`4*cellWidth*endpointAbsMax(rationalSeedTransitionJet2738(B_i,m_i,k)) <=
rowHead3040(i,k) + 2e-10` for `k=4,7`. Summing these inequalities bounds the
integral over `[1/4096, 1/2]` by the sum of the 3040 row heads plus the
allowances. Then add the separately proved endpoint integral bound from 2803
for `[0, 1/4096]`. This recovers the full 3040 row sum plus the allowance and
does not double-count the endpoint share.

The 3071 module now contains full-target arithmetic theorems that add the
endpoint integral bound to the cell sum. The remaining connection is proving
that the actual row-head vector satisfies its aggregate hypothesis; these
theorem statements are still uncompiled.

The arithmetic contract has been written as
`C1RouteBSeedLedgerAllowance3071.lean`: it proves a generic `2e-10`
per-cell allowance sum and target bound, conditional on per-cell inequalities
and a ledger-sum bound. Its ledger must be instantiated by the row heads, with
their sum bounded by the full 3042 aggregate. The source theorem 2738 already
proves that each rational jet encloses the actual derivative; the endpoint
comparisons and the formal connection from 3040/3042 row-head data to 3071
remain open. The module has not yet been Lean-compiled.

An exact-Fraction cross-read of the 8192 stored rows confirms that each 3040
row sum equals the corresponding 3042 rational aggregate, and that subtracting
then restoring the endpoint charge recovers the sum exactly. This checks the
artifact arithmetic only. Converting the endpoint charge to binary64 underflows
to zero, so the equality check must remain rational rather than float-based.

## Reproduction and limits

Run `python scripts/diag_seed_rational_charge_3070.py --all`. The result is
stored at `results/3070_seed_rational_box_margin.json`. This verifies only an
mpmath interval replay against stored rational rows. It does not prove the
row comparisons in Lean, close the row-B pins, transfer the poweredSeed
carrier, discharge rho-quantified duties, or prove RH. Route A remains the
binding producer lane.
