# 2172 — CC20 (143) premise discharge

Date: 2026-09-29.

Status: **FORMAL CONTRACT SHRINK**. This is a proved reduction of one CC20
comparison premise. It is not a same-owner sign certificate and does not
claim RH.

## Consumer and owner

The downstream consumer is the existing CC20 endpoint readback
`qw_nonneg_of_archimedeanComparison`, whose owner is the exact compact-log
test `g` carried by `CC20ArchimedeanComparison g`. The consumer still needs
the root-support hypothesis supplied by that readback. No selected Route-A
owner is replaced by a root-window test.

## Discharged premise

The old contract stored an auxiliary test `k` together with

```text
laplaceAt k (1/2) = -2 • laplaceAt g (1/2).       (143)
```

The new definition `cc20AuxiliaryNegTwo g = testNeg (testAdd g g)` chooses `k`
on the same owner. Existing exact linearity lemmas give, for every complex
`s`,

```text
laplaceAt (cc20AuxiliaryNegTwo g) s
  = -(2 : ℂ) • laplaceAt g s.
```

The same definition also has the exact support guard
`support_cc20AuxiliaryNegTwo_subset`: `support(k) ⊆ support(g)`.

Consequently `cc20ArchimedeanComparison_of_h142_hEchain` constructs the
original `CC20ArchimedeanComparison g` from only the nonnegative trace field,
(142), and the `E`-chain evaluated on this canonical auxiliary test. The
fields `h142` and `hEchain` are unchanged analytic inputs; neither is
asserted or renamed.

The companion theorem `qw_nonneg_of_h142_hEchain` feeds that package directly
to the existing endpoint consumer, under its unchanged triple-vanishing and
root-support hypotheses.

## Evidence

- implementation: `ConnesWeilRH/Dev/C1CC20ArchimedeanComparisonH143.lean`;
- paired audit: `ConnesWeilRH/Dev/C1CC20ArchimedeanComparisonH143Audit.lean`;
- build log: `results/20260929_cc20_h143_build7.log`;
- focused WSL build: 3610 jobs, footer `Build completed successfully`;
- audit leaves use exactly `[propext, Classical.choice, Quot.sound]`; no
  `sorryAx` occurs.

## Remaining failure criterion

This reduction does not close the CC20 consumer until a genuine trace
identification `h142` and the gamma-side `hEchain` are proved for the actual
owner, with the required support hypothesis. If either remains only a caller
field, this record is contract progress, not a producer Go.
