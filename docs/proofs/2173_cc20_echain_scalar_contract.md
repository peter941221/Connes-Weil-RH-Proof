# 2173 — CC20 E-chain scalar contract after canonical `(143)`

Date: 2026-09-29.

Status: **FORMAL CONTRACT SHRINK**. This is a proved reduction of the
gamma-side comparison premise. It is not a trace identification, a
same-owner sign certificate, or an RH conclusion.

## Consumer and owner

The consumer remains the CC20 endpoint readback on the exact compact-log test
`g`, ending in `qw_nonneg_of_archimedeanComparison`. The owner, triple
vanishing set, and root-support hypothesis are unchanged.

## Reduced obligation

For the canonical auxiliary test

```text
k = testNeg (testAdd g g),
```

the previous exact identity `(143)` gives

```text
laplaceAt k (1/2) = -2 • laplaceAt g (1/2).
```

The existing triple-vanishing readback proves the right side is zero. Hence
the stored vector inequality

```text
eTerm ≤ (gamma / log 2) * normSq (laplaceAt k (1/2))
```

is exactly equivalent, on this owner and under the consumer's
vanishing hypothesis, to the scalar statement

```text
eTerm ≤ 0.
```

`cc20Echain_iff_nonpos_of_vanishes` proves the equivalence. The new
`cc20ArchimedeanComparison_of_h142_eNonpos` constructor then builds the
original comparison package from `trace ≥ 0`, (142), and `eTerm ≤ 0`; the
companion `qw_nonneg_of_h142_eNonpos` feeds it to the unchanged consumer.
The coefficient `gamma` remains only as inert package metadata.

This makes the remaining analytic target explicit: prove the sign of the
scalar remainder `eTerm` for the actual owner, together with (142). No
existing `CC20TraceModel` theorem supplies either one: that model exposes
support-square/no-defect read-off and nonnegative trace, but no equation
connecting its trace rows to `cc20WInfinityLog + eTerm`.

## Evidence

- implementation: `ConnesWeilRH/Dev/C1CC20ArchimedeanComparisonH143.lean`;
- paired audit: `ConnesWeilRH/Dev/C1CC20ArchimedeanComparisonH143Audit.lean`;
- build log: `results/20260929_cc20_h143_build8.log`;
- focused WSL build: 3610 jobs, footer `Build completed successfully`;
- all audited declarations use exactly `[propext, Classical.choice, Quot.sound]`;
  no `sorryAx` occurs.

## Failure criterion

This is not producer progress until a source theorem proves (142) and
`eTerm ≤ 0` for the selected owner. If either remains caller data, the
consumer is still conditional.
