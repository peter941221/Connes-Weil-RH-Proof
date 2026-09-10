# 1276 — G8 P1 literal-cutoff metric channels

Date: 2026-09-10.

Status: FORMAL Lean fact. This record supplies no finite-prime equality, limit,
sign, `qw` readback, or RH claim.

Consumer: the healthy-`CompactLog`, selected-detector, same-owner B5/P2
consumer `G8SameOwnerReadbackData` of record 1257, through P1 of record 1266.

## Statement

For the literal G8 source cutoff

```text
C_n = (sourceInclusion lambda)^* o g8SourceCutoffPairData(..., n).left,
```

the existing finite Euler coframe decomposition is lifted inside the actual
metric sandwich. Writing

```text
E_surv = upperFactor * terminal-survivor-coframe,
E_bdry = upperFactor * sum finiteEulerMetricCoframeBoundaryMaps,
```

Lean proves, before a trace is taken,

```text
C_n^* (E_surv + E_bdry)^* W_g (E_surv + E_bdry) C_n
 = C_n^* E_surv^* W_g E_surv C_n
 + C_n^* E_surv^* W_g E_bdry C_n
 + C_n^* E_bdry^* W_g E_surv C_n
 + C_n^* E_bdry^* W_g E_bdry C_n.
```

All four terms retain the selected detector, literal cutoff, Sonin scale, and
finite prime-power family. The proof uses only the prior exact metric-coframe
split and additive operator algebra; it does not unfold the cutoff leg.

## Consequence for P1

The boundary maps are indexed by the deduplicated `family.visiblePrimes`,
whereas the established arithmetic trace readback is indexed by
`family.terms : Finset (prime, exponent)`. Therefore the old prime-power
readback theorem cannot be applied term-by-term to these columns. The next P1
theorem must be an aggregate same-owner cutoff trace comparison: it must
identify a named combination of the four channels with the finite prime-power
Euler sum plus explicitly named survivor/cross/remainder channels. It may not
replace this operator by the uncut `projectionResponse`.

## Verification

`1276_g8_p1_metric_channels_retry.log` records a green owning/Audit build of
`C1G8P1MetricChannels` and its audit (3925 jobs), zero `error:` lines, zero
`sorryAx`, and only `[propext, Classical.choice, Quot.sound]` for every audited
declaration.
