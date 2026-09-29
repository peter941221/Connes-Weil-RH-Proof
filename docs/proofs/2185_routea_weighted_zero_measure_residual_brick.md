# 2185 — Route-A weighted-zero-measure residual brick

Date: 2026-09-29  
Status: `FORMAL SMALLER OBLIGATION`; A.005.1 remains `GO-CANDIDATE / UNPRICED`.

## Contract

The consumer is the same selected healthy `CompactLog` detector:

```text
same owner g -> qw(g) >= 0 -> SourceRH -> Mathlib RH.
```

The owner is unchanged: the actual selected square, its source-zero shell
owner, and its support-derived finite visible-prime owner. No ROOT, fixed-prime,
known-prefix replacement, or fitted weight is used.

## Landed brick

For an actual compact-log test `F` and source zero `z`, define the fixed weight

```text
W(F,z) = spectralNormTerm(F,z)
       = xiMultiplicity(z) * ||laplaceAt F (z - 1/2)||.
```

The new audited declarations in
`ConnesWeilRH/Dev/C1RouteAWeightedZeroMeasure.lean` prove:

```text
0 <= W(F,z)
Re(spectralTerm(F,z)) <= W(F,z)
Re(sum omitted spectralTerm(F,z)) <= sum omitted W(F,z).
```

The last statement uses the exact dyadic shell prefix and the actual source-zero
subtype. It is not a sampled estimate and does not discard owner identity.

## Verification

- owning module: `results/20260929_a0051_owner.log`, resource result `exit=0`;
- paired audit: `results/20260929_a0051_audit.log`, resource result `exit=0`;
- all three audited leaves use exactly `[propext, Classical.choice, Quot.sound]`;
- no `sorryAx` and no route consumer or RH conclusion is introduced.

## Remaining gate

The producer premise is reduced, not discharged. The next gate is an exact-owner
bound for the explicit omitted sum, with a certified `B_zm` and a separately
certified positive `epsilon`; the required strict test remains

```text
B_zm < epsilon.
```

Until that gate is priced, A.005.1 remains a candidate and the selected-detector
producer remains open.
