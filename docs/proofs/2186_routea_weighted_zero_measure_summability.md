# 2186 — Route-A weighted-zero-measure summability bridge

Date: 2026-09-29  
Status: `FORMAL SMALLER OBLIGATION`; no producer closure.

## Contract

The consumer remains the same selected healthy `CompactLog` detector and its
same-owner `qw(g) >= 0` producer. The exact source-zero subtype and the
support-derived owner are unchanged.

## Landed brick

`C1RouteAWeightedZeroMeasure.lean` now proves

```text
0 <= q, q < 4,
spectralHeightMultiplicity (n+1) <= K*q^n for every n
  -> Summable (weightedZeroMeasure F).
```

The proof transports the existing quadratic vertical Laplace estimate and
analytic multiplicity-shell consumer from `spectralTerm` to its exact norm
`weightedZeroMeasure = spectralNormTerm`. The result is scalar and
owner-preserving; it does not replace the source-zero set by a sampled or
fixed-prime set.

## Verification

- owning module: `results/20260929_a0051_owner_build1.log`;
- aggregate module refresh: `results/20260929_a0051_module_build2.log`;
- paired audit: `results/20260929_a0051_audit_build4.log`;
- audited new leaf axioms: `[propext, Classical.choice, Quot.sound]`;
- no `sorryAx`, no RH premise, and no route consumer was introduced.

## Remaining gate

This only makes the weighted budget summable under an explicit shell-mass
premise. It does not provide the numerical/unconditional strict inequality
`B_zm(rho,N) < epsilon(rho,N)`. The next brick must expose an exact finite
prefix plus tail bound and price that inequality on the selected owner.
