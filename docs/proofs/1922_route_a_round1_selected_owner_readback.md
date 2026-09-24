# 1922 — Route A Round 1: selected-owner readback

Date: 2026-09-24.

Status: FORMAL round-1 completion. The signed residual inequality is still
OPEN; no RH claim is made.

## Completed target

For the actual parameterized selected owner
`(selectedOwner base correction n).sourceTest`, the new leaf
`C1RouteASelectedOwnerResidualReadback.lean` proves:

```text
ICgate(selectedOwner.square)
  = archimedeanTerm(selectedOwner.square)
    + selectedOwnerVisiblePrimeProfileWeightedSum.
```

Under the existing triple-vanishing hypothesis it also proves:

```text
qw(selectedOwner)
  = -archimedeanTerm(selectedOwner.square)
    - selectedOwnerVisiblePrimeProfileWeightedSum.
```

The intermediate iff states exactly that the selected-owner gate is nonpositive
iff the explicit Archimedean-plus-visible-profile budget is nonpositive.

This is an owner-preserving reduction: the finite sum is the exact
support-derived visible-prime set of the selected owner, not a fixed cutoff,
continuous density, or surrogate detector.

## Verification

Owning module and paired audit:
`ConnesWeilRH/Dev/C1RouteASelectedOwnerResidualReadback.lean` and
`C1RouteASelectedOwnerResidualReadbackAudit.lean`.

Focused log: `20260924_routeA_round1_retry5.log`.

Build completed successfully (3662 jobs), with zero `error:` lines. The audit
prints all three declarations with only `[propext, Classical.choice,
Quot.sound]`; no `sorryAx` occurs.

## What remains

The first round removes `finitePrimeSum` as an opaque owner input. The next
producer obligation is the strict signed residual budget on this same owner,
with an explicit positive margin. No sign estimate was smuggled into the
readback.
