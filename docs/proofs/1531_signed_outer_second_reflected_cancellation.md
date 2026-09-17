# 1531 — Signed outer/second/reflected cancellation on the source inclusion

Date: 2026-09-17

The isolated outer-pair consumer from record 1529 is not the correct physical
target, because the ambient leakage branch is obstructed by the separated
orthonormal orbit (record 1530).  On the actual inclusion `J`, the next three
branches must therefore be kept together.

The new theorem
`sourceSoninOuterSecondReflected_comp_sourceInclusion_eq_hardySubId` proves
the exact operator identity

```text
(E Q [E,M] + E [Q,M] E + [E,M] Q E) J
  = (E Q E M - M) J.
```

The proof uses only `E J = J`, `Q J = J`, and pointwise ring algebra.  All six
noncommuting terms are retained until those two source-fixing identities are
applied; the middle `E Q M J` and `E M Q J` terms cancel.

This is a cancellation-preserving normal form for the B4 source block.  It
does not claim square-summability or positivity.  The prolate commutator must
still be combined with this block, and the resulting source-compressed root
object remains the analytic target.  WO-B stays OPEN.

The same file now records the direct completion identity
`[P,M] J = ((E Q E) M - M) J - [K_prol,M] J`.
Thus a future energy producer can consume the two signed columns directly;
it need not reconstruct the three-branch ledger or estimate the isolated
outer pair.

The paired square-sum consumer is now formal as well: summability of the
Hardy-sub-identity column and of the prolate commutator column implies the
full source-commutator square-sum after arbitrary bounded ambient/source
factors.  This is a consumer theorem only; both analytic premises remain
open for the physical boundary factors.

Owning declaration: `ConnesWeilRH.Dev.C1G8R3BoundaryOutputFactorizationBridge`.
Audit: `...BoundaryOutputFactorizationBridgeAudit`.
