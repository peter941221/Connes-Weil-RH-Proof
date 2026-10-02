# 2463 - indexed owner panel theorem on the nonnegative half-line

Date: 2026-10-02.

The owner data from 2460 is now lifted from one fixed panel to an indexed
30-family theorem for every `x0 <= x1` with `0 <= x0` and every point
`x ∈ [x0, x1]`.  The theorem uses the exact owner coefficient rectangles,
the right-half-line monotonicity of the bump, midpoint Lipschitz boxes for
cosine and sine, and the 2459 composed-sum door.  The result is
`ownerPanelMem_2463`; it keeps the finite-family sum composed before any
modulus.

The module and its axiom audit were built in the fresh ext4 mirror
`/home/peter/verify/cwr-2460` with Lean 4.30.  The audit reports exactly
`[propext, Classical.choice, Quot.sound]` for
`ownerCoefMem_2463`, `ownerPhaseBound_2463`, `ownerBumpMem_2463`,
`ownerPhaseMem_2463`, `ownerFamilyPanelMem_2463`, and `ownerPanelMem_2463`.
No `sorryAx` or project axiom was reported.

This is a formal positive-half-line indexed panel layer, not yet the full
producer certificate: the negative half-line, cross-zero panels, weighted
node sum, zeta attachment, strip norm, and 2351 invertibility import remain
open.  No GO or RH claim.

Evidence: `ConnesWeilRH/Dev/C1RouteAOwnerIndexedPanel2463.lean` and
`ConnesWeilRH/Dev/C1RouteAOwnerIndexedPanel2463Audit.lean`.
