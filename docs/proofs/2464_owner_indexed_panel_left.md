# 2464 - indexed owner panel theorem on the nonpositive half-line

Date: 2026-10-02.

The 2463 indexed owner-panel layer now has its left-sided companion.  For
every `x0 <= x1 <= 0` and `x ∈ [x0,x1]`, the bump box takes its maximum at
the right endpoint `x1`, using the exact 2459 `MonotoneOn` theorem on
`(-radius, 0]`.  The exact owner coefficient rectangles and 2463 midpoint
phase boxes are reused, and the 2459 finite-family sum is still composed
before any modulus.

The module and audit build in the fresh ext4 mirror
`/home/peter/verify/cwr-2460` with Lean 4.30.  The audit reports exactly
`[propext, Classical.choice, Quot.sound]` for
`ownerBumpMemLeft_2464`, `ownerFamilyPanelMemLeft_2464`, and
`ownerPanelMemLeft_2464`; no `sorryAx` or project axiom was reported.

This closes only the nonpositive-half-line indexed panel layer.  Cross-zero
panels, the weighted node sum, zeta attachment, strip norm, and 2351
invertibility import remain open.  No GO or RH claim.

Evidence: `ConnesWeilRH/Dev/C1RouteAOwnerIndexedPanel2464.lean` and
`ConnesWeilRH/Dev/C1RouteAOwnerIndexedPanel2464Audit.lean`.
