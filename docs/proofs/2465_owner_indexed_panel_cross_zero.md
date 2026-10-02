# 2465 - indexed owner panel theorem across zero

Date: 2026-10-02.

The three geometric panel cases are now formalized.  For every
`x0 <= 0 <= x1` and `x ∈ [x0,x1]`, the cross-zero bump box uses the exact
global bound `widthBump radius x ≤ exp(-30)`.  The proof handles the inside
support branch by the positive denominator inequality and the outside branch
by the zero extension.  Exact owner coefficient rectangles, midpoint phase
boxes, and the 2459 composed 30-family sum door are reused.

The module and audit build in the fresh ext4 mirror
`/home/peter/verify/cwr-2460` with Lean 4.30.  The audit reports exactly
`[propext, Classical.choice, Quot.sound]` for
`ownerRadPos_2465`, `ownerBumpMemCross_2465`,
`ownerFamilyPanelMemCross_2465`, and `ownerPanelMemCross_2465`; no `sorryAx`
or project axiom was reported.

This closes only the indexed panel-envelope geometry.  The weighted node
sum, trapezoid/zeta attachment, strip norm, and 2351 invertibility import
remain open.  No GO or RH claim.

Evidence: `ConnesWeilRH/Dev/C1RouteAOwnerIndexedPanel2465.lean` and
`ConnesWeilRH/Dev/C1RouteAOwnerIndexedPanel2465Audit.lean`.
