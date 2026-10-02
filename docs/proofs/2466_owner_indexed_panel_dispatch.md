# 2466 - universal indexed owner-panel dispatcher

Date: 2026-10-02.

The positive, negative, and cross-zero panel proofs from 2463--2465 are now
exposed through one universal rectangle family.  For every `x0 <= x1` and
`x ∈ [x0,x1]`, `ownerPanelMem_2466` selects the appropriate geometry and
proves the composed 30-family sum containment.  This is the single panel
interface intended for the weighted-node and quadrature attachment.

The module and audit build in the fresh ext4 mirror
`/home/peter/verify/cwr-2460` with Lean 4.30.  The audit reports exactly
`[propext, Classical.choice, Quot.sound]` for
`ownerFamilyPanelMem_2466` and `ownerPanelMem_2466`; no `sorryAx` or project
axiom was reported.

This is still only the panel envelope.  The weighted node sum, trapezoid
bound instantiation, zeta attachment, strip norm, and 2351 invertibility
import remain open.  No GO or RH claim.

Evidence: `ConnesWeilRH/Dev/C1RouteAOwnerIndexedPanel2466.lean` and
`ConnesWeilRH/Dev/C1RouteAOwnerIndexedPanel2466Audit.lean`.
