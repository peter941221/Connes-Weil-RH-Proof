# 2470 - first actual-owner node-upper read

Date: 2026-10-02.

The 2453/2454 node-norm certificate was checked before reuse.  Its
`capBaseCoef2453`/`capCorrCoef2453` data are the older 2275 captured owner,
so its node bounds are not transferred to the exact 2460 owner.

This record closes one current-owner node instead.  At `x = 1/4`, the theorem
`ownerNodeUpper2470_zero` consumes the universal indexed panel rectangle
(`2466`) through `ownerPanelNormBound_2467`, with the exact 2460 owner
coefficients, modulations, radii, and production panel containing `1/4`.
The bound is exposed as `ownerNodeUpper2470 0`; no old capture is imported.

The ext4 mirror build and direct declaration audit pass.  The audited theorem
has exactly `[propext, Classical.choice, Quot.sound]` and no `sorryAx`.

Scope: one node only.  This is not yet the `∀ index ≤ cells` nodeUpper
certificate required by `ownerPanelStripNorm_le_nodeUpper_2469`, and it makes
no producer, GO, RH, or strip verdict claim.
