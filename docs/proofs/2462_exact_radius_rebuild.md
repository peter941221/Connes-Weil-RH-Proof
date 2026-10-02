# 2462 - exact-radius 2460 rebuild and axiom audit

Date: 2026-10-02.

The exact-radius correction from `2c86f76a` was rebuilt in a fresh ext4
verification mirror at commit `4c02da3d`. The dependency order was compiled
with Lake and Lean 4.30:

- Mathlib `TrapezoidalRule`: 2676/2676;
- `C1RouteAPanelQuadrature2457`: 2678/2678;
- `C1RouteAQuadratureAttachment2459`: 3711/3711;
- `C1RouteAOwnerPanelSample2460`: 3712/3712;
- `C1RouteAOwnerPanelSample2460Audit`: 3713/3713.

The audit lists all 33 declarations in the sample and reports exactly
`[propext, Classical.choice, Quot.sound]` for every one. No `sorryAx` or
project axiom was reported. Existing Mathlib/package local-change warnings
were from the transplanted warm cache; they did not affect the source build.

This verifies the exact-radius sample only. The full indexed panel theorem,
weighted node sum, zeta attachment, endpoint strip bounds, and 2351
invertibility import remain open.

Evidence: the source and audit are
`ConnesWeilRH/Dev/C1RouteAOwnerPanelSample2460.lean` and
`ConnesWeilRH/Dev/C1RouteAOwnerPanelSample2460Audit.lean`; the build was run
in the isolated mirror `/home/peter/verify/cwr-2460`.
