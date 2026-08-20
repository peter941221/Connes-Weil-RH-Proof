# RH Mainline Freeze

Status: active from 2026-08-19.

## Active Objective

The repository has one active mathematical objective: close the unconditional
Connes--Weil route to the Riemann Hypothesis. The active theorem root is

```text
normalizedSelectedFinalRouteDetectorCriterionCoverageRoot
  -> normalizedSelectedFinalRouteSourceRHFrom08AFromTheorems
  -> cc20FiniteVanishingExitFromTheorems
  -> rhDefinitionBridgeToMathlibFromTheorems
  -> unconditional_rh_skeleton
```

The repository does not currently contain an unconditional RH proof. The root
still consumes explicit project assumptions. This lock prevents diagnostic
results from being mistaken for progress on that root.

## Frozen Routes

The following are archival context only and receive no new theorem work:

- Physical Gate 3U, including the finite/decaying-band Route-A deliverable.
- The infinite-carrier Gate-3U cancellation and leakage identities.
- Gate-3U source owners, renewal/trace probes, and physical audit modules.
- Lane R and Gamma_R prefix/tail sign experiments that do not imply global
  spectral nonnegativity.
- Nyman--Beurling, Mobius, Burnol, prolate, Sonin, adelic, Clifford, and other
  rejected or diagnostic alternatives recorded under `plan/`, `docs/proofs/`,
  `external-opinions/`, and `formalization/`.

The independent finite-band deliverable is physically archived at
`archive/diagnostic_gate3u/deliverable_finite_gate/`. The untracked narrow
Lane-R prefix leaf was archived at
`archive/diagnostic_lane_r/lean/C1XiCenterTwoGammaFinitePrefixNarrow.lean`.
Shared source modules
that are still imported by the RH-facing interfaces remain in place for build
compatibility, but are frozen and may not gain new consumers.

## Allowed Work

New Lean or analytic work is allowed only when the proposed theorem names a
direct consumer in the active RH chain. The current open consumers are:

1. The concrete cutoff remainder/readback on the same mathematical owner.
2. The finite-vanishing Weil criterion on that owner.
3. Global spectral nonnegativity of vanishing squares.

Before editing, record which consumer is being advanced. A bound that ends at
a physical trace, finite band, numerical scan, or conditional contract is not
an RH step and must remain frozen.

The repository check is `scripts/check_rh_mainline_freeze.ps1`. It is read-only
and fails closed on changes under frozen route namespaces. Use its archival
override only for an explicitly reviewed provenance edit.

## Unfreeze Rule

A frozen route may be reopened only after a checked theorem proves a direct
implication to `normalizedSelectedFinalRouteDetectorCriterionCoverageRoot`.
The theorem statement, assumptions, build evidence, and axiom audit must be
recorded in `MEMORY.md` before the route is reactivated.
