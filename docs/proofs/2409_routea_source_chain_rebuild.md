# 2409 — Route A coordinate/composite source-chain rebuild

Date: 2026-10-02.

The repaired 2406/2408 numerical bridge was rechecked independently with
`scripts/routea_repaired_fullgrid_audit_2407.py`.  The readback remains

```text
REPAIRED_FULL_GRID_SAME_EXPRESSION_AUDIT_PASS
```

with 776611 nodes, 39 contiguous spans, four-channel same-expression span
and integral dominance, term-roundup dominance, and matching evaluator/source
hashes.  It still reports `lean_numeric_imported = false` and
`producer_go = false`.

The following source chain was then rebuilt from Lean source in a native
temporary build, rather than relying on existing object files:

```text
C1RouteACoordinateCharge
C1RouteAOwnerDerivativeBudget
C1RouteAOwnerCoordinateCharge
C1RouteACompositeCharge
C1RouteAWeightedChordPanel
C1RouteAChordPanel
C1RouteAExternalOwnerZeroExtension
C1RouteAEndpointStrip
C1RouteAStripTransfer
C1RouteADirectProductDecay
```

The directed accumulation and composite-charge audit modules both compiled;
their audited declarations depend only on
`[propext, Classical.choice, Quot.sound]`.

The source repairs were structural only: explicit owner-scale imports/opens,
the current `WithTop (WithTop ℕ)` smoothness type, interval endpoint order,
`deriv`/`iteratedDeriv` normalization, and the finite trapezoid constant-term
identity.  The expanded dependency closure was rebuilt after replacing stale
`ℕ∞ω` annotations and making second-derivative smoothness orders explicit;
this exposed and repaired the same hidden metavariable issue in the endpoint
strip and strip-transfer consumers.  No numerical conclusion was inserted
into Lean and no RH claim is made here.

The remaining bridge obligations are unchanged: a mathematical nodewise term
dominance theorem, a proved trapezoid remainder bound, and a certified import
of the selected-detector signed kernel/C3' budget.
