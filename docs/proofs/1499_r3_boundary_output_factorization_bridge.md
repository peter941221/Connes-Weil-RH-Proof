# 1499 — R3 boundary output factorization bridge (map 042 WO-B, B1+B2)

**Status: FORMAL.** New leaf
[`C1G8R3BoundaryOutputFactorizationBridge.lean`](../../ConnesWeilRH/Dev/C1G8R3BoundaryOutputFactorizationBridge.lean)
(+ paired audit `C1G8R3BoundaryOutputFactorizationBridgeAudit.lean`).
RH is not claimed; no leg estimate is claimed.

## What is bridged

Map 042 left the boundary-side diagonal energy `hBoundary` as per-output
obligations over `finiteEulerMetricCoframeBoundaryMaps`. This brick closes the
*reduction* of every output to three named source-carrier legs.

* **B1 (factorization).** By structural induction on the visible-prime suffix,
  every actual boundary output of `suffixEulerBoundaryOutputMaps` — hence every
  summand of `finiteEulerMetricCoframeBoundaryMaps` — factors exactly as
  `output = M ∘L J ∘L N` with an ambient factor `M` and a source-side factor
  `N` (`suffixEulerBoundaryOutputMaps_factorization`,
  `finiteEulerMetricCoframeBoundaryMaps_factorization`). The head step uses the
  Schur-step identity
  `boundaryDagger = (I − newFrame newFrame†) ∘L transport† ∘L oldFrame` with
  the transport ambient-side (`suffixEulerFrameSchurStep`) and the old frame
  `oldSuffixFrame lambda p S = parameterizedFiniteEulerFactor 1 (p :: S) ∘L J ∘L GramInvSqrt (p :: S)`;
  the tail step absorbs the transition adjoint into `N`.
* **B2 (per-output exact split).** For every `M`, `N` the composed diagonal
  energy splits pointwise (`g8AmbientSourceLeg_energy_normSq_split`), and the
  OUT band carries `M` inside the exact record-1494 identity
  (`g8AmbientSourceLeg_outLeg_pointwise_eq_boundary_add_gap`):

```text
‖(C ∘L M ∘L J ∘L N) w‖^2
  = ‖(J† ∘L C ∘L M ∘L J) (N w)‖^2            (in-Sonin response leg)
  + ‖((I−E) ∘L C ∘L M ∘L J) (N w)‖^2         (radial-boundary leg)
  + ‖((E−P) ∘L E ∘L C ∘L M ∘L J) (N w)‖^2    (internal-gap leg).
```

Consequences, per output and for the aggregate:

* necessity: the composed energy controls the in-Sonin leg
  (`g8AmbientSourceLeg_inLeg_normSq_summable_of_energy`);
* sufficiency: the three legs reproduce the composed energy
  (`g8AmbientSourceLeg_energy_normSq_summable_of_legs`, recombining the two
  leakage legs by the record-1494 identity);
* assembly: if every output admits such a factorization with all three legs
  square-summable, the exact `hBoundary` condition of the record-1492/1493
  consumer holds, unchanged
  (`g8MetricVisibleBoundary_root_energy_summable_of_legs`).

## What this does and does not close

WO-B items B1 and B2 are landed as exact operator identities. The three leg
estimates remain open: the committed record-1495/1496/1497 window identities
are for the owner's root convolution, while each leg here carries an extra
ambient factor `M_p` from the Schur boundary step, so none of them is
instantiated by existing theorems. The diagonal energies, trace-to-`qw`
readback, and RH remain open.
