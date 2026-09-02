# 994 — Route-root option 1: confirmed already-in-place (independent re-verification)

Date: 2026-08-11. Status: verification-confirmation of an existing route-root decision.
No new proof, no new root change. RH NOT claimed.

## Why this memo

User asked to "do option 1": make the finite-band Route-A gate the canonical deliverable
and separate the infinite-carrier open bottom. A source/tree audit shows this decision
is ALREADY the active state of the repo, implemented by the docs/928 route-root margin
(2026-08-10) and carried in the route status document. This memo independently re-verifies that the
claimed closure is real and sorry-free, so no future session needs to re-attempt the
re-point.

## The state (source-verified this session)

1. **Route-root decision** (`docs/proofs/928_gate3u_route_root_decision.md`):
   - canonical deliverable = finite/decaying-band Route-A `bandTerminalGate`
     (`ConnesWeilRH/Dev/RouteATailBandBound.lean`);
   - infinite-carrier Gate (= `(I-P)F = -(I-P)D` / `L_S = 0` on whole carrier)
     stays OPEN, separate, genuinely-new-math bottom;
   - carrier re-point (Piece 2) is not a path to closing the infinite Gate.
2. **Route-A closed** (`docs/proofs/861_routeA_finite_band_gate_closed.md`).
3. **The route status document's active-root section** already carries this
   (`[2026-08-10, docs/proofs/928]`).

## Independent re-verification of the closure (this session)

`RouteATailBandBound.bandTerminalGate` (RouteATailBandBound.lean:115):
  `owner -> lambda -> {rho : Type*} [Fintype rho] -> b : HilbertBasis rho C (sourceSoninCarrier lambda) -> B : Real`
   =>  `canonicalRealGate3UAt owner lambda b ( card_rho*||Support|| + card_rho*C0*exp(-B/4)*prod )`
   via `isTraceClassAlong_finite b (<tail/support>)` + `finiteBandSupport_le` +
   `finiteBand_tail_trace_le` + `inverseLowerFactorPhysicalRenewalTrace_split_bound` +
   `canonicalRealGate3UAt_of_tailNormBound`.
- `sorry`/`admit` grep in `RouteATailBandBound.lean`: 0.  No project axiom introduced.
- This is a REAL finite-band closure of the canonical Gate-3U readout (NOT the
  infinite-carrier seam docs/860).

## Conclusion

Option 1 (elevate finite-band Route-A to sole canonical deliverable; mark infinite open)
is already done and verified. No new route-root paragraph is created (AGENTS §[ returned
rule). The remaining open lane for anyone who wants it is docs/928-§4: prove/refute
`(I-P)F = -(I-P)D` on a non-empty finite-prime family (genuinely new analysis) or Burnol.

RH not claimed. No axiom/sorry introduced.
