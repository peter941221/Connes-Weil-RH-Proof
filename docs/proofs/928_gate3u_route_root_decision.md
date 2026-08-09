# 928 — Route-root decision: elevate the finite/decaying-band Gate as the canonical deliverable

Date: 2026-08-10. Type: route-judgment milestone (design-level root change). No `sorry`,
no new `axiom`. RH NOT claimed.

## 0. Why this memo exists

docs/925, 926, 927 established: (a) the finite-band (route-A) Gate is CLOSED axiom-clean
(`Dev/RouteATailBandBound.lean` `bandTerminalGate`); (b) the infinite-carrier Gate splits
into one load-bearing analytic identity `(I-P)F = -(I-P)D` (Piece 1) plus a carrier
re-point that doc 927 proves is necessary-but-not-sufficient; (c) the deciding `(I-P)F`
term is numerically unreachable (exact Sonin intersection `R0`, AGENT 818/819) and the
reproducible numeric evidence opposes the outer channel. This memo EXECUTES the design
decision those docs recommend: re-point the working route root to the only constructible
Gate, and formally declare the infinite-carrier identity as an open, separate bottom.

## 1. The re-checked Lean state (this session, source-verified)

- The complete off-Sonin leakage `L_S = sourceActualBandCombinedCoframeLeakage
  = sourceActualBandForwardCoframe + sourceSoninCoframeLeakage` is proved orthogonal to
  both `(sourceInclusion)^dagger` (CoframeGuard: optimal) and the Sonin projection
  `P` (`sourceSoninProjection_comp_combined...eq_zero`), so it is fully off-reg.
- `sourcePhysicalCoframeLeakage = Outer + SecondSupport + Prolate`; the nil-family
  cancellation `= 0` relies on `finiteEulerMetricCoframe_eq_sourceInclusion...` for
  `visiblePrimes=[]` (MarkovRawBase). There is NO theorem asserting `L_S = 0` for a
  non-empty family — that is precisely Piece 1.
- Trace-class: the one-prime increment `sourceBand_gGramIncrement_isTraceClassAlong` is
  already proven on `sourceSoninCarrier` (CompletedTraceDifference). The gap is NOT
  increment trace-legality; it is the divergence of `card(B)*‖Support(B)‖` on the
  infinite carrier (docs/927), since `‖Support‖` does not decay in `B`.

These are all consistent with docs 925-927; nothing new in Lean closes the infinite Gate.

## 2. DECISION (this memo)

1. The **canonical Gate deliverable going forward is the finite/decaying-band route-A
   Gate** (`bandTerminalGate`), which is axiom-clean closed on ANY finite Hilbert band
   `rho` with bound `card*‖Support‖ + card*C0*exp(-B/4) prod` for every finite `B`.
2. The **infinite-carrier Gate** (= `(I-P)F = -(I-P)D` / equivalently `L_S = 0` on the
   whole Sonin carrier) is a **separate, open, genuinely-math bottom**: no in-repo
   mechanism forces it, carries repel it, and the deciding term is not numerically
   reachable. It remains OPEN and is NOT claimed.
3. The carrier re-point (Piece 2) is **not a path to closing the infinite Gate** (docs/927);
   it concerns only how a trace certificate transfers, and it does not remove the support
   divergence.

## 3. Why this is the honest close for the constructible route

Concrete verifiable deliverable (finite band) vs. an identity (infinite carrier) that
needs genuinely new analysis. Marking the infinite identified as OPEN (not "remaining
assembly leaf") avoids treating the route as a finite collection of Lean leaves when it
is in fact a real analytic bottom.

## 4. Next frontier (single open step)

Either:
 a) Prove/refute `(I-P)F = -(I-P)D` on a non-empty finite-prime family (Piece 1 —
    load-bearing, genuinely new analysis);
 b) If forced by counterexample, the honest conclusion is that the infinite-carrier Gate
    as defined is not reachable; keep the finite-decaying-band Gate as the deliverable.

RH NOT claimed. This is a route-root decision artifact, not a mathematical proof of RH.

