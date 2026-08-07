# 863 - Gate 3U infinite-carrier reopen: 1A vs 1B

Status: decision brief (roadmap comparison, not a Lean proof). Date: 2026-08-07.
Lane: infinite-carrier Gate readout. Preceded by 860 (tail-trace block) and 861
(finite-band route-A closed, on main).

## The single seam

Finite-band Gate is closed (bandTerminalGate, RouteATailBandBound.lean). The infinite Gate
needs one missing piece:

    |(ordinaryTraceAlong b tailResp).re| <= bound   on b : HilbertBasis rho (sourceSoninCarrier),  rho infinite.

860: sourceSoninCarrier lambda = (radial ^ fourier support intersection) is an infinite-dim
closed submodule with no FiniteDimensional / IsTraceClassAlong / HS / nuclear instance; the
prolate trace-class bundle lives on finiteCarrier/globalBasis, not on the Gate carrier.

## Option 1A - re-point the Gate carrier to an HS / finite-rank basis

Change: move the trace readout to a carrier where trace-class is provable.
+ trace-class true by construction; |Re Tr| <= card * opNorm formalizable.
+ reuses the already-proved operator-PSD machine (windowedBoundaryDetector IsPositive).
- re-defines the carrier that Gate-3U = trace-of-sourceOwner is built on.
- A2 blocker: SourceTestAlgebra needs LegacyTestEquiv Test; re-point to CompactLogTest fails
  (no decode: TestFunction -> CompactLogTest).
- must prove the readout is invariant under the swap (AGENTS same-owner rule).
- wide blast radius (SSG M1/M3, canonicalRealGate, tail users).

## Option 1B - prove a new analytic trace (Schatten/nuclear) bound on the existing carrier

Change: keep sourceSoninCarrier; prove the tail is trace-class from geometry
(exp operator-norm decay pushed through a Schatten/interleaving).
+ no model change; true trace on the object you want; narrow blast radius.
- genuinely hard, may be analytically degenerate (probes 819-824: Son transport non-decay,
  outer channel plateaus ~0.62); the missing step is a real analytic bound, not a Lean gap.

## Comparison

| axis           | 1A re-point              | 1B analytic trace bound     |
|----------------|--------------------------|-----------------------------|
| change         | carrier type + owner     | none; new bound             |
| trace-class    | by construction          | must be synthesized         |
| reads the gate | risk "on a rebased space"| yes, on the true object     |
| big unknown    | same-owner invariance    | existence of Schatten bound |
| structural     | A2 LegacyTest (no cheap)| Sonin transport non-decay   |
| blast radius   | wide                     | narrow (module + 1 lemma)   |

Recommended order: (1) run the analytic (math) check of 1B first, low blast; (2) only if 1B
confirms open, do 1A with explicit review of readout invariance under the swap.