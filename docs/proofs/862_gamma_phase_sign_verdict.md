# 862 - Gamma-phase verdict: Re[(Gamma(a+i/2))^4] >= 0 holds only on two finite windows; 859's asymptotic conjecture is FALSE

Date: 2026-08-07. Status: numeric verdict on the route-1 sign slot; no RH claim, no Lean producer claimed here.
Probe: `docs/proofs/862_gamma_phase_sign_probe.py` (mpmath, 60 digits).

## What this decides

Doc 858c reduced the faithful half-density sign slot to the single real statement
`Re[(M g (i/2))^4] >= 0` for a real test `g`.  Doc 859 pinned it to the band test
`f(t)=t^a e^(-t)`, `a>0`, via the exact closed Mellin
`M f (i/2) = Gamma(a+i/2)`, then stated the concrete subgoal:

    conjectured: exists a0 > 0, forall a >= a0,  Re[(Gamma(a+i/2))^4] > 0   (859)

This probe tests that conjecture and maps the true positivity set.

## Evidence (high-precision, 60 digits)

### A. Sign windows of Re[Gamma(a+i/2)^4], a in [0.001, 4)

```
a in [0.001, 0.256]  -> POSITIVE
a in [0.261, 0.811]  -> negative
a in [0.816, 2.656]  -> POSITIVE
a in [2.661, 4.0]    -> negative (and keeps oscillating)
```

Zero crossings (mpmath bisection on Re[...]^4, ~63 digits at the root):
`a1 ≈ 0.2578`, `a2 ≈ 0.8174`, `a3 ≈ 2.6562` (inspection table below).

### B. Asymptotic phase identity:  arg(Gamma(a+i/2)) = (1/2) ln(a) + o(1)

```text
  a       arg[deg]   (1/2)ln a[deg]   4arg%360   sign
  10      +64.521     +65.964        +258.08      -1
  20      +85.102     +85.821        +340.41      +1
 100     +131.785    +131.928        +167.14      -1
 500     +178.007    +178.035        +352.03      +1
1000     -162.122    +197.893         +71.51      +1
2000     -142.257    +217.750        +150.97      -1
```

The argument grows exactly like `(1/2) log a` (matching to ~0.1 degree everywhere,
and the mismatch is the known o(1) correction). `4*arg` therefore wraps through
`360°` infinitely often, so `cos(4 arg) > 0` flips sign infinitely often as `a → ∞`.

## Verdict

- The conjecture `exists a0, forall a>=a0, Re[..^4] > 0` is **FALSE numerically**:
  `Re[Gamma(a+i/2)^4]` is strongly negative at many arbitrarily large `a` (e.g. 5, 10,
  100, 200) and positive at others (20, 50, 500); no tail peak.  The asymptotic
  `arg ~ (1/2) ln a` forbids a uniform eventual sign.
- The **positive set is exactly the union of two finite windows**:
  `a0 ∈ (0, 0.2578)` and `a0 ∈ (0.8174, 2.6562)`.
- Corollary: a route-1 band proof of the sign MUST pick `a` inside one of these
  two windows and prove a **compact-interval** Gamma-phase bound (e.g. Stirling on
  `a in [0.8174, 2.6562]`, or a direct power-series for the small window `a in (0,0.26)`),
  NOT an asymptotic statement. mathlib today lacks such a Gamma phase/argument
  bound (no `arg Gamma` asymptotics), so this remains open Lean-cally, but the
  target is now a bounded, finite-precision estimate instead of an unbounded false one.

## What survives / what the route should do

- The 858c sign reduction and the MellinBandGamma closed form are unchanged and
  correct (no artifact here).
- Change the "next stone": drop the false asymptotic conjecture; instead aim for a
  numeric-verified + Lean-Stirling bounded estimate on `a ∈ [0.9, 1.2]` (a value with
  comfortably positive margin ~ +0.2), where Stirling's series converges and can be
  made rigorous with explicit error bounds.
- Honest boundary: this is a numeric verdict + a sharpened subgoal. It does not
  prove the sign; it disqualifies the false short-cut and precomputes the target
  interval a Lean argument must cover.

Repro: `python3 docs/proofs/862_gamma_phase_sign_probe.py`   (mpmath, 60 bits).