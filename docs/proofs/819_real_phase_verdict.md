# Proof-717 / Gate-3U: 819 — real archimedean phase does not rescue numeric R0 (rank ≠ 0 but never a projector)

Date: 2026-08-06
Status: confirmatory negative — reinstalling 818's toy phase with the repo's
REAL archimedean Gamma-phase `m` raises the numerical intersection's `rank`
from 0 to 8 at logλ=0, but **idempotence still does not converge** as iteration
grows.  So R0 is still NOT a usable orthogonal projection, and the inner
second/band channels remain numerically untrustworthy.  The outer channel stays
the only honest number and it is again non-zero and primes-growing.
Branch: `proof/gate3u-completed-readout`
RELATED: `docs/proofs/815_rh_route_conditional_boundary.md`, `816`, `817`, `818`

## 1. The real object installed (vs 818's toy clone)

The actual archimedean phase/local factor, now used explicitly as the spectral
"scattering" clone (`CCM24HardyTitchmarsh.lean`):

```
archFactor(xi) = GammaR(1/2 - 2 pi i xi) = pi^-(z/2) * Gamma(z/2),   z = 1/2 - 2 pi i xi   (:43-45)
archFactor(-xi) = conj(archFactor xi)                                                        (:74, proved)
archFactor(xi) ≠ 0                                                                          (:47, proved)
m(xi) = archFactor(xi) / archFactor(-xi)          has |m| = 1                                (:104-106)
HT0   = F . m . spectralReflection . F                                                        (:331-336)
```

818 had used a toy `m = exp(2 * tanh(x))`; the point of 819 was to see whether the
toy was the source of 818's degeneracy.

## 2. Result — rank rescued, convergence lost

On a finite `n=80` grid at `logλ=0`, alternating projection onto
`range(R) ∩ range(Q0)`, `Q0 = HT†R·HT`:

```
             rank(R0)   idempotence   characterization
REAL-Gamma    8         8.7e-2        NOT a projector (no convergence)
toy           0         3.9e-12       collapsed to 0 (a valid projector, wrong dim)
```

The dim responds to the phase, the convergence does not: real → 8-dim
intersection but non-idempotent; toy → 0-dim but idempotent.  Neither is a
usable `R0`.

## 3. Convergence profile — the real blocker

```
logλ=0, real archimedean phase, alternating projection:
  k=10    rank  8   idempotence 3.04e-1
  k=50    rank  8   idempotence 3.19e-2
  k=200   rank  8   idempotence 1.10e-1
  k=800   rank  8   idempotence 2.54e-1
  k=3000  rank  8   idempotence 2.55e-1
```

Idempotence does not → 0; it rises after k≈200.  The iterate stabilizes at a
non-idempotent ~8-dim limit.  Von Neumann alternating projection converges
geometrically only if the angle between the two subspaces is bounded away from
0; here `range(R)` and `range(HT†R·HT)` are almost-parallel (their analytic
intersection is the thin Sonin band), so the finite discretized projection
cannot be forced to an idempotent limit on the grid.

## 4. Verdict (honest)

```
819 did NOT make R0 usable; it confirmed 818 with the real phase.
  - dimension rescued (0 -> 8) but convergence NOT (idempotence never -> 0)
  - second/band channels STILL not trustworthy numerically
  - outer channel re-measured on the same engine: {2}=0.16, {2,3}=0.22,
    {2,3,5}=0.25 at logλ=0  (0.17/0.25/0.31 at logλ=1), non-zero & growing
```

## 5. Consequence (Lean-shaped)

`818+819` together are a **numerical-geometry negative**: the exact Sonin
projection `R0` is not stably computable on a finite grid, even with the true
archimedean phase, because the underlying subspace pair has no AngleLowerBound.
Meaning anything that cannot reach the analytic prolate/Sonin frame 815 named
cannot measure the inner gate channel — it is "analytic, not algebraic" in
815's own words.

## Discipline

819 is a confirmatory methodological negative; it does not decide the gate and
asserts nothing about RH. It rules out finite alternating-projection `R0` even
with the real phase, and re-measures the outer channel.