# 987 — healthyPsi numeric probe on the raw bump conv-square

Date: 2026-08-11. Status: numeric probe (numpy, WSL). RH NOT claimed. Evidence only.
Companion: docs/proofs/987_healthy_psi_probe.py.

## What was measured (log coordinate additive convolution)

    g = f*f  (f = unitFourierCoreBump = smoothTransition(2-2|x|)), N=40001, dom=4
    psi(g) = pole(g) - arch(g) - term2(g)          (healthyPsi, explicit Weil psi)
    pole(g) = 2 Re M(g, i/2)                     , M(g,c)=int_t e^{c t} g(t)
    arch(g) = C*g(0)+I,  C=log(4pi)+gamma        (docs/967 formula)
    term2(g) = (log 2)/sqrt(2) * (g(2)+g(1/2))

| quantity | value |
|---|---|
| A = g(0) = (f*f)(0) | 1.40571 |
| arch | 2.93078 |
| pole | 4.28576 |
| term2 | 0.49013  (g(2)~1e-16, g(1/2)=1.00000) |
| psi = pole-arch-term2 | +0.86485 |
| vanishing Mellin @0 / @1/2 / @1 | 2.250 / 2.361 / 2.723 |

## What this says (honest)

- **The raw bump is NOT in the finite-vanishing domain** {0,1/2,1}: its Mellins at
  those points are far from 0 (2.25/2.36/2.72).  The C1 criterion only ranges over
  tests that vanish there, so `psi(g)=+0.86` on this bump is **not** a counterexample
  to `CC20Finite VanishingWeilCriterion <= 0` — it just shows the raw sign.
- **Structural observation (useful)**: `term2` is not trivially zero — `g(1/2)=1.0`
  (in log coordinate t=0.5 g is nonzero).  So the healthy finite-`{2}` prime term
  CAN be non-null; it is not a guaranteed-zero cancellation on an arbitrary test.
- arch's sign matches docs/967 (same bump, +2.93). The docs/972 plateau-bump is a
  different test (arch ~ +14.6); this probe uses the 967 witness family.

## Honest bottom line
The healthy `psi` sign is now numeric-probed but gives **no** RH/criterion closure:
the relevant test must first vanish at {0,1/2,1} (a real orthogonal-filter condition),
then `psi(conv^2)` measured. Building such a finite-vanishing test + certifying `psi<=0`
(if it holds) is the actual RH-equivalent step, still open. RH NOT claimed.
