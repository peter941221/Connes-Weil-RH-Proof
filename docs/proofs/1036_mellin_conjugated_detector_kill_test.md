# 1036 — Mellin-conjugated Hilbert detector kill-test

Date: 2026-08-19.

Status: **rejected as a Weil readback owner**.  The finite matrices are
positive and finite-section trace class, but the candidate fails the two
structural tests that matter for the active C1 consumer: the Mellin
half-density conjugation leaves a cutoff-length bulk, and removing that
conjugation still gives the wrong `m=2` prime-power coefficient.  No Lean
namespace was changed and RH remains unproved.

## Candidate

In the additive logarithmic coordinate, let `H` be the periodic Hilbert
transform, `M_sigma` multiplication by `exp(sigma*x)`, and `P_[0,L]` the
one-sided cutoff.  The screened positive factor is

```text
B_L(g) = [ M_(1/2) H M_(-1/2), P_[0,L] ] C_g,
positive_trace_L(g) = ||B_L(g)||_HS^2.
```

The root `g` is used unchanged for the convolution owner
`F = g^* * g`, the triple Laplace constraints, and every prime-power
readback.  This is the minimum same-owner requirement before any analytic
estimate could be promoted to `C1PositiveTraceLimitBridge`.

The local coefficient that must be reproduced is fixed by the half-line
crossing identity

```text
Tr(C_g^* C_g (J_b + J_b^*)) = b (F(b) + F(-b)),
b = m log(p).
```

The logarithmic Euler coefficient `p^(-m/2)/m` therefore gives

```text
p^(-m/2) log(p) (F(m log(p)) + F(-m log(p))).
```

In particular, passing `m=1` is not enough; `m=2` must carry the factor two
from the crossing length and no extra factor from the detector.

## WSL2 runs

All runs below used the Ubuntu-24.04 ext4 verification mirror, NumPy only,
and `OPENBLAS_NUM_THREADS=4`.  The command was run from the repository mirror
with the new script copied from the Windows source tree.

```text
python3 -B docs/proofs/1036_mellin_conjugated_detector_kill_test.py
python3 -B docs/proofs/1036_mellin_conjugated_detector_kill_test.py \
  --mellin-sigma 0 --size 256 --step 0.05 \
  --cutoffs 0.75,1.5,2.25,3.0,3.75
```

The first command uses `sigma=1/2`, `size=256`, `step=0.06`, and cutoffs
`0.75,1.5,2.25,3.0,3.75,4.5`.  The second is a control with the ordinary
Hilbert transform (`sigma=0`) on a finer grid.

## Results

```text
+----------------------+----------------------+----------------------+
| diagnostic            | Mellin sigma=1/2     | control sigma=0      |
+----------------------+----------------------+----------------------+
| narrow bulk slope/mass| +1.649832402865e+00  | +4.693871275067e-04  |
| p=2 root bulk slope   | +1.091378207646e+01  | -3.458838276961e-03  |
| narrow tail step/mass | +5.090610573687e+00  | +2.542846571371e-04  |
| p=2 tail step/mass    | +3.787508097170e+01  | +5.301294394400e-05  |
| minimum finite trace  | +1.722205501199e-01  | +8.547178066248e-02  |
| triple-node residual  |  8.393286066166e-16  |  4.218847493576e-16  |
| anti-Hermitian error  | +1.414159318284e+00  | +2.996376932980e-16  |
+----------------------+----------------------+----------------------+
```

The prime-power ratio test calibrates only one harmless overall scalar at
`m=1`, then compares the observed `m=2/m=1` ratio with the exact owner ratio.
This removes normalization ambiguity while retaining the `m=2` obstruction.

```text
+----------------------+----------------------+----------------------+
| prime / check        | Mellin sigma=1/2     | control sigma=0      |
+----------------------+----------------------+----------------------+
| p=2 m=2 ratio error   |  6.270075554431e-01  |  5.505217656057e-01  |
| p=3 m=2 ratio error   |  1.193045144733e+00  |  1.892996700322e+00  |
| p=2 Euler sum error   |  4.037412623102e+01  |  7.524426762948e-01  |
| p=3 Euler sum error   |  1.266514456753e+02  |  1.261657395348e+00  |
+----------------------+----------------------+----------------------+
```

The output also reports `finite_cutoff_trace_class=PASS`,
`same_owner_readback=PASS`, and `positivity_verdict=PASS`.  Those are
necessary bookkeeping checks, not evidence for a limiting trace theorem.

## Interpretation

```text
+--------------------------------------+-------------------------------+
| layer                                | verdict                       |
+--------------------------------------+-------------------------------+
| finite A* A positivity               | survives                      |
| finite cutoff trace-class             | survives as a matrix fact    |
| Mellin sigma=1/2 no-bulk condition    | FAIL                          |
| ordinary-H no-bulk control            | passes sampled control       |
| same-owner g -> F readback            | enforced by the probe        |
| exact p=2, m=2 coefficient            | FAIL for both variants       |
| remainder limit / analytic readback   | not reached                  |
| global spectral nonnegativity         | OPEN                          |
| RH                                   | UNPROVED                      |
+--------------------------------------+-------------------------------+
```

The `sigma=1/2` failure is not a small quadrature fluctuation: the conjugated
Hilbert matrix is no longer skew-adjoint in the unweighted finite-section
inner product (error approximately `sqrt(2)`), and the trace grows rapidly
with the moving endpoint.  The `sigma=0` control shows that the same grid and
window geometry can resolve a boundary-stable commutator, so the bulk signal
is tied to the proposed conjugation rather than to the cutoff alone.

The control still fails the arithmetic owner test.  For `p=2`, its calibrated
`m=2` ratio error stays near `0.55` under grid refinement; for `p=3` the
observed and required ratios have opposite signs.  Thus the detector does not
contain the `a^m/m` logarithmic coefficient before the crossing length is
inserted.  This is the same failure mode isolated abstractly for the metric
Sonin endpoint in
`docs/proofs/042_metric_sonin_second_prime_power_rejection.md`.

## Scope and caveat

The probe is a finite periodic discretisation.  It is evidence against this
operator family and its stated owner, not a theorem that every Hilbert or
Mellin construction is impossible.  A successor must specify a unitary
weighted Hilbert space (or an explicitly symmetrized conjugation), keep one
root/autocorrelation owner, and pass the exact `m=2` coefficient before any
remainder estimate is worth formalizing.

## Decision

Do not add a Lean detector, a `PositiveTraceLimitFamily`, or a route import for
this candidate.  The active RH root remains
`normalizedSelectedFinalRouteDetectorCriterionCoverageRoot`; this screen only
removes one proposed producer for its open global spectral-nonnegativity
consumer.

## Next steps

1. Require the logarithmic-derivative owner to expose the `1/m` coefficient
   before applying a boundary projection.
2. Re-screen a unitary weighted/Hilbert pair with the same `m=2` ledger and a
   finite-window remainder subtraction.
3. Only after those gates pass, build a same-owner Lean interface feeding
   `C1PositiveTraceLimitBridge`.
