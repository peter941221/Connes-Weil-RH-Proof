# 1107 - SOS upper-bound machinery, diagnostic preview (pre-registration)

Date: 2026-09-03.

Status: PRE-REGISTRATION, committed BEFORE the run. Record 1105 made
A + P = -Z an internal decision-grade fact; record 1106 shrank the E0
multiplier set to ONE constraint. This record previews the re-registered
E0 machinery - an SOS upper bound instead of eigenvalue-margin surgery:

```text
A + P = -Z_N - Z_tail   (Z_N = first-N zero Gram, Z_tail the rest),
top(A+P)|_V <= -lambda_min(Z_N) + ||Z_tail||,
```

so a CERTIFIED negative upper bound on the gate top follows once
lambda_min(Z_N) exceeds a certified tail bound - no eigenvalue sign
has to be resolved at the pinning scale. This is the certified-
upper-bound machinery named as the next C3 target by 1100b/1101.

## 1. What this diagnostic record can and cannot preview

The identity residual measured numerically (record 1105: 1.7e-6 of
||A|| at (2,8)) is QUADRATURE noise. In the certified route the
identity is the EXACT Lean kernel identity (the Weil explicit formula
on the carrier; the arch-vs-Weil kernel agreement already stands at
1e-26, record 1020/1102 lineage), so the residual term drops out of
the certified bound and only two computable ingredients remain:

1. lambda_min(Z_N) on V (interval-certifiable eigenvalue of an
   explicitly constructed PSD sum of squares);
2. tau_N = ||Z_tail||, bounded analytically by zero-counting measure
   times the Fourier decay of the window basis at ordinates above
   gamma_N (RH-free: absolute-value bound, horizontal position of the
   zeros irrelevant).

This probe measures both ingredients at diagnostic float64 and checks
whether a margin exists. It does NOT certify anything; certification
is a later record on the 1101 interval machine. RH is not claimed;
the margin, if positive, certifies (star) on the fixed window space V
only - the Q-F2 function-class gap is untouched.

## 2. Cells, quantities, verdict mapping (literal, law 42)

Cells (a, K) = (2, 8) and (4, 8); N in {60, 120, 300}; reference tail
at N_ref = 600 + density tail. Per (cell, N):

- lam_N = lambda_min(Z_N|_V) (eigh, symmetrized);
- tau_N = ||Z_ref - Z_N||_F (measured tail mass proxy);
- m_N = lam_N - tau_N (preview margin);
- also printed: top(M) for orientation.

Registered feasibility criterion: PASS iff for at least one cell some
N gives m_N > 1e-7 (one full decade below the 1101 certified straddle
band of 9.68e-8 - the SOS margin must BEAT the old noise band to be
worth certifying). FAIL => the SOS route is demoted (eigenvalue
surgery or a different decomposition); ABORT on anchor drift > 2e-3 or
zetazero failure. Registered expectation (honest): lam_N decreases
with N toward the true pin depth while tau_N decreases too; the margin
is expected to peak at intermediate N, and at (4, 8) lam_N may already
sit below the quadrature floor (then only (2, 8) can PASS).

## 3. Execution

Probe `1107_sos_upper_bound_probe.py` imports the verbatim p6_weil
zero_gram construction (1105 bundle). WSL-side through `.venv-probe`,
log local (gitignored).
