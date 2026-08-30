# 1058 - Alpha reconnaissance verdict: the endpoint profile is 11 terms deep

Date: 2026-08-30.  Follows 1056, 1057.  Probe:
`docs/proofs/1058_alpha_chi_reconnaissance_probe.py`.

Result up front: **GOOD.**  All three blocks pass, the paper's own tail
arithmetic reproduces to six digits, and the prolate concentration
eigenvalues decay superexponentially exactly as the appendix (169) bound
requires.  The GATE 1 (alpha) long pole changes from "indefinite spectral
realization project" to "11-mode validated-ODE campaign with a published
tail".  It is still weeks of work - it is no longer open-ended.

## 1. What was decided

`1044` left alpha as two open fields (`hchi`: concrete
`CC20EndpointSpectralData` + enclosure of chi on e^|v| in [1,2]; `hmass`:
certified L1 quadrature of |chi - tau|).  `1057` section 3 discovered that
CC20's own eq (170) truncates chi to 11 terms with remainder <= 2.366e-12.
This probe decides whether that truncation story is arithmetically TRUE
(control block A), whether the eigenvalue decay it relies on is real
(B), and whether the slope series the Lean structure demands converges at
reconnaissance level (C).

## 2. Measurements

```text
A  control, mpmath dps=60, the paper's closed-form series of eq (169):
   sum_11^34 term_n        = 2.36527e-12      (paper states ~ 2.365e-12)  MATCH
   sum_11^inf term_n       = 2.36527e-12  <= 2.366e-12                    PASS
   nu_{n+1}/nu_n ratio identity (tex proof of (170)), n = 35..59          PASS (tol 1e-40)
   nu_35                   = 4.11096e-81 <= 5e-81                         PASS
   sum_35^inf nu_n         = 4.11306e-81 <= 1e-80                         PASS
   p(n) <= 120 n^2, n = 35..199 (no violations)                           PASS

B  scale, concentration eigenvalues of P_window Q_band on [-1,1],
   Gauss-Legendre collocation M = 600:
   [AMENDED 1059: this row's "c = 2 pi" label was WRONG - collocation
    bandwidth was omega = pi; the paper's actual lambda(n) spectrum is
    the omega = 2 pi EVEN branch, measured in probe block B2:
    [0.9999428, 0.9593903, 0.2746660, 3.478238e-3, 7.465620e-6,
    5.820371e-9], paper bound (983) verified n = 0..5.]
   band c = 2 pi:  lambda_0..4 = [0.981046, 0.749620, 0.243593,
                    0.024647, 0.001066], all |lambda_n| < 1
                    consecutive ratios (above float64 floor, depth 11):
                    3.25e-01, 1.01e-01, 4.33e-02, 2.57e-02, 1.75e-02,
                    1.28e-02, 9.74e-03, 7.67e-03, 6.21e-03
   repo kernel scale c = 2:  [0.572582, 0.062791, 0.001237, ...] (floor idx 7)
   Reading: per-step decay ~ (C/n)^2 consistent with the (169) ratio limit
   pi^2/(16 n^2); lambda_10(c=2pi) ~ 1e-22 sits BELOW float64 eigvalsh
   resolution (collocation floor hit at index 11).

C  slope feasibility: sum lambda_n^2/(1 - lambda_n^2) * v_n(1)^2 over the
   top 20 collocated modes: partial sum 11.8254, terms drop from
   1.182e+01 (n=0) to 8.4e-26 (n=9); no non-summable behavior detected.
   Normalization is discrete collocation, not the paper's xi_n^an -
   magnitude is reconnaissance only.
```

## 3. Judgment

```text
GO (shape decision for the alpha brick):
  1. Enclosing chi on [1,2] = high-precision (mpmath/arb) data for n <= 10
     only: lambda_n, the analytic-continuation modes xi_n^an at the needed
     arguments (including the x > 1 continuation side of rho in [1,2]), and
     the slope series; the REST is bounded by the paper's own published
     2.366e-12 tail, whose arithmetic this probe reproduced exactly.
  2. Precision floor note (AGENTS 7c rule family): float64 eigvalsh cannot
     see lambda_7..10 (they fall below the collocation noise floor); the
     campaign must compute eigenvalues/modes in arbitrary precision.  This
     is a classical, well-conditioned regime (fixed depth 11, no Krylov
     amplification, no moment problem - 7c rule (8) does not bite).
  3. The Lean shape: CC20EndpointSpectralData instance with
     eigenvalue_sq_lt_one and endpointSlope_summable proved from the (169)
     comparison, qEpsilonSummand enclosure via interval Taylor for the
     angular prolate ODE plus continuation across x = 1, hmass via the
     yoshida_intervals pattern against the enclosed chi.
RESOLVED:
  4. [CLOSED by 1059, then CORRECTED by 1062] the block-B2 values
     [0.99994, ...] are the CONCENTRATION (squared) eigenvalues, i.e. the
     paper's lambda(n)^2, NOT lambda(n); the true convention (tex:967-983
     re-read verbatim) is lambda(n) = (-1)^n sqrt(these) = the SINGLE
     windowed-Fourier eigenvalue (prolateeq/cosalphan), and the paper's
     own printed list [0.999971, -0.979485, 0.524086, ...] confirms it.
     The repo c = 2 / omega = pi rows are different spectra and must not
     be substituted.  MP/ARB onset: n >= 6 on the even branch.
STILL OPEN:
  5. beta stays blocked by alpha; F1 is re-scoped by 1059 (2b perturbation
     REVOKED; 2a algebra + conditional premise are the default).
```

## 4. Reproduction

```text
wsl bash scripts/run_1058_probe.sh
# interpreter: /home/peter/venv-46937-py312 (mpmath 1.3.0, numpy 2.3.5)
# log: /home/peter/cc20/probe1058.log
# expected: section 2 output verbatim (deterministic; no RNG).
```

## 5. Sources

```text
docs/proofs/1057 sections 2-4 (eqs 115, 119, 140-143, 169-170, verbatim).
docs/proofs/1044 (reduction fields), 1046 (payload table), 1049 (Bessel branch).
CC20 arXiv:2006.13771 source sha256 b01d353b...20f3fc (1057 section 0).
Probe: docs/proofs/1058_alpha_chi_reconnaissance_probe.py.
```
