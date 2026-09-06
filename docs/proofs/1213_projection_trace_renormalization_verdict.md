# Record 1213 - Projection-trace renormalization probe VERDICT: H2

Date: 2026-09-06.  Status: VERDICT RECORD for the probe pre-registered in
`1212_projection_trace_renormalization_probe_preregistration.md`
(committed `5dbbdd2` BEFORE any run; law 42 no-rescoping respected — all
method changes below were made BEFORE the first official run and are
disclosed here in full).

## 0. Verdict (registered branch H2)

```text
Q1  The insertion trace T_n has NO divergent leading term under the
    projection kernel K = P_r P_f P_r - P_V.  The continuum-normalized
    trace Tn^cont = T_n * dt^2 is WINDOW-INDEPENDENT: consecutive
    two-point slopes are alpha ~ +2.2..2.7e28, i.e. 1.6e-5 .. 1.9e-5 of
    the constant part.  The 1210 linear divergence (tr ~ 2 R_n * f0,
    growing) is fully absorbed by the projection; the "divergent
    counterterm" that exit A needs does not arise.  bulk^cont = 2 R_n f0
    grows linearly as registered, but T_n^cont does not follow it
    (T_n / tr(C_n^* C_n) falls from 0.0399 at n=8 to 0.0101 at n=64).
Q2  The finite part settles, but NOT at qw(g):

        FP_inf = +1.3791e33   (fine grade, stable to ~2e-4 relative
                               across n = 8, 16, 32, 64)
        qw(g)  = -4.1526e32   (pinned 1116 delta=0 twin)
        FP_inf / qw = -3.321  (opposite sign, 3.32x magnitude)

Verdict branch: H2 (refutation) — "FP_n settles outside the acceptance
band".  |FP_inf - qw| = 1.794e33 against an H1 band of 4.75e31
(10 * eps_effective, eps_effective = worst coarse-vs-fine relative
discrepancy 3.4e-3).  The margin is 38x; even taking the full rung-to-
rung FP spread (1.6e-4 relative) as eps_effective leaves the mismatch
13x outside the band.  The verdict is robust.
Registered consequence: exit A (retain a divergent counterterm, read qw
from the renormalized finite part) is CLOSED for this family.  Pivot to
exit B (moving/renormalized response) or the 1209 signed-tail route —
a routing decision, not made by this record.
```

## 1. Official run identity

- Script: `docs/proofs/1212_projection_trace_probe.py` (commit `2d242b9`
  state + the two fixes disclosed in §3, both pre-verdict).
- Machine: WSL2 Ubuntu-24.04, `uv run --with numpy --with scipy
  --with mpmath`, in-house only (no external AI, directive 2026-09-03).
- Registered dials: LAMBDA=1.0, S_PRIMES={2,3,5}, R0=10.05, R_n=R0+n+1,
  n in {8,16,32,64}, PAD=24, RANK=320, N_COARSE=8192, N_FINE=16384,
  PV_TAU=1e-8.
- Two invocations:
  1. `..._invocation1_fineonly.json` — a pairs-loop bug iterated only
     the fine grade (N=16384) of each rung.  Its four fine rows are
     statistically identical to invocation 2's (same dials; eigsh start
     vector differs).  Preserved as evidence.
  2. `1212_probe_results.json` — the corrected loop, both grades at
     every n; THE official dataset (exit code 0, 8/8 rungs).
- Raw outputs: the JSON files plus the task log lines reproduced in §2.

## 2. Data

Physical normalization: `Tn^cont = T_n * dt^2`, `bulk^cont = bulk * dt^2`.
Two factors of dt: one from `tr_disc ~ tr_cont/dt`, one from the kernel
integral inside `W[i,i] = sum_k |gt(t_k-t_i)|^2 win(t_k) ~ f0/dt`.
Check: `bulk*dt^2 = 2 R_n f0` holds to <= 1.3e-4 relative at every rung
(the Nw+1 grid-count rounding).  `f0d * dt = f0 = 9.083104e32` to six
digits at every grade — the grids RESOLVE the detector (see §3.7).

Fine grade (N=16384), physical values:

```text
  n      Rn        Tn^cont     Tn/bulk   bulk^cont=2Rn*f0   tail_gap
  8   19.05   +1.380102e+33   0.039875     3.461107e+34     1.2e-16
 16   27.05   +1.380528e+33   0.028095     4.913709e+34    -4.8e-16
 32   43.05   +1.381247e+33   0.017663     7.820187e+34     3.0e-15
 64   75.05   +1.382789e+33   0.010142     1.363469e+35     2.5e-14
```

Coarse grade (N=8192) agrees to 1.5e-3..3.4e-3 relative (this measured
spread IS eps_effective).  tail_gap <= 2.5e-14 everywhere: the RANK=320
spectral trace captures the whole window operator; no truncation bias.

Q1 slopes (fine, consecutive two-point, law 60):

```text
[n=8,16]:  alpha = +2.658e28   (1.93e-05 of the constant part)
[n=16,32]: alpha = +2.247e28   (1.63e-05)
[n=32,64]: alpha = +2.410e28   (1.75e-05)
```

Q2 finite part after removing the (negligible) fitted slope:

```text
FP_8 = +1.379089e33   FP_16 = +1.379089e33
FP_32 = +1.379312e33  FP_64 = +1.379171e33     FP/qw = -3.3210..-3.3216
```

S0 gates at the official invocation (all green before any sign readout,
per prereg §5):

```text
S0.1 correction residual 2.26e-79; f0/arch/prime vs committed 1116
     delta=0 row: 0.00e+00 / 0.00e+00 / 1.83e-16
S0.2 HT involution 4.7e-16; readback 0; E o E^-1 and E* o (E^-1)*
     4.0e-15; T_S involution 5.1e-16
S0.4 P_f idempotent 9.8e-13, self-adjoint 6.8e-18, G cond hint 1.0;
     P_V idempotent 9.7e-15, self-adjoint 1.0e-16, range within t>=0
     exactly, spectral gap 6.6e8 (rank 811/1024 at the gate grid),
     per-rung gap 3.8e8..1.3e9 at every ladder rung
S0.5 dense-vs-spectral T_n 4.1e-14; tr(W) dense vs closed form
     8.7e-15; hermiticity 4.7e-16; VN 12-step monotone cross-check OK
S0.6 fixed-dt wrap gate (PAD 24 -> 40 at dt=0.005255): Tn/bulk drift
     5.3e-05 (tolerance 1e-3)
```

## 3. Method disclosures (all pre-official-run; law 42 clean)

1. **Torus model**: L^2(R) is modeled by the periodic box
   [-R_n-PAD, R_n+PAD] with N samples; all operators are the exact
   spectral (Fourier-multiplier) versions on that torus.  Detector
   content spans |t| <= 31.9 < box edge 43.05, so no box wrapping of
   content occurs; S0.6 certifies this numerically.
2. **Fourier-multiplier T_S**: E_p is diagonal in Fourier
   (e(xi) = prod_p (1 - c_p e^{-2 pi i xi log p})); T_S = reflection
   composed with e-ratio multiplier and the HT readback phase.  The
   adjoint of a reflected multiplier is conj(d(-xi)) (roll-corrected);
   the centered-grid reflection is k -> (-k) mod N (np.roll(a[::-1],1)).
3. **Direct P_V replaces von Neumann alternating projections**
   (object unchanged, method changed): the measured Friedrichs rate
   ~0.998/iter would need ~1.3e4 iterations for 1e-11; the exact Gram
   projector P_V = P_r (I - C^* (C C^*)^dagger C) with C = P_neg T_S P_r
   is used instead, with the Moore-Penrose pseudo-inverse realized by a
   SPECTRAL SPLIT of G_C (threshold PV_TAU = 1e-8 * scale).  G_C is
   measured rank-deficient with a huge clean gap (smallest kept vs
   largest dropped = 1e8..1e9 at every rung), so the split is exact and
   I - C^* G_C^dagger C is exactly the orthogonal projector onto ker(C)
   (standard SVD identity).  A plain regularized inverse is NOT a
   projector on a rank-deficient Gram — that was the 1.7e-4 smoke
   failure that motivated the change.  ker(C P_r) = M (+) H_neg, so the
   trailing P_r (commuting) is required; dim M is measured per rung
   (pv_rank 6651..7438 of 16384 negative bins — the discrete M grows
   with the grid, as the continuum theory predicts).
4. **Spectral trace method**: term1 and term_pv are computed on the
   top-320 eigenpairs of W (eigsh 'LA', tol 1e-10) with the exact tail
   check tail_gap <= 2.5e-14; validated against a DENSE path at
   N=2048 (agreement 4.1e-14).  The von Neumann sequence is retained
   as a one-sided 12-step monotonicity cross-check only.
5. **Scattering phase stabilization**: the HT readback phase
   Gamma(1/2 - 2 pi i xi)/conj(...) is computed as exp(2i arg); the raw
   quotient underflows 0/0 at |2 pi xi| >~ 400 — exactly the official
   fine-grid frequencies (smoke dt is coarser and hides this).  There
   the detector's spectral weight is e^{-400}: convention inert.
6. **Fixed-dt wrap gate**: the first S0.6 design compared absolute sn
   across PAD at fixed N, which conflates bulk's dt artifact with wrap
   contamination; redesigned pre-run to hold dt = T/N fixed while the
   box grows (N scaled proportionally).  Measured drift 5.3e-05.
7. **Sampling fidelity (aliasing suspicion REFUTED)**: the operator
   grids reproduce the detector mass exactly — f0d*dt = f0 to six
   digits at N = 8192..131072, and 100% of the sampled spectral mass
   lies inside the resolved band (gamma_9 = 48.01, Nyquist dt <=
   0.0654, all grades dt <= 0.0121).  A earlier hand estimate that
   suggested ~190x mass mismatch was an arithmetic slip (the correct
   identity is bulk*dt^2 = 2 R_n f0, verified to 1.3e-4); the aliasing
   diagnostic `1212_alias_diagnostic.py` pins the refutation.
8. **Normalization**: all physical readouts use Tn^cont = T_n dt^2 and
   bulk^cont = bulk dt^2 (derivation in §2).  The `sn_dt` field in the
   JSON is the raw (T_n - bulk)*dt and is NOT the physical finite part.

## 4. Interpretation guard (law 65)

This is a MODEL probe: torus truncation, finite grids, spectral
truncation at RANK=320.  It certifies nothing on the Lean side.  What
it establishes numerically is the shape of the three-owner ledger on
the pinned detector twin: under the projection kernel the insertion
trace carries NO divergent window term, its renormalized finite part is
window-independent to ~2e-4, and that finite part is -3.321 * qw(g) —
not qw(g).  The 1211 shape-(A) contract (renormalized finite part
readback converging to qw) has no numeric support in this family; per
the pre-registered consequence, exit A is closed here.

## 5. What this record does NOT claim

No Lean theorem, no P2, no SourceRH, no RH.  The H2 verdict closes a
probe, not a proof route: the 1209 signed-tail route and exit B
(moving/renormalized response) remain open and are unaffected by this
no-go.  Line B content remains frozen (record 1196).
