# Record 1220 - numeric-layer probe for the 1219 entrywise campaign

Pre-registration.  Committed BEFORE any run of this probe (law 42).
Status: IMPLEMENTATION-INVALID (2026-09-08); see record 1222.  The run-4
readout is not an F1/F2 verdict and cannot be used to choose a recovery.
Parent: 1219_entrywise_envelope_preregistration.md (E2-E5).
Consumers: records 1217 (boxes), 1218 (chain), 1219 (bricks).
No P2, no SourceRH, no RH.

## 1. Purpose

De-risk the two registered falsifiers of the 1219 campaign before any
Lean build:

```text
F1  a cell interval or tail budget fails to certify at the claimed
    width
F2  the assembled entry interval misses the record-1217 box (the
    2.4e-13 budget is eaten by quadrature/rounding overhead)
```

The probe implements the full enclosure pipeline in Python over EXACT
Fractions (mpmath only for independent float sanity checks) and reports
achieved widths and per-entry margins for the (0,0) and (7,7) entries
(even-even diagonal, the widest Legendre factors).

## 2. The pinned analytic reduction (the probe's ground truth)

For F = pairTest (classTestFamily 2) i j, i+j even (D1 parity: F even):

```text
C_ij(x)  := F.test x = integral t, w_i(-t) * w_j(x-t)   (real)
C_ij(0)  = classGramEntry 2 i j        (substitution u = -t)
entry    = ICgate F = archimedeanTerm F + finitePrimeSum F
arch     = kappa * C(0) + integral_{y in (0,4)} H(y) dy
kappa    = log(4 pi) + gamma + log(tanh 2)
H(y)     = (2 e^{y/2} C(y) - 2 C(0)) / (e^y - e^{-y})
           (the bracket vanishes at y = 0: O(y), smooth at 0)
prime    = sum over n in P24 of Lambda(n)/sqrt n * 2 C(log n)
P24      = the 24 prime powers <= 53 (|log n| < 4)
```

Substitution s = t/2, u = y/2 - s (dt = 2 ds, t-interval (-2,2) maps to
s in (-1,1); classWindowFun vanishes outside):

```text
C_ij(y)  = integral_{s in (-1,1)} 2 P_i(-s) P_j(u) b(s) b(u) ds,
           u = y/2 - s,  b = classBump = exp(-1/(1-s^2)) on |s|<1.
```

The bump models, the s/y partitions, the kernel bounds and the 24 log
enclosures are ENTRY-INDEPENDENT; per entry only the degree-<=7
Legendre factors enter, bounded on cells by exact rational in-cell
Taylor bounds (no interval-arithmetic coupling between entries).

## 3. Probe machinery (parameters provisional, pinned by addendum)

```text
S partition   s in [0, S_max], S_max = 0.98, N_S cells, in-cell
              Taylor model of g(s) = -1/(1-s^2) at the cell center,
              degree d_S, exact rational remainder bound per cell;
              b(s) in [exp(T-r), exp(T+r)] via exact exp partial sums
              (1137-style); bump tail |s| in [S_max, 1) budgeted by
              exp(-1/(1-S_max^2)) constants.
Y partition   y in [0,4], N_Y cells; per cell the u-range of an s-cell
              is [y_lo/2 - s_hi, y_hi/2 - s_lo], modeled with the same
              machinery at the range center.
Kernels       e^{y/2} and 1/(e^y - e^{-y}) bounded per y-cell by
              monotonicity + exact exp partial sums.
Cancellation   H(y) is enclosed through the bracket
               2 e^{y/2} P_j(u) b(u) - 2 P_j(-s) b(-s) INSIDE the
               s-integral (per-cell difference of two model
               evaluations), never through C(y) and C(0) separately.
Constants      pi via 4(arctan(1/2)+arctan(1/3)) partial sums;
               log 2 via 2 artanh(1/3); log 20 = 2 log 2 + log(5/4);
               gamma via Euler-Maclaurin on H_N - log N at N = 20
               with explicit Bernoulli remainder bounds;
               e^{-4} via exp partial sums of e^4;
               log tanh 2 = log(1-q) - log(1+q), q = e^{-4}.
Log readouts   log n in rational intervals by exp-comparison
               bisection (width <= 1e-30); C enclosed ON the interval
               by the y-cell machinery.
```

## 4. Registered branches

```text
GO    total entry enclosure width <= 5e-13 AND the assembled
      (0,0)/(7,7) intervals are inside the committed MLo_q28M/MHi_q28M
      rationals -> pin parameters in an addendum (degrees, N_S, N_Y,
      N for each constant), proceed to the Lean generators (E2a/E3a
      first, law-42 order: numeric layer before Lean consumers).
NO-GO widths exceed the box budget after honest accumulation ->
      ABORTED-UNINFORMATIVE (1219 F1/F2); the only legal recoveries
      are a 1219 prereg amendment with a different enclosure strategy
      or a 1217 prereg amendment + box regeneration.  No hand-widening
      of anything (1097).
```

Width ledger to report: constants, bump-model total, quadrature total,
log-readout total, prime-sum accumulation, assembly total, margin vs
the committed box for each probed entry.

RH NOT claimed.

## 5. Run-4 invalidation (2026-09-08)

The first completed `(0,0)` assembly printed
`H_mid = 1.2980715223869489e33`, while `C0`, `kappa`, and `I_B` remained
order one.  This is not an honest budget failure: record 1222 identifies two
implementation violations of the pinned reduction.

1. The point-coefficient routine evaluated the analytic expression
   `exp(-1/(1-u^2))` for `|u| >= 1`, although the compact bump is identically
   zero there.  Cells crossing `u = +/-1` were not split, so a Taylor centre
   could lie outside the support while its cell still met the support.
2. The intended positive/negative `s` split was written as
   `for sign in (1, -1)`, but `sign` never changed the interval endpoints;
   the code duplicated the positive half-axis instead of integrating
   `s in (-1,1)`.

The interrupted run logs are retained as diagnostic evidence only.  A new
pre-registration amendment must specify a support-boundary-respecting
partition and the signed-half-axis substitution before any replacement probe
or Lean consumer is run.  No box is widened and record 1221 remains dormant.
