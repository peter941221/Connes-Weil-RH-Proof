# 1675 — Annular Gram trace rig: the truncated-grid meet is dimension-forced, so absolute carrier readings are void

Date: 2026-09-19.

Status: numerical research record + two laws. The rig's decision target
(the decay law of B(N)) was NOT obtained — the grid cannot read it at all.
The negative result is precise, mechanized by dimension counting, and
control-confirmed. RH is not claimed.

## 1. The object, exactly (from committed definitions)

Read from the tree (record derivation, all pinned this round):

```text
space     finiteSCarrier = L^2(R, du), u = log variable
kernel C  = rootConvolution owner = convolution by the compactly supported
          involution test g* (SelectedWeilSquare.lean:25; radius R)
window    P_n = kernelIntervalProjection (-(n:R)) (n:R) 0 = M_{1_{[-n,n]}}
          — a u-SIDE window (SelectedCrossingOperatorBridge.lean:1564)
H         ccm24ArchimedeanHardyTitchmarsh: (Hu)^ = m(xi) * uhat(-xi),
          m(s) = Gamma_R(1/2 - i s)/Gamma_R(1/2 + i s)   (HardyTitchmarsh
          :104/:365; equivalently Hu = (K * u)(-.) with K = F^{-1}(m(-.)))
carrier   archimedeanSoninCarrier(lambda) = range(E) meet range(H^-1 E H),
          E = M_{1_{[log lambda, infinity)}}   (:352)
object    tr(sourceRootAnnularGram(N,n)) = SUM_i || 1_{N<=|u|<=n} C e_i ||^2
          over a carrier ONB  =  || (P_n - P_N) C R_0 ||_HS^2
```

Exact model answers (hand-derived before running, law F27/F28):

```text
m = 1:  H = reflection, carrier = L^2[-a, a], a = log(1/lambda), and
        B(N) = 0 EXACTLY for N >= a + R  (support algebra; hard edge).
one-sided bounds:  tr(W*W E) and tr(W*W Q) both GROW LINEARLY in n
        (infinite-measure half-lines, 1585's infinite-rank lesson), so the
        uniform bound can only come from the MEET — 1599's stop rule again.
```

The carrier condition `supp(K*u)(-.) subset [log lambda, infinity)` is
record 1634's one-sided convolution vanishing; the annular bound, the
StripDensity local trace and the base are one object.

## 2. Rig verdict: real-phase grid readings are indistinguishable from the m = 1 model

`scripts/annular_gram_trace_1675.py` (build log
`build-logs/1675_annular_gram_trace.log`, exit 0):

```text
self-tests:  H^2 = I on the grid at 5.5e-16;  max||m|-1| = 2.2e-16;
             K left-mass 0.961 (real) vs 0.040 (opposite orientation),
             matching the 1633 orientation anchor 0.984 up to window
             normalization — the convention is pinned.
m = 1:       accept dimension = block cap, exact zeros past a + R, live
             inner mass — the machinery passes its own calibration.
real m:      Rayleigh spectrum [1.0 x 8] at every (lambda, M, L) tried;
             family support [-1, 1]-like; T(N, n) CONSTANT in n;
             B(N) = 0 past the model edge.  Identical to m = 1.
```

## 3. The mechanism: the truncated-grid meet is dimension-forced

On a grid of M points, dim E = dim Q = (L + a)/du, so for ANY unitary
conjugation with involutive phase (Q = H^-1 E H a true projection):

```text
dim(range E meet range Q)  >=  dim E + dim Q - M  =  2a/du     (= 102 here)
```

The intersection is FORCED nontrivial at the discretization level; in the
continuum dim E = dim Q = infinity and no forcing occurs — the meet is
exactly the open base. Decision control (dim = 40 block, λ = e^-1, M = 4096):

```text
[dim40-real]   accepted 40/40, sigma_top = 1.0, support [-1, 1]
[dim40-model]  accepted 40/40, sigma_top = 1.0, support [-1, 1]
[dim40-random] accepted 40/40, sigma_top = 1.0, support [-1, 1]
```

with `random` = a generic unit-modulus phase: the committed symbol has NO
special footprint at grid level. The first random control run read
sigma_top = 0.905 with accepted = 0 — that run was INVALID (it applied H
where H^-1 was required; H E H is not a projection for a non-involutive
phase) and is recorded as a rig note, not evidence.

## 4. Laws

```text
F59  (numbered here as map 044 proposed, from record 1655) the ambient
     leakage leg is not Hilbert-Schmidt on ANY basis at unit scale whenever
     the selected source Laplace value is nonzero: the global full-basis HS
     shortcut does not exist and must not be retried.
F60  a truncated-grid meet E meet (U^-1 E U) of half-line projections is
     dimension-forced: dim >= dim E + dim Q - M = 2a/du for every
     involutive unitary U.  Exact carrier readings on truncated grids
     (sigma = 1, supports, trace values) are discretization products and
     carry NO information about the continuum base.  Base numerics are
     admissible only as TREND quantities measured against the forced count
     (dimension excess, defect rates) — the E-and-Q-grid form of F43.
```

## 5. Consequence for the map 044 decision gate

The "rig first" plan item resolved NEGATIVELY: B(N)'s decay law cannot be
read on any truncated rig, so the uniform annular Gram upper bound must be
attacked ANALYTICALLY — the kernel-diagonal / local-trace route (the
1625-specified basis-to-measure trace identity, double consumer with the
StripDensity content), with the m = 1 exact answers above as the
calibration targets the proof must degenerate to. Numerics on the base stay
on front B only, as trend quantities (1640 obligations 2-3).

## 6. Boundary

The S3 producer is unchanged and OPEN: `0 <= Re tr Gram(N,n) <= B` uniformly
in n, lower side closed (1674). The carrier base is unchanged and OPEN.
No Lean brick this round. RH NOT claimed.
