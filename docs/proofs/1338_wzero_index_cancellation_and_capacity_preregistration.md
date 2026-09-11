# Record 1338 — M1-prime: W_zero index cancellation + corridor capacity: preregistration

Date: 2026-09-11.
Status: PREREGISTRATION. Committed BEFORE any 1338 cell executes (law 42).
Executes the re-scoped M1 of record 1337 section 4. No Lean brick.
MODEL-twin numerics only: no claim about the formal carrier, no vanishing
of the real `qw`, no `SourceRH`, no RH statement. RH is not claimed.

## 0. Object under test

The record-1336 candidate `W_zero` = (model carrier W) intersected with
vanishing at the zero lattice, implemented in the SAME finite Toeplitz
instrument as records 1332-1334: the near-kernel sector `V_eps` of
`T_phi` (phi = the committed archimedean Gamma-only phase) on the grid of
domain `[-L, L]`, N = 8192 — a proxy for the truncated carrier — and then
the CONSTRAINT PROJECTION onto functions vanishing at the zero points.
Two constraint encodings (record 1337 section 5) are recorded: on
RH-typical certified data both reduce to the same real points, so the
probe imposes complex vanishing at `±xi_n = ±gamma_n / (2 pi)`, each zero
contributing two functionals (signs), and counts them; the beta-dependence
question is out of numerical reach (caveat R2 of 1337) and is flagged for
M2's definition stage, not settled here.

Phase flavors (record 1337 section 6): each cell is run for TWO phases —
`LC` (two-gamma, the exact 1332-1334 instrument phase, for continuity) and
`LR` (single-Gamma_R flavor: `arg phi_R(x) = -2 Im [ -(s/2) ln pi +
logGamma(s/2) ]`, `s = 1/2 + 2 pi i x`). The constraint set, statistics and
bands are per flavor. The LR winding closed form `2 L (ln L - 1)` matches
`2 N(2 pi L)` at leading order, which is exactly what the LC flavor
misses by the factor 2.

SECTOR DEFECT FOUND DURING 1338 IMPLEMENTATION (corrigendum to record 1334,
committed pre-run as the 1334-A2-style amendment channel): 1334's script
took `V = Vh.conj().T[:, :r]` — the FIRST `r` right-singular vectors, i.e.
the LARGEST singular values (s is descending), while its preregistered
sector is `sigma < 1e-6` = the LAST `r` columns (`[:, D-r:]`). The record
1334 CAPACITY reading (`A_tau ~ 2.0`, and therefore 1335's "capacity
falsifies" headline and the corridor half of the record-1333
identification) was thus computed on the WRONG BLOCK: a generic
non-kernel sector, where `A_tau ~ 2` is trivially the average value. The
KERNEL-count half of 1334 is unaffected (counts only). 1338 fixes the
sector (`Vh.conj().T[:, D-r:]`) and reports, per cell, the capacity of the
CORRECTED unconstrained sector as a control statistic S0unc
(`A_tau_unc`, same bands as S2), which re-runs the true 1334 measurement
with the right block. If S0unc on the LC flavor reads `CONCENTRATES`, the
1335 falsification is REFUTED-BY-INSTRUMENT-DEFECT and the committed model
is back in play before any C4 flavor discussion; if it reads `FALSIFIES`
again, 1335 stands and this record's amendment changes nothing
substantively. Either outcome is registered before running; no
after-the-fact arbitration (law 68 family).

## 1. Statistics

Zero data: imaginary parts `gamma_n` of the nontrivial zeta zeros computed
by `mpmath.zetazero` (mp.dps = 25, version recorded in the JSON), with
fidelity gate G5 below. Constraint set per cell: all `n` with
`xi_n = gamma_n/(2 pi) < L - MARGIN`, `MARGIN = 3.0`; both signs imposed.

S1 (index cancellation). `E in C^{2M x r}` rows `phi_{±n}` = evaluation
functionals of the sector, computed via the exact trig-coefficient path of
section 2 (gate G4 witnesses consistency). Statistics:
`rankE := rank(F)` at tolerance, `r' := r - rankE`, fraction
`f := r'/r`, and the independence floor `f0 := 1 - 2M/r`. Decisive cell
`L = 48`; `L = 32, 64` trend only.

S2 (corridor capacity of the survivors). Same statistic as record 1334
section 1 S2 — `A_tau = (1/r') sum_k (2 + 2 cos(2 pi tau xi_k)) K'(xi_k) h`
— with `K'` the kernel diagonal of the CONSTRAINED sector
(`Vc = V · null(F)`), `tau = log p`, p in {2,3,5,7,11}. Decisive cell
`L = 48`.

## 2. Implementation path (fixed in advance)

1. Sector: `T_phi` dense SVD as record 1334 (`r = #{sigma < 1e-6}`, sharp
   cliff gate G2 unchanged).
2. Sector grid values -> trig coefficients: `A = h · Eb^H V`, `A in
   C^{D x r}`, `Eb[k,m-1] = exp(2 pi i k m / N) (-1)^m / sqrt(2L)`
   (1334's basis).
3. Evaluation row at real `x`: `evec(x)[m-1] = (-1)^m
   exp(2 pi i m (x + L) / (2L)) / sqrt(2L)`; `phi_x = evec(x) @ A`.
   Exact for the trig-poly model space (no interpolation error).
4. `F` = stacked rows over the ± constraint points. Null space via SVD of
   F at tolerance `tol · sigma_max(F)`; `tol` fixed to a PAIR {1e-8, 1e-6}:
   G3 requires the two ranks to agree within `2% of r`, else ABORTED-
   UNINFORMATIVE (soft rank = threshold arbitration forbidden, 1334 law 68
   cousin).
5. `Vc = V @ nullbasis(F)`; `K' = sum_k |Vc[k,:]|^2 * h`; S2 as 1334.

## 3. Gates (all before any verdict; breach => exit 1, ABORTED-UNINFORMATIVE)

```text
G0  identity control at (48, 8192): phi=1 gives unitary diagonal
    (max offdiag < 1e-12 AND min |diag| >= 1 - 1e-10)          [as 1334 A1]
G1  diagonal machinery exactness (all cells): K_full = D/N witness
    and sector trace sum_k K h = r to 1e-8 rel                 [as 1334]
G2  sharp cliff: sigma_{r}/sigma_{r+1} positions per 1334 A2   [as 1334]
G3  rank sharpness of F: ranks at {1e-8,1e-6}·sigma_0 differ   [new]
    by at most 2% of r; else ABORT
G4  evaluation-path cross-check (AMENDED inv5, see ledger): the trial
    space is exactly the D = N/2 Fourier modes m = 1..D on the period-2L
    grid. Two independent evaluation paths:
    (P1) trig coefficients at any real x: evec(x) @ V;
    (P2) OVERSAMPLED band-limited interpolation on an ODD grid: M = 2N+1
         points of period 2L, values obtained by zero-padding the
         coefficient vector to length M and applying an FFT, then the
         Dirichlet kernel d(u) = sin(pi M u / (2L)) / (M sin(pi u / (2L))).
    WHY the amendments (inv5 + inv7): (inv5) mode m = D = N/2 is the
    NYQUIST bin of the N-point grid, where the originally preregistered
    N-sample Dirichlet formula aliases (smoke disagreement 2.8e-04..
    9.4e-02); (inv7, caught by the SECOND smoke at residual 1e-5..1e-7)
    the sin(pi M u / P)/(M sin(pi u / P)) formula reproduces the symmetric
    band EXACTLY only for ODD M — an even-M grid needs 2K+1 = M-1 — so P2
    uses M = 2N+1, where the identity is exact and d(0) = 1. After the
    fix, standalone P1 vs P2 agreement is ~2e-13 relative, and the
    kernel reproduces constants exactly (row sums = 1). All modes
    m <= N/2 are strictly interior to the |m| <= N band.
    Witness: at every constraint point and THREE sector vectors
    (j in {0, r/2, r-1}): |P1 - P2| <= 1e-9 * max(1, |P1|). This
    validates the coefficient/evaluation machinery on exactly the points
    that enter F, through two separately-coded implementations.
G7  constrained-sector trace (AMENDED inv6, machinery gate, both smoke
    and official): sum_k K'(x_k) h = r' to 1e-8 relative. This is the
    witness that caught the thin-SVD null-space defect (inv4): an
    all-zero "sector" is instantly visible as trace deviation O(1).
SMOKE POLICY (amendment inv6): with P_SMOKE=1 the two RESOLUTION-LIMITED
    gates G2 (cliff > 10) and G3 (soft rank) are downgraded to WARN and
    the cell is recorded incomplete; every other gate still aborts. At
    the official N = 8192 the policy is off and 1334's measured cliffs
    (376x / 143x / 70x per L) make G2's margin comfortable. No official
    verdict is ever produced under SMOKE mode (script prints
    SMOKE-MACHINERY-GREEN and writes no license reading).
G5  zero-data fidelity (AMENDED pre-smoke, see section 6 ledger):     [new]
    (i) |zeta(1/2 + i gamma_n)| <= 1e-3 for EVERY gamma_n used;
    (ii) strict monotonicity of the gamma list;
    (iii) first 10 gammas match the anchor table 14.134725, 21.022040,
    25.010858, 30.424876, 32.935062, 37.586178, 40.918719, 43.327073,
    48.005151, 49.773832 to 1e-4. Anchor table is mpmath-generated and
    residual-verified THIS session; the original hand-typed table (three
    fabricated entries: 36.822281/37.680407/41.058034 at ranks 6/7/8) was
    REFUTED by the residual witness before any cell ran — G5 exists for
    exactly this failure mode; the smoke caught it. mpmath version + dps
    recorded in the JSON.
```

## 4. Verdict bands (pre-committed; applied only if all gates pass)

```text
S1 (per flavor, decisive cell L=48; report f, f0 = 1 - 2M/r, rankE vs 2M):
   THINS      iff f <= 0.25
   NO-THIN    iff f >= 0.50
   else       INCONCLUSIVE
   (f >= f0 by the rank bound. For LC, f0 -> 0.50 by 1337 section 6's
   counting: an LC NO-THIN is CONFIRMATION of the paper prediction, not a
   discovery, and licenses nothing by itself. The scientific question is
   LR: thinning is arithmetically possible there, the probe measures
   whether it happens.)
S2 (per flavor, decisive cell L=48):
   CONCENTRATES  iff max_tau A_tau <= 0.30
   FALSIFIES     iff min_tau A_tau >= 1.20
   else          INCONCLUSIVE
LICENSE:
   M2 funding REQUIRES some flavor with S1 = THINS AND S2 = CONCENTRATES,
   plus the 1337 section 6 requirement that the winning flavor be
   reconciled with the committed Lean phase definition BEFORE any Lean
   re-parameterization.
   Both flavors NO-THIN or capacity-FALSIFIES => record-1336 thinning
   claim refuted at truncation level on line-zero data => Option H
   permanent for the radial leg; pivot per 1337 section 4 (L4 Fork B +
   A4 + NM registry).
   Anything INCONCLUSIVE => one amendment + one rerun allowed (law 42),
   never arbitration.
INTERPRETATION LIMITS (registered, non-negotiable):
   - All numbers are MODEL twins on the finite Toeplitz proxy; no
     statement about the formal `ran P_S` or `sourceSoninCarrier`.
   - Data are line-certified zeros only; the probe says NOTHING about
     models with off-line zeros (1337 caveat R2) and licenses no
     relativized conclusion beyond the finite-perturbation reading of
     1337 section 3, which is itself paper-level.
   - No vanishing consumed from the repository's zero tower; RH not
     assumed, not claimed.
```

## 5. Run plan

`docs/proofs/1338_wzero_vanishing_index_and_capacity_probe.py`, mirror at
`/home/peter/rh` synced and verified (cmp), `PYTHONUNBUFFERED=1`,
`setsid` detach, checkpoint log path under
`/home/peter/rh/build-logs/`-style convention, completion judged ONLY by
the `DONE 1338` sentinel (1329 law), timeout exit code not trusted.
Smoke first at N=1024 (all gates must be green or the smoke fails loudly);
official at N=8192, cells L in {32,48,64}, per-cell wall budget 580 s.
Outputs: `docs/proofs/1338_probe_results.json` + run log. Zero data cached
in the JSON (list actually used) for independent replay.

## 6. Invocation / amendment ledger (pre-run)

```text
inv1  AttributeError mp.mp.dps — mpmath context fixed directly. script fix.
inv2  zetazero returns mpc — im() extraction. script fix.
inv3  G5 FIRED on the smoke (exit 1, zero cells executed): the hand-typed
      anchor table contained three fabricated gammas (ranks 6-8); residual
      witness |zeta| at the mpmath values <= 3.1e-7, at the fabricated
      values O(1). Anchor table replaced by residual-verified values; G5
      rewritten to include the residual witness for every used gamma.
      This is the KSHAPE pattern (1329 A1) recurring: plausible constants
      from an unverified source; the data-fidelity gate is now MANDATORY
      for any probe consuming external tables.
corr  SECTOR DEFECT (section 0): Vh.conj().T[:, :r] -> [:, D-r:]; record
      1334's capacity statistic was on the wrong singular block; S0unc
      control added to re-measure it correctly. Pre-run, committed.
inv4  thin-SVD NULL-SPACE defect (smoke N=1024): np.linalg.svd(F1,
      full_matrices=False) on a 2M x r matrix (2M < r) returns only the
      2M row-space vectors, so VhF.conj().T[:, rk:] is the WRONG slice —
      at L=32 it was a 0-column "null basis" (phantom A_tau = 0.000), at
      L=48 it silently mixed 28 row-space vectors in (A = [1.17, 1.32]
      were NOT constrained-sector numbers). Fixed: full_matrices=True.
      Detected by the new G7 trace witness, NOT by any A value — smoke
      machinery controls earn their cost. SMOKE-ONLY defect: no official
      digit was ever produced under the bug; the smoke A readings are
      VOID and were never recorded anywhere as findings.
inv5  G4 P2 Nyquist aliasing (see section 3): replaced the N-sample
      Dirichlet path by the exact 2N oversampled FFT path. Amendment
      before any official cell; P1 (the production evaluation path)
      unchanged and is the basis of F.
inv6  SMOKE gate policy (see section 3): G2/G3 downgraded to WARN under
      P_SMOKE=1 only; G7 (constrained-sector trace) added as machinery
      gate at every resolution. Official discipline unchanged.
inv7  SECOND smoke (P_SMOKE=1, N=1024): machinery ran end-to-end, G4
      still 1e-5..1e-7 -> root-caused as EVEN-M parity in the P2
      Dirichlet kernel (the sin(pi M u/P) form is the exact symmetric-
      band kernel only for odd M). Fixed: M = 2N+1. Third smoke:
      SMOKE-MACHINERY-GREEN, G4 ~ 2e-13 all cells, G7 trk ~ 1e-16,
      LR windings match the 1337 section 6 closed form 2 L (ln L - 1)
      (157.6 vs 157.8 at L=32). Smoke f/A digits remain NON-
      REPRESENTATIVE (N=1024 under-resolves the cliff: LC L=48 r=279
      vs official target 658) and are excluded from any verdict.
```

RH is not claimed.
