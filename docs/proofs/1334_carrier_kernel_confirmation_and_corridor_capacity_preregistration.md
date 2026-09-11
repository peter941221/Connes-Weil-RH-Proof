# Record 1334 — Kernel confirmation and corridor capacity: preregistration

Date: 2026-09-11.
Status: PREREGISTRATION. Committed BEFORE any 1334 cell executes. Fixes the
statistic that record 1333 diagnosed as machine-floor-saturated in 1332, and
opens the C0b measurement (corridor capacity) with pre-committed bands.
No Lean brick. RH is not claimed.

## 1. Statistics

S1 (kernel confirmation). For each cell `(L, N)`, `N = 8192`,
`L in {32, 48, 64}`: `c := #{ sigma_j(T_N) < 1e-6 }` and
`W(L) := (arg phi(L) - arg phi(-L))/(2 pi)` computed by 200001-point
continuous-branch unwrap of `-2 Im logGamma_R(1/2 + 2 pi i x)` (same code
path as record 1333). Ratio `R1 := c / |W(L)|`.
Resolution budget check (pre-registered): phase step per grid cell at the
domain edge, `|psi'(L)| * 2L/N`, must be < 1.5 rad; at N=8192 the values are
0.40 (L=32), 0.65 (L=48), 0.93 (L=64): all pass, L=64 flagged marginal.

S2 (corridor capacity). At each cell let `V_eps` = right-singular vectors
with `sigma < 1e-6` (rank `r`), `Pi_eps = V_eps V_eps*` the near-kernel
sector, and `K_eps(xi) = sum_j |w_j(xi)|^2` its kernel diagonal on the
grid (the xi-plane boundary values; the SVD model of 1332 identifies
`ker T ~ W`). For each visible-prime lag `tau = log p`, p in {2,3,5,7,11}:

```text
A_tau := (1/r) * sum_k (2 + 2 cos(2 pi tau xi_k)) K_eps(xi_k) * h
```

A generic sector gives `A_tau ~ 2`; hcolumn-compatible hiding requires
`A_tau -> 0` for EVERY prime simultaneously (record 1332 section 1, lemma
L1: `E_col(p)` convergence <=> kernel-diagonal mass inside the zero
corridors of the weight). Decisive cell: `L=48` (fully resolved); `L=32`
and `L=64` reported as trend only.

## 2. Gates (all must pass before any verdict; breach => exit 1, ABORTED-UNINFORMATIVE)

```text
G0  identity control at (48, 8192): phi=1 gives sigma_min >= 1 - 1e-10
    [Amendment A1, committed pre-run: in the grid-center basis e_m(x_j) =
     (-1)^m exp(2 pi i m j / N)/sqrt(2L), phi=1 yields the UNITARY DIAGONAL
     T = diag((-1)^m), not the literal identity; the witness is therefore
     implemented as (max off-diagonal entry < 1e-12 AND min |diag| >=
     1 - 1e-10), which implies the registered sigma_min >= 1 - 1e-10. The
     smoke test at reduced size caught a naive max|T - I| witness failing
     with value 2 on exactly these diagonal phases; this amendment makes
     the gate STRICTER, never weaker.]
G1  exactness of the diagonal machinery: taking ALL d trial vectors
    (eps := 4), K_full must equal d/(2L) at every grid point to 1e-10,
    and sum_k K_eps h = r to 1e-8 relative.
G2  floor sanity: the cliff gap: sigma_{r} < 1e-6 <= sigma_{r+1} * 10
    (sharp cliff, as observed in 1332; if the cliff is soft, the sector
    cutoff is arbitrary -> abort rather than arbitrate).

[Amendments A2, committed pre-run after a reduced-size smoke test:
(i) G2 indexing: singular values come out DESCENDING from the SVD, so the
    floor block occupies the TAIL of the array; the cliff witness is
    sigma_{D-r}/sigma_{D-r+1} in array positions, i.e. (first above floor) /
    (largest floor value) > 10 — the written formula is unchanged in
    meaning, only the implementation direction is fixed.
(ii) G1 constant: the script's K carries one factor of the grid measure h
    (density convention, so that sum_k K = trace exactly and the A_tau sum
    needs no extra h); the K_full witness is therefore D*h/(2L) = D/N,
    consistent with the raw-kernel constant D/(2L) of the text above.]
```

## 3. Verdict bands (pre-committed, applied only if all gates pass)

```text
KERNEL:  CONFIRMED     iff R1 in [0.95, 1.05] at L=32 AND L=48 AND L=64
         NOT-CONFIRMED iff any R1 outside [0.90, 1.10]
         else           INCONCLUSIVE
CAPACITY (decisive cell L=48):
         CONCENTRATES     iff max_tau A_tau <= 0.30
         FALSIFIES        iff min_tau A_tau >= 1.20
         else             INCONCLUSIVE
```

Interpretation table (what each combination licenses next):

```text
+---------------------+----------------------------------------------+
| CONFIRMED+FALSIFIES | the committed carrier cannot satisfy hcolumn |
|                     | at truncation level: the 1329-1330 conditional|
|                     | chain has an inconsistent premise on the     |
|                     | model. Next authorized step after that: a     |
|                     | paper record formalizing the truncation       |
|                     | divergence into a ¬hcolumn attack sketch      |
|                     | (constructing an explicit carrier sequence is|
|                     | then the formalization target; NOT free).     |
| CONFIRMED+CONCENTR. | hcolumn is model-consistent: G2/G3 marathon |
|                     | (C3) becomes justified; new prereg needed.    |
| any INCONCLUSIVE    | stop and report; no re-reading of numbers.    |
+---------------------+----------------------------------------------+
```

## 4. Budget and completion rule

Per-cell dense SVD at d=4096: budget 580 s; total <= 4 SVDs (3 main + G0
identity, whose spectrum is exactly 1 - no SVD needed: G0 may use the
analytic identity). Diagonal machinery: one `N x d` times `d x r` matmul
per cell (~10 s). Completion judged ONLY by the `DONE 1334` sentinel plus
JSON (1329 lesson). JSON: `docs/proofs/1334_probe_results.json`.

## 5. Authorization

Protocol above only. No further statistic, no model change, no formal
brick, and no re-thresholding after seeing numbers is authorized by this
record. Follow-ups require new records. RH is not claimed.
