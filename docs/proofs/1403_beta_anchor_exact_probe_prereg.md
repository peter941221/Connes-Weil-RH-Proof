# 1403 — PREREG: the route-beta exact-anchor probe (7-node root-window interpolant, n=7 transcription of the certified 1398 v3 instrument)

Date: 2026-09-14. Law 42: this file is committed BEFORE any anchor digit;
the committed text is never edited — a revision costs a NEW prereg file.
Outcome record will be 1404. Recon basis: 1402. Instrument basis:
run_1398_rig.py as locked by the v1 -> v2 -> v3 chain (gate classes are
its v3 values, unchanged). RH not claimed; every number this rig emits
is MODEL (law 65), never a Lean fact.

## 0. What is measured, and what the answer is allowed to mean

The object is the single open inequality of the root-supported branch,
in its 1084/1085 final form: for hypothetical off-line zeros `rho`,

```text
A_beta(rho) := arch h_rho.convolutionSquare,  where
h_rho(x) is the 7-node symmetric interpolant on the node set
  pairNodeSet rho = {rho, -rho, 0, 1/2, -1/2, 1, -1}
with targets 1 at rho, -1 at -rho, 0 elsewhere, realized (MODEL
mirror, this prereg's section 1) as the solved tapered Gram-exponential
factor on the LOCKED window |x| <= log 2 / 2, and arch = the committed
C1SameOwnerWeil.archimedeanTerm functional evaluated on F = h~ * h.
```

Scope, stated up front:

* `A_beta(rho) > 0` at any cohort cell means: pillar A of the 1081 exit
  is SATISFIABLE on the natural interpolant class at that rho —
  MODEL-level only, and it would re-open (not prove) the
  root-supported exit as a conjecture.
* `A_beta(rho) < 0` at every cell means: the 1086/1087 negatives
  generalize from real-slice/Galerkin to the exact complex
  7-node class — the beta anchor CONJECTURE is retired at MODEL level,
  joining the law F14 alpha verdict. It kills NOTHING in Lean.
* 1402 settled the strategic question: even a fully proved pillar A
  leaves the exit's pillar B (endpoint certificates => the gate =>
  SourceRH by B0b) — the wall. This probe is the last rung-3 science,
  not a campaign.

## 1. Model spec (VERBATIM transcription; deltas from 1398 are only
the two structural ones beta forces: n=7 and ONE factor instead of u,f)

**Nodes and target (locked order).** `nodes = [0, -1/2, +1/2, rho,
-rho, -1, +1]` (indices 0..6; rho deliberately at index 3 so the
locked instrument's `nodes[3]` frequency proxy in F_at/compute_A
applies unchanged), `p = [0, 0, 0, 1, -1, 0, 0]`. Set equality with
`pairNodeSet`/`pairNodeTarget` (EvenOddPair.lean:185-194) is exact.

**Factor layer (n=7 generalization of solve_factor, formulas
character-for-character from run_1398_rig.solve_factor):**

```text
G_ij = 2*sinh(A*R)/A, A = s_i + conj(s_j);  A = 0 -> 2R     [r13.gram]
alpha = lambda_min(G) via the same 150-step LDL^T bisection [1398]
TB    = sum_k exp(|s_k| R)
Delta = eps*alpha / (4*(1+eps)*TB^2);   delta = min(R/2, Delta)
rIn = R - delta;  rOut = R - delta/2
T_ij = [delta = 0] G_ij, else
  2*sinh(A*rIn)/A + (delta/2)*(e^{A*rIn} J(A*delta/2)
                              + e^{-A*rIn} J(-A*delta/2))   [1398]
J and J2: the imported J_master with the S(1-v) profile        [1398]
rhs: the NESTED mp.matrix constructor + the per-entry assert
     (the 1398 inv1 mpmath trap, law F13)
coeff = mp.lu_solve(T, rhs);  resid = ||T c - p||_inf        [1398]
h(x)  = tau(x) * sum_i c_i e^{conj(s_i) x},  tau = 1 on |x|<=rIn,
        S-profile on the two slivers of width delta/2 (1398 1.4),
        0 outside |x| >= rOut.
```

**Window.** `R = log 2 / 2` LOCKED — no grid: the support obligation
of the root window is the theorem (Icc(±log2/2), 1083/1084). `eps =
0.01` LOCKED (section 5: delta is sub-ulp at EVERY cohort point, so
eps is an inert recorded parameter — the 1400-style F14 re-test is
run as one informational variant eps=0.1 at the tier-1 cell).

**Pairing identity (why the solve interpolates — symbolic, no digits).**
With W(a) := int_{-R}^{R} e^{a x} dx and L_j := lap h(s_j):
L_j = sum_i c_i W(conj(s_i) + s_j) = sum_i c_i conj(W(s_i + conj s_j))
= sum_i c_i conj(T_ij) = sum_i c_i T_ji = (T c)_j = p_j, using W
real-symmetric and T Hermitian. The tapered case differs by O(delta),
which section 5 shows is below float64 ulp(R) everywhere: the model
reduces to this exact sharp-window interpolation, and GD-β (§3)
re-verifies it END-TO-END numerically against the 1398 convention
(`laplaceAt f s = int f e^{+s x}`, plus sign,
CC20YoshidaConvolution.lean:55 — the same `np.exp(rho*x)` integrator
the alpha rigs passed 82/82 times).

**Owner layer.** `SingleOwner` replaces `Owner(u,f)`: F_at, compute_A,
gv_scale, band_of_A, laplace_g are IMPORTED UNCHANGED from
run_1398_rig and consume only the fields `.g(xs)`, `.Cg`, `.Rs`,
`.Rg`, `.nodes` — which SingleOwner supplies with
`Rs = rOut64`, `Rg = R` (so F support = 2R = log 2 exactly: the sharp
Weil window; note that at this radius the n=2 prime term sits ON the
boundary of the empty-prime-sum lemma's domain — irrelevant here,
because A_beta IS the arch functional directly, no qw rewrite is used
or claimed), and `Cg = {-Rs, 0, Rs}` (sharp window: no interior
kinks; the template state machine of Owner is u*f-specific and its
absence here is a SIMPLIFICATION, not a formula change).

**Arch functional.** compute_A verbatim:
`A = re[(log4pi+gamma) F(0) + int_0^{2Rg} [e^{y/2}(F(y)+F(-y)) - 2F(0)]
/ (e^y - e^{-y}) dy + reF0 * ln tanh(Rg)]`, 1397/1398 form, npw =
32/64/96 battery, Richardson A_R = 2A64 - A32 informational.

## 2. Cohort, tiering, sentinels

**Cohort (25 cells, all TESTED — the beta family is 2-parameter,
no selection rule exists or is needed):**
`rr in {0.55, 0.6, 0.75, 0.9, 0.99} x im in {14.134725, 21.022040,
25.010858, 100, 1054}`; cell = (rr, im); rho = rr + im*I.
Heights 14.134725/21.022040/25.010858 are the three first zeta
ordinates (same constants as the 1393 grid); 100 and 1054 extend the
height-scaling probe (1401 §3: alpha |A| grew with height — beta is
free data on that question).

**Tiering.** tier-1 = (0.99, 14.134725): full 8-gate battery + GR
npw-96 + A_R + GQ + alpha/2 variant + eps=0.1 F14 re-test (all
informational/locked as in 1398 v3). tier-2 = the other 24 cells:
GS/GF/GD-integrity per cell (BADCELL scope rule, v3 clause 4), band
from GV-locked tie width. tier-3 = full battery (no eps variant) at
(0.99, 100) and (0.99, 1054), reported as cells with battery extras.

**Sentinels (locked strings):**

```text
DONE gates=G0:..,GI:..,GS:..,GT:..,GF:..,GD:..,GR:..,GQ:..
VERDICT betaAnchorWitness=<rho=rr+im*I|NONE> cells=POS:n,NEG:m,TIE:k,BAD:b
VERDICT betaAnchorWitness=NONE cells=VOID     (on any validity failure)
```

`validity = [G0, GI, GS, GT, GF, GD, GR, GQ]` (same 8 names, beta
semantics in section 3; the run is VOID if any is not PASS after the
tier-1 battery). Artifacts: `docs/proofs/1403_rig_{run.log,
results.json,cells.tsv.gz}`; acceptance = log-not-exit-code;
rename-before-rerun `*.invN.*` (law 7j).

## 3. Gates (classes = 1398 v3 values, UNCHANGED; semantics beta-ized)

| gate | beta semantics | class |
|---|---|---|
| G0 | admissibility: every cell has 1/2 < rr <= 0.99 and R = log2/2 (asserted, definitional) | exact |
| GI | mechanical instantiation of the section-1 pairing derivation, tier-1 only: reassemble L_j^{mp} = sum_i c_i^{mp} * 2sinh((conj s_i + s_j)R)/(conj s_i + s_j) (branch 0 -> 2R) FROM THE SOLVED COEFFICIENTS (never from T), assert |L_j^{mp} - p_j| <= 1e-30 for all 7 j — catches a transposed solve, node-order drift, or target-sign error, none of which GS can see (GS would pass on T^t c = p); second clause |laplace_g(h, s_j) - L_j^{mp}| <= 1e-6 ties the float evaluator to the mp convention | 1e-30 (mp) / 1e-6 |
| GS | 7x7 lu_solve residual max_j |Tc-p|_j | 1e-30 (M) |
| GT | S-symmetry, J+J2 identity, J(0) — imported gt_tier1 generalized to the single factor (identities are dimension-free) | 1e-40 / 1e-10 / 1e-12 |
| GF | F(0) = ||h||_2^2: re > 0 strict, |Im| <= 1e-6*re, npw-24 recompute <= 1e-5*re | 1e-6 / 1e-5 |
| GD | END-TO-END interpolation at ALL SEVEN nodes: |lap h(rho) - 1|, |lap h(-rho) + 1|, and |lap h(s)| for s in {0, +-1/2, +-1}, float64 quadrature, max | 1e-6 |
| GR | |A64 - A| <= 1e-5*|A|; A96, A_R printed | 1e-5 |
| GQ | A(2h) = 4A via p -> 2p re-solve | 1e-9 |
| GV | band: POS iff A > (1+1e-3)*1e-6*S, S = gv_scale(reF0, Rg=log2/2) (v3 clause 3 verbatim) | 1e-6 relative |

BADCELL (per-cell integrity only, v3 clause 4): GS/GF-positivity/GD
failure at a tier-2 cell -> that cell EXCLUDED from the census
(counted in BAD:b), never a NEG. TIE = |A| below the band threshold.

## 4. Kill scope

* POS cell -> pillar A alive on the natural class (MODEL); 1404 must
  then re-examine convention suspect first (GD/GI are exactly the
  gates that would catch a wrong pairing — a POS with a passing GD is
  a clean positive).
* All NEG -> beta-anchor conjecture retired at model level on the
  natural class; the 1081 exit is closed at model level (pillar A
  dead, pillar B = wall); no formal record changes.
* Either way rung 5/B0b remains the single open face of the tower and
  RH stays unclaimed. This rig cannot falsify any Lean statement and
  its negatives falsify nothing by the sup-law discipline.

## 5. Pre-run conditioning audit (rung-2 quantities ONLY — lambda_min,
TB, delta, untapered solve norm; computed 2026-09-14 on the 200-bit
model exactly as section 1 locks it; no A, no F, no anchor value was
or will be computed before the prereg commit). Worst-rr row per
height; `|c|max` is the untapered sharp-window solve norm (band term
is below ulp, see delta column):

```text
R = log2/2 = 0.34657359;  ulp(R) = 5.55e-17
im          worst-rr  lammin   TB        delta     |c|max   G-resid
14.134725   0.9       3.686e-12 2.771e+02 1.188e-19 9.673e+03 5e-57
21.022040   0.99      3.489e-11 2.948e+03 9.933e-21 6.117e+02 5e-58
25.010858   0.99      4.313e-11 1.171e+04 7.780e-22 1.436e+03 6e-58
100         0.99      4.632e-11 2.256e+15 2.253e-44 2.719e+02 2e-58
200 (not    0.99      4.645e-11 2.537e+30 1.786e-74 1.336e+02 8e-59
 in cohort,
 measured
 as margin)
1054.0      0.99      4.648e-11 8.788e+158 0.000    1.794e+01 1e-59
```

Readings (F12 audit — every gate's pre-run SATISFIABILITY):

* **GS**: mp residuals 1e-57..1e-59 at every height -> class 1e-30
  satisfied by 27+ orders; 200-bit lock unchanged from 1398 v3.
* **Taper absorption (F14-beta)**: delta <= 1.19e-19 < ulp(R) = 5.6e-17
  at EVERY cohort point (strongest form at im=14.13; delta64 -> 0.0
  itself at 1054): the band term vanishes below float64 resolution,
  the model IS the sharp-window interpolation of section 1, and eps
  is inert — recorded 0.01, re-tested once at 0.1 (informational).
* **GD**: with |c|max <= 9.7e3 (im=14.13, the worst) and pairing
  integrals bounded by 2R = 0.693 in modulus, the predicted float64
  cancellation error is <= ~1e-11 per node (terms O(1e4), eps ~ 2e-16,
  7-term sum) -> class 1e-6 has >= 5 orders of margin at every cohort
  point. im=1054 has the SMALLEST |c| (1.79e1) — inclusion decided by
  this line, mirroring how 1400 excluded 1054 by its own audit.
* **GF**: F(0) = ||h||_2^2 ~ |c|^2 * R scale, from 1e2 (1054) to 1e8
  (14.13) — positive definite by construction; |Im| noise relative
  float64 ~ 1e-16 << 1e-6 class.
* **GV/S**: gv_scale at Rg = 0.3466: I = 0.5*(ln tanh(Rg) - ln
  tanh(5e-4)) = 3.2504, S = |3.108*reF0| + 2*3.25*|reF0| ~ 9.6*reF0
  — tie threshold ~ 1e-5*reF0: A (O(1)-O(1e8), sign unknown in
  advance) cannot be band-degenerate unless it is genuinely near
  zero; a TIE outcome would itself be the finding.
* **GR**: 1398/1400 measured the p=1 C/npw law for the alpha owner;
  the beta owner has the same integrand class -> 1e-5 relative class
  predicted satisfiable at npw 32->64 (observed spreads were <= 1e-6).
* **Runtime estimate**: worst cell (tier-2 @1054) ~ 5.6e7 complex g
  evaluations ~ 1-2 min; full battery @1054 ~ 10 min; whole 25-cell
  run < 60 min. Class normal.

## 6. What is NOT here

No Lean statement is funded or refuted by any outcome (law 65); no
rung-5 input exists or is pretended; the Lean `correction` is
noncanonical (1402 §4) and this probe measures the natural class
declared in section 1; committed preregs 1398 v1/v2/v3 and 1400 are
untouched; this file is never edited — only 1404 may revise the
world. RH not claimed.

## 7. Next steps

1. Commit this prereg + scripts/run_1403_rig.py together (law 42:
   commit precedes any A_beta value), sync to the mirror, run via the
   resource runner (class normal).
2. On the first clean VALID: write 1404 with the census, the F14-beta
   statement, and the 1402-consolidating verdict; on a VOID: invN
   discipline (new prereg for any model/gate change, law 42; bug fix
   on the rig alone if the model is untouched).
3. Register closing pass: map README items, project memory cards and
   law notes (out of tree), superseding the "route-beta formal prereq"
   phrasing per 1402 §5.
