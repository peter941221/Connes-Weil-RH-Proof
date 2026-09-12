# 1372 - Total-variant phase-diagram offensive: step-0 source verdicts, corrected detector anatomy, and the rebuilt attack chain

Date: 2026-09-12. Owner instruction: "全部做完，开干" on the four proposed
steps (step-0 source checks, 008 offensive section, phase-rig prereg design,
targeted sweep). Class: SOURCE READBACK + PAPER DERIVATION + targeted
SWEEP. No Lean build, no Lean source change. All formulas in sections 4-7
are PAPER sketches with lossy constants; all digits live in the MODEL rig
governed by [1373](1373_phase_rig_prereg.md) (law 42: bands locked before
any digit; law 65: every digit MODEL until Lean-certified). RH is not
claimed; CB-HB1 remains NEEDS-ANALYSIS; this record opens a NEW candidate
card CB-PD1 in [006](../map/006_new_math_creation_workflow.md) §5.

## 1. Step-0 source verdicts (FORMAL SOURCE READBACK, all verified 2026-09-12)

### (a) The B5 exit consumes the PURE spectral side; the prime side is irrelevant

[C1SameOwnerWeil](../../ConnesWeilRH/Dev/C1SameOwnerWeil.lean):192-197 defines
`psi F = poleTerm F - archimedeanTerm F - finitePrimeSum F` and
`qw g = psi g.convolutionSquare`. The composition exit
`healthy_sourceRH_of_right_healthyDetectorData_and_spectral_nonneg`
([C1HealthyYoshidaSpectralNegativity](../../ConnesWeilRH/Dev/C1HealthyYoshidaSpectralNegativity.lean):585-605)
takes `hsign : ... 0 <= spectralWeilValue g.convolutionSquare` — the
hypothesis is the ZERO-SIDE sum only. The minimal exit
`healthy_sourceRH_of_right_detector_specific_qw_nonneg` (:611) consumes the
same shape per selected detector. VERDICT: the attack target is
`spectralWeilValue` (on-line masses + off-line pairings); no prime-side
square structure is needed, and the earlier brainstorm question (a) is
resolved as "not on the critical path".

### (b) n is free; the WRAPPER pins R ≈ 2|Im rho|; the tail theorem is one-sided

The construction family
`exists_fixedWindows_nearbyZero_healthyUnscaledOrbit_selectedOwner_with_raw_targets`
([C1HealthyYoshidaUnscaledOrbit](../../ConnesWeilRH/Dev/C1HealthyYoshidaUnscaledOrbit.lean):492-534)
returns, for EVERY `R >= 0` (line 504), a correction, C, n realizing the
target values with source support in `(-(n+2), n+2)` (lines 507-509). So the
support radius `R = n+2` is a FREE PARAMETER of the family.

The spectral-negativity wrapper
`exists_healthyDetectorData_of_fixedWindows_nearbyZero_spectral_neg`
([C1HealthyYoshidaSpectralNegativity](../../ConnesWeilRH/Dev/C1HealthyYoshidaSpectralNegativity.lean):521-563)
pins `R := 2^(n0+1) + 2 + dist(2, rho)` (line 535) where `n0` comes from
`exists_dyadic_tail_start_with_budget_lt_xiMultiplicity`
([C1SpectralTailBound](../../ConnesWeilRH/Dev/C1SpectralTailBound.lean):284-290):
`T <= 2^(n0+1)`, `2*|rho.im| <= 2^(n0+1)`,
`4*epsilon^2*C*(3/4)^n0 < xiMultiplicity rho`. All three conditions are
LOWER bounds on n0, so n0 (hence R) is free upward, but the MINIMAL n0 is
~log2(2|Im rho|), giving minimal R ≈ 2|Im rho|.

WHY the wrapper needs the big ball: its tail decay hypotheses (lines
524-534) require `2 * |rho.im| <= |z.im|` AND `T <= |z.im|` — the tail
theorem is UPWARD-ONLY, starting at twice the target height. Every zero
below that height must therefore be killed exactly, and the ball must reach
down to height 0, forcing radius ~|Im rho|.

VERDICT: the R-lever is REAL but gated by ONE new formal ingredient — a
TWO-SIDED quadratic tail bound (section 6, task N0'). The quadratic decay
mechanism is distance-based (`||z - rho||^2 * ||(1 - conj z) - rho||^2 *
||laplaceAt square (z - 1/2)|| < epsilon^2`), and the companion distance
`||(1 - conj z) - rho|| >= |Im z| + |Im rho|` is large for LOW zeros, so a
downward mirror of the same argument is expected to cost a new leaf, not a
new idea. This is a PAPER expectation, not a built theorem.

### (c) Anchor readback re-verified

Raw target values
([C1HealthyYoshidaUnscaledOrbit](../../ConnesWeilRH/Dev/C1HealthyYoshidaUnscaledOrbit.lean):39-43,
[CC20YoshidaFullProduct](../../ConnesWeilRH/Source/CC20YoshidaFullProduct.lean):52-61):
`rho -> 1`, `1 - conj rho -> -1`, `rho + 1/2 -> -1`, `1/2, 1, 3/2 -> 0`,
remaining orbit points 0. The centered-orbit square sum is EXACT:
`sum over centeredFunctionalEquationOrbit rho of laplaceAt convolutionSquare
= -2` (line 515-517). The 1371 §1 readback (pairedMass = m,
horizontalDefect = 2m under the raw equations) stands.

### (d) Detector anatomy: SPLINE, not a Dirichlet orbit sum

The selected owner is
`(convolutionIterate base n).convolution correction` with
`support base, correction ⊆ (-1, 1)` (lines 502-507, 541-554): the detector
is a SPLINE (n-fold self-convolution of a fixed unit-window bump, then one
correction convolution). Consequences that REPLACE the earlier chat-sketch's
Dirichlet-polynomial assumptions:

```text
G(z) = corrHat(z) * baseHat(z)^(n+1)      (convolution -> product)
support(g) ⊆ (-(n+2), n+2),  R = n + 2,
|G(s)| <= C_c * C_b^(n+1) * (1 + |Im s|)^(-2(n+1))-shaped vertical DECAY
```

There are NO visible-prime coefficients in this family; the vertical
behavior is n-exponential DECAY, not exponential growth. The earlier
e^(dR)-catastrophe analysis is void for this family.

## 2. Strategy ruling: total variant, per-window A2 demoted

The B5 exit needs `spectralWeilValue >= 0` for ONE selected g. The
windowMassBalance / targetA2Schema route organizes the budget per window;
its near-line counting premise at FIXED window width is GUE-strength and is
demoted from main budget to audit interface (as already recorded in 008
§1). The lawful total variant (008 §4 alternative, 008 §8.4 assembly with
summable c_k, e_k through `qw_window_assembly`) needs only:

```text
spectralWeilValue(g^2) >= Sum gain_k - Sum loss_k - Sum error_k,  net >= 0.
```

CB-PD1 is the total-variant candidate. CB-HB1 (sampling/hBridge mechanism)
stays NEEDS-ANALYSIS; PD1 does not consume hBridge or hA2.

## 3. The rebuilt chain S1-S7 (PAPER, with the spline anatomy)

S1 NORMALIZE. The anchor normalization pins `|G(d + i*t0)| = 1`; every
quadratic quantity then has absolute scale, and no norm variable survives
in the final race (norm floors only constrain ACHIEVABILITY of the anchor,
i.e. the correction norm, not the sign race).

S2 BAND DISCREPANCY (1371 R8 applied per height band with the spline
decay). With f(t) = |G(it)|^2 decaying like (1+|t|)^(-4(n+1)), the band
error sum converges: total R8 error ~ C_8 * C_c^2 * C_b^(2n+2) *
T^(-(4n+2)) * polylog — negligible against the anchor for n >= 1.

S3 OFF-LINE ABSORPTION. Per off-line zero outside the killed ball,
`|G(w) G(1-w)| <= C_c^2 * C_b^(2n+2) * (1 + |Im w - t0|)^(-4(n+1))`
(bump centered at t0; both factors decay). Summing over the
density-theorem band counts N(sigma, T) (Simonič explicit / Ingham
baseline; multiplicity convention to be pinned in the formal adapter):

```text
Absorption <= C_c^2 C_b^(2n+2) * T^( -(4n+2) ) * (1/eps) * (4n+2)^(-1) * sum_j T^(-delta(j*eps))
```

For n >= 1 this is astronomically small at every T >= 10^2. In the SPLINE
family the absorption wall of the earlier sketch DOES NOT EXIST. This is
the single largest correction to the 2026-09-12 chat sketch.

S4 LOCAL LINE MASS (sinc kernel). G(it) is of exponential type R and in
L2, so the PW_R evaluation bound gives
`|G(i t0)|^2 <= (R/pi) * K_loc(delta) * int_{t0±delta} |G(it)|^2 dt` with
K_loc(delta) = coth(delta R/2)-shaped; at delta = pi/R the model locks
K_loc = 2.13 * 1.5 (safety factor 1.5; the sharp constant is a named
verification task N2). Hence a point value of size 1 forces local line
mass >= pi/(1.5 * 2.13 * R) near t0, where the zero density is
eta(t0) ~ log(t0/2pi)/pi... (Riemann-von Mangoldt local error O(log T),
band-relative error -> 0, which is what makes bandwise R8 lawful).

S5 VERTICAL BRIDGE (THE open analytic task N1). The gain needs line mass
NEAR t0 on the sigma = 0 line, while the anchor lives at sigma = ±d. The
spline factorization gives |corrHat(it0)| >= e^{-d} |corrHat(d+it0)| at
best (support width 1), and NO pointwise lower bridge is proved for the
baseHat^(n+1) factor. The model therefore carries a bridge coefficient
rho_b in {0, 1/2, 1}:

```text
|G(i t0)| >= e^{-d * (1 + rho_b * (n+1) * R)} * |G(d + i t0)|    (MODEL)
rho_b = 0: corr-factor only;  rho_b = 1: full generic bridge.
```

N1 = prove ANY fixed positive rho_b version for the spline class.
Candidate tools: two-subharmonic/local mass comparison in the width-d
strip; the spline product structure; de Branges subspace ordering.

S6 R-OPTIMIZATION. R = n + 2 enters three ways: larger R worsens the
bridge penalty e^(-2 d rho_b (n+1) R) and the sinc constant R/pi, but
enlarges the killed ball (fewer absorbed neighbors) and eases the anchor
norm cost. The rig optimizes n in {1..8} per cell.

S7 ASSEMBLY AND CONTRADICTION. On cells where
`Gain - Absorption - R8error >= 2m`, the same-detector contradiction
closes: spectralWeilValue(g^2) >= (net) > 0 against the formal strict
negativity, killing the off-line-zero hypothesis AT THAT CELL's regime.
The closed region must be joined with (i) exact low-height certificates
(D7, Platt-Trudgian style verification) and (ii) the remaining seam.

## 4. The seam and the height threshold (PAPER model formulas)

With m = multiplicity >= 1, eta(t0) >= log(t0/2pi)/(2pi) - O(1/t0) for
t0 beyond the first zeros, and the locked model constants:

```text
Gain >= e^(-2 d (1 + rho_b (n+1) R)) * log(t0/2pi) / (2 * 1.5 * 2.13 * R)
CLOSED  iff  log(t0/2pi) >= 4 pi * 1.5 * 2.13 * R * m * e^(2 d (1 + rho_b (n+1) R))
              := L*(R, m, d, rho_b)
```

Reading (to be RE-DERIVED BY THE RIG, not trusted from prose):

- rho_b = 0, R = 3 (n = 1), m = 1, d = 0.05: L* ~ 28 -> t0 ~ e^28 ~ 10^12.2:
  AT the current verification frontier.
- rho_b = 1, same cell: L* ~ 51 -> t0 ~ 10^22.
- d = 0.1, rho_b = 1: L* ~ 104 -> t0 ~ 10^45.

THE WHOLE GAME IS THE CONSTANT WAR on L* and the bridge coefficient.
Every factor salvaged in N0'/N1/N2 multiplies the reachable territory.
The seam d*(t0) = log(log(t0/2pi)/(4pi*1.5*2.13*R*m))/(2(1 + rho_b(n+1)R))
is INCREASING in height: higher zeros tolerate larger d under the bridge
penalty.

## 5. Sweep harvest (beat-1 targeted, retrieval only)

| Target | Result | Use |
|---|---|---|
| Explicit near-line zero density | Simonič, [Explicit bounds on ζ(s) in the critical strip and a zero-free region](https://arxiv.org/abs/2301.03165), and "Explicit zero density estimate for the Riemann zeta-function near the critical line" (J. Math. Anal. Appl.); explicit N(sigma,T) tables in [2010.10675](https://arxiv.org/abs/2010.10675) | supplies delta(d-band) and the multiplicity convention to pin in the D3-total adapter |
| Guth-Maynard 2024 engine | survey [2607.04632](https://arxiv.org/abs/2607.04632), Tao's overview and [tag](https://terrytao.wordpress.com/tag/zero-density-theorems) | near-line form of the new N(sigma,T) is a harvest slot; exact statement to be read before any adapter claims it |
| Sinc/PW local evaluation constant | standard RKHS fact k(t0,t0) = R/pi for PW_R; sharp localized constant via prolate/de Branges | N2 verification task: pin K_loc exactly |

No sweep item contradicts the chain; none of them is yet an adapter.

## 6. New named tasks (consume 008 D-ledger IDs where applicable)

| ID | Task | Kind | Unblocks |
|---|---|---|---|
| N0' | Two-sided quadratic tail leaf: mirror the existing upward decay theorem to cover `|Im z| <= 2|Im rho|` zeros by distance-from-rho decay, so the killed ball is a FREE small R | NEW FORMAL LEAF (same decay family) | unlocks the R-lever; without it R ~ 2t0 and the whole offense is confined to R-huge cells |
| N1 | Vertical bridge: any fixed rho_b > 0 version of `|G(it0)| >= e^{-d(1+rho_b (n+1) R)}|G(d+it0)|` for the spline family | ANALYTIC | converts scenario cells into theorem cells |
| N2 | Sharp localized PW_R evaluation constant K_loc(delta) | ANALYTIC (classical) | constant war, 1.5x safety currently modeled |
| N3 | Density adapter: windowless total version of Simonič/GM N(sigma,T) with multiplicity convention pinned, consumed by S3 | ANALYTIC + adapter | absorption leg (already negligible in-model; adapter makes it formal) |
| N4 | Exact low-height certificate interface for the closed region's base (existing D7 rails) | CERTIFICATE | joins the closed region to verified territory |

## 7. What this record does NOT claim

No closure region is claimed. No bridge lemma is proved. The rig of 1373
evaluates MODEL formulas whose constants (C_b, C_c, C_8, K_loc, rho_b) are
unproved placeholders in locked bands; its output is a SCOREBOARD for the
constant war, not evidence of RH progress. The chain S1-S7 is a proof
DESIGN; every arrow is a separate future proof. The R-lever conclusion
(section 1b) is exact source readback and is the record's most load-bearing
new fact.

## 8. Falsifiers

- F-PD1-1: if the two-sided tail sum over LOW zeros is NOT small for
  small R (i.e. the downward mirror of the decay argument fails), N0' dies
  and R stays ~2|Im rho|; the rig's small-R cells become irrelevant.
- F-PD1-2: if a spline-class example violates every rho_b > 0 bridge
  (mass genuinely slides to eta-poor heights), N1 dies and the gain leg
  collapses to scenario cells that the rig will show as OPEN.
- F-PD1-3: if the rig's OWN negative control (a cell with the bridge
  coefficient set against a deliberately misscaled K_loc) does not flip
  the verdict, the instrument is invalid and the run is void.
