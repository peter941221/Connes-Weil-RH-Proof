# 1698 — lane R-D3 closes its detector side: the frame theorem compresses premise 1 of the two-premise exit to exactly {interpolation frame, archimedean sign field on the D3 squares}; brick `C1LaneRD3Detects`

Date: 2026-09-19.

Status: one Lean brick + Audit, machine-checked, standard axioms.  No sign
statement is proved; the compression is the content.  Companion rig record:
1699.  RH is not claimed.

## 1. What was already committed vs what this brick adds

`Dev/C1LaneRD3Root.lean` (committed earlier) builds the differential
interpolation engine: `derivativeShift f a = f' + a·f` with transform law
`laplaceAt (derivativeShift f a) s = (a − s) · laplaceAt f s`
(`C1LaneRD3Root.lean:84`), hence `tripleVanishingRoot h = D_0 D_{1/2} D_1 h`
(`:264`) with the Vandermonde law

```text
  laplaceAt (tripleVanishingRoot h) s
    = (0 − s) · ((1/2 − s) · ((1 − s) · laplaceAt h s))          (:271)
```

plus the vanishing theorem at `F = {0, 1/2, 1}` (`:316`), the support chain
(`:349`, `:371`), and the window confinement `supp h ⊆ [−w, w]`, `w < 3/10`
⟹ `supp (root²) ⊆ (−log 2, log 2)` (`:380`).

What was MISSING was the detector side: nothing tied a seed test with
nonvanishing Laplace value at ρ to an actual `HealthyYoshidaDetectorData` on
the genuine carrier.  That closure is `Dev/C1LaneRD3Detects.lean`, in four
steps.

## 2. The brick

1. **A concrete nonzero test exists.**  `bumpLogTest` is the complexified
   `ContDiffBump` at the origin (`rIn = 1`, `rOut = 2`), packaged as a
   `CompactLogTest` via Mathlib's
   `HasCompactSupport.toSchwartzMap`.  At the origin of the Laplace variable
   it reads the mass integral, which is strictly positive by Mathlib's
   `integral_pos_of_integrable_nonneg_nonzero`
   (`laplaceAt_bumpLogTest_zero_eq`, `laplaceAt_bumpLogTest_zero_ne_zero`).
   Twisting by the committed exponential weight
   (`C1SpectralWeil.laplaceAt_exponentialWeight_eq`) shifts the bilateral
   Laplace variable to the origin:

```text
  exists_compactLogTest_laplaceAt_ne_zero (rho : ℂ) :
    ∃ h, CompactLogTest.laplaceAt h rho ≠ 0
```

   — the nondegeneracy half of the interpolation frame is FREE at every ρ;
   the hard part is only doing it with a confined window simultaneously.

2. **The D3 root detects every off-node point**
   (`tripleVanishingRoot_laplaceAt_ne_zero`): nonzero seed Laplace at ρ and
   ρ ∉ {0, 1/2, 1} imply nonzero root Laplace at ρ — the Vandermonde factor
   is a product of three nonvanishing factors.  The three off-node
   hypotheses are discharged for every off-critical source zero by the
   committed nonvanishing lemmas
   (`standard_source_nontrivial_zero_ne_cc20_zero/_half_of_off_line/_one`,
   `CC20YoshidaCriterion.lean:43/:55/:64`).

3. **The frame theorem** `healthyDetectorData_of_rootFrame_and_arch_pos`:
   given ρ, a seed h confined to `[−w, w]` with `w < 3/10`, `laplaceAt h ρ ≠ 0`,
   ρ ∉ {0, 1/2, 1}, and STRICT POSITIVITY of
   `C1SameOwnerWeil.archimedeanTerm ((tripleVanishingRoot h).convolutionSquare)`,
   it produces the full `HealthyYoshidaDetectorData ρ (tripleVanishingRoot h)`:
   `compactSupportSmooth` is unconditional on the healthy carrier
   (`C1.healthyCC20CompactSupportSmooth`), `vanishesOnF` is `:316`,
   `detectsRho` is step 2, and `weilSquareSumPositive` is exactly the
   committed window-class readback
   `weilSquareSumPositive_iff_archimedeanTerm_pos_of_vanishesOn_cc20Triple`
   (`C1HealthyYoshidaDetector.lean:204`) fed by the confinement `:380`.

4. **The reduction** `CC20YoshidaDetectorExists_of_existsFrame_and_arch_pos`:
   premise 1 of the committed two-premise exit
   (`healthy_spectral_nonneg_sourceRH_of_yoshida_detector`,
   `C1CenterTwoRHExit.lean:67`) follows from

```text
  for every off-critical source zero ρ:
    ∃ h, w:  supp h ⊆ [−w, w]  ∧  w < 3/10  ∧  laplaceAt h ρ ≠ 0  ∧
             0 < archimedeanTerm ((tripleVanishingRoot h)²)
```

   composed with the committed packing
   (`healthyCC20YoshidaDetectorExists_of_healthyDetectorData`,
   `C1HealthyYoshidaDetector.lean:235`).

## 3. Why this is the right compression

After 1697, the whole program is the two-premise exit.  This brick makes the
premise-1 side EXACT: the interpolation engine (differential orbit —
committed), the transport from seed nondegeneracy to detector nondegeneracy
(this brick — committed), the window confinement (committed, `:380`), and
the packing (committed).  What remains of premise 1 is precisely:

  (a) one window-confined seed per off-critical zero with nonvanishing
      Laplace value — a concrete interpolation-with-constraint problem;
  (b) the archimedean sign on the D3 squares — the SAME sign field that the
      window class reads as `qw < 0`.

No positivity is manufactured anywhere in the chain; the sign field enters
as an input hypothesis, per the model-fidelity laws (F67/F68, record 1697).

## 4. Build evidence

`ConnesWeilRH.Dev.C1LaneRD3Detects` + `...Audit`: all four declarations
`#print axioms` = `[propext, Classical.choice, Quot.sound]` (standard), zero
errors, see build log `1698_lane_rd3_detects_v6.log`.

## 5. Next

1. 1699 rig (companion record): the committed laws of this exact frame are
   reproduced numerically, and the state of the sign field on the NAIVE
   confined frame family is measured — with a negative result that sharpens
   where the construction freedom must come from (see 1699 §3).
2. The sign field on shaped seeds: the classical Yoshida negative-test
   shapes the test so that the ρ-pair term, not the arch book, dominates —
   the naive family shows this shaping is NOT optional.
3. Premise 2 stays the RH core; any future detector producer must pass the
   F67 sign check at detector tests.
