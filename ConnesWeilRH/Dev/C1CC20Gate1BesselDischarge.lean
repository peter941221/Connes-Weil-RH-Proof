/-
Copyright (c) 2026 ConnesWeilRH contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ConnesWeilRH.Dev.C1CC20Gate1Assembly
import ConnesWeilRH.Dev.C1CC20GammaBesselCoercivity

/-!
# The GATE 1 Bessel discharge: the T-side payload leaves the assembly

The Bessel brick `C1CC20GammaBesselCoercivity` supplies the flagship T-side
coercivity premise `hT` for every scale `lam < 1` at the level
`epsilon2 <= 1 - lam`.  This leaf turns that producer into CONCRETE gap data
and discharges `hT` from the GATE 1 assembly, so that the assembly's
consumers no longer carry the T-side spectral block at all.

The exhibited gap data is the honest ORDER-STRUCTURE choice

    a        := 1
    epsilon1 := (1 - lam) / 2
    epsilon2 := 1 - lam
    ePrime   := free (caller-supplied, >= 0)

for which `h_gap : epsilon1 < epsilon2` is exactly the statement
`0 < 1 - lam`.  It is NOT the paper's numeric scale (`a ~ 0.064`,
`epsilon2 ~ 0.00441`): the archimedean constants stay tied to payload
(delta).  What the exhibit closes is the STRUCTURAL residue: at this data
every GATE 1 consumer premise is a grid number, the endpoint continuity,
the endpoint `MemLp` premise, or the single scalar `ePrime` - and the
rank-one constant reads `gamma = 2 * ePrime`, so the paper band
`294/100 < gamma < 2944/1000` becomes the one-dimensional interval
`147/100 < ePrime < 1472/1000` for the caller.

Discharges proved here:

* `cc20Eq115_negativeForm_le_rankOne_of_uniformGrid_bessel` - CC20 Lemma
  `second`'s rank-one bound at `ell := 0` with NO `hT` premise: the
  `-(2 ePrime)`-weighted `K_I` defect form is `<= 0`, i.e. `q(K_I) >= 0`
  in the `ePrime > 0` branch, conditional only on the grid table, the
  endpoint continuity and `MemLp` premises, and `lam in [0, 1)`.
* `cc20Eq115_kf_defect_nonneg_of_uniformGrid` - the same statement at the
  concrete scale `ePrime := 1`, stated as plain nonnegativity of the `K_I`
  defect form.
* `cc20Eq115_gate1Residual_nonpositive_of_uniformGrid_bessel` - the GATE 1
  flagship residual `trace <= 0` with NO `hT` premise: the eq-(100)
  slope-matched endpoint residual is nonpositive from the grid table and
  the trace identification alone (the archimedean comparison against
  `W-infinity` remains payload (delta)).

Reference: equations (100), (115), (119)-(121) of
<https://arxiv.org/html/2006.13771>; companion records docs/proofs/1046,
docs/proofs/1048.
-/

namespace ConnesWeilRH
namespace Source
namespace C1CC20Gate1BesselDischarge

open MeasureTheory Set
open CC20Concrete
open C1CC20DisplacementKernel C1CC20Eq115Symmetry C1CC20Eq115Table
  C1CC20Eq115MassBound C1CC20FiniteRankApproximation
  C1CC20FiniteRankDifference C1CC20KernelLpLift C1CC20LpOperator
  C1CC20FiniteRankLocalGapCertificate C1CC20OperatorGap
  C1CC20EndpointCertificateData C1CC20EndpointCoefficient
  C1CC20RawKernelMass C1CC20RootWindowOperator
open C1CC20Gate1Assembly C1CC20GammaBesselCoercivity

noncomputable section

/-- The exhibited GATE 1 gap data at the Bessel coercivity level
`epsilon2 = 1 - lam`: the order relations `epsilon1 < epsilon2 <= 1 - lam`
hold by construction, and the repair weight is normalized to `a = 1` so the
rank-one constant reads `gamma = 2 * ePrime`.  The paper's numeric scale is
a separate archimedean payload; this exhibit closes the structural residue
`h_gap` together with `epsilon2 <= 1 - lam`. -/
def cc20Eq115Gate1GapData (lam ePrime : ℝ)
    (_hlam1 : lam < 1) (hePrime : 0 ≤ ePrime) :
    CC20OperatorGapData (Lp ℂ 2 (volume : Measure ℝ)) where
  a := 1
  epsilon1 := (1 - lam) / 2
  epsilon2 := 1 - lam
  ePrime := ePrime
  h_epsilon2_pos := by linarith
  h_epsilon1_nonneg := by linarith
  h_a_nonneg := by norm_num
  h_ePrime_nonneg := hePrime
  h_gap := by linarith

/-- The rank-one constant of the exhibited gap data is `2 * ePrime`. -/
theorem cc20Eq115_exhibitedGapData_gamma_eq (lam ePrime : ℝ)
    (hlam1 : lam < 1) (hePrime : 0 ≤ ePrime) :
    CC20OperatorGapData.gamma
        (cc20Eq115Gate1GapData lam ePrime hlam1 hePrime) =
      2 * ePrime := by
  show 2 * (cc20Eq115Gate1GapData lam ePrime hlam1 hePrime).ePrime *
      (cc20Eq115Gate1GapData lam ePrime hlam1 hePrime).a =
    2 * ePrime
  have h1 : (cc20Eq115Gate1GapData lam ePrime hlam1 hePrime).ePrime = ePrime :=
    rfl
  have h2 : (cc20Eq115Gate1GapData lam ePrime hlam1 hePrime).a = 1 := rfl
  rw [h1, h2]
  norm_num

/-- The paper's coefficient band `294/100 < gamma < 2944/1000` becomes, at
the exhibited gap data, the one-dimensional interval `147/100 < ePrime <
1472/1000` - the caller's only remaining rank-one-side obligation. -/
theorem cc20Eq115_exhibitedGapData_band_iff (lam ePrime : ℝ)
    (hlam1 : lam < 1) (hePrime : 0 ≤ ePrime) :
    ((294 : ℝ) / 100 < CC20OperatorGapData.gamma
        (cc20Eq115Gate1GapData lam ePrime hlam1 hePrime) ∧
      CC20OperatorGapData.gamma
        (cc20Eq115Gate1GapData lam ePrime hlam1 hePrime) <
        (2944 : ℝ) / 1000) ↔
      ((147 : ℝ) / 100 < ePrime ∧ ePrime < (1472 : ℝ) / 1000) := by
  rw [cc20Eq115_exhibitedGapData_gamma_eq]
  constructor
  · rintro ⟨h1, h2⟩
    exact ⟨by linarith, by linarith⟩
  · rintro ⟨h1, h2⟩
    exact ⟨by linarith, by linarith⟩

/-- The T-side coercivity premise of the GATE 1 assembly, discharged by the
Bessel brick at the exhibited gap data.  This is the concrete `hT` the
consumers below feed to the assembly; the linear form is the zero filler. -/
theorem cc20Eq115_gate1hT_exhibited (lam : ℝ) (hlam : 0 ≤ lam)
    (hlam1 : lam < 1) (ePrime : ℝ) (hePrime : 0 ≤ ePrime)
    (xi : Lp ℂ 2 (volume : Measure ℝ)) :
    cc20DefectQuadraticForm
        (cc20FiniteRankOperator (cc20Eq115Data lam)) xi +
      (cc20Eq115Gate1GapData lam ePrime hlam1 hePrime).a *
        ((fun _ => (0 : ℝ)) xi) ^ 2 ≥
      (cc20Eq115Gate1GapData lam ePrime hlam1 hePrime).epsilon2 * ‖xi‖ ^ 2 :=
  cc20Eq115_gate1hT lam hlam hlam1 _ (le_refl _) xi

/-- **The rank-one conclusion with the T-side payload discharged.**  CC20
Lemma `second` at the CONCRETE extracted-table operators holds from the
uniform-grid Fact-1 table plus the endpoint premises alone: no `hT` premise
remains, the linear form is the zero filler, and the bound reads
`-(2 * ePrime) * q(K_I) <= 0`. -/
theorem cc20Eq115_negativeForm_le_rankOne_of_uniformGrid_bessel
    (lam : Real) (hlam : 0 ≤ lam) (hlam1 : lam < 1)
    (endpointData : CC20EndpointSpectralData)
    (ePrime : Real) (hePrime : 0 ≤ ePrime)
    (hchi : ContinuousOn (endpointDisplacementProfile endpointData)
      cc20RootDisplacementWindow)
    (count : ℕ) (step : ℝ) (hstep : 0 < step)
    (hcover : (count : ℝ) * step ≤ cc20RootLength)
    (bound : ℕ → ℝ) (boundTail : ℝ)
    (hbound : ∀ j : ℕ, j < count → ∀ v ∈ Set.Icc ((j : ℝ) * step)
      (((j : ℝ) + 1) * step),
      ‖cc20FiniteRankDifferenceProfile endpointData (cc20Eq115Data lam) v‖ ≤
        bound j)
    (hboundTail : ∀ v ∈ Set.Icc ((count : ℝ) * step) cc20RootLength,
      ‖cc20FiniteRankDifferenceProfile endpointData (cc20Eq115Data lam) v‖ ≤
        boundTail)
    (hsum : 2 * (step * ∑ j ∈ Finset.range count, bound j +
        (cc20RootLength - (count : ℝ) * step) * boundTail) ≤
      (1 - lam) / 2)
    (hendpoint : MemLp
      (endpointKernelOnSquare endpointData cc20RootHalfWidth) 2 volume) :
    ∀ xi : Lp ℂ 2 (volume : Measure ℝ),
      -(2 * ePrime) *
        cc20DefectQuadraticForm
          (applyKernelLp (endpointKernelOnSquare endpointData cc20RootHalfWidth)
            hendpoint) xi ≤
        0 := by
  intro xi
  have h := cc20Eq115_negativeForm_le_rankOne_of_uniformGrid lam endpointData
    (cc20Eq115Gate1GapData lam ePrime hlam1 hePrime) hchi count step hstep
    hcover bound boundTail hbound hboundTail hsum hendpoint
    (ell := fun _ => (0 : ℝ))
    (hT := cc20Eq115_gate1hT_exhibited lam hlam hlam1 ePrime hePrime)
  have hxi := h xi
  have hE : (cc20Eq115Gate1GapData lam ePrime hlam1 hePrime).ePrime = ePrime :=
    rfl
  have h0 : ((fun _ => (0 : ℝ)) xi) ^ 2 = 0 := by simp
  rw [hE, cc20Eq115_exhibitedGapData_gamma_eq, h0, mul_zero] at hxi
  exact hxi

/-- **The `K_I` defect form is nonnegative, conditional on the grid table
alone (T-side discharged).**  The discharged rank-one bound at the concrete
scale `ePrime := 1`: `q(K_I) >= 0` on the ROOT window operator, i.e. the
eq-(100)-identified endpoint trace is nonpositive in the operator channel. -/
theorem cc20Eq115_kf_defect_nonneg_of_uniformGrid
    (lam : Real) (hlam : 0 ≤ lam) (hlam1 : lam < 1)
    (endpointData : CC20EndpointSpectralData)
    (hchi : ContinuousOn (endpointDisplacementProfile endpointData)
      cc20RootDisplacementWindow)
    (count : ℕ) (step : ℝ) (hstep : 0 < step)
    (hcover : (count : ℝ) * step ≤ cc20RootLength)
    (bound : ℕ → ℝ) (boundTail : ℝ)
    (hbound : ∀ j : ℕ, j < count → ∀ v ∈ Set.Icc ((j : ℝ) * step)
      (((j : ℝ) + 1) * step),
      ‖cc20FiniteRankDifferenceProfile endpointData (cc20Eq115Data lam) v‖ ≤
        bound j)
    (hboundTail : ∀ v ∈ Set.Icc ((count : ℝ) * step) cc20RootLength,
      ‖cc20FiniteRankDifferenceProfile endpointData (cc20Eq115Data lam) v‖ ≤
        boundTail)
    (hsum : 2 * (step * ∑ j ∈ Finset.range count, bound j +
        (cc20RootLength - (count : ℝ) * step) * boundTail) ≤
      (1 - lam) / 2)
    (hendpoint : MemLp
      (endpointKernelOnSquare endpointData cc20RootHalfWidth) 2 volume) :
    ∀ xi : Lp ℂ 2 (volume : Measure ℝ),
      0 ≤ cc20DefectQuadraticForm
        (applyKernelLp (endpointKernelOnSquare endpointData cc20RootHalfWidth)
          hendpoint) xi := by
  intro xi
  have h := cc20Eq115_negativeForm_le_rankOne_of_uniformGrid_bessel lam hlam
    hlam1 endpointData 1 (by norm_num) hchi count step hstep hcover bound
    boundTail hbound hboundTail hsum hendpoint xi
  have h2 : (2 : Real) * 1 = 2 := by norm_num
  rw [h2] at h
  linarith

/-- **The GATE 1 flagship residual with the T-side payload discharged.**
The eq-(100) slope-matched endpoint residual is nonpositive from the
uniform-grid table, the endpoint premises, and the trace identification
alone: `trace xi <= 0` with NO `hT` premise and NO scale on `ePrime`.  The
archimedean comparison of this residual against `W-infinity` remains
payload (delta). -/
theorem cc20Eq115_gate1Residual_nonpositive_of_uniformGrid_bessel
    (lam : Real) (hlam : 0 ≤ lam) (hlam1 : lam < 1)
    (endpointData : CC20EndpointSpectralData)
    (ePrime : Real) (hePrime : 0 ≤ ePrime)
    (hchi : ContinuousOn (endpointDisplacementProfile endpointData)
      cc20RootDisplacementWindow)
    (count : ℕ) (step : ℝ) (hstep : 0 < step)
    (hcover : (count : ℝ) * step ≤ cc20RootLength)
    (bound : ℕ → ℝ) (boundTail : ℝ)
    (hbound : ∀ j : ℕ, j < count → ∀ v ∈ Set.Icc ((j : ℝ) * step)
      (((j : ℝ) + 1) * step),
      ‖cc20FiniteRankDifferenceProfile endpointData (cc20Eq115Data lam) v‖ ≤
        bound j)
    (hboundTail : ∀ v ∈ Set.Icc ((count : ℝ) * step) cc20RootLength,
      ‖cc20FiniteRankDifferenceProfile endpointData (cc20Eq115Data lam) v‖ ≤
        boundTail)
    (hsum : 2 * (step * ∑ j ∈ Finset.range count, bound j +
        (cc20RootLength - (count : ℝ) * step) * boundTail) ≤
      (1 - lam) / 2)
    (hendpoint : MemLp
      (endpointKernelOnSquare endpointData cc20RootHalfWidth) 2 volume)
    (trace : Lp ℂ 2 (volume : Measure ℝ) → ℝ)
    (htrace : ∀ xi : Lp ℂ 2 (volume : Measure ℝ), trace xi =
      -(4 / Real.log 2) *
        cc20DefectQuadraticForm
          (applyKernelLp (endpointKernelOnSquare endpointData cc20RootHalfWidth)
            hendpoint) xi) :
    ∀ xi : Lp ℂ 2 (volume : Measure ℝ), trace xi ≤ 0 := by
  intro xi
  have h := cc20Eq115_gate1Residual_nonpositive_of_uniformGrid lam endpointData
    (cc20Eq115Gate1GapData lam ePrime hlam1 hePrime) hchi count step hstep
    hcover bound boundTail hbound hboundTail hsum hendpoint
    (ell := fun _ => (0 : ℝ))
    (hT := cc20Eq115_gate1hT_exhibited lam hlam hlam1 ePrime hePrime)
    trace htrace xi
  have hA : (cc20Eq115Gate1GapData lam ePrime hlam1 hePrime).a = 1 := rfl
  have h0 : ((fun _ => (0 : ℝ)) xi) ^ 2 = 0 := by simp
  rw [hA, h0, mul_zero] at h
  simpa using h

end

end C1CC20Gate1BesselDischarge
end Source
end ConnesWeilRH
