/-
Copyright (c) 2026 ConnesWeilRH contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ConnesWeilRH.Dev.C1CC20Eq115MassBound
import ConnesWeilRH.Dev.C1CC20FiniteRankLocalGapCertificate
import ConnesWeilRH.Dev.C1CC20EndpointCertificateData
import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-!
# The GATE 1 conditional assembly for the extracted eq-(115) table

This leaf composes every landed layer of the CC20 route into one concrete
entry point.  From a uniform-grid Fact-1 table plus the analytic caller
fields it produces, for the CONCRETE extracted table:

* the equation-(121) operator-norm gap `‖K_I − T‖ ≤ ε₁`,
* the rank-one conclusion of CC20 Lemma `second`,
* the coefficient band `13 < 4γ/log 2 < 17`,
* the scaled endpoint residual `trace − coefficient · rank ≤ 0` once the
  trace identification `trace = −(4/log 2)·q(K_I)` is supplied.

What remains for GATE 1 is exactly the four named analytic/data payloads:
the endpoint profile enclosure (`hchi`), the grid numbers themselves, the
T-side coercivity block (`hT`), and the archimedean trace comparison.  The
T-side spectral problem does NOT decouple into 2x2 blocks (the windowed
Fourier modes couple through sinc-type Gram entries), so the coercivity
block needs a certified eigenvalue enclosure of the concrete operator.

Reference: equations (100), (115), (119)-(121) of
<https://arxiv.org/html/2006.13771>; companion records docs/proofs/1044,
docs/proofs/1045, docs/proofs/1046.
-/

namespace ConnesWeilRH
namespace Source
namespace C1CC20Gate1Assembly

open MeasureTheory Set
open CC20Concrete
open C1CC20DisplacementKernel C1CC20Eq115Symmetry C1CC20Eq115Table
  C1CC20Eq115MassBound C1CC20FiniteRankApproximation
  C1CC20FiniteRankDifference C1CC20KernelLpLift C1CC20LpOperator
  C1CC20FiniteRankLocalGapCertificate C1CC20OperatorGap
  C1CC20EndpointCertificateData C1CC20EndpointCoefficient
  C1CC20RawKernelMass C1CC20RootWindowOperator

/-- The uniform-grid Fact-1 table becomes the ROOT-local gap certificate of
the extracted eq-(115) table. -/
theorem cc20Eq115_localGapCertificate_of_uniformGrid
    (lam : Real) (endpointData : CC20EndpointSpectralData)
    (gapData : CC20OperatorGapData (Lp ℂ 2 (volume : Measure ℝ)))
    (hchi : ContinuousOn (endpointDisplacementProfile endpointData)
      cc20RootDisplacementWindow)
    (count : ℕ) (step : ℝ) (hstep : 0 < step)
    (hcover : (count : ℝ) * step ≤ cc20RootLength)
    (bound : ℕ → ℝ) (boundTail : ℝ)
    (hbound : ∀ j : ℕ, j < count → ∀ v ∈ Set.Icc ((j : ℝ) * step) (((j : ℝ) + 1) * step),
      ‖cc20FiniteRankDifferenceProfile endpointData (cc20Eq115Data lam) v‖ ≤ bound j)
    (hboundTail : ∀ v ∈ Set.Icc ((count : ℝ) * step) cc20RootLength,
      ‖cc20FiniteRankDifferenceProfile endpointData (cc20Eq115Data lam) v‖ ≤ boundTail)
    (hsum : 2 * (step * ∑ j ∈ Finset.range count, bound j +
        (cc20RootLength - (count : ℝ) * step) * boundTail) ≤ gapData.epsilon1) :
    CC20FiniteRankLocalGapCertificate endpointData (cc20Eq115Data lam) gapData :=
  (cc20Eq115_halfGapCertificate_of_uniformGrid lam endpointData gapData hchi
    count step hstep hcover bound boundTail hbound hboundTail
    hsum).toLocalCertificate endpointData (cc20Eq115Data lam) gapData

/-- The grid-table mass becomes the equation-(121) operator-norm gap
`‖K_I − T‖ ≤ ε₁` at the CONCRETE extracted-table operators. -/
theorem cc20Eq115_gapNorm_le_of_uniformGrid
    (lam : Real) (endpointData : CC20EndpointSpectralData)
    (gapData : CC20OperatorGapData (Lp ℂ 2 (volume : Measure ℝ)))
    (hchi : ContinuousOn (endpointDisplacementProfile endpointData)
      cc20RootDisplacementWindow)
    (count : ℕ) (step : ℝ) (hstep : 0 < step)
    (hcover : (count : ℝ) * step ≤ cc20RootLength)
    (bound : ℕ → ℝ) (boundTail : ℝ)
    (hbound : ∀ j : ℕ, j < count → ∀ v ∈ Set.Icc ((j : ℝ) * step) (((j : ℝ) + 1) * step),
      ‖cc20FiniteRankDifferenceProfile endpointData (cc20Eq115Data lam) v‖ ≤ bound j)
    (hboundTail : ∀ v ∈ Set.Icc ((count : ℝ) * step) cc20RootLength,
      ‖cc20FiniteRankDifferenceProfile endpointData (cc20Eq115Data lam) v‖ ≤ boundTail)
    (hsum : 2 * (step * ∑ j ∈ Finset.range count, bound j +
        (cc20RootLength - (count : ℝ) * step) * boundTail) ≤ gapData.epsilon1)
    (hendpoint : MemLp
      (endpointKernelOnSquare endpointData cc20RootHalfWidth) 2 volume) :
    ‖applyKernelLp (endpointKernelOnSquare endpointData cc20RootHalfWidth) hendpoint -
      cc20FiniteRankOperator (cc20Eq115Data lam)‖ ≤ gapData.epsilon1 :=
  cc20FiniteRankGapNorm_le_of_localCertificate endpointData (cc20Eq115Data lam)
    gapData (cc20Eq115_localGapCertificate_of_uniformGrid lam endpointData
      gapData hchi count step hstep hcover bound boundTail hbound hboundTail
      hsum) hendpoint

/-- CC20 Lemma `second`'s rank-one conclusion at the CONCRETE extracted-table
operators, from the grid table plus the T-side coercivity block. -/
theorem cc20Eq115_negativeForm_le_rankOne_of_uniformGrid
    (lam : Real) (endpointData : CC20EndpointSpectralData)
    (gapData : CC20OperatorGapData (Lp ℂ 2 (volume : Measure ℝ)))
    (hchi : ContinuousOn (endpointDisplacementProfile endpointData)
      cc20RootDisplacementWindow)
    (count : ℕ) (step : ℝ) (hstep : 0 < step)
    (hcover : (count : ℝ) * step ≤ cc20RootLength)
    (bound : ℕ → ℝ) (boundTail : ℝ)
    (hbound : ∀ j : ℕ, j < count → ∀ v ∈ Set.Icc ((j : ℝ) * step) (((j : ℝ) + 1) * step),
      ‖cc20FiniteRankDifferenceProfile endpointData (cc20Eq115Data lam) v‖ ≤ bound j)
    (hboundTail : ∀ v ∈ Set.Icc ((count : ℝ) * step) cc20RootLength,
      ‖cc20FiniteRankDifferenceProfile endpointData (cc20Eq115Data lam) v‖ ≤ boundTail)
    (hsum : 2 * (step * ∑ j ∈ Finset.range count, bound j +
        (cc20RootLength - (count : ℝ) * step) * boundTail) ≤ gapData.epsilon1)
    (hendpoint : MemLp
      (endpointKernelOnSquare endpointData cc20RootHalfWidth) 2 volume)
    {ell : Lp ℂ 2 (volume : Measure ℝ) → ℝ}
    (hT : ∀ xi : Lp ℂ 2 (volume : Measure ℝ),
      cc20DefectQuadraticForm (cc20FiniteRankOperator (cc20Eq115Data lam)) xi +
        gapData.a * (ell xi) ^ 2 ≥ gapData.epsilon2 * ‖xi‖ ^ 2) :
    ∀ xi : Lp ℂ 2 (volume : Measure ℝ),
      -(2 * gapData.ePrime) *
        cc20DefectQuadraticForm
          (applyKernelLp (endpointKernelOnSquare endpointData cc20RootHalfWidth)
            hendpoint) xi ≤
        gapData.gamma * (ell xi) ^ 2 :=
  cc20FiniteRankNegativeForm_le_rankOne_of_localCertificate endpointData
    (cc20Eq115Data lam) gapData
    (cc20Eq115_localGapCertificate_of_uniformGrid lam endpointData gapData
      hchi count step hstep hcover bound boundTail hbound hboundTail hsum)
    hendpoint hT

/-- The concrete table's gamma lands in the paper's band: the coefficient
`4γ/log 2` of the rank-one correction lies in `(13, 17)`. -/
theorem cc20Eq115_coefficient_band_of_uniformGrid
    (gapData : CC20OperatorGapData (Lp ℂ 2 (volume : Measure ℝ)))
    (hband : (294 : ℝ) / 100 < gapData.gamma)
    (hband' : gapData.gamma < (2944 : ℝ) / 1000) :
    13 < (gapData.toGammaSpectralData hband hband').coefficient ∧
      (gapData.toGammaSpectralData hband hband').coefficient < 17 :=
  (gapData.toGammaSpectralData hband hband').coefficient_band

/-- The GATE 1 flagship for the extracted table: from the uniform-grid
Fact-1 table, the endpoint continuity, and the T-side coercivity block, the
coercivity transfer through the grid-certified operator gap leaves the
`K_I`-side defect form bounded by the rank-one repair weight `a`.  With the
trace identification `trace = −(4/log 2)·q(K_I)` (the eq-(100) slope
consumption), the slope-matched endpoint residual `trace − (4a/log 2)·rank`
is nonpositive - the exact shape of the certificate's `endpoint_bound` left
side at the repair-weight constant.  What is NOT claimed here: the
archimedean comparison of that residual against `W∞` (the named analytic
payload of GATE 1), and the gamma-weighted form of the shift, which needs
the certified spectral block of the concrete operator itself. -/
theorem cc20Eq115_gate1Residual_nonpositive_of_uniformGrid
    (lam : Real) (endpointData : CC20EndpointSpectralData)
    (gapData : CC20OperatorGapData (Lp ℂ 2 (volume : Measure ℝ)))
    (hchi : ContinuousOn (endpointDisplacementProfile endpointData)
      cc20RootDisplacementWindow)
    (count : ℕ) (step : ℝ) (hstep : 0 < step)
    (hcover : (count : ℝ) * step ≤ cc20RootLength)
    (bound : ℕ → ℝ) (boundTail : ℝ)
    (hbound : ∀ j : ℕ, j < count → ∀ v ∈ Set.Icc ((j : ℝ) * step) (((j : ℝ) + 1) * step),
      ‖cc20FiniteRankDifferenceProfile endpointData (cc20Eq115Data lam) v‖ ≤ bound j)
    (hboundTail : ∀ v ∈ Set.Icc ((count : ℝ) * step) cc20RootLength,
      ‖cc20FiniteRankDifferenceProfile endpointData (cc20Eq115Data lam) v‖ ≤ boundTail)
    (hsum : 2 * (step * ∑ j ∈ Finset.range count, bound j +
        (cc20RootLength - (count : ℝ) * step) * boundTail) ≤ gapData.epsilon1)
    (hendpoint : MemLp
      (endpointKernelOnSquare endpointData cc20RootHalfWidth) 2 volume)
    (ell : Lp ℂ 2 (volume : Measure ℝ) → ℝ)
    (hT : ∀ xi : Lp ℂ 2 (volume : Measure ℝ),
      cc20DefectQuadraticForm (cc20FiniteRankOperator (cc20Eq115Data lam)) xi +
        gapData.a * (ell xi) ^ 2 ≥ gapData.epsilon2 * ‖xi‖ ^ 2)
    (trace : Lp ℂ 2 (volume : Measure ℝ) → ℝ)
    (htrace : ∀ xi : Lp ℂ 2 (volume : Measure ℝ), trace xi =
      -(4 / Real.log 2) *
        cc20DefectQuadraticForm
          (applyKernelLp (endpointKernelOnSquare endpointData cc20RootHalfWidth)
            hendpoint) xi) :
    ∀ xi : Lp ℂ 2 (volume : Measure ℝ),
      trace xi - (4 * gapData.a / Real.log 2) * (ell xi) ^ 2 ≤ 0 := by
  intro xi
  have hgap := cc20Eq115_gapNorm_le_of_uniformGrid lam endpointData gapData hchi
    count step hstep hcover bound boundTail hbound hboundTail hsum hendpoint
  have hcoer := cc20GapCoercivity_transfer_of_opNorm gapData
    (applyKernelLp (endpointKernelOnSquare endpointData cc20RootHalfWidth) hendpoint)
    (cc20FiniteRankOperator (cc20Eq115Data lam)) hT hgap xi
  have hdiff : (0 : ℝ) ≤ gapData.epsilon2 - gapData.epsilon1 := by
    linarith [gapData.h_gap]
  have htail : 0 ≤ (gapData.epsilon2 - gapData.epsilon1) * ‖xi‖ ^ 2 :=
    mul_nonneg hdiff (sq_nonneg _)
  have hshift : 0 ≤
      cc20DefectQuadraticForm
        (applyKernelLp (endpointKernelOnSquare endpointData cc20RootHalfWidth)
          hendpoint) xi +
      gapData.a * (ell xi) ^ 2 := by
    linarith
  have hlog_pos : 0 < Real.log 2 :=
    lt_trans (by norm_num) Real.log_two_gt_d9
  have hscale : 0 ≤ (4 : ℝ) / Real.log 2 :=
    div_nonneg (by norm_num) hlog_pos.le
  have hmul : 0 ≤ (4 / Real.log 2) *
      (cc20DefectQuadraticForm
          (applyKernelLp (endpointKernelOnSquare endpointData cc20RootHalfWidth)
            hendpoint) xi +
        gapData.a * (ell xi) ^ 2) :=
    mul_nonneg hscale hshift
  rw [mul_add] at hmul
  calc trace xi - (4 * gapData.a / Real.log 2) * (ell xi) ^ 2
      = -(4 / Real.log 2) *
          cc20DefectQuadraticForm
            (applyKernelLp (endpointKernelOnSquare endpointData cc20RootHalfWidth)
              hendpoint) xi -
        (4 / Real.log 2) * (gapData.a * (ell xi) ^ 2) := by
        rw [htrace xi]
        ring
    _ ≤ 0 := by linarith [hmul]

end C1CC20Gate1Assembly
end Source
end ConnesWeilRH
