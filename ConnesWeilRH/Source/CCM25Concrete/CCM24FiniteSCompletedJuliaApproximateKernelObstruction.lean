/-
Copyright (c) 2026 ConnesWeilRH contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ConnesWeilRH.Source.CCM25Concrete.CCM24FiniteSCompletedJuliaRawDouglasReadout

/-!
# Approximate-kernel obstruction for the raw physical producer

An exact zero mode is not the only obstruction to a uniform Douglas producer.
If a family of source vectors makes the packed physical analysis tend to zero
while the raw adjoint stays uniformly away from zero, then no finite common
Douglas bound can exist.  This is the functional-analytic form of the
near-resonant wave-packet test: a bounded readout would force the raw output
to tend to zero along every approximate kernel.

The theorem below is only a necessary-condition guard.  It does not assert
that the actual finite-S carrier contains such a sequence.  Constructing or
excluding that sequence remains a source theorem.
-/

namespace ConnesWeilRH
namespace Source
namespace CCM25Concrete
namespace CCM24FiniteSCompletedJuliaApproximateKernelObstruction

open scoped InnerProduct InnerProductSpace
open scoped Topology

open CC20Concrete
open CCM24FiniteSActualSchurCascade
open CCM24FiniteSCompletedJuliaAmbientDefectFactorization
open CCM24FiniteSCompletedJuliaMismatchFactorization
open CCM24FiniteSCompletedJuliaRawDouglasReadout
open CCM24FiniteSCompletedJuliaUniformRawReadout
open CCM24FiniteSFrameGramCalculus

noncomputable local instance sourceSoninCarrierCompleteSpace
    (lambda : CCM24SoninScale) : CompleteSpace (sourceSoninCarrier lambda) :=
  (ccm24ArchimedeanSoninClosedSubspace lambda).isClosed.completeSpace_coe

/-! ## Uniform approximate-kernel obstruction -/

/-- A normalized approximate zero mode of the packed physical analysis on
which the raw adjoint stays above a fixed positive threshold rules out every
finite uniform raw Douglas bound. -/
theorem noExistsUniformRawDomination_of_approximateAnalysisZeroMode
    {owner : SelectedWeilSquare.SelectedWeilSquareOwner}
    {lambda : CCM24SoninScale}
    (prime : ℕ → CCM24VisiblePrime)
    (suffix : ℕ → List CCM24VisiblePrime)
    (x : ℕ → sourceSoninCarrier lambda)
    (epsilon : ℝ) (hepsilon : 0 < epsilon)
    (hraw : ∀ᶠ n in Filter.atTop,
      epsilon ≤
        ‖((suffixActualBandRawQuadraticIntertwiningDefect
          owner lambda (prime n) (suffix n))†) (x n)‖)
    (hanalysis : Filter.Tendsto
      (fun n =>
        ‖suffixEulerFrameAmbientBoundaryAnalysis lambda (prime n)
          (suffix n) (x n)‖)
      Filter.atTop (𝓝 0)) :
    ¬ ∃ bound : ℝ,
      Nonempty
        (SuffixRawAmbientBoundaryUniformDominationData owner lambda bound) := by
  rintro ⟨bound, ⟨data⟩⟩
  have hbound : 0 ≤ bound := data.bound_nonneg
  have hdenom : 0 < bound + 1 := by linarith
  have hdelta : 0 < epsilon / (bound + 1) :=
    div_pos hepsilon hdenom
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.mp
    (Metric.tendsto_nhds.mp hanalysis (epsilon / (bound + 1)) hdelta)
  obtain ⟨n, hn⟩ :=
    (hraw.and (Filter.eventually_ge_atTop N)).exists
  have hsmallDist := hN n hn.2
  have hsmall :
      ‖suffixEulerFrameAmbientBoundaryAnalysis lambda (prime n)
          (suffix n) (x n)‖ < epsilon / (bound + 1) := by
    simpa [Real.dist_eq, abs_of_nonneg (norm_nonneg _)] using
      hsmallDist
  have hsq := (data.domination (prime n) (suffix n)).2 (x n)
  rw [← suffixEulerFrameAmbientBoundaryAnalysis_normSq_eq_channels] at hsq
  have hnorm :
      ‖((suffixActualBandRawQuadraticIntertwiningDefect
        owner lambda (prime n) (suffix n))†) (x n)‖ ≤
        bound *
          ‖suffixEulerFrameAmbientBoundaryAnalysis lambda (prime n)
            (suffix n) (x n)‖ := by
    apply (sq_le_sq₀ (norm_nonneg _)
      (mul_nonneg hbound (norm_nonneg _))).mp
    simpa [mul_pow] using hsq
  have hscaled :
      bound *
          ‖suffixEulerFrameAmbientBoundaryAnalysis lambda (prime n)
            (suffix n) (x n)‖ ≤
        bound * (epsilon / (bound + 1)) :=
      mul_le_mul_of_nonneg_left hsmall.le hbound
  have hratio : bound * (epsilon / (bound + 1)) < epsilon := by
    calc
      bound * (epsilon / (bound + 1)) =
          (bound * epsilon) / (bound + 1) := by ring
      _ < epsilon := by
        apply (div_lt_iff₀ hdenom).2
        nlinarith
  have hlt :
      ‖((suffixActualBandRawQuadraticIntertwiningDefect
        owner lambda (prime n) (suffix n))†) (x n)‖ < epsilon :=
    lt_of_le_of_lt hnorm (hscaled.trans_lt hratio)
  exact (not_lt_of_ge hn.1) hlt

/-- The same approximate-kernel witness rules out the family-uniform physical
Douglas contract, using the already proved raw/physical existence equivalence.
-/
theorem noExistsUniformPhysicalDomination_of_approximateAnalysisZeroMode
    {owner : SelectedWeilSquare.SelectedWeilSquareOwner}
    {lambda : CCM24SoninScale}
    (prime : ℕ → CCM24VisiblePrime)
    (suffix : ℕ → List CCM24VisiblePrime)
    (x : ℕ → sourceSoninCarrier lambda)
    (epsilon : ℝ) (hepsilon : 0 < epsilon)
    (hraw : ∀ᶠ n in Filter.atTop,
      epsilon ≤
        ‖((suffixActualBandRawQuadraticIntertwiningDefect
          owner lambda (prime n) (suffix n))†) (x n)‖)
    (hanalysis : Filter.Tendsto
      (fun n =>
        ‖suffixEulerFrameAmbientBoundaryAnalysis lambda (prime n)
          (suffix n) (x n)‖)
      Filter.atTop (𝓝 0)) :
    ¬ ∃ bound : ℝ,
      Nonempty
        (SuffixMismatchAmbientBoundaryUniformDominationData owner lambda bound) := by
  intro hphysical
  have hrawDom :
      ∃ bound : ℝ,
        Nonempty
          (SuffixRawAmbientBoundaryUniformDominationData owner lambda bound) :=
    (exists_uniformRawDomination_iff_exists_uniformPhysicalDomination
      owner lambda).mpr hphysical
  exact noExistsUniformRawDomination_of_approximateAnalysisZeroMode
    prime suffix x epsilon hepsilon hraw hanalysis hrawDom

end CCM24FiniteSCompletedJuliaApproximateKernelObstruction
end CCM25Concrete
end Source
end ConnesWeilRH
