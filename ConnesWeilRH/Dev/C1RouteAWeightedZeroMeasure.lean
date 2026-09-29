import ConnesWeilRH.Dev.C1SpectralWeil

/-!
# C1RouteAWeightedZeroMeasure

The first executable brick for Route-A grandchild A.005.1.  The omitted
low-shell spectral residual is bounded by a fixed, owner-preserving weight:
the norm of the actual multiplicity-weighted spectral term.  This is only a
residual reduction; it does not assert that the resulting weight budget is
small enough for the producer.
-/

namespace ConnesWeilRH
namespace Source
namespace C1RouteAWeightedZeroMeasure

open C1SpectralWeil
open CC20YoshidaNearZeros
open CCM25Concrete.CompactLogConvolution

noncomputable section

/-- Local spelling of the exact low-shell owner, kept here so this brick does
not depend on the larger residual consumer during its focused audit. -/
noncomputable def weightedZeroMeasureShellPrefix (N : Nat) :
    Finset CC20YoshidaNearZeros.sourceNontrivialZeroSet :=
  (Finset.range N).biUnion fun k => (spectralHeightShell_finite k).toFinset

/-- Fixed nonnegative weight attached to the same test and source-zero owner.
It is not fitted to a sampled sign or to a replacement prime owner. -/
noncomputable def weightedZeroMeasure
    (F : CCM25Concrete.CompactLogConvolution.CompactLogTest)
    (rho : CC20YoshidaNearZeros.sourceNontrivialZeroSet) : Real :=
  spectralNormTerm F rho

theorem weightedZeroMeasure_nonneg
    (F : CCM25Concrete.CompactLogConvolution.CompactLogTest)
    (rho : CC20YoshidaNearZeros.sourceNontrivialZeroSet) :
    0 ≤ weightedZeroMeasure F rho := by
  exact spectralNormTerm_nonnegative F rho

/-- The fixed weight controls the real part of each actual spectral term. -/
theorem spectralTerm_re_le_weightedZeroMeasure
    (F : CCM25Concrete.CompactLogConvolution.CompactLogTest)
    (rho : CC20YoshidaNearZeros.sourceNontrivialZeroSet) :
    (spectralTerm F rho).re ≤ weightedZeroMeasure F rho := by
  change (spectralTerm F rho).re ≤ spectralNormTerm F rho
  exact (Complex.re_le_norm (spectralTerm F rho)).trans_eq
    (norm_spectralTerm F rho)

/-- The omitted low-shell residual is reduced to an explicit weighted-zero
measure budget, with no change to the source-zero owner. -/
theorem finite_prefix_residual_re_le_weightedZeroMeasure
    (F : CCM25Concrete.CompactLogConvolution.CompactLogTest) (N : Nat)
    (S : Finset CC20YoshidaNearZeros.sourceNontrivialZeroSet) :
    (∑ z ∈ weightedZeroMeasureShellPrefix N \ S, spectralTerm F z).re ≤
      ∑ z ∈ weightedZeroMeasureShellPrefix N \ S, weightedZeroMeasure F z := by
  calc
    (∑ z ∈ weightedZeroMeasureShellPrefix N \ S, spectralTerm F z).re =
        ∑ z ∈ weightedZeroMeasureShellPrefix N \ S, (spectralTerm F z).re := by
      simp
    _ ≤ ∑ z ∈ weightedZeroMeasureShellPrefix N \ S, weightedZeroMeasure F z := by
      exact Finset.sum_le_sum fun z hz =>
        spectralTerm_re_le_weightedZeroMeasure F z

end
end C1RouteAWeightedZeroMeasure
end Source
end ConnesWeilRH
