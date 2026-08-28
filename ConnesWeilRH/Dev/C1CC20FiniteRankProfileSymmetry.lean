/-
Copyright (c) 2026 ConnesWeilRH contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ConnesWeilRH.Dev.C1CC20FiniteRankHalfGapCertificate

/-!
# Paired plus/minus symmetry of the CC20 finite-rank profile

The half-window form of CC20 Fact 1 needs the equation-(120) finite profile
to be even.  This leaf derives that fact from paired finite data rather than
accepting it as an opaque certificate field: a permutation of the finite index
set negates both frequencies and preserves the associated coefficient.

Fixed points are allowed, so the zero-frequency term is covered directly.

Reference: equation (114) and the conventions
`alpha_{-n} = -alpha_n`, `d(-n) = d(n)` in
<https://arxiv.org/html/2006.13771>.
-/

namespace ConnesWeilRH
namespace Source
namespace C1CC20FiniteRankProfileSymmetry

open C1CC20FiniteRankApproximation

/-- A finite reindexing which realizes the `plus/minus` pairing of the CC20
frequency data.  An involution law is unnecessary: bijectivity already gives
the finite-sum reindexing, and the displayed data equations carry the required
negation information. -/
structure CC20FiniteRankProfileNegationData {ι : Type*} [Fintype ι]
    (data : CC20FiniteRankData ι) where
  negIndex : ι ≃ ι
  frequency_at_negIndex : ∀ i : ι,
    data.frequency (negIndex i) = -data.frequency i
  perturbedFrequency_at_negIndex : ∀ i : ι,
    data.perturbedFrequency (negIndex i) = -data.perturbedFrequency i
  coefficient_at_negIndex : ∀ i : ι,
    data.coefficient (negIndex i) = data.coefficient i

/-- Negating both the frequency and the displacement leaves the Fourier phase
unchanged. -/
theorem cc20FourierPhase_neg_neg (alpha v : Real) :
    cc20FourierPhase (-alpha) (-v) = cc20FourierPhase alpha v := by
  unfold cc20FourierPhase
  congr 1
  push_cast
  ring

/-- The root displacement window is invariant under negation. -/
theorem neg_mem_cc20RootDisplacementWindow_iff (v : Real) :
    -v ∈ cc20RootDisplacementWindow ↔ v ∈ cc20RootDisplacementWindow := by
  unfold cc20RootDisplacementWindow
  constructor <;> intro hv <;> constructor <;> linarith [hv.1, hv.2]

/-- A Fourier-projection displacement profile transforms covariantly under the
simultaneous negation of frequency and displacement. -/
theorem cc20FourierProjectionProfile_neg_neg (alpha v : Real) :
    cc20FourierProjectionProfile (-alpha) (-v) =
      cc20FourierProjectionProfile alpha v := by
  unfold cc20FourierProjectionProfile
  by_cases hv : v ∈ cc20RootDisplacementWindow
  · have hneg : -v ∈ cc20RootDisplacementWindow :=
      neg_mem_cc20RootDisplacementWindow_iff v |>.mpr hv
    simp only [Set.indicator_of_mem hneg, Set.indicator_of_mem hv, neg_neg]
    congr 1
    unfold cc20FourierPhase
    congr 1
    push_cast
    ring
  · have hneg : -v ∉ cc20RootDisplacementWindow := by
      intro hneg
      exact hv (neg_mem_cc20RootDisplacementWindow_iff v |>.mp hneg)
    simp only [Set.indicator_of_notMem hneg, Set.indicator_of_notMem hv]

/-- Each paired finite-rank profile term is preserved by simultaneous index and
displacement negation. -/
theorem cc20FiniteRankProfileTerm_neg_neg_of_negationData
    {ι : Type*} [Fintype ι]
    (data : CC20FiniteRankData ι)
    (symmetry : CC20FiniteRankProfileNegationData data)
    (i : ι) (v : Real) :
    cc20FiniteRankProfileTerm data (symmetry.negIndex i) (-v) =
      cc20FiniteRankProfileTerm data i v := by
  calc
    cc20FiniteRankProfileTerm data (symmetry.negIndex i) (-v) =
    cc20FourierProjectionProfile (-data.frequency i) (-v) -
          ((data.coefficient i : Real) : Complex) •
            cc20FourierProjectionProfile (-data.perturbedFrequency i) (-v) := by
      simp only [cc20FiniteRankProfileTerm, Pi.sub_apply, Pi.smul_apply]
      rw [symmetry.frequency_at_negIndex,
        symmetry.perturbedFrequency_at_negIndex,
        symmetry.coefficient_at_negIndex]
    _ = cc20FourierProjectionProfile (data.frequency i) v -
          ((data.coefficient i : Real) : Complex) •
            cc20FourierProjectionProfile (data.perturbedFrequency i) v := by
      rw [cc20FourierProjectionProfile_neg_neg,
        cc20FourierProjectionProfile_neg_neg]
    _ = cc20FiniteRankProfileTerm data i v := rfl

/-- Paired `plus/minus` finite data makes the entire equation-(120) profile
even.  This is the structural producer consumed by the Fact-1 half-window
certificate. -/
theorem cc20FiniteRankProfile_even_of_negationData
    {ι : Type*} [Fintype ι]
    (data : CC20FiniteRankData ι)
    (symmetry : CC20FiniteRankProfileNegationData data)
    (v : Real) :
    cc20FiniteRankProfile data (-v) = cc20FiniteRankProfile data v := by
  have hsum :
      (∑ i : ι, cc20FiniteRankProfileTerm data i (-v)) =
        ∑ i : ι, cc20FiniteRankProfileTerm data i v := by
    calc
      (∑ i : ι, cc20FiniteRankProfileTerm data i (-v)) =
          ∑ i : ι, cc20FiniteRankProfileTerm data (symmetry.negIndex i) (-v) :=
        (Equiv.sum_comp symmetry.negIndex
          (fun i : ι => cc20FiniteRankProfileTerm data i (-v))).symm
      _ = ∑ i : ι, cc20FiniteRankProfileTerm data i v := by
        apply Finset.sum_congr rfl
        intro i _
        exact cc20FiniteRankProfileTerm_neg_neg_of_negationData data symmetry i v
  unfold cc20FiniteRankProfile
  simp only [Pi.smul_apply, Finset.sum_apply]
  exact congrArg (fun profile => ((data.lambda : Real) : Complex) • profile) hsum

end C1CC20FiniteRankProfileSymmetry
end Source
end ConnesWeilRH
