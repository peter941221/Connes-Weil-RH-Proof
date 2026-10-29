import ConnesWeilRH.Source.AnalyticSourceModel
import ConnesWeilRH.Dev.AmbientPrimeVisibleProbe
import ConnesWeilRH.Dev.ConcreteP1SupportProbe

/-!
# 3163 - the live concrete source object is not yet an indexed producer

The live `concreteWeilForm` is a genuine
`SourceWeilFormData`, but its concrete test algebra uses the diagnostic
addition carrier. Therefore an arbitrary convolution can expose prime `3`
even though the selected common bump has no prime-`3` term.

This proves that the 3162 `IndexedFinitePrimeProducer` contract cannot be
constructed from the current common-only support object. No RH claim.
-/

namespace ConnesWeilRH
namespace Source
namespace Dev
namespace IndexedProducerConcreteNoGo3163

open AnalyticCore
open AnalyticCore.SourceConcreteBaseLayer
open ConcreteP1SupportProbe
open CC20YoshidaInterpolationNode

noncomputable def counterBump : TestFunction :=
  Classical.choose
    (exists_testFunction_supported_Icc_eq_one
      (a := (5/2 : ℝ)) (x := (3 : ℝ)) (b := (7/2 : ℝ))
      (hax := by norm_num) (hxb := by norm_num))

lemma counterBump_value_three : counterBump (3 : ℝ) = 1 :=
  (Classical.choose_spec
    (exists_testFunction_supported_Icc_eq_one
      (a := (5/2 : ℝ)) (x := (3 : ℝ)) (b := (7/2 : ℝ))
      (hax := by norm_num) (hxb := by norm_num))).2.2

noncomputable abbrev W : SourceWeilFormData concreteTestAlgebra :=
  concreteWeilForm

lemma concrete_counter_term_three_ne_zero :
    concreteWeilForm.evaluation.sourceFinitePrimeTerm
        3 counterBump ≠ 0 := by
  have hval :
      concreteWeilForm.evaluation.valueAt
          counterBump (3 : ℝ) = 1 := by
    rw [SourceEvaluationData.valueAt_eq_norm]
    have henc :
        concreteTestAlgebra.legacy.encode
            counterBump (3 : ℝ) = 1 := by
      simp [concreteTestAlgebra,
        concreteLegacyTestEquiv, counterBump_value_three]
    rw [henc]
    norm_num
  have hvalInv :
      0 ≤ concreteWeilForm.evaluation.valueAt
        counterBump ((3 : ℝ)⁻¹) := by
    rw [SourceEvaluationData.valueAt_eq_norm]
    exact norm_nonneg _
  have hsum :
      0 < concreteWeilForm.evaluation.valueAt
          counterBump (3 : ℝ) +
        concreteWeilForm.evaluation.valueAt
          counterBump ((3 : ℝ)⁻¹) := by
    calc
      0 < concreteWeilForm.evaluation.valueAt counterBump (3 : ℝ) := by rw [hval]; norm_num
      _ ≤ concreteWeilForm.evaluation.valueAt counterBump (3 : ℝ) +
          concreteWeilForm.evaluation.valueAt counterBump ((3 : ℝ)⁻¹) :=
        le_add_of_nonneg_right hvalInv
  have hLam : 0 < ArithmeticFunction.vonMangoldt 3 := by
    rw [ArithmeticFunction.vonMangoldt_apply_prime Nat.prime_three]
    exact Real.log_pos (by norm_num)
  have hsqrt : 0 < Real.sqrt (3 : ℝ) :=
    Real.sqrt_pos.mpr (by norm_num)
  rw [SourceEvaluationData.sourceFinitePrimeTerm_eq_valueAt]
  exact ne_of_gt (mul_pos hLam
    (mul_pos (div_pos zero_lt_one hsqrt) hsum))

lemma concrete_counter_prime_three_visible :
    W.toWeilFormSymbols.finitePrimeAtomVisible 3
        (W.toWeilFormSymbols.convolutionStar
          counterBump 0) := by
  change W.finitePrime.sourceAtomVisible 3
    (concreteTestAlgebra.convolutionStar
      (concreteTestAlgebra.legacy.decode
        counterBump)
      (concreteTestAlgebra.legacy.decode 0))
  rw [show concreteTestAlgebra.convolutionStar
      (concreteTestAlgebra.legacy.decode
        counterBump)
      (concreteTestAlgebra.legacy.decode 0) =
      concreteTestAlgebra.legacy.decode
        counterBump by
        simp [concreteTestAlgebra,
          concreteLegacyTestEquiv]]
  simpa [W, SourceWeilFormData.toWeilFormSymbols_finitePrimeAtomVisible,
    SourceFinitePrimeData.sourceAtomVisible,
    concreteTestAlgebra,
    concreteLegacyTestEquiv] using concrete_counter_term_three_ne_zero

lemma concrete_common_prime_three_not_visible :
    ¬ W.toWeilFormSymbols.finitePrimeAtomVisible 3
        (concreteTestAlgebra.legacy.encode W.common) := by
  intro hvisible
  have hzero :
      concreteWeilForm.evaluation.sourceFinitePrimeTerm
          3 commonBump = 0 := by
    rw [SourceEvaluationData.sourceFinitePrimeTerm_eq_valueAt,
      SourceEvaluationData.valueAt_eq_norm]
    have hforward : commonBump (3 : ℝ) = 0 := by
      by_contra hne
      have hmem : (3 : ℝ) ∈ Set.Icc (3 / 2 : ℝ) (5 / 2 : ℝ) :=
        commonBump_support_subset hne
      norm_num at hmem
    have hinverse : commonBump ((3 : ℝ)⁻¹) = 0 := by
      by_contra hne
      have hmem : ((3 : ℝ)⁻¹ : ℝ) ∈ Set.Icc (3 / 2 : ℝ) (5 / 2 : ℝ) :=
        commonBump_support_subset hne
      exact AmbientPrimeProbe.not_mem_Icc_two_inv hmem
    simp [concreteTestAlgebra,
      concreteLegacyTestEquiv, hforward, hinverse]
  have hne : concreteWeilForm.evaluation.sourceFinitePrimeTerm
      3 commonBump ≠ 0 := by
    simpa [W, SourceWeilFormData.toWeilFormSymbols_finitePrimeAtomVisible,
      SourceFinitePrimeData.sourceAtomVisible, concreteTestAlgebra,
      concreteLegacyTestEquiv] using hvisible
  exact hne hzero

theorem not_indexedFinitePrimeProducer :
    ¬ Nonempty W.IndexedFinitePrimeProducer := by
  rintro ⟨producer⟩
  have hdom : W.finitePrimeDominance :=
    SourceWeilFormData.finitePrimeDominance_of_indexed_certificates W
      producer.indexedSourceTestCertificates
  have hcommon := hdom counterBump 0 3
    concrete_counter_prime_three_visible
  exact concrete_common_prime_three_not_visible hcommon

#print axioms concrete_counter_term_three_ne_zero
#print axioms concrete_counter_prime_three_visible
#print axioms concrete_common_prime_three_not_visible
#print axioms not_indexedFinitePrimeProducer

end IndexedProducerConcreteNoGo3163
end Dev
end Source
end ConnesWeilRH
