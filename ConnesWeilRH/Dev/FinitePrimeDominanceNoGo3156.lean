import ConnesWeilRH.Dev.AmbientPrimeVisibleProbe
import ConnesWeilRH.Source.AnalyticCore

/-!
# 3156: per-common support does not imply finite-prime dominance

This file gives a small axiom-clean countermodel.  Its per-common support is
the same exact `{2}` support used by the ambient prime-2 probe, but its test
algebra sends every convolution to a different bump visible at `3`.  Thus the
common support rows hold while `SourceWeilFormData.finitePrimeDominance` fails.
-/

namespace ConnesWeilRH
namespace Source
namespace Dev
namespace FinitePrimeDominanceNoGo3156

open AnalyticCore
open AmbientPrimeProbe
open CC20YoshidaInterpolationNode
open scoped FourierTransform SchwartzMap

noncomputable def counterBump : TestFunction :=
  Classical.choose
    (exists_testFunction_supported_Icc_eq_one
      (a := (5 / 2 : ℝ)) (x := (3 : ℝ)) (b := (7 / 2 : ℝ))
      (hax := by norm_num) (hxb := by norm_num))

lemma counterBump_support_subset :
    Function.support (fun t : ℝ => counterBump t) ⊆
      Set.Icc (5 / 2 : ℝ) (7 / 2 : ℝ) :=
  (Classical.choose_spec
    (exists_testFunction_supported_Icc_eq_one
      (a := (5 / 2 : ℝ)) (x := (3 : ℝ)) (b := (7 / 2 : ℝ))
      (hax := by norm_num) (hxb := by norm_num))).1

lemma counterBump_value_three : counterBump (3 : ℝ) = 1 :=
  (Classical.choose_spec
    (exists_testFunction_supported_Icc_eq_one
      (a := (5 / 2 : ℝ)) (x := (3 : ℝ)) (b := (7 / 2 : ℝ))
      (hax := by norm_num) (hxb := by norm_num))).2.2

lemma counter_valueAt_three :
    ambientEval.valueAt counterBump (3 : ℝ) = 1 := by
  rw [SourceEvaluationData.valueAt_eq_norm]
  have henc : ambientSourceAlgebra.legacy.encode counterBump (3 : ℝ) = 1 := by
    simp [ambientSourceAlgebra, ambientLegacy, counterBump_value_three]
  rw [henc]
  norm_num

lemma counter_term_three_pos :
    0 < ambientEval.sourceFinitePrimeTerm 3 counterBump := by
  have hvalInv : 0 ≤ ambientEval.valueAt counterBump ((3 : ℝ)⁻¹) := by
    rw [SourceEvaluationData.valueAt_eq_norm]
    exact norm_nonneg _
  have hsum : 0 < ambientEval.valueAt counterBump (3 : ℝ) +
      ambientEval.valueAt counterBump ((3 : ℝ)⁻¹) := by
    rw [counter_valueAt_three]
    linarith
  have hLam : 0 < ArithmeticFunction.vonMangoldt 3 := by
    rw [ArithmeticFunction.vonMangoldt_apply_prime Nat.prime_three]
    exact Real.log_pos (by norm_num)
  have hsqrt : 0 < Real.sqrt (3 : ℝ) := by
    exact Real.sqrt_pos.mpr (by norm_num)
  have hsc : 0 < (1 / Real.sqrt (3 : ℝ) : ℝ) := by
    exact div_pos zero_lt_one hsqrt
  rw [SourceEvaluationData.sourceFinitePrimeTerm_eq_valueAt]
  exact mul_pos hLam (mul_pos hsc hsum)

lemma counter_term_three_ne_zero :
    ambientEval.sourceFinitePrimeTerm 3 counterBump ≠ 0 :=
  ne_of_gt counter_term_three_pos

lemma common_term_three_zero :
    ambientEval.sourceFinitePrimeTerm 3 commonBump = 0 := by
  have hcommon : commonBump (3 : ℝ) = 0 := by
    by_contra hne
    have hmem : (3 : ℝ) ∈ Set.Icc (3 / 2 : ℝ) (5 / 2 : ℝ) :=
      commonBump_support_subset hne
    norm_num at hmem
  have hcommonInv : commonBump ((3 : ℝ)⁻¹) = 0 := by
    by_contra hne
    have hmem : ((3 : ℝ)⁻¹ : ℝ) ∈ Set.Icc (3 / 2 : ℝ) (5 / 2 : ℝ) :=
      commonBump_support_subset hne
    exact not_mem_Icc_two_inv hmem
  rw [SourceEvaluationData.sourceFinitePrimeTerm_eq_valueAt,
    SourceEvaluationData.valueAt_eq_norm]
  simp [ambientSourceAlgebra, ambientLegacy, hcommon, hcommonInv]

noncomputable def counterexampleAlgebra : SourceTestAlgebra where
  Test := TestFunction
  legacy := ambientLegacy
  convolutionStar := fun _ _ => counterBump
  involution := id
  convolutionSquare := fun _ => counterBump
  convolutionSquare_eq := by intro; rfl

noncomputable def counterexampleEval :
    SourceEvaluationData counterexampleAlgebra :=
  {}

noncomputable def counterexampleSupport :
    PerCommonSourceFinitePrimeSupport counterexampleAlgebra
      counterexampleEval commonBump :=
  { globalIndexSet := ({2} : Finset ℕ)
    restrictedIndexSet := fun lambda : ℝ =>
      if 2 ≤ lambda ^ 2 then ({2} : Finset ℕ) else ∅
    sourceVisibleGlobalIndex := by
      intro n hn
      have hn2 : n = 2 := forward_mem n hn
      subst n
      simp
    sourceVisibleRestrictedIndex := by
      intro lambda n hn hOne hle
      have hn2 : n = 2 := forward_mem n hn
      subst n
      rw [if_pos]
      · simp
      · simpa using hle
    commonGlobalIndex := by
      intro n hn
      simp at hn
      rw [hn]
      simpa [counterexampleEval, counterexampleAlgebra] using term_two_ne_zero
    commonRestrictedIndex := by
      intro lambda n hn
      by_cases hcut : 2 ≤ lambda ^ 2
      · simp [hcut] at hn
        have hn2 : n = 2 := by simpa using hn
        rw [hn2]
        exact ⟨by simpa [counterexampleEval, counterexampleAlgebra] using term_two_ne_zero,
          by norm_num, hcut⟩
      · simp [hcut] at hn }
noncomputable def counterexampleWeilForm :
    SourceWeilFormData counterexampleAlgebra where
  evaluation := counterexampleEval
  common := commonBump
  finitePrime := { support := counterexampleSupport }
  archimedeanTerm := fun _ => 0

theorem not_finitePrimeDominance :
    ¬ counterexampleWeilForm.finitePrimeDominance := by
  intro hdom
  have hvis :
      counterexampleWeilForm.toWeilFormSymbols.finitePrimeAtomVisible 3
        (counterexampleWeilForm.toWeilFormSymbols.convolutionStar
          (0 : TestFunction) 0) := by
    simpa [counterexampleWeilForm, counterexampleAlgebra, counterexampleEval,
      SourceWeilFormData.toWeilFormSymbols_finitePrimeAtomVisible,
      SourceFinitePrimeData.sourceAtomVisible] using counter_term_three_ne_zero
  have hcommon := hdom 0 0 3 hvis
  have hnot :
      ¬ counterexampleWeilForm.toWeilFormSymbols.finitePrimeAtomVisible 3
        (counterexampleAlgebra.legacy.encode commonBump) := by
    have hzero : counterexampleEval.sourceFinitePrimeTerm 3 commonBump = 0 := by
      simpa [counterexampleEval, counterexampleAlgebra] using common_term_three_zero
    simpa [counterexampleWeilForm, counterexampleEval, counterexampleAlgebra,
      SourceWeilFormData.toWeilFormSymbols_finitePrimeAtomVisible,
      SourceFinitePrimeData.sourceAtomVisible, ambientLegacy] using
      (show ¬ counterexampleEval.sourceFinitePrimeTerm 3 commonBump ≠ 0 from
        fun hne => hne hzero)
  exact hnot hcommon

#print axioms not_finitePrimeDominance

end FinitePrimeDominanceNoGo3156
end Dev
end Source
end ConnesWeilRH
