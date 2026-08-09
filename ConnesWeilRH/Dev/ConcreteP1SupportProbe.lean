import ConnesWeilRH.Source.AnalyticCore
import ConnesWeilRH.Source.AnalyticCoreBase
import ConnesWeilRH.Dev.AmbientPrimeVisibleProbe
import Mathlib.Analysis.Fourier.Convolution

/-!
# S1 (source-model refactor) — concrete-carrier per-common prime-2 support

The false L137 axiom (`normalizedCoreSourceWeilFormDataRoot`) asserts
`SourceWeilFormData concreteTestAlgebra` exists.  After the S2 per-common
refactor, the correct object is constructible: a `PerCommonSourceFinitePrimeSupport`
on the CONCRETE carrier with exact index `{2}`, witnessed by a compact-support
smooth bump whose prime-`2` finite-prime term is strictly positive.  This lifts
to a real, axiom-clean `SourceWeilFormData concreteTestAlgebra` — the exact
substitute for that axiom.  No `axiom`, no `sorry`; only the library trio.

No RH claim.
-/

namespace ConnesWeilRH
namespace Source
namespace Dev
namespace ConcreteP1SupportProbe

open AnalyticCore
open AnalyticCore.SourceConcreteBaseLayer
open scoped FourierTransform

/-- Evaluation data on the concrete skeleton carrier. -/
noncomputable def concreteEval : AnalyticCore.SourceEvaluationData concreteTestAlgebra :=
  AnalyticCore.SourceEvaluationData.mk

/-- A compact-support smooth bump, value `1` at `t = 2`, supported in `Icc (3/2) (5/2)`.
   Reused from the ambient probe (same `TestFunction` carrier). -/
noncomputable def commonBump : TestFunction :=
  AmbientPrimeProbe.commonBump

lemma commonBump_support_subset :
    Function.support (fun t : ℝ => commonBump t) ⊆
      Set.Icc (3 / 2 : ℝ) (5 / 2 : ℝ) :=
  AmbientPrimeProbe.commonBump_support_subset

lemma commonBump_value_two : commonBump (2 : ℝ) = 1 :=
  AmbientPrimeProbe.commonBump_value_two

/-- `valueAt` of the common bump at `2` is exactly `1` (concrete carrier). -/
lemma concrete_valueAt_two : concreteEval.valueAt commonBump (2 : ℝ) = 1 := by
  rw [AnalyticCore.SourceEvaluationData.valueAt_eq_norm]
  have henc : concreteTestAlgebra.legacy.encode commonBump (2 : ℝ) = 1 := by
    simp [concreteTestAlgebra, concreteLegacyTestEquiv, commonBump_value_two]
  rw [henc]
  norm_num

lemma concrete_valueAt_two_pos : 0 < concreteEval.valueAt commonBump (2 : ℝ) := by
  rw [concrete_valueAt_two]
  norm_num

/-- The finite-prime term at `2` is strictly positive on the concrete carrier. -/
lemma term_two_pos : 0 < concreteEval.sourceFinitePrimeTerm 2 commonBump := by
  have hvalInv : 0 ≤ concreteEval.valueAt commonBump ((2 : ℝ)⁻¹) := by
    rw [AnalyticCore.SourceEvaluationData.valueAt_eq_norm]
    exact norm_nonneg _
  have hsum : 0 < concreteEval.valueAt commonBump (2 : ℝ) +
      concreteEval.valueAt commonBump ((2 : ℝ)⁻¹) := by
    exact lt_of_lt_of_le concrete_valueAt_two_pos (le_add_of_nonneg_right hvalInv)
  have hLam : 0 < ArithmeticFunction.vonMangoldt 2 := by
    rw [ArithmeticFunction.vonMangoldt_apply_prime Nat.prime_two]
    exact Real.log_pos (by norm_num)
  have hsqrt : 0 < Real.sqrt (2 : ℝ) := by
    exact Real.sqrt_pos.mpr (by norm_num)
  have hsc : 0 < (1 / Real.sqrt (2 : ℝ) : ℝ) := by
    exact div_pos zero_lt_one hsqrt
  rw [AnalyticCore.SourceEvaluationData.sourceFinitePrimeTerm_eq_valueAt]
  exact mul_pos hLam (mul_pos hsc hsum)

lemma term_two_ne_zero : concreteEval.sourceFinitePrimeTerm 2 commonBump ≠ 0 :=
  ne_of_gt term_two_pos

/-- If the bump encoded value is non-zero at `n`, then `n = 2`. -/
theorem forward_mem (n : ℕ)
    (hn : concreteEval.sourceFinitePrimeTerm n commonBump ≠ 0) :
    n = 2 := by
  have hcoef : ((1 / Real.sqrt (n : ℝ)) *
      (concreteEval.valueAt commonBump (n : ℝ) +
        concreteEval.valueAt commonBump ((n : ℝ)⁻¹))) ≠ 0 := by
    intro hzero
    have ht : concreteEval.sourceFinitePrimeTerm n commonBump = 0 := by
      rw [AnalyticCore.SourceEvaluationData.sourceFinitePrimeTerm_eq_valueAt, hzero]
      norm_num
    exact hn ht
  have hsum : concreteEval.valueAt commonBump (n : ℝ) +
      concreteEval.valueAt commonBump ((n : ℝ)⁻¹) ≠ 0 := by
    intro hs
    apply hcoef
    rw [hs]
    norm_num
  have hdisc : concreteEval.valueAt commonBump (n : ℝ) ≠ 0 ∨
      concreteEval.valueAt commonBump ((n : ℝ)⁻¹) ≠ 0 := by
    by_contra hne
    push_neg at hne
    exact hsum (by
      have hz1 : concreteEval.valueAt commonBump (n : ℝ) = 0 := hne.1
      have hz2 : concreteEval.valueAt commonBump ((n : ℝ)⁻¹) = 0 := hne.2
      rw [hz1, hz2]
      norm_num)
  rcases hdisc with h1 | h2
  · have hcne : commonBump (n : ℝ) ≠ 0 := by
      intro hc
      exact h1 (by
        rw [AnalyticCore.SourceEvaluationData.valueAt_eq_norm]
        simp [concreteTestAlgebra, concreteLegacyTestEquiv, hc])
    have hmem : (n : ℝ) ∈ Set.Icc (3 / 2 : ℝ) (5 / 2 : ℝ) :=
      commonBump_support_subset hcne
    exact AmbientPrimeProbe.two_of_mem_Icc_two hmem
  · have hc2 : commonBump ((n : ℝ)⁻¹) ≠ 0 := by
      intro hc
      exact h2 (by
      rw [AnalyticCore.SourceEvaluationData.valueAt_eq_norm]
      simp [concreteTestAlgebra, concreteLegacyTestEquiv, hc])
    have hmem : ((n : ℝ)⁻¹ : ℝ) ∈ Set.Icc (3 / 2 : ℝ) (5 / 2 : ℝ) :=
      commonBump_support_subset hc2
    exact False.elim (AmbientPrimeProbe.not_mem_Icc_two_inv hmem)

/-- The concrete-carrier per-common support: exact index set `{2}`, prime `2`
visible. -/
noncomputable def perCommonSupport :
    AnalyticCore.PerCommonSourceFinitePrimeSupport concreteTestAlgebra
      concreteEval commonBump :=
{ globalIndexSet := ({2} : Finset ℕ)
  restrictedIndexSet := fun lambda : ℝ =>
    if 2 ≤ lambda ^ 2 then ({2} : Finset ℕ) else ∅
  sourceVisibleGlobalIndex := by
    intro n hn
    rw [forward_mem n hn]
    simp
  sourceVisibleRestrictedIndex := by
    intro lambda n hn hOne hle
    have hn2 : n = 2 := forward_mem n hn
    subst hn2
    rw [if_pos]
    · simp
    · simpa using hle
  commonGlobalIndex := by
    intro n hn
    simp at hn
    rw [hn]
    exact term_two_ne_zero
  commonRestrictedIndex := by
    intro lambda n hn
    by_cases hcut : 2 ≤ lambda ^ 2
    · simp [hcut] at hn
      have hn2 : n = 2 := by simpa using hn
      rw [hn2]
      exact ⟨term_two_ne_zero, by norm_num, hcut⟩
    · simp [hcut] at hn }

/-- The concrete per-common support is realizable (non-degenerate). -/
theorem perCommon_nonempty :
    Nonempty (AnalyticCore.PerCommonSourceFinitePrimeSupport concreteTestAlgebra
      concreteEval commonBump) :=
  ⟨perCommonSupport⟩

/-- Lift to a real, axiom-clean `SourceWeilFormData concreteTestAlgebra` — the
L137-axiom substitute. -/
noncomputable def concreteWeilForm : SourceWeilFormData concreteTestAlgebra :=
{ evaluation := concreteEval
  common := commonBump
  finitePrime := { support := perCommonSupport }
  archimedeanTerm := fun _ => 0 }

theorem concreteWeilForm_nonempty :
    Nonempty (SourceWeilFormData concreteTestAlgebra) :=
  ⟨concreteWeilForm⟩

#print axioms concreteWeilForm

end ConcreteP1SupportProbe
end Dev
end Source
end ConnesWeilRH

