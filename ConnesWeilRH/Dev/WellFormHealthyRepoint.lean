/-
Re-point transport brick: `valueAt`/`sourceFinitePrimeTerm` agree between the healthy
Mellin source algebra `healthyMellinSourceTestAlgebra` and the concrete additive carrier,
and this transfers the per-common finite-prime support ({2}) and a real, axiom-clean
`SourceWeilFormData` onto the healthy carrier.

RH NOT claimed (finite-S Weil sign stays open).
-/
import ConnesWeilRH.Dev.HealthySourceMellinAlgebra
import ConnesWeilRH.Dev.ConcreteP1SupportProbe

namespace ConnesWeilRH
namespace Source
namespace Dev
namespace WellFormHealthyRepoint

open AnalyticCore
open HealthySourceMellinAlgebra
open ConcreteP1SupportProbe

/-- The healthy-Mellin evaluation data (empty structure). -/
noncomputable def healthyEval :
    AnalyticCore.SourceEvaluationData healthyMellinSourceTestAlgebra :=
  AnalyticCore.SourceEvaluationData.mk

/-- `valueAt` agrees with the concrete carrier (both identity-encode). -/
theorem healthyEval_valueAt_eq_concrete
    (F : TestFunction) (x : ℝ) :
    healthyEval.valueAt F x = ConcreteP1SupportProbe.concreteEval.valueAt F x := by
  rfl

theorem healthyEval_sourceFinitePrimeTerm_eq_concrete
    (n : ℕ) (F : TestFunction) :
    healthyEval.sourceFinitePrimeTerm n F =
      ConcreteP1SupportProbe.concreteEval.sourceFinitePrimeTerm n F := by
  unfold AnalyticCore.SourceEvaluationData.sourceFinitePrimeTerm
  rw [healthyEval_valueAt_eq_concrete, healthyEval_valueAt_eq_concrete]

/-- If the healthy-carrier bump term is non-zero at `n`, then `n = 2` (the
`valueAt`-only definition transfers from the concrete carrier). -/
theorem healthyForward_mem (n : ℕ)
    (hn : healthyEval.sourceFinitePrimeTerm n commonBump ≠ 0) :
    n = 2 := by
  have hnc : ConcreteP1SupportProbe.concreteEval.sourceFinitePrimeTerm n commonBump ≠ 0 := by
    rwa [healthyEval_sourceFinitePrimeTerm_eq_concrete] at hn
  exact ConcreteP1SupportProbe.forward_mem n hnc

/-- The healthy-carrier source-finite-prime term at `2` is strictly positive. -/
theorem healthyTerm_two_pos :
    0 < healthyEval.sourceFinitePrimeTerm 2 commonBump := by
  rw [healthyEval_sourceFinitePrimeTerm_eq_concrete]
  exact ConcreteP1SupportProbe.term_two_pos

/-- The healthy-carrier source-finite-prime term at `2` is non-zero. -/
theorem healthyTerm_two_ne_zero :
    healthyEval.sourceFinitePrimeTerm 2 commonBump ≠ 0 :=
  ne_of_gt healthyTerm_two_pos

/-- The healthy-carrier per-common finite-prime support: exact index set
`{2}`, prime `2` visible.  Structurally mirrors the concrete support but
is stated for the healthy Mellin algebra. -/
noncomputable def healthyPerCommonSupport :
    AnalyticCore.PerCommonSourceFinitePrimeSupport
      healthyMellinSourceTestAlgebra healthyEval commonBump :=
{ globalIndexSet := ({2} : Finset ℕ)
  restrictedIndexSet := fun lambda : ℝ =>
    if 2 ≤ lambda ^ 2 then ({2} : Finset ℕ) else ∅
  sourceVisibleGlobalIndex := by
    intro n hn
    rw [healthyForward_mem n hn]
    simp
  sourceVisibleRestrictedIndex := by
    intro lambda n hn hOne hle
    have hn2 : n = 2 := healthyForward_mem n hn
    subst hn2
    rw [if_pos]
    · simp
    · simpa using hle
  commonGlobalIndex := by
    intro n hn
    simp at hn
    rw [hn]
    exact healthyTerm_two_ne_zero
  commonRestrictedIndex := by
    intro lambda n hn
    by_cases hcut : 2 ≤ lambda ^ 2
    · simp [hcut] at hn
      have hn2 : n = 2 := by simpa using hn
      rw [hn2]
      exact ⟨healthyTerm_two_ne_zero, by norm_num, hcut⟩
    · simp [hcut] at hn }

/-- The healthy-carrier per-common support is realizable. -/
theorem healthyPerCommon_nonempty :
    Nonempty (AnalyticCore.PerCommonSourceFinitePrimeSupport
      healthyMellinSourceTestAlgebra healthyEval commonBump) :=
  ⟨healthyPerCommonSupport⟩

/-- A real, axiom-clean `SourceWeilFormData` on the healthy Mellin carrier —
the healthy analog of the L137-axiom substitute. -/
noncomputable def healthyWeilForm :
    SourceWeilFormData healthyMellinSourceTestAlgebra :=
  { evaluation := healthyEval
    common := commonBump
    finitePrime := { support := healthyPerCommonSupport }
    archimedeanTerm := fun _ => 0 }

theorem healthyWeilForm_nonempty :
    Nonempty (SourceWeilFormData healthyMellinSourceTestAlgebra) :=
  ⟨healthyWeilForm⟩

#print axioms healthyWeilForm

end WellFormHealthyRepoint
end Dev
end Source
end ConnesWeilRH