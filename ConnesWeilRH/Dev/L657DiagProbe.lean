import ConnesWeilRH.Dev.ConcreteP1SupportProbe
import ConnesWeilRH.Source.CCM25Concrete.FinitePrimeSourceData
import ConnesWeilRH.Source.CCM25Concrete.PrimePowerArithmeticBridge

/-!
# L657 diagnostic-probe corrected balance.
Builds the on-{2} finite-prime arithmetic data and proves the fixed probe test
fails the drained scoped balance at lambda = 0.  Axiom-clean.
-/

namespace ConnesWeilRH
namespace Source
namespace Dev
namespace L657DiagProbe

open ConnesWeilRH.Source.Dev.ConcreteP1SupportProbe
open ConnesWeilRH.Source.CCM25Concrete
open ConnesWeilRH.Source.CCM25Concrete.FinitePrimeSourceData
open ConnesWeilRH.Source.CCM25Concrete.CommonSourceTest
open ConnesWeilRH.Source.CCM25Concrete.PrimePowerArithmetic
open ConnesWeilRH.Source.AnalyticCore.SourceConcreteBaseLayer
open ConnesWeilRH.Source.AnalyticCore

noncomputable def W0 : WeilFormSymbols :=
  concreteWeilForm.toWeilFormSymbols

noncomputable def E0 : SourceEvaluationData concreteTestAlgebra :=
  concreteEval

noncomputable def f0 : TestFunction := commonBump

noncomputable def common0 : ConcreteCommonSourceTest W0 :=
  concreteCommonSourceTest W0 f0

lemma f0_apply_two : f0 (2 : Real) = 1 := by
  simpa [f0] using commonBump_value_two

lemma f0_apply_inv_two : f0 (2 : Real) ⁻¹ = 0 := by
  unfold f0
  by_contra h
  have hmem : (2 : Real)⁻¹ ∈ Set.Icc (3 / 2 : Real) (5 / 2 : Real) :=
    commonBump_support_subset h
  exact AmbientPrimeProbe.not_mem_Icc_two_inv (n := 2) hmem

lemma valueAt_f0f0_two : E0.valueAt (f0 + f0) (2 : Real) = 2 := by
  rw [SourceEvaluationData.valueAt_eq_norm]
  change ‖(f0 + f0) (2 : Real)‖ = 2
  simp [f0_apply_two]
  norm_num

lemma valueAt_f0f0_inv : E0.valueAt (f0 + f0) (2 : Real)⁻¹ = 0 := by
  rw [SourceEvaluationData.valueAt_eq_norm]
  change ‖(f0 + f0) ((2 : Real)⁻¹)‖ = 0
  simp [f0_apply_inv_two]

lemma term_two_pos : 0 < E0.sourceFinitePrimeTerm 2 (f0 + f0) := by
  rw [SourceEvaluationData.sourceFinitePrimeTerm_eq_valueAt]
  have hval : E0.valueAt (f0 + f0) (2 : Real) = 2 := valueAt_f0f0_two
  have hvali : E0.valueAt (f0 + f0) ((2 : Real)⁻¹) = 0 := valueAt_f0f0_inv
  have hsum : 0 < E0.valueAt (f0 + f0) (2 : Real) + E0.valueAt (f0 + f0) ((2 : Real)⁻¹) := by
    rw [hval, hvali]
    norm_num
  have hLam : 0 < ArithmeticFunction.vonMangoldt 2 := by
    exact Real.log_pos (by norm_num)
  positivity
lemma term_two_ne_zero : E0.sourceFinitePrimeTerm 2 (f0 + f0) ≠ 0 := ne_of_gt term_two_pos

lemma isPrimePow_2 : IsPrimePow 2 := Nat.prime_two.isPrimePow

lemma visible_two : W0.finitePrimeAtomVisible 2 (W0.convolutionStar f0 f0) := by
  unfold W0
  change E0.sourceFinitePrimeTerm 2 (f0 + f0) ≠ 0
  exact term_two_ne_zero

noncomputable def atom2 : SourceFinitePrimeArithmeticData W0 f0 f0 2 :=
  SourceFinitePrimeArithmeticData.ofSourceEvaluationData
    (A := concreteTestAlgebra)
    (E := E0)
    (W := W0)
    (common := common0)
    (n := 2)
    (sourcePrimePowerIndex := isPrimePow_2)
    (visible := visible_two)
    (weightReadOff := by rfl)
    (termReadOff := by rfl)
    (pairingReadOff := by rfl)

lemma globalSetTwo : W0.globalPrimeIndexSet = ({2} : Finset Nat) := by rfl

lemma restrictedSetZero : W0.restrictedPrimeIndexSet 0 = (∅ : Finset Nat) := by
  unfold W0
  simp [concreteWeilForm, perCommonSupport]

noncomputable def gd : SourceGlobalFinitePrimeArithmeticData W0 f0 f0 :=
  { atIndex := by
      intro n hn
      have h2 : n = 2 := by
        rw [globalSetTwo] at hn
        exact Finset.mem_singleton.mp hn
      subst h2
      exact atom2 }

noncomputable def rd : SourceRestrictedFinitePrimeArithmeticData W0 f0 f0 0 :=
  { atIndex := by
      intro n hn
      rw [restrictedSetZero] at hn
      simp at hn }

lemma restrictedSumZero :
    MathlibRestrictedFinitePrimeEvaluatorSumOnIndexSet W0 f0 f0 0 rd = 0 := by
  simp [MathlibRestrictedFinitePrimeEvaluatorSumOnIndexSet,
        MathlibFinitePrimeEvaluatorSumOnIndexSet,
        restrictedSetZero]

lemma archimedeanTerm_zero (F : TestFunction) : W0.archimedeanTerm F = 0 := by
  unfold W0
  rfl

lemma polePairingEqual :
    W0.polePairing f0 = W0.poleFunctional (W0.convolutionStar f0 f0) := by
  unfold W0 f0
  rfl

lemma gd_fwd {h : 2 ∈ W0.globalPrimeIndexSet} :
    (gd.atIndex 2 h).sourcePairing.model.sourceEvaluation.forwardValue
      = E0.valueAt (f0 + f0) 2 := by
  rfl

lemma gd_inv {h : 2 ∈ W0.globalPrimeIndexSet} :
    (gd.atIndex 2 h).sourcePairing.model.sourceEvaluation.inverseValue
      = E0.valueAt (f0 + f0) ((2 : Real)⁻¹) := by
  rfl

lemma gd_sum_two {h : 2 ∈ W0.globalPrimeIndexSet} :
    (gd.atIndex 2 h).sourcePairing.model.sourceEvaluation.forwardValue +
    (gd.atIndex 2 h).sourcePairing.model.sourceEvaluation.inverseValue = 2 := by
  rw [gd_fwd, gd_inv, valueAt_f0f0_two, valueAt_f0f0_inv]
  norm_num

lemma globalSum_positive :
    0 < MathlibGlobalFinitePrimeEvaluatorSumOnIndexSet W0 f0 f0 gd := by
  simp [MathlibGlobalFinitePrimeEvaluatorSumOnIndexSet,
        MathlibFinitePrimeEvaluatorSumOnIndexSet,
        MathlibFinitePrimeEvaluatorAtom,
        globalSetTwo]
  rw [gd_sum_two]
  have hLam : 0 < ArithmeticFunction.vonMangoldt 2 := by
    simpa [ArithmeticFunction.vonMangoldt_apply_prime Nat.prime_two] using
      (Real.log_pos (by norm_num : 1 < (2 : Real)))
  have hProd : 0 < (Real.sqrt (2 : Real))⁻¹ * (2 : Real) := by positivity
  exact mul_pos hLam hProd

theorem probe_balance_false :
    SourceScopedArchimedeanContributionBalance W0 f0 0 gd rd -> False := by
  intro hb
  unfold SourceScopedArchimedeanContributionBalance at hb
  simp only [SourceScopedRestrictedArchimedeanFormula,
             SourceScopedGlobalArchimedeanFormula,
             archimedeanTerm_zero, restrictedSumZero] at hb
  rw [polePairingEqual] at hb
  nlinarith [globalSum_positive]
end L657DiagProbe
end Dev
end Source
end ConnesWeilRH