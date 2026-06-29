/-
Copyright (c) 2026 ConnesWeilRH contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ConnesWeilRH contributors
-/

import ConnesWeilRH.Basic
import ConnesWeilRH.Source.CCM25Concrete.PrimePowerEvaluation
import Mathlib.Data.Real.Sqrt

/-!
# CCM25 source prime-power pairing boundary

This module names the source pairing `<g | T(n) g>` before it is multiplied by
`Lambda(n)`.  The current phase-1 boundary has `TestFunction := Type`, so this
file does not pretend to evaluate a test function at `n` or `n⁻¹`.  Instead it
records the source forward/inverse evaluations, the `n^(-1/2)` normalizing
factor, and the read-off of the route pairing into that source expression.
-/

namespace ConnesWeilRH
namespace Source
namespace CCM25Concrete
namespace PrimePowerPairing

noncomputable def SourceNormalizationFactor (n : ℕ) : ℝ :=
  1 / Real.sqrt (n : ℝ)

theorem source_normalization_factor_eq_inv_sqrt
    {n : ℕ} :
    SourceNormalizationFactor n = 1 / Real.sqrt (n : ℝ) :=
  rfl

structure SourcePrimePowerPairingModel
    (W : WeilFormSymbols) (f g : TestFunction) (n : ℕ) where
  convolutionSquare : TestFunction := W.convolutionStar f g
  sourceEvaluation :
    PrimePowerEvaluation.SourceConvolutionEvaluationModel W f g n
  sourceForwardEvaluation : ℝ
  forwardEvaluationReadOff :
    sourceForwardEvaluation = sourceEvaluation.forwardValue
  sourceInverseEvaluation : ℝ
  inverseEvaluationReadOff :
    sourceInverseEvaluation = sourceEvaluation.inverseValue
  sourceNormalizationFactor : ℝ
  normalizationFactorReadOff :
    sourceNormalizationFactor = SourceNormalizationFactor n
  sourceTPairing : ℝ
  tPairingFormula :
    sourceTPairing =
      sourceNormalizationFactor *
        (sourceForwardEvaluation + sourceInverseEvaluation)

structure SourcePrimePowerPairingData
    (W : WeilFormSymbols) (f g : TestFunction) (n : ℕ) where
  model : SourcePrimePowerPairingModel W f g n
  pairingReadOff :
    W.primePowerPairing n f g = model.sourceTPairing

/--
Goal 0C concrete-common pairing data.

The underlying pairing model is still the existing source pairing model, but
its evaluation leg is required to be the concrete-common evaluation attached to
the same `ConcreteCommonSourceTest`.
-/
structure ConcreteCommonPrimePowerPairingData
    (W : WeilFormSymbols)
    (common : CommonSourceTest.ConcreteCommonSourceTest W) (n : ℕ) where
  concreteEvaluation :
    PrimePowerEvaluation.ConcreteCommonPrimePowerEvaluation W common n
  model : SourcePrimePowerPairingModel W common.sourceTest common.sourceTest n
  modelEvaluationReadOff :
    model.sourceEvaluation = concreteEvaluation.model
  pairingReadOff :
    W.primePowerPairing n common.sourceTest common.sourceTest =
      model.sourceTPairing

namespace ConcreteCommonPrimePowerPairingData

def toSourcePrimePowerPairingData
    {W : WeilFormSymbols}
    {common : CommonSourceTest.ConcreteCommonSourceTest W} {n : ℕ}
    (h : ConcreteCommonPrimePowerPairingData W common n) :
    SourcePrimePowerPairingData W common.sourceTest common.sourceTest n where
  model := h.model
  pairingReadOff := h.pairingReadOff

theorem source_evaluation_eq_concrete
    {W : WeilFormSymbols}
    {common : CommonSourceTest.ConcreteCommonSourceTest W} {n : ℕ}
    (h : ConcreteCommonPrimePowerPairingData W common n) :
    h.model.sourceEvaluation = h.concreteEvaluation.model :=
  h.modelEvaluationReadOff

theorem source_evaluator_test_eq_common
    {W : WeilFormSymbols}
    {common : CommonSourceTest.ConcreteCommonSourceTest W} {n : ℕ}
    (h : ConcreteCommonPrimePowerPairingData W common n) :
    h.model.sourceEvaluation.sourceEvaluator.sourceTest =
      common.toSourceTestEvaluationInterface := by
  rw [h.modelEvaluationReadOff]
  exact h.concreteEvaluation.model_evaluator_test_read_off

theorem source_evaluation_square_eq_common_square
    {W : WeilFormSymbols}
    {common : CommonSourceTest.ConcreteCommonSourceTest W} {n : ℕ}
    (h : ConcreteCommonPrimePowerPairingData W common n) :
    h.model.sourceEvaluation.sourceConvolutionSquare =
      common.sourceConvolutionSquare := by
  rw [h.modelEvaluationReadOff]
  exact h.concreteEvaluation.source_convolution_square_eq_common_square

theorem source_forward_value_at_concrete_square
    {W : WeilFormSymbols}
    {common : CommonSourceTest.ConcreteCommonSourceTest W} {n : ℕ}
    (h : ConcreteCommonPrimePowerPairingData W common n) :
    h.model.sourceEvaluation.forwardValue =
      h.concreteEvaluation.sourceEvaluator.valueAt
        common.sourceConvolutionSquare (n : ℝ) := by
  rw [h.modelEvaluationReadOff]
  exact h.concreteEvaluation.forward_value_at_concrete_square

theorem source_inverse_value_at_concrete_square
    {W : WeilFormSymbols}
    {common : CommonSourceTest.ConcreteCommonSourceTest W} {n : ℕ}
    (h : ConcreteCommonPrimePowerPairingData W common n) :
    h.model.sourceEvaluation.inverseValue =
      h.concreteEvaluation.sourceEvaluator.valueAt
        common.sourceConvolutionSquare ((n : ℝ)⁻¹) := by
  rw [h.modelEvaluationReadOff]
  exact h.concreteEvaluation.inverse_value_at_concrete_square

end ConcreteCommonPrimePowerPairingData

theorem source_t_pairing_formula
    {W : WeilFormSymbols} {f g : TestFunction} {n : ℕ}
    (h : SourcePrimePowerPairingData W f g n) :
    h.model.sourceTPairing =
      h.model.sourceNormalizationFactor *
        (h.model.sourceForwardEvaluation +
          h.model.sourceInverseEvaluation) :=
  h.model.tPairingFormula

theorem source_normalization_factor_read_off
    {W : WeilFormSymbols} {f g : TestFunction} {n : ℕ}
    (h : SourcePrimePowerPairingData W f g n) :
    h.model.sourceNormalizationFactor = SourceNormalizationFactor n :=
  h.model.normalizationFactorReadOff

theorem source_forward_evaluation_read_off
    {W : WeilFormSymbols} {f g : TestFunction} {n : ℕ}
    (h : SourcePrimePowerPairingData W f g n) :
    h.model.sourceForwardEvaluation =
      h.model.sourceEvaluation.forwardValue :=
  h.model.forwardEvaluationReadOff

theorem source_inverse_evaluation_read_off
    {W : WeilFormSymbols} {f g : TestFunction} {n : ℕ}
    (h : SourcePrimePowerPairingData W f g n) :
    h.model.sourceInverseEvaluation =
      h.model.sourceEvaluation.inverseValue :=
  h.model.inverseEvaluationReadOff

theorem source_prime_power_pairing_read_off
    {W : WeilFormSymbols} {f g : TestFunction} {n : ℕ}
    (h : SourcePrimePowerPairingData W f g n) :
    W.primePowerPairing n f g = h.model.sourceTPairing :=
  h.pairingReadOff

theorem source_prime_power_pairing_formula
    {W : WeilFormSymbols} {f g : TestFunction} {n : ℕ}
    (h : SourcePrimePowerPairingData W f g n) :
    W.primePowerPairing n f g =
      h.model.sourceNormalizationFactor *
        (h.model.sourceForwardEvaluation +
          h.model.sourceInverseEvaluation) := by
  rw [h.pairingReadOff, h.model.tPairingFormula]

theorem source_prime_power_pairing_formula_inv_sqrt
    {W : WeilFormSymbols} {f g : TestFunction} {n : ℕ}
    (h : SourcePrimePowerPairingData W f g n) :
    W.primePowerPairing n f g =
      SourceNormalizationFactor n *
        (h.model.sourceForwardEvaluation +
          h.model.sourceInverseEvaluation) := by
  rw [source_prime_power_pairing_formula h,
    h.model.normalizationFactorReadOff]

theorem source_prime_power_pairing_formula_real_sqrt
    {W : WeilFormSymbols} {f g : TestFunction} {n : ℕ}
    (h : SourcePrimePowerPairingData W f g n) :
    W.primePowerPairing n f g =
      (1 / Real.sqrt (n : ℝ)) *
        (h.model.sourceForwardEvaluation +
          h.model.sourceInverseEvaluation) := by
  rw [source_prime_power_pairing_formula_inv_sqrt h,
    source_normalization_factor_eq_inv_sqrt]

theorem source_prime_power_pairing_formula_source_evaluations
    {W : WeilFormSymbols} {f g : TestFunction} {n : ℕ}
    (h : SourcePrimePowerPairingData W f g n) :
    W.primePowerPairing n f g =
      (1 / Real.sqrt (n : ℝ)) *
        (h.model.sourceEvaluation.forwardValue +
          h.model.sourceEvaluation.inverseValue) := by
  rw [source_prime_power_pairing_formula_real_sqrt h,
    h.model.forwardEvaluationReadOff,
    h.model.inverseEvaluationReadOff]

theorem source_prime_power_pairing_formula_source_evaluator
    {W : WeilFormSymbols} {f g : TestFunction} {n : ℕ}
    (h : SourcePrimePowerPairingData W f g n) :
    W.primePowerPairing n f g =
      (1 / Real.sqrt (n : ℝ)) *
        (h.model.sourceEvaluation.sourceEvaluator.valueAt
            (W.convolutionStar f g) (n : ℝ) +
          h.model.sourceEvaluation.sourceEvaluator.valueAt
            (W.convolutionStar f g) ((n : ℝ)⁻¹)) := by
  rw [source_prime_power_pairing_formula_source_evaluations h,
    PrimePowerEvaluation.source_forward_value_at_source_points
      h.model.sourceEvaluation,
    PrimePowerEvaluation.source_inverse_value_at_source_points
      h.model.sourceEvaluation]

theorem concrete_common_prime_power_pairing_formula_source_evaluator
    {W : WeilFormSymbols}
    {common : CommonSourceTest.ConcreteCommonSourceTest W} {n : ℕ}
    (h : ConcreteCommonPrimePowerPairingData W common n) :
    W.primePowerPairing n common.sourceTest common.sourceTest =
      (1 / Real.sqrt (n : ℝ)) *
        (h.concreteEvaluation.sourceEvaluator.valueAt
            common.sourceConvolutionSquare (n : ℝ) +
          h.concreteEvaluation.sourceEvaluator.valueAt
            common.sourceConvolutionSquare ((n : ℝ)⁻¹)) := by
  rw [source_prime_power_pairing_formula_source_evaluations
      h.toSourcePrimePowerPairingData]
  change
    (1 / Real.sqrt (n : ℝ)) *
        (h.model.sourceEvaluation.forwardValue +
          h.model.sourceEvaluation.inverseValue) =
      (1 / Real.sqrt (n : ℝ)) *
        (h.concreteEvaluation.sourceEvaluator.valueAt
            common.sourceConvolutionSquare (n : ℝ) +
          h.concreteEvaluation.sourceEvaluator.valueAt
            common.sourceConvolutionSquare ((n : ℝ)⁻¹))
  rw [h.source_forward_value_at_concrete_square,
    h.source_inverse_value_at_concrete_square]

end PrimePowerPairing
end CCM25Concrete
end Source
end ConnesWeilRH
