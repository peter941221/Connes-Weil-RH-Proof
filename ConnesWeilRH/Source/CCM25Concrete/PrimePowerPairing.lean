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
`Lambda(n)`.  The route-level `TestFunction` is Mathlib's Schwartz space on
`ℝ` with complex values, but this file still records the source forward/inverse
evaluations, the `n^(-1/2)` normalizing factor, and the read-off of the route
pairing into that source expression until the finite-prime row is proved from
pointwise Schwartz evaluation.
-/

namespace ConnesWeilRH
namespace Source
namespace CCM25Concrete
namespace PrimePowerPairing

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
  sourceTPairing : ℝ
  tPairingFormula :
    sourceTPairing =
      (1 / Real.sqrt (n : ℝ)) *
        (sourceForwardEvaluation + sourceInverseEvaluation)

structure SourcePrimePowerPairingData
    (W : WeilFormSymbols) (f g : TestFunction) (n : ℕ) where
  model : SourcePrimePowerPairingModel W f g n
  pairingReadOff :
    W.primePowerPairing n f g = model.sourceTPairing

namespace SourcePrimePowerPairingModel

theorem forward_evaluation_eq_source_forward_value
    {W : WeilFormSymbols} {f g : TestFunction} {n : ℕ}
    (h : SourcePrimePowerPairingModel W f g n) :
    h.sourceForwardEvaluation = h.sourceEvaluation.forwardValue :=
  h.forwardEvaluationReadOff

theorem inverse_evaluation_eq_source_inverse_value
    {W : WeilFormSymbols} {f g : TestFunction} {n : ℕ}
    (h : SourcePrimePowerPairingModel W f g n) :
    h.sourceInverseEvaluation = h.sourceEvaluation.inverseValue :=
  h.inverseEvaluationReadOff

theorem source_t_pairing_formula_source_evaluations
    {W : WeilFormSymbols} {f g : TestFunction} {n : ℕ}
    (h : SourcePrimePowerPairingModel W f g n) :
    h.sourceTPairing =
      (1 / Real.sqrt (n : ℝ)) *
        (h.sourceEvaluation.forwardValue +
          h.sourceEvaluation.inverseValue) := by
  rw [h.tPairingFormula, h.forwardEvaluationReadOff,
    h.inverseEvaluationReadOff]

theorem source_t_pairing_formula_source_normalization
    {W : WeilFormSymbols} {f g : TestFunction} {n : ℕ}
    (h : SourcePrimePowerPairingModel W f g n) :
    h.sourceTPairing =
      (1 / Real.sqrt (n : ℝ)) *
        (h.sourceEvaluation.forwardValue +
          h.sourceEvaluation.inverseValue) :=
  source_t_pairing_formula_source_evaluations h

theorem source_t_pairing_formula_real_sqrt
    {W : WeilFormSymbols} {f g : TestFunction} {n : ℕ}
    (h : SourcePrimePowerPairingModel W f g n) :
    h.sourceTPairing =
      (1 / Real.sqrt (n : ℝ)) *
        (h.sourceEvaluation.forwardValue +
          h.sourceEvaluation.inverseValue) :=
  source_t_pairing_formula_source_normalization h

theorem source_t_pairing_formula_source_evaluator
    {W : WeilFormSymbols} {f g : TestFunction} {n : ℕ}
    (h : SourcePrimePowerPairingModel W f g n) :
    h.sourceTPairing =
      (1 / Real.sqrt (n : ℝ)) *
        (h.sourceEvaluation.sourceEvaluator.valueAt
            (W.convolutionStar f g) (n : ℝ) +
          h.sourceEvaluation.sourceEvaluator.valueAt
            (W.convolutionStar f g) ((n : ℝ)⁻¹)) := by
  rw [source_t_pairing_formula_real_sqrt h,
    PrimePowerEvaluation.source_forward_value_at_source_points
      h.sourceEvaluation,
    PrimePowerEvaluation.source_inverse_value_at_source_points
      h.sourceEvaluation]

theorem source_t_pairing_formula_source_evaluator_source_points
    {W : WeilFormSymbols} {f g : TestFunction} {n : ℕ}
    (h : SourcePrimePowerPairingModel W f g n) :
    h.sourceTPairing =
      (1 / Real.sqrt (n : ℝ)) *
        (h.sourceEvaluation.sourceEvaluator.valueAt
            (W.convolutionStar f g)
            (PrimePowerEvaluation.SourceForwardPoint n) +
          h.sourceEvaluation.sourceEvaluator.valueAt
            (W.convolutionStar f g)
            (PrimePowerEvaluation.SourceInversePoint n)) := by
  rw [source_t_pairing_formula_real_sqrt h,
    PrimePowerEvaluation.source_forward_value_at_route_square_source_point
      h.sourceEvaluation,
    PrimePowerEvaluation.source_inverse_value_at_route_square_source_point
      h.sourceEvaluation]

theorem source_t_pairing_formula_model_square
    {W : WeilFormSymbols} {f g : TestFunction} {n : ℕ}
    (h : SourcePrimePowerPairingModel W f g n) :
    h.sourceTPairing =
      (1 / Real.sqrt (n : ℝ)) *
        (h.sourceEvaluation.sourceEvaluator.valueAt
            h.sourceEvaluation.sourceConvolutionSquare (n : ℝ) +
          h.sourceEvaluation.sourceEvaluator.valueAt
            h.sourceEvaluation.sourceConvolutionSquare ((n : ℝ)⁻¹)) := by
  rw [source_t_pairing_formula_real_sqrt h,
    PrimePowerEvaluation.source_forward_value_at_model_square_nat_cast
      h.sourceEvaluation,
    PrimePowerEvaluation.source_inverse_value_at_model_square_inv_nat_cast
      h.sourceEvaluation]

theorem source_t_pairing_formula_model_square_source_points
    {W : WeilFormSymbols} {f g : TestFunction} {n : ℕ}
    (h : SourcePrimePowerPairingModel W f g n) :
    h.sourceTPairing =
      (1 / Real.sqrt (n : ℝ)) *
        (h.sourceEvaluation.sourceEvaluator.valueAt
            h.sourceEvaluation.sourceConvolutionSquare
            (PrimePowerEvaluation.SourceForwardPoint n) +
          h.sourceEvaluation.sourceEvaluator.valueAt
            h.sourceEvaluation.sourceConvolutionSquare
            (PrimePowerEvaluation.SourceInversePoint n)) := by
  rw [source_t_pairing_formula_real_sqrt h,
    PrimePowerEvaluation.source_forward_value_at_model_square_source_point
      h.sourceEvaluation,
    PrimePowerEvaluation.source_inverse_value_at_model_square_source_point
      h.sourceEvaluation]

end SourcePrimePowerPairingModel

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

theorem concrete_evaluation_eq_source_evaluation
    {W : WeilFormSymbols}
    {common : CommonSourceTest.ConcreteCommonSourceTest W} {n : ℕ}
    (h : ConcreteCommonPrimePowerPairingData W common n) :
    h.concreteEvaluation.model = h.model.sourceEvaluation :=
  h.modelEvaluationReadOff.symm

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

theorem source_evaluation_source_evaluator_eq_concrete
    {W : WeilFormSymbols}
    {common : CommonSourceTest.ConcreteCommonSourceTest W} {n : ℕ}
    (h : ConcreteCommonPrimePowerPairingData W common n) :
    h.model.sourceEvaluation.sourceEvaluator =
      h.concreteEvaluation.sourceEvaluator := by
  rw [h.modelEvaluationReadOff]
  exact h.concreteEvaluation.modelEvaluatorReadOff

theorem source_evaluation_source_test_eq_common
    {W : WeilFormSymbols}
    {common : CommonSourceTest.ConcreteCommonSourceTest W} {n : ℕ}
    (h : ConcreteCommonPrimePowerPairingData W common n) :
    h.model.sourceEvaluation.sourceTest =
      common.toSourceTestEvaluationInterface := by
  rw [h.modelEvaluationReadOff]
  exact h.concreteEvaluation.source_test_read_off

theorem common_source_test_eq_source_evaluation_source_test
    {W : WeilFormSymbols}
    {common : CommonSourceTest.ConcreteCommonSourceTest W} {n : ℕ}
    (h : ConcreteCommonPrimePowerPairingData W common n) :
    common.toSourceTestEvaluationInterface =
      h.model.sourceEvaluation.sourceTest :=
  (source_evaluation_source_test_eq_common h).symm

theorem source_forward_point_eq_source_point
    {W : WeilFormSymbols}
    {common : CommonSourceTest.ConcreteCommonSourceTest W} {n : ℕ}
    (h : ConcreteCommonPrimePowerPairingData W common n) :
    h.model.sourceEvaluation.forwardPoint =
      PrimePowerEvaluation.SourceForwardPoint n := by
  rw [h.modelEvaluationReadOff]
  exact h.concreteEvaluation.forward_point_eq_source_point

theorem source_inverse_point_eq_source_point
    {W : WeilFormSymbols}
    {common : CommonSourceTest.ConcreteCommonSourceTest W} {n : ℕ}
    (h : ConcreteCommonPrimePowerPairingData W common n) :
    h.model.sourceEvaluation.inversePoint =
      PrimePowerEvaluation.SourceInversePoint n := by
  rw [h.modelEvaluationReadOff]
  exact h.concreteEvaluation.inverse_point_eq_source_point

theorem source_forward_point_eq_nat_cast
    {W : WeilFormSymbols}
    {common : CommonSourceTest.ConcreteCommonSourceTest W} {n : ℕ}
    (h : ConcreteCommonPrimePowerPairingData W common n) :
    h.model.sourceEvaluation.forwardPoint = (n : ℝ) :=
  PrimePowerEvaluation.source_forward_point_read_off h.model.sourceEvaluation

theorem source_inverse_point_eq_inv_nat_cast
    {W : WeilFormSymbols}
    {common : CommonSourceTest.ConcreteCommonSourceTest W} {n : ℕ}
    (h : ConcreteCommonPrimePowerPairingData W common n) :
    h.model.sourceEvaluation.inversePoint = (n : ℝ)⁻¹ :=
  PrimePowerEvaluation.source_inverse_point_read_off h.model.sourceEvaluation

theorem source_forward_value_eq_concrete_model_forward_value
    {W : WeilFormSymbols}
    {common : CommonSourceTest.ConcreteCommonSourceTest W} {n : ℕ}
    (h : ConcreteCommonPrimePowerPairingData W common n) :
    h.model.sourceEvaluation.forwardValue =
      h.concreteEvaluation.model.forwardValue := by
  rw [h.modelEvaluationReadOff]

theorem source_inverse_value_eq_concrete_model_inverse_value
    {W : WeilFormSymbols}
    {common : CommonSourceTest.ConcreteCommonSourceTest W} {n : ℕ}
    (h : ConcreteCommonPrimePowerPairingData W common n) :
    h.model.sourceEvaluation.inverseValue =
      h.concreteEvaluation.model.inverseValue := by
  rw [h.modelEvaluationReadOff]

theorem source_forward_evaluation_eq_concrete_model_forward_value
    {W : WeilFormSymbols}
    {common : CommonSourceTest.ConcreteCommonSourceTest W} {n : ℕ}
    (h : ConcreteCommonPrimePowerPairingData W common n) :
    h.model.sourceForwardEvaluation =
      h.concreteEvaluation.model.forwardValue := by
  rw [h.model.forwardEvaluationReadOff,
    h.source_forward_value_eq_concrete_model_forward_value]

theorem source_inverse_evaluation_eq_concrete_model_inverse_value
    {W : WeilFormSymbols}
    {common : CommonSourceTest.ConcreteCommonSourceTest W} {n : ℕ}
    (h : ConcreteCommonPrimePowerPairingData W common n) :
    h.model.sourceInverseEvaluation =
      h.concreteEvaluation.model.inverseValue := by
  rw [h.model.inverseEvaluationReadOff,
    h.source_inverse_value_eq_concrete_model_inverse_value]

theorem source_t_pairing_formula_concrete_model_evaluations
    {W : WeilFormSymbols}
    {common : CommonSourceTest.ConcreteCommonSourceTest W} {n : ℕ}
    (h : ConcreteCommonPrimePowerPairingData W common n) :
    h.model.sourceTPairing =
      (1 / Real.sqrt (n : ℝ)) *
        (h.concreteEvaluation.model.forwardValue +
          h.concreteEvaluation.model.inverseValue) := by
  rw [h.model.tPairingFormula,
    h.source_forward_evaluation_eq_concrete_model_forward_value,
    h.source_inverse_evaluation_eq_concrete_model_inverse_value]

theorem source_t_pairing_formula_source_normalization_concrete_model_evaluations
    {W : WeilFormSymbols}
    {common : CommonSourceTest.ConcreteCommonSourceTest W} {n : ℕ}
    (h : ConcreteCommonPrimePowerPairingData W common n) :
    h.model.sourceTPairing =
      (1 / Real.sqrt (n : ℝ)) *
        (h.concreteEvaluation.model.forwardValue +
          h.concreteEvaluation.model.inverseValue) :=
  h.source_t_pairing_formula_concrete_model_evaluations

theorem source_t_pairing_formula_real_sqrt_concrete_model_evaluations
    {W : WeilFormSymbols}
    {common : CommonSourceTest.ConcreteCommonSourceTest W} {n : ℕ}
    (h : ConcreteCommonPrimePowerPairingData W common n) :
    h.model.sourceTPairing =
      (1 / Real.sqrt (n : ℝ)) *
        (h.concreteEvaluation.model.forwardValue +
          h.concreteEvaluation.model.inverseValue) :=
  h.source_t_pairing_formula_source_normalization_concrete_model_evaluations

theorem source_t_pairing_formula_source_evaluations
    {W : WeilFormSymbols}
    {common : CommonSourceTest.ConcreteCommonSourceTest W} {n : ℕ}
    (h : ConcreteCommonPrimePowerPairingData W common n) :
    h.model.sourceTPairing =
      (1 / Real.sqrt (n : ℝ)) *
        (h.model.sourceEvaluation.forwardValue +
          h.model.sourceEvaluation.inverseValue) :=
  h.model.source_t_pairing_formula_real_sqrt

theorem prime_power_pairing_formula_concrete_model_evaluations
    {W : WeilFormSymbols}
    {common : CommonSourceTest.ConcreteCommonSourceTest W} {n : ℕ}
    (h : ConcreteCommonPrimePowerPairingData W common n) :
    W.primePowerPairing n common.sourceTest common.sourceTest =
      (1 / Real.sqrt (n : ℝ)) *
        (h.concreteEvaluation.model.forwardValue +
          h.concreteEvaluation.model.inverseValue) := by
  rw [h.pairingReadOff,
    h.source_t_pairing_formula_real_sqrt_concrete_model_evaluations]

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

theorem source_forward_value_at_concrete_square_source_point
    {W : WeilFormSymbols}
    {common : CommonSourceTest.ConcreteCommonSourceTest W} {n : ℕ}
    (h : ConcreteCommonPrimePowerPairingData W common n) :
    h.model.sourceEvaluation.forwardValue =
      h.concreteEvaluation.sourceEvaluator.valueAt
        common.sourceConvolutionSquare
        (PrimePowerEvaluation.SourceForwardPoint n) := by
  rw [h.modelEvaluationReadOff]
  exact h.concreteEvaluation.forward_value_at_concrete_square_source_point

theorem source_inverse_value_at_concrete_square_source_point
    {W : WeilFormSymbols}
    {common : CommonSourceTest.ConcreteCommonSourceTest W} {n : ℕ}
    (h : ConcreteCommonPrimePowerPairingData W common n) :
    h.model.sourceEvaluation.inverseValue =
      h.concreteEvaluation.sourceEvaluator.valueAt
        common.sourceConvolutionSquare
        (PrimePowerEvaluation.SourceInversePoint n) := by
  rw [h.modelEvaluationReadOff]
  exact h.concreteEvaluation.inverse_value_at_concrete_square_source_point

theorem prime_power_pairing_formula_source_evaluations
    {W : WeilFormSymbols}
    {common : CommonSourceTest.ConcreteCommonSourceTest W} {n : ℕ}
    (h : ConcreteCommonPrimePowerPairingData W common n) :
    W.primePowerPairing n common.sourceTest common.sourceTest =
      (1 / Real.sqrt (n : ℝ)) *
        (h.model.sourceEvaluation.forwardValue +
          h.model.sourceEvaluation.inverseValue) := by
  rw [h.pairingReadOff, h.source_t_pairing_formula_source_evaluations]

theorem prime_power_pairing_formula_concrete_square
    {W : WeilFormSymbols}
    {common : CommonSourceTest.ConcreteCommonSourceTest W} {n : ℕ}
    (h : ConcreteCommonPrimePowerPairingData W common n) :
    W.primePowerPairing n common.sourceTest common.sourceTest =
      (1 / Real.sqrt (n : ℝ)) *
        (h.concreteEvaluation.sourceEvaluator.valueAt
            common.sourceConvolutionSquare (n : ℝ) +
          h.concreteEvaluation.sourceEvaluator.valueAt
            common.sourceConvolutionSquare ((n : ℝ)⁻¹)) := by
  rw [prime_power_pairing_formula_source_evaluations h,
    h.source_forward_value_at_concrete_square,
    h.source_inverse_value_at_concrete_square]

theorem prime_power_pairing_formula_concrete_square_source_points
    {W : WeilFormSymbols}
    {common : CommonSourceTest.ConcreteCommonSourceTest W} {n : ℕ}
    (h : ConcreteCommonPrimePowerPairingData W common n) :
    W.primePowerPairing n common.sourceTest common.sourceTest =
      (1 / Real.sqrt (n : ℝ)) *
        (h.concreteEvaluation.sourceEvaluator.valueAt
            common.sourceConvolutionSquare
            (PrimePowerEvaluation.SourceForwardPoint n) +
          h.concreteEvaluation.sourceEvaluator.valueAt
            common.sourceConvolutionSquare
            (PrimePowerEvaluation.SourceInversePoint n)) := by
  rw [prime_power_pairing_formula_source_evaluations h,
    h.source_forward_value_at_concrete_square_source_point,
    h.source_inverse_value_at_concrete_square_source_point]

end ConcreteCommonPrimePowerPairingData

theorem source_t_pairing_formula
    {W : WeilFormSymbols} {f g : TestFunction} {n : ℕ}
    (h : SourcePrimePowerPairingData W f g n) :
    h.model.sourceTPairing =
      (1 / Real.sqrt (n : ℝ)) *
        (h.model.sourceForwardEvaluation +
          h.model.sourceInverseEvaluation) :=
  h.model.tPairingFormula

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

theorem source_prime_power_pairing_formula_model_source_evaluations
    {W : WeilFormSymbols} {f g : TestFunction} {n : ℕ}
    (h : SourcePrimePowerPairingData W f g n) :
    W.primePowerPairing n f g =
      (1 / Real.sqrt (n : ℝ)) *
        (h.model.sourceEvaluation.forwardValue +
          h.model.sourceEvaluation.inverseValue) := by
  rw [h.pairingReadOff,
    h.model.source_t_pairing_formula_source_evaluations]

theorem source_prime_power_pairing_formula_source_normalization_source_evaluations
    {W : WeilFormSymbols} {f g : TestFunction} {n : ℕ}
    (h : SourcePrimePowerPairingData W f g n) :
    W.primePowerPairing n f g =
      (1 / Real.sqrt (n : ℝ)) *
        (h.model.sourceEvaluation.forwardValue +
          h.model.sourceEvaluation.inverseValue) := by
  rw [h.pairingReadOff,
    h.model.source_t_pairing_formula_source_normalization]

theorem source_prime_power_pairing_formula
    {W : WeilFormSymbols} {f g : TestFunction} {n : ℕ}
    (h : SourcePrimePowerPairingData W f g n) :
    W.primePowerPairing n f g =
      (1 / Real.sqrt (n : ℝ)) *
        (h.model.sourceForwardEvaluation +
          h.model.sourceInverseEvaluation) := by
  rw [h.pairingReadOff, h.model.tPairingFormula]

theorem source_prime_power_pairing_formula_inv_sqrt
    {W : WeilFormSymbols} {f g : TestFunction} {n : ℕ}
    (h : SourcePrimePowerPairingData W f g n) :
    W.primePowerPairing n f g =
      (1 / Real.sqrt (n : ℝ)) *
        (h.model.sourceForwardEvaluation +
          h.model.sourceInverseEvaluation) :=
  source_prime_power_pairing_formula h

theorem source_prime_power_pairing_formula_real_sqrt
    {W : WeilFormSymbols} {f g : TestFunction} {n : ℕ}
    (h : SourcePrimePowerPairingData W f g n) :
    W.primePowerPairing n f g =
      (1 / Real.sqrt (n : ℝ)) *
        (h.model.sourceForwardEvaluation +
          h.model.sourceInverseEvaluation) :=
  source_prime_power_pairing_formula_inv_sqrt h

theorem source_prime_power_pairing_formula_source_evaluations
    {W : WeilFormSymbols} {f g : TestFunction} {n : ℕ}
    (h : SourcePrimePowerPairingData W f g n) :
    W.primePowerPairing n f g =
      (1 / Real.sqrt (n : ℝ)) *
        (h.model.sourceEvaluation.forwardValue +
          h.model.sourceEvaluation.inverseValue) := by
  rw [h.pairingReadOff, h.model.source_t_pairing_formula_real_sqrt]

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

theorem source_prime_power_pairing_formula_source_evaluator_source_points
    {W : WeilFormSymbols} {f g : TestFunction} {n : ℕ}
    (h : SourcePrimePowerPairingData W f g n) :
    W.primePowerPairing n f g =
      (1 / Real.sqrt (n : ℝ)) *
        (h.model.sourceEvaluation.sourceEvaluator.valueAt
            (W.convolutionStar f g)
            (PrimePowerEvaluation.SourceForwardPoint n) +
          h.model.sourceEvaluation.sourceEvaluator.valueAt
            (W.convolutionStar f g)
            (PrimePowerEvaluation.SourceInversePoint n)) := by
  rw [source_prime_power_pairing_formula_source_evaluations h,
    PrimePowerEvaluation.source_forward_value_at_route_square_source_point
      h.model.sourceEvaluation,
    PrimePowerEvaluation.source_inverse_value_at_route_square_source_point
      h.model.sourceEvaluation]

theorem source_prime_power_pairing_formula_model_square
    {W : WeilFormSymbols} {f g : TestFunction} {n : ℕ}
    (h : SourcePrimePowerPairingData W f g n) :
    W.primePowerPairing n f g =
      (1 / Real.sqrt (n : ℝ)) *
        (h.model.sourceEvaluation.sourceEvaluator.valueAt
            h.model.sourceEvaluation.sourceConvolutionSquare (n : ℝ) +
          h.model.sourceEvaluation.sourceEvaluator.valueAt
            h.model.sourceEvaluation.sourceConvolutionSquare ((n : ℝ)⁻¹)) := by
  rw [source_prime_power_pairing_formula_source_evaluations h,
    PrimePowerEvaluation.source_forward_value_at_model_square_nat_cast
      h.model.sourceEvaluation,
    PrimePowerEvaluation.source_inverse_value_at_model_square_inv_nat_cast
      h.model.sourceEvaluation]

theorem source_prime_power_pairing_formula_model_square_source_points
    {W : WeilFormSymbols} {f g : TestFunction} {n : ℕ}
    (h : SourcePrimePowerPairingData W f g n) :
    W.primePowerPairing n f g =
      (1 / Real.sqrt (n : ℝ)) *
        (h.model.sourceEvaluation.sourceEvaluator.valueAt
            h.model.sourceEvaluation.sourceConvolutionSquare
            (PrimePowerEvaluation.SourceForwardPoint n) +
          h.model.sourceEvaluation.sourceEvaluator.valueAt
            h.model.sourceEvaluation.sourceConvolutionSquare
            (PrimePowerEvaluation.SourceInversePoint n)) := by
  rw [source_prime_power_pairing_formula_source_evaluations h,
    PrimePowerEvaluation.source_forward_value_at_model_square_source_point
      h.model.sourceEvaluation,
    PrimePowerEvaluation.source_inverse_value_at_model_square_source_point
      h.model.sourceEvaluation]

theorem concrete_common_prime_power_pairing_formula_source_evaluations
    {W : WeilFormSymbols}
    {common : CommonSourceTest.ConcreteCommonSourceTest W} {n : ℕ}
    (h : ConcreteCommonPrimePowerPairingData W common n) :
    W.primePowerPairing n common.sourceTest common.sourceTest =
      (1 / Real.sqrt (n : ℝ)) *
        (h.model.sourceEvaluation.forwardValue +
          h.model.sourceEvaluation.inverseValue) :=
  source_prime_power_pairing_formula_source_evaluations
    h.toSourcePrimePowerPairingData

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
  rw [h.prime_power_pairing_formula_concrete_model_evaluations,
    h.concreteEvaluation.forward_value_at_concrete_square,
    h.concreteEvaluation.inverse_value_at_concrete_square]

end PrimePowerPairing
end CCM25Concrete
end Source
end ConnesWeilRH
