/-
Copyright (c) 2026 ConnesWeilRH contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ConnesWeilRH contributors
-/

import ConnesWeilRH.Basic
import ConnesWeilRH.Source.CCM25Concrete.CommonSourceTest
import ConnesWeilRH.Source.CCM25Concrete.PrimePowerTest

/-!
# CCM25 source evaluation points for prime-power atoms

The finite-prime pairing uses the same source convolution square
`F_g = g^* * g` evaluated at `n` and `n⁻¹`.  The route-level `TestFunction` is
Mathlib's Schwartz space on `ℝ` with complex values.  The model stores the
source evaluator and the two source points; the forward and inverse values are
defined from that evaluator rather than accepted as separate cache fields.
-/

namespace ConnesWeilRH
namespace Source
namespace CCM25Concrete
namespace PrimePowerEvaluation

def SourceForwardPoint (n : ℕ) : ℝ :=
  n

noncomputable def SourceInversePoint (n : ℕ) : ℝ :=
  (n : ℝ)⁻¹

theorem source_forward_point_eq_nat_cast
    {n : ℕ} :
    SourceForwardPoint n = (n : ℝ) :=
  rfl

theorem source_inverse_point_eq_inv_nat_cast
    {n : ℕ} :
    SourceInversePoint n = (n : ℝ)⁻¹ :=
  rfl

structure SourceEvaluationFunctional
    (W : WeilFormSymbols) (f g : TestFunction) where
  sourceTest : PrimePowerTest.SourceTestEvaluationInterface W f g
  sourceConvolutionSquare : TestFunction := sourceTest.sourceConvolutionSquare
  convolutionSquareReadOff :
    sourceConvolutionSquare = sourceTest.sourceConvolutionSquare
  valueAt : TestFunction → ℝ → ℝ

theorem source_evaluator_source_convolution_square_read_off
    {W : WeilFormSymbols} {f g : TestFunction}
    (h : SourceEvaluationFunctional W f g) :
    h.sourceConvolutionSquare = h.sourceTest.sourceConvolutionSquare :=
  h.convolutionSquareReadOff

theorem source_evaluator_source_test_square_eq_route_square
    {W : WeilFormSymbols} {f g : TestFunction}
    (h : SourceEvaluationFunctional W f g) :
    h.sourceTest.sourceConvolutionSquare = W.convolutionStar f g :=
  h.sourceTest.convolutionSquareReadOff

theorem source_evaluator_convolution_square_eq_route_square_direct
    {W : WeilFormSymbols} {f g : TestFunction}
    (h : SourceEvaluationFunctional W f g) :
    h.sourceConvolutionSquare = W.convolutionStar f g :=
  h.convolutionSquareReadOff.trans h.sourceTest.convolutionSquareReadOff

theorem source_evaluator_route_square_eq_convolution_square
    {W : WeilFormSymbols} {f g : TestFunction}
    (h : SourceEvaluationFunctional W f g) :
    W.convolutionStar f g = h.sourceConvolutionSquare :=
  (source_evaluator_convolution_square_eq_route_square_direct h).symm

structure SourceConvolutionEvaluationModel
    (W : WeilFormSymbols) (f g : TestFunction) (n : ℕ) where
  sourceTest : PrimePowerTest.SourceTestEvaluationInterface W f g
  sourceEvaluator : SourceEvaluationFunctional W f g
  evaluatorSourceTestReadOff :
    sourceEvaluator.sourceTest = sourceTest
  sourceConvolutionSquare : TestFunction := W.convolutionStar f g
  convolutionSquareReadOff :
    sourceConvolutionSquare = sourceTest.sourceConvolutionSquare
  forwardPoint : ℝ
  inversePoint : ℝ
  forwardPointReadOff : forwardPoint = SourceForwardPoint n
  inversePointReadOff : inversePoint = SourceInversePoint n

noncomputable def SourceConvolutionEvaluationModel.forwardValue
    {W : WeilFormSymbols} {f g : TestFunction} {n : ℕ}
    (h : SourceConvolutionEvaluationModel W f g n) : ℝ :=
  h.sourceEvaluator.valueAt h.sourceConvolutionSquare h.forwardPoint

noncomputable def SourceConvolutionEvaluationModel.inverseValue
    {W : WeilFormSymbols} {f g : TestFunction} {n : ℕ}
    (h : SourceConvolutionEvaluationModel W f g n) : ℝ :=
  h.sourceEvaluator.valueAt h.sourceConvolutionSquare h.inversePoint

theorem source_convolution_square_read_off
    {W : WeilFormSymbols} {f g : TestFunction} {n : ℕ}
    (h : SourceConvolutionEvaluationModel W f g n) :
    h.sourceConvolutionSquare = W.convolutionStar f g :=
  h.convolutionSquareReadOff.trans h.sourceTest.convolutionSquareReadOff

theorem source_test_convolution_square_eq_model_square
    {W : WeilFormSymbols} {f g : TestFunction} {n : ℕ}
    (h : SourceConvolutionEvaluationModel W f g n) :
    h.sourceTest.sourceConvolutionSquare = h.sourceConvolutionSquare :=
  h.convolutionSquareReadOff.symm

theorem source_test_convolution_square_eq_route_square
    {W : WeilFormSymbols} {f g : TestFunction} {n : ℕ}
    (h : SourceConvolutionEvaluationModel W f g n) :
    h.sourceTest.sourceConvolutionSquare = W.convolutionStar f g :=
  h.sourceTest.convolutionSquareReadOff

theorem source_evaluator_convolution_square_eq_source_test_square
    {W : WeilFormSymbols} {f g : TestFunction} {n : ℕ}
    (h : SourceConvolutionEvaluationModel W f g n) :
    h.sourceEvaluator.sourceConvolutionSquare =
      h.sourceTest.sourceConvolutionSquare := by
  rw [h.sourceEvaluator.convolutionSquareReadOff, h.evaluatorSourceTestReadOff]

theorem source_evaluator_convolution_square_eq_model_square
    {W : WeilFormSymbols} {f g : TestFunction} {n : ℕ}
    (h : SourceConvolutionEvaluationModel W f g n) :
    h.sourceEvaluator.sourceConvolutionSquare = h.sourceConvolutionSquare :=
  (source_evaluator_convolution_square_eq_source_test_square h).trans
    h.convolutionSquareReadOff.symm

theorem source_evaluator_convolution_square_eq_route_square
    {W : WeilFormSymbols} {f g : TestFunction} {n : ℕ}
    (h : SourceConvolutionEvaluationModel W f g n) :
    h.sourceEvaluator.sourceConvolutionSquare = W.convolutionStar f g :=
  (source_evaluator_convolution_square_eq_model_square h).trans
    (source_convolution_square_read_off h)

theorem source_test_visibility_iff_route_visibility
    {W : WeilFormSymbols} {f g : TestFunction} {n : ℕ}
    (h : SourceConvolutionEvaluationModel W f g n) :
    W.finitePrimeAtomVisible n (W.convolutionStar f g) ↔
      h.sourceTest.sourceAtomVisible n :=
  PrimePowerTest.route_visibility_iff_source_visibility h.sourceTest n

theorem source_forward_point_read_off
    {W : WeilFormSymbols} {f g : TestFunction} {n : ℕ}
    (h : SourceConvolutionEvaluationModel W f g n) :
    h.forwardPoint = (n : ℝ) := by
  rw [h.forwardPointReadOff, source_forward_point_eq_nat_cast]

theorem source_inverse_point_read_off
    {W : WeilFormSymbols} {f g : TestFunction} {n : ℕ}
    (h : SourceConvolutionEvaluationModel W f g n) :
    h.inversePoint = (n : ℝ)⁻¹ := by
  rw [h.inversePointReadOff, source_inverse_point_eq_inv_nat_cast]

theorem source_evaluator_source_test_read_off
    {W : WeilFormSymbols} {f g : TestFunction} {n : ℕ}
    (h : SourceConvolutionEvaluationModel W f g n) :
    h.sourceEvaluator.sourceTest = h.sourceTest :=
  h.evaluatorSourceTestReadOff

theorem source_test_eq_source_evaluator_source_test
    {W : WeilFormSymbols} {f g : TestFunction} {n : ℕ}
    (h : SourceConvolutionEvaluationModel W f g n) :
    h.sourceTest = h.sourceEvaluator.sourceTest :=
  h.evaluatorSourceTestReadOff.symm

theorem source_convolution_square_eq_source_test_square
    {W : WeilFormSymbols} {f g : TestFunction} {n : ℕ}
    (h : SourceConvolutionEvaluationModel W f g n) :
    h.sourceConvolutionSquare = h.sourceTest.sourceConvolutionSquare :=
  h.convolutionSquareReadOff

theorem route_square_eq_source_convolution_square
    {W : WeilFormSymbols} {f g : TestFunction} {n : ℕ}
    (h : SourceConvolutionEvaluationModel W f g n) :
    W.convolutionStar f g = h.sourceConvolutionSquare :=
  (source_convolution_square_read_off h).symm

theorem source_test_square_eq_source_evaluator_square
    {W : WeilFormSymbols} {f g : TestFunction} {n : ℕ}
    (h : SourceConvolutionEvaluationModel W f g n) :
    h.sourceTest.sourceConvolutionSquare =
      h.sourceEvaluator.sourceConvolutionSquare :=
  (source_evaluator_convolution_square_eq_source_test_square h).symm

theorem source_convolution_square_eq_source_evaluator_square
    {W : WeilFormSymbols} {f g : TestFunction} {n : ℕ}
    (h : SourceConvolutionEvaluationModel W f g n) :
    h.sourceConvolutionSquare = h.sourceEvaluator.sourceConvolutionSquare :=
  (source_evaluator_convolution_square_eq_model_square h).symm

theorem source_forward_value_read_off
    {W : WeilFormSymbols} {f g : TestFunction} {n : ℕ}
    (h : SourceConvolutionEvaluationModel W f g n) :
    h.forwardValue =
      h.sourceEvaluator.valueAt h.sourceConvolutionSquare h.forwardPoint :=
  rfl

theorem source_inverse_value_read_off
    {W : WeilFormSymbols} {f g : TestFunction} {n : ℕ}
    (h : SourceConvolutionEvaluationModel W f g n) :
    h.inverseValue =
      h.sourceEvaluator.valueAt h.sourceConvolutionSquare h.inversePoint :=
  rfl

theorem source_forward_value_at_model_square_source_point
    {W : WeilFormSymbols} {f g : TestFunction} {n : ℕ}
    (h : SourceConvolutionEvaluationModel W f g n) :
    h.forwardValue =
      h.sourceEvaluator.valueAt h.sourceConvolutionSquare
        (SourceForwardPoint n) := by
  rw [source_forward_value_read_off h, h.forwardPointReadOff]

theorem source_inverse_value_at_model_square_source_point
    {W : WeilFormSymbols} {f g : TestFunction} {n : ℕ}
    (h : SourceConvolutionEvaluationModel W f g n) :
    h.inverseValue =
      h.sourceEvaluator.valueAt h.sourceConvolutionSquare
        (SourceInversePoint n) := by
  rw [source_inverse_value_read_off h, h.inversePointReadOff]

theorem source_forward_value_at_model_square_nat_cast
    {W : WeilFormSymbols} {f g : TestFunction} {n : ℕ}
    (h : SourceConvolutionEvaluationModel W f g n) :
    h.forwardValue =
      h.sourceEvaluator.valueAt h.sourceConvolutionSquare (n : ℝ) := by
  rw [source_forward_value_read_off h, source_forward_point_read_off h]

theorem source_inverse_value_at_model_square_inv_nat_cast
    {W : WeilFormSymbols} {f g : TestFunction} {n : ℕ}
    (h : SourceConvolutionEvaluationModel W f g n) :
    h.inverseValue =
      h.sourceEvaluator.valueAt h.sourceConvolutionSquare ((n : ℝ)⁻¹) := by
  rw [source_inverse_value_read_off h, source_inverse_point_read_off h]

theorem source_forward_value_at_source_points
    {W : WeilFormSymbols} {f g : TestFunction} {n : ℕ}
    (h : SourceConvolutionEvaluationModel W f g n) :
    h.forwardValue =
      h.sourceEvaluator.valueAt (W.convolutionStar f g) (n : ℝ) := by
  rw [source_forward_value_read_off h, source_convolution_square_read_off h,
    source_forward_point_read_off h]

theorem source_inverse_value_at_source_points
    {W : WeilFormSymbols} {f g : TestFunction} {n : ℕ}
    (h : SourceConvolutionEvaluationModel W f g n) :
    h.inverseValue =
      h.sourceEvaluator.valueAt (W.convolutionStar f g) ((n : ℝ)⁻¹) := by
  rw [source_inverse_value_read_off h, source_convolution_square_read_off h,
    source_inverse_point_read_off h]

theorem source_forward_value_at_source_test_square
    {W : WeilFormSymbols} {f g : TestFunction} {n : ℕ}
    (h : SourceConvolutionEvaluationModel W f g n) :
    h.forwardValue =
      h.sourceEvaluator.valueAt h.sourceTest.sourceConvolutionSquare (n : ℝ) := by
  rw [source_forward_value_read_off h, h.convolutionSquareReadOff,
    source_forward_point_read_off h]

theorem source_inverse_value_at_source_test_square
    {W : WeilFormSymbols} {f g : TestFunction} {n : ℕ}
    (h : SourceConvolutionEvaluationModel W f g n) :
    h.inverseValue =
      h.sourceEvaluator.valueAt h.sourceTest.sourceConvolutionSquare
        ((n : ℝ)⁻¹) := by
  rw [source_inverse_value_read_off h, h.convolutionSquareReadOff,
    source_inverse_point_read_off h]

theorem source_forward_value_at_source_test_square_source_point
    {W : WeilFormSymbols} {f g : TestFunction} {n : ℕ}
    (h : SourceConvolutionEvaluationModel W f g n) :
    h.forwardValue =
      h.sourceEvaluator.valueAt h.sourceTest.sourceConvolutionSquare
        (SourceForwardPoint n) := by
  rw [source_forward_value_read_off h, h.convolutionSquareReadOff,
    h.forwardPointReadOff]

theorem source_inverse_value_at_source_test_square_source_point
    {W : WeilFormSymbols} {f g : TestFunction} {n : ℕ}
    (h : SourceConvolutionEvaluationModel W f g n) :
    h.inverseValue =
      h.sourceEvaluator.valueAt h.sourceTest.sourceConvolutionSquare
        (SourceInversePoint n) := by
  rw [source_inverse_value_read_off h, h.convolutionSquareReadOff,
    h.inversePointReadOff]

theorem source_forward_value_at_evaluator_square
    {W : WeilFormSymbols} {f g : TestFunction} {n : ℕ}
    (h : SourceConvolutionEvaluationModel W f g n) :
    h.forwardValue =
      h.sourceEvaluator.valueAt h.sourceEvaluator.sourceConvolutionSquare
        (n : ℝ) := by
  rw [source_forward_value_read_off h,
    ← source_evaluator_convolution_square_eq_model_square h,
    source_forward_point_read_off h]

theorem source_inverse_value_at_evaluator_square
    {W : WeilFormSymbols} {f g : TestFunction} {n : ℕ}
    (h : SourceConvolutionEvaluationModel W f g n) :
    h.inverseValue =
      h.sourceEvaluator.valueAt h.sourceEvaluator.sourceConvolutionSquare
        ((n : ℝ)⁻¹) := by
  rw [source_inverse_value_read_off h,
    ← source_evaluator_convolution_square_eq_model_square h,
    source_inverse_point_read_off h]

theorem source_forward_value_at_evaluator_square_source_point
    {W : WeilFormSymbols} {f g : TestFunction} {n : ℕ}
    (h : SourceConvolutionEvaluationModel W f g n) :
    h.forwardValue =
      h.sourceEvaluator.valueAt h.sourceEvaluator.sourceConvolutionSquare
        (SourceForwardPoint n) := by
  rw [source_forward_value_read_off h,
    ← source_evaluator_convolution_square_eq_model_square h,
    h.forwardPointReadOff]

theorem source_inverse_value_at_evaluator_square_source_point
    {W : WeilFormSymbols} {f g : TestFunction} {n : ℕ}
    (h : SourceConvolutionEvaluationModel W f g n) :
    h.inverseValue =
      h.sourceEvaluator.valueAt h.sourceEvaluator.sourceConvolutionSquare
        (SourceInversePoint n) := by
  rw [source_inverse_value_read_off h,
    ← source_evaluator_convolution_square_eq_model_square h,
    h.inversePointReadOff]

theorem source_forward_value_at_route_square_source_point
    {W : WeilFormSymbols} {f g : TestFunction} {n : ℕ}
    (h : SourceConvolutionEvaluationModel W f g n) :
    h.forwardValue =
      h.sourceEvaluator.valueAt (W.convolutionStar f g) (SourceForwardPoint n) := by
  rw [source_forward_value_read_off h, source_convolution_square_read_off h,
    h.forwardPointReadOff]

theorem source_inverse_value_at_route_square_source_point
    {W : WeilFormSymbols} {f g : TestFunction} {n : ℕ}
    (h : SourceConvolutionEvaluationModel W f g n) :
    h.inverseValue =
      h.sourceEvaluator.valueAt (W.convolutionStar f g)
        (SourceInversePoint n) := by
  rw [source_inverse_value_read_off h, source_convolution_square_read_off h,
    h.inversePointReadOff]

theorem source_forward_value_at_evaluator_square_model_point
    {W : WeilFormSymbols} {f g : TestFunction} {n : ℕ}
    (h : SourceConvolutionEvaluationModel W f g n) :
    h.forwardValue =
      h.sourceEvaluator.valueAt h.sourceEvaluator.sourceConvolutionSquare
        h.forwardPoint := by
  rw [source_forward_value_read_off h,
    ← source_evaluator_convolution_square_eq_model_square h]

theorem source_inverse_value_at_evaluator_square_model_point
    {W : WeilFormSymbols} {f g : TestFunction} {n : ℕ}
    (h : SourceConvolutionEvaluationModel W f g n) :
    h.inverseValue =
      h.sourceEvaluator.valueAt h.sourceEvaluator.sourceConvolutionSquare
        h.inversePoint := by
  rw [source_inverse_value_read_off h,
    ← source_evaluator_convolution_square_eq_model_square h]

/--
Goal 0C concrete-common evaluation data.

This wraps the existing source evaluation model but fixes its source-test
interface to the `ConcreteCommonSourceTest` object from Goal 0A/0B.  The
analytic operation `valueAt` remains abstract at this phase, while the source
test, source square, and evaluation points no longer drift.
-/
structure ConcreteCommonPrimePowerEvaluation
    (W : WeilFormSymbols)
    (common : CommonSourceTest.ConcreteCommonSourceTest W) (n : ℕ) where
  sourceEvaluator : SourceEvaluationFunctional W common.sourceTest common.sourceTest
  sourceEvaluatorTestReadOff :
    sourceEvaluator.sourceTest = common.toSourceTestEvaluationInterface
  model :
    SourceConvolutionEvaluationModel W common.sourceTest common.sourceTest n
  modelEvaluatorReadOff : model.sourceEvaluator = sourceEvaluator
  modelSourceTestReadOff :
    model.sourceTest = common.toSourceTestEvaluationInterface

namespace ConcreteCommonPrimePowerEvaluation

theorem source_test_read_off
    {W : WeilFormSymbols}
    {common : CommonSourceTest.ConcreteCommonSourceTest W} {n : ℕ}
    (h : ConcreteCommonPrimePowerEvaluation W common n) :
    h.model.sourceTest = common.toSourceTestEvaluationInterface :=
  h.modelSourceTestReadOff

theorem common_source_test_eq_model_source_test
    {W : WeilFormSymbols}
    {common : CommonSourceTest.ConcreteCommonSourceTest W} {n : ℕ}
    (h : ConcreteCommonPrimePowerEvaluation W common n) :
    common.toSourceTestEvaluationInterface = h.model.sourceTest :=
  h.modelSourceTestReadOff.symm

theorem source_evaluator_test_read_off
    {W : WeilFormSymbols}
    {common : CommonSourceTest.ConcreteCommonSourceTest W} {n : ℕ}
    (h : ConcreteCommonPrimePowerEvaluation W common n) :
    h.sourceEvaluator.sourceTest = common.toSourceTestEvaluationInterface :=
  h.sourceEvaluatorTestReadOff

theorem common_source_test_eq_source_evaluator_test
    {W : WeilFormSymbols}
    {common : CommonSourceTest.ConcreteCommonSourceTest W} {n : ℕ}
    (h : ConcreteCommonPrimePowerEvaluation W common n) :
    common.toSourceTestEvaluationInterface = h.sourceEvaluator.sourceTest :=
  h.sourceEvaluatorTestReadOff.symm

theorem model_evaluator_test_read_off
    {W : WeilFormSymbols}
    {common : CommonSourceTest.ConcreteCommonSourceTest W} {n : ℕ}
    (h : ConcreteCommonPrimePowerEvaluation W common n) :
    h.model.sourceEvaluator.sourceTest = common.toSourceTestEvaluationInterface := by
  rw [h.modelEvaluatorReadOff]
  exact h.sourceEvaluatorTestReadOff

theorem source_evaluator_eq_model_evaluator
    {W : WeilFormSymbols}
    {common : CommonSourceTest.ConcreteCommonSourceTest W} {n : ℕ}
    (h : ConcreteCommonPrimePowerEvaluation W common n) :
    h.sourceEvaluator = h.model.sourceEvaluator :=
  h.modelEvaluatorReadOff.symm

theorem source_evaluator_test_eq_model_source_test
    {W : WeilFormSymbols}
    {common : CommonSourceTest.ConcreteCommonSourceTest W} {n : ℕ}
    (h : ConcreteCommonPrimePowerEvaluation W common n) :
    h.sourceEvaluator.sourceTest = h.model.sourceTest := by
  rw [h.sourceEvaluatorTestReadOff, h.modelSourceTestReadOff]

theorem source_convolution_square_eq_common_square
    {W : WeilFormSymbols}
    {common : CommonSourceTest.ConcreteCommonSourceTest W} {n : ℕ}
    (h : ConcreteCommonPrimePowerEvaluation W common n) :
    h.model.sourceConvolutionSquare = common.sourceConvolutionSquare := by
  rw [source_convolution_square_read_off h.model]
  exact (common.source_convolution_square_read_off).symm

theorem common_square_eq_source_convolution_square
    {W : WeilFormSymbols}
    {common : CommonSourceTest.ConcreteCommonSourceTest W} {n : ℕ}
    (h : ConcreteCommonPrimePowerEvaluation W common n) :
    common.sourceConvolutionSquare = h.model.sourceConvolutionSquare :=
  (source_convolution_square_eq_common_square h).symm

theorem source_evaluator_square_eq_common_square
    {W : WeilFormSymbols}
    {common : CommonSourceTest.ConcreteCommonSourceTest W} {n : ℕ}
    (h : ConcreteCommonPrimePowerEvaluation W common n) :
    h.sourceEvaluator.sourceConvolutionSquare = common.sourceConvolutionSquare := by
  rw [← h.modelEvaluatorReadOff,
    source_evaluator_convolution_square_eq_model_square h.model,
    source_convolution_square_eq_common_square h]

theorem common_square_eq_source_evaluator_square
    {W : WeilFormSymbols}
    {common : CommonSourceTest.ConcreteCommonSourceTest W} {n : ℕ}
    (h : ConcreteCommonPrimePowerEvaluation W common n) :
    common.sourceConvolutionSquare = h.sourceEvaluator.sourceConvolutionSquare :=
  (source_evaluator_square_eq_common_square h).symm

theorem source_evaluator_square_eq_route_square
    {W : WeilFormSymbols}
    {common : CommonSourceTest.ConcreteCommonSourceTest W} {n : ℕ}
    (h : ConcreteCommonPrimePowerEvaluation W common n) :
    h.sourceEvaluator.sourceConvolutionSquare =
      W.convolutionStar common.sourceTest common.sourceTest := by
  rw [source_evaluator_square_eq_common_square h]
  exact common.source_convolution_square_read_off

theorem route_square_eq_source_evaluator_square
    {W : WeilFormSymbols}
    {common : CommonSourceTest.ConcreteCommonSourceTest W} {n : ℕ}
    (h : ConcreteCommonPrimePowerEvaluation W common n) :
    W.convolutionStar common.sourceTest common.sourceTest =
      h.sourceEvaluator.sourceConvolutionSquare :=
  (source_evaluator_square_eq_route_square h).symm

theorem model_evaluator_square_eq_common_square
    {W : WeilFormSymbols}
    {common : CommonSourceTest.ConcreteCommonSourceTest W} {n : ℕ}
    (h : ConcreteCommonPrimePowerEvaluation W common n) :
    h.model.sourceEvaluator.sourceConvolutionSquare =
      common.sourceConvolutionSquare := by
  rw [h.modelEvaluatorReadOff]
  exact source_evaluator_square_eq_common_square h

theorem model_evaluator_square_eq_route_square
    {W : WeilFormSymbols}
    {common : CommonSourceTest.ConcreteCommonSourceTest W} {n : ℕ}
    (h : ConcreteCommonPrimePowerEvaluation W common n) :
    h.model.sourceEvaluator.sourceConvolutionSquare =
      W.convolutionStar common.sourceTest common.sourceTest := by
  rw [h.modelEvaluatorReadOff]
  exact source_evaluator_square_eq_route_square h

theorem forward_point_eq_source_point
    {W : WeilFormSymbols}
    {common : CommonSourceTest.ConcreteCommonSourceTest W} {n : ℕ}
    (h : ConcreteCommonPrimePowerEvaluation W common n) :
    h.model.forwardPoint = SourceForwardPoint n :=
  h.model.forwardPointReadOff

theorem inverse_point_eq_source_point
    {W : WeilFormSymbols}
    {common : CommonSourceTest.ConcreteCommonSourceTest W} {n : ℕ}
    (h : ConcreteCommonPrimePowerEvaluation W common n) :
    h.model.inversePoint = SourceInversePoint n :=
  h.model.inversePointReadOff

theorem forward_point_eq_nat_cast
    {W : WeilFormSymbols}
    {common : CommonSourceTest.ConcreteCommonSourceTest W} {n : ℕ}
    (h : ConcreteCommonPrimePowerEvaluation W common n) :
    h.model.forwardPoint = (n : ℝ) :=
  source_forward_point_read_off h.model

theorem inverse_point_eq_inv_nat_cast
    {W : WeilFormSymbols}
    {common : CommonSourceTest.ConcreteCommonSourceTest W} {n : ℕ}
    (h : ConcreteCommonPrimePowerEvaluation W common n) :
    h.model.inversePoint = (n : ℝ)⁻¹ :=
  source_inverse_point_read_off h.model

theorem forward_value_at_concrete_square
    {W : WeilFormSymbols}
    {common : CommonSourceTest.ConcreteCommonSourceTest W} {n : ℕ}
    (h : ConcreteCommonPrimePowerEvaluation W common n) :
    h.model.forwardValue =
      h.sourceEvaluator.valueAt common.sourceConvolutionSquare (n : ℝ) := by
  rw [source_forward_value_read_off h.model, h.modelEvaluatorReadOff,
    source_convolution_square_eq_common_square h,
    source_forward_point_read_off h.model]

theorem inverse_value_at_concrete_square
    {W : WeilFormSymbols}
    {common : CommonSourceTest.ConcreteCommonSourceTest W} {n : ℕ}
    (h : ConcreteCommonPrimePowerEvaluation W common n) :
    h.model.inverseValue =
      h.sourceEvaluator.valueAt common.sourceConvolutionSquare ((n : ℝ)⁻¹) := by
  rw [source_inverse_value_read_off h.model, h.modelEvaluatorReadOff,
    source_convolution_square_eq_common_square h,
    source_inverse_point_read_off h.model]

theorem forward_value_at_concrete_square_source_point
    {W : WeilFormSymbols}
    {common : CommonSourceTest.ConcreteCommonSourceTest W} {n : ℕ}
    (h : ConcreteCommonPrimePowerEvaluation W common n) :
    h.model.forwardValue =
      h.sourceEvaluator.valueAt common.sourceConvolutionSquare
        (SourceForwardPoint n) := by
  rw [source_forward_value_read_off h.model, h.modelEvaluatorReadOff,
    source_convolution_square_eq_common_square h,
    h.model.forwardPointReadOff]

theorem inverse_value_at_concrete_square_source_point
    {W : WeilFormSymbols}
    {common : CommonSourceTest.ConcreteCommonSourceTest W} {n : ℕ}
    (h : ConcreteCommonPrimePowerEvaluation W common n) :
    h.model.inverseValue =
      h.sourceEvaluator.valueAt common.sourceConvolutionSquare
        (SourceInversePoint n) := by
  rw [source_inverse_value_read_off h.model, h.modelEvaluatorReadOff,
    source_convolution_square_eq_common_square h,
    h.model.inversePointReadOff]

theorem forward_value_at_route_square
    {W : WeilFormSymbols}
    {common : CommonSourceTest.ConcreteCommonSourceTest W} {n : ℕ}
    (h : ConcreteCommonPrimePowerEvaluation W common n) :
    h.model.forwardValue =
      h.sourceEvaluator.valueAt
        (W.convolutionStar common.sourceTest common.sourceTest) (n : ℝ) := by
  rw [forward_value_at_concrete_square h,
    common.source_convolution_square_read_off]

theorem inverse_value_at_route_square
    {W : WeilFormSymbols}
    {common : CommonSourceTest.ConcreteCommonSourceTest W} {n : ℕ}
    (h : ConcreteCommonPrimePowerEvaluation W common n) :
    h.model.inverseValue =
      h.sourceEvaluator.valueAt
        (W.convolutionStar common.sourceTest common.sourceTest) ((n : ℝ)⁻¹) := by
  rw [inverse_value_at_concrete_square h,
    common.source_convolution_square_read_off]

theorem forward_value_at_route_square_source_point
    {W : WeilFormSymbols}
    {common : CommonSourceTest.ConcreteCommonSourceTest W} {n : ℕ}
    (h : ConcreteCommonPrimePowerEvaluation W common n) :
    h.model.forwardValue =
      h.sourceEvaluator.valueAt
        (W.convolutionStar common.sourceTest common.sourceTest)
        (SourceForwardPoint n) := by
  rw [forward_value_at_concrete_square_source_point h,
    common.source_convolution_square_read_off]

theorem inverse_value_at_route_square_source_point
    {W : WeilFormSymbols}
    {common : CommonSourceTest.ConcreteCommonSourceTest W} {n : ℕ}
    (h : ConcreteCommonPrimePowerEvaluation W common n) :
    h.model.inverseValue =
      h.sourceEvaluator.valueAt
        (W.convolutionStar common.sourceTest common.sourceTest)
        (SourceInversePoint n) := by
  rw [inverse_value_at_concrete_square_source_point h,
    common.source_convolution_square_read_off]

theorem forward_value_at_source_evaluator_square
    {W : WeilFormSymbols}
    {common : CommonSourceTest.ConcreteCommonSourceTest W} {n : ℕ}
    (h : ConcreteCommonPrimePowerEvaluation W common n) :
    h.model.forwardValue =
      h.sourceEvaluator.valueAt h.sourceEvaluator.sourceConvolutionSquare
        (n : ℝ) := by
  rw [forward_value_at_concrete_square h,
    ← source_evaluator_square_eq_common_square h]

theorem inverse_value_at_source_evaluator_square
    {W : WeilFormSymbols}
    {common : CommonSourceTest.ConcreteCommonSourceTest W} {n : ℕ}
    (h : ConcreteCommonPrimePowerEvaluation W common n) :
    h.model.inverseValue =
      h.sourceEvaluator.valueAt h.sourceEvaluator.sourceConvolutionSquare
        ((n : ℝ)⁻¹) := by
  rw [inverse_value_at_concrete_square h,
    ← source_evaluator_square_eq_common_square h]

theorem forward_value_at_source_evaluator_square_source_point
    {W : WeilFormSymbols}
    {common : CommonSourceTest.ConcreteCommonSourceTest W} {n : ℕ}
    (h : ConcreteCommonPrimePowerEvaluation W common n) :
    h.model.forwardValue =
      h.sourceEvaluator.valueAt h.sourceEvaluator.sourceConvolutionSquare
        (SourceForwardPoint n) := by
  rw [forward_value_at_concrete_square_source_point h,
    ← source_evaluator_square_eq_common_square h]

theorem inverse_value_at_source_evaluator_square_source_point
    {W : WeilFormSymbols}
    {common : CommonSourceTest.ConcreteCommonSourceTest W} {n : ℕ}
    (h : ConcreteCommonPrimePowerEvaluation W common n) :
    h.model.inverseValue =
      h.sourceEvaluator.valueAt h.sourceEvaluator.sourceConvolutionSquare
        (SourceInversePoint n) := by
  rw [inverse_value_at_concrete_square_source_point h,
    ← source_evaluator_square_eq_common_square h]

theorem source_visibility_iff_concrete_visibility
    {W : WeilFormSymbols}
    {common : CommonSourceTest.ConcreteCommonSourceTest W} {n : ℕ}
    (h : ConcreteCommonPrimePowerEvaluation W common n) :
    W.finitePrimeAtomVisible n
        (W.convolutionStar common.sourceTest common.sourceTest) ↔
      h.model.sourceTest.sourceAtomVisible n := by
  exact PrimePowerTest.route_visibility_iff_source_visibility h.model.sourceTest n

theorem source_visibility_iff_common_visibility
    {W : WeilFormSymbols}
    {common : CommonSourceTest.ConcreteCommonSourceTest W} {n : ℕ}
    (h : ConcreteCommonPrimePowerEvaluation W common n) :
    h.model.sourceTest.sourceAtomVisible n ↔ common.sourceAtomVisible n := by
  rw [h.modelSourceTestReadOff]
  rfl

end ConcreteCommonPrimePowerEvaluation

end PrimePowerEvaluation
end CCM25Concrete
end Source
end ConnesWeilRH
