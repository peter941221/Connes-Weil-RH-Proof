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
`F_g = g^* * g` evaluated at `n` and `n⁻¹`.  Since the current Lean boundary
keeps `TestFunction := Type`, this module records the source evaluation object
without pretending that a test function already has a Lean function
application operation.
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
  forwardValue : ℝ
  inverseValue : ℝ
  forwardValueReadOff :
    forwardValue =
      sourceEvaluator.valueAt sourceConvolutionSquare forwardPoint
  inverseValueReadOff :
    inverseValue =
      sourceEvaluator.valueAt sourceConvolutionSquare inversePoint

theorem source_convolution_square_read_off
    {W : WeilFormSymbols} {f g : TestFunction} {n : ℕ}
    (h : SourceConvolutionEvaluationModel W f g n) :
    h.sourceConvolutionSquare = W.convolutionStar f g :=
  h.convolutionSquareReadOff.trans h.sourceTest.convolutionSquareReadOff

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

theorem source_forward_value_read_off
    {W : WeilFormSymbols} {f g : TestFunction} {n : ℕ}
    (h : SourceConvolutionEvaluationModel W f g n) :
    h.forwardValue =
      h.sourceEvaluator.valueAt h.sourceConvolutionSquare h.forwardPoint :=
  h.forwardValueReadOff

theorem source_inverse_value_read_off
    {W : WeilFormSymbols} {f g : TestFunction} {n : ℕ}
    (h : SourceConvolutionEvaluationModel W f g n) :
    h.inverseValue =
      h.sourceEvaluator.valueAt h.sourceConvolutionSquare h.inversePoint :=
  h.inverseValueReadOff

theorem source_forward_value_at_source_points
    {W : WeilFormSymbols} {f g : TestFunction} {n : ℕ}
    (h : SourceConvolutionEvaluationModel W f g n) :
    h.forwardValue =
      h.sourceEvaluator.valueAt (W.convolutionStar f g) (n : ℝ) := by
  rw [h.forwardValueReadOff, source_convolution_square_read_off h,
    source_forward_point_read_off h]

theorem source_inverse_value_at_source_points
    {W : WeilFormSymbols} {f g : TestFunction} {n : ℕ}
    (h : SourceConvolutionEvaluationModel W f g n) :
    h.inverseValue =
      h.sourceEvaluator.valueAt (W.convolutionStar f g) ((n : ℝ)⁻¹) := by
  rw [h.inverseValueReadOff, source_convolution_square_read_off h,
    source_inverse_point_read_off h]

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

theorem source_evaluator_test_read_off
    {W : WeilFormSymbols}
    {common : CommonSourceTest.ConcreteCommonSourceTest W} {n : ℕ}
    (h : ConcreteCommonPrimePowerEvaluation W common n) :
    h.sourceEvaluator.sourceTest = common.toSourceTestEvaluationInterface :=
  h.sourceEvaluatorTestReadOff

theorem model_evaluator_test_read_off
    {W : WeilFormSymbols}
    {common : CommonSourceTest.ConcreteCommonSourceTest W} {n : ℕ}
    (h : ConcreteCommonPrimePowerEvaluation W common n) :
    h.model.sourceEvaluator.sourceTest = common.toSourceTestEvaluationInterface := by
  rw [h.modelEvaluatorReadOff]
  exact h.sourceEvaluatorTestReadOff

theorem source_convolution_square_eq_common_square
    {W : WeilFormSymbols}
    {common : CommonSourceTest.ConcreteCommonSourceTest W} {n : ℕ}
    (h : ConcreteCommonPrimePowerEvaluation W common n) :
    h.model.sourceConvolutionSquare = common.sourceConvolutionSquare := by
  rw [source_convolution_square_read_off h.model]
  exact (common.source_convolution_square_read_off).symm

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

theorem forward_value_at_concrete_square
    {W : WeilFormSymbols}
    {common : CommonSourceTest.ConcreteCommonSourceTest W} {n : ℕ}
    (h : ConcreteCommonPrimePowerEvaluation W common n) :
    h.model.forwardValue =
      h.sourceEvaluator.valueAt common.sourceConvolutionSquare (n : ℝ) := by
  rw [h.model.forwardValueReadOff, h.modelEvaluatorReadOff,
    source_convolution_square_eq_common_square h,
    source_forward_point_read_off h.model]

theorem inverse_value_at_concrete_square
    {W : WeilFormSymbols}
    {common : CommonSourceTest.ConcreteCommonSourceTest W} {n : ℕ}
    (h : ConcreteCommonPrimePowerEvaluation W common n) :
    h.model.inverseValue =
      h.sourceEvaluator.valueAt common.sourceConvolutionSquare ((n : ℝ)⁻¹) := by
  rw [h.model.inverseValueReadOff, h.modelEvaluatorReadOff,
    source_convolution_square_eq_common_square h,
    source_inverse_point_read_off h.model]

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
