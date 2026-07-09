/-
Copyright (c) 2026 ConnesWeilRH contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ConnesWeilRH contributors
-/

import ConnesWeilRH.Source.AnalyticCoreBase
import ConnesWeilRH.Source.CCM25Concrete.PrimePowerEvaluation
import ConnesWeilRH.Source.CCM25Concrete.PrimePowerPairing

/-!
# Bridge from source evaluation data to CCM25 prime-power evaluation

This module is intentionally downstream of both the source analytic base and
the CCM25 prime-power evaluator.  It exposes the existing source evaluator
through the legacy `TestFunction` bridge without changing the current CCM25
consumer surface.
-/

namespace ConnesWeilRH
namespace Source
namespace CCM25Concrete
namespace PrimePowerEvaluation

namespace SourceEvaluationFunctional

noncomputable def ofSourceEvaluationData
    {A : AnalyticCore.SourceTestAlgebra}
    (E : AnalyticCore.SourceEvaluationData A)
    {W : WeilFormSymbols} {f g : TestFunction}
    (sourceTest : PrimePowerTest.SourceTestEvaluationInterface W f g) :
    SourceEvaluationFunctional W f g where
  sourceTest := sourceTest
  convolutionSquareReadOff := rfl
  valueAt := E.legacyValueAt

@[simp] theorem ofSourceEvaluationData_sourceTest
    {A : AnalyticCore.SourceTestAlgebra}
    (E : AnalyticCore.SourceEvaluationData A)
    {W : WeilFormSymbols} {f g : TestFunction}
    (sourceTest : PrimePowerTest.SourceTestEvaluationInterface W f g) :
    (ofSourceEvaluationData E sourceTest).sourceTest = sourceTest :=
  rfl

@[simp] theorem ofSourceEvaluationData_sourceConvolutionSquare
    {A : AnalyticCore.SourceTestAlgebra}
    (E : AnalyticCore.SourceEvaluationData A)
    {W : WeilFormSymbols} {f g : TestFunction}
    (sourceTest : PrimePowerTest.SourceTestEvaluationInterface W f g) :
    (ofSourceEvaluationData E sourceTest).sourceConvolutionSquare =
      sourceTest.sourceConvolutionSquare :=
  rfl

@[simp] theorem ofSourceEvaluationData_valueAt
    {A : AnalyticCore.SourceTestAlgebra}
    (E : AnalyticCore.SourceEvaluationData A)
    {W : WeilFormSymbols} {f g : TestFunction}
    (sourceTest : PrimePowerTest.SourceTestEvaluationInterface W f g)
    (F : TestFunction) (x : ℝ) :
    (ofSourceEvaluationData E sourceTest).valueAt F x =
      E.valueAt (A.legacy.decode F) x :=
  rfl

@[simp] theorem ofSourceEvaluationData_valueAt_eq_norm
    {A : AnalyticCore.SourceTestAlgebra}
    (E : AnalyticCore.SourceEvaluationData A)
    {W : WeilFormSymbols} {f g : TestFunction}
    (sourceTest : PrimePowerTest.SourceTestEvaluationInterface W f g)
    (F : TestFunction) (x : ℝ) :
    (ofSourceEvaluationData E sourceTest).valueAt F x = ‖F x‖ := by
  change ‖A.legacy.encode (A.legacy.decode F) x‖ = ‖F x‖
  simp

@[simp] theorem ofSourceEvaluationData_valueAt_sourceSquare
    {A : AnalyticCore.SourceTestAlgebra}
    (E : AnalyticCore.SourceEvaluationData A)
    {W : WeilFormSymbols} {f g : TestFunction}
    (sourceTest : PrimePowerTest.SourceTestEvaluationInterface W f g)
    (x : ℝ) :
    (ofSourceEvaluationData E sourceTest).valueAt
        sourceTest.sourceConvolutionSquare x =
      E.valueAt (A.legacy.decode sourceTest.sourceConvolutionSquare) x :=
  rfl

@[simp] theorem ofSourceEvaluationData_valueAt_sourceSquare_eq_norm
    {A : AnalyticCore.SourceTestAlgebra}
    (E : AnalyticCore.SourceEvaluationData A)
    {W : WeilFormSymbols} {f g : TestFunction}
    (sourceTest : PrimePowerTest.SourceTestEvaluationInterface W f g)
    (x : ℝ) :
    (ofSourceEvaluationData E sourceTest).valueAt
        sourceTest.sourceConvolutionSquare x =
      ‖sourceTest.sourceConvolutionSquare x‖ := by
  change
    ‖A.legacy.encode (A.legacy.decode sourceTest.sourceConvolutionSquare) x‖ =
      ‖sourceTest.sourceConvolutionSquare x‖
  simp

@[simp] theorem ofSourceEvaluationData_valueAt_routeSquare
    {A : AnalyticCore.SourceTestAlgebra}
    (E : AnalyticCore.SourceEvaluationData A)
    {W : WeilFormSymbols} {f g : TestFunction}
    (sourceTest : PrimePowerTest.SourceTestEvaluationInterface W f g)
    (x : ℝ) :
    (ofSourceEvaluationData E sourceTest).valueAt (W.convolutionStar f g) x =
      E.valueAt (A.legacy.decode (W.convolutionStar f g)) x :=
  rfl

@[simp] theorem ofSourceEvaluationData_valueAt_routeSquare_eq_norm
    {A : AnalyticCore.SourceTestAlgebra}
    (E : AnalyticCore.SourceEvaluationData A)
    {W : WeilFormSymbols} {f g : TestFunction}
    (sourceTest : PrimePowerTest.SourceTestEvaluationInterface W f g)
    (x : ℝ) :
    (ofSourceEvaluationData E sourceTest).valueAt (W.convolutionStar f g) x =
      ‖(W.convolutionStar f g) x‖ := by
  change
    ‖A.legacy.encode (A.legacy.decode (W.convolutionStar f g)) x‖ =
      ‖(W.convolutionStar f g) x‖
  simp

@[simp] theorem ofSourceEvaluationData_valueAt_sourceSquare_forwardPoint
    {A : AnalyticCore.SourceTestAlgebra}
    (E : AnalyticCore.SourceEvaluationData A)
    {W : WeilFormSymbols} {f g : TestFunction}
    (sourceTest : PrimePowerTest.SourceTestEvaluationInterface W f g)
    (n : ℕ) :
    (ofSourceEvaluationData E sourceTest).valueAt
        sourceTest.sourceConvolutionSquare (SourceForwardPoint n) =
      E.valueAt (A.legacy.decode sourceTest.sourceConvolutionSquare)
        (SourceForwardPoint n) :=
  rfl

@[simp] theorem ofSourceEvaluationData_valueAt_sourceSquare_inversePoint
    {A : AnalyticCore.SourceTestAlgebra}
    (E : AnalyticCore.SourceEvaluationData A)
    {W : WeilFormSymbols} {f g : TestFunction}
    (sourceTest : PrimePowerTest.SourceTestEvaluationInterface W f g)
    (n : ℕ) :
    (ofSourceEvaluationData E sourceTest).valueAt
        sourceTest.sourceConvolutionSquare (SourceInversePoint n) =
      E.valueAt (A.legacy.decode sourceTest.sourceConvolutionSquare)
        (SourceInversePoint n) :=
  rfl

@[simp] theorem ofSourceEvaluationData_valueAt_sourceSquare_nat
    {A : AnalyticCore.SourceTestAlgebra}
    (E : AnalyticCore.SourceEvaluationData A)
    {W : WeilFormSymbols} {f g : TestFunction}
    (sourceTest : PrimePowerTest.SourceTestEvaluationInterface W f g)
    (n : ℕ) :
    (ofSourceEvaluationData E sourceTest).valueAt
        sourceTest.sourceConvolutionSquare (n : ℝ) =
      E.valueAt (A.legacy.decode sourceTest.sourceConvolutionSquare) (n : ℝ) :=
  rfl

@[simp] theorem ofSourceEvaluationData_valueAt_sourceSquare_inv_nat
    {A : AnalyticCore.SourceTestAlgebra}
    (E : AnalyticCore.SourceEvaluationData A)
    {W : WeilFormSymbols} {f g : TestFunction}
    (sourceTest : PrimePowerTest.SourceTestEvaluationInterface W f g)
    (n : ℕ) :
    (ofSourceEvaluationData E sourceTest).valueAt
        sourceTest.sourceConvolutionSquare ((n : ℝ)⁻¹) =
      E.valueAt (A.legacy.decode sourceTest.sourceConvolutionSquare) ((n : ℝ)⁻¹) :=
  rfl

@[simp] theorem ofSourceEvaluationData_valueAt_routeSquare_forwardPoint
    {A : AnalyticCore.SourceTestAlgebra}
    (E : AnalyticCore.SourceEvaluationData A)
    {W : WeilFormSymbols} {f g : TestFunction}
    (sourceTest : PrimePowerTest.SourceTestEvaluationInterface W f g)
    (n : ℕ) :
    (ofSourceEvaluationData E sourceTest).valueAt
        (W.convolutionStar f g) (SourceForwardPoint n) =
      E.valueAt (A.legacy.decode (W.convolutionStar f g))
        (SourceForwardPoint n) :=
  rfl

@[simp] theorem ofSourceEvaluationData_valueAt_routeSquare_inversePoint
    {A : AnalyticCore.SourceTestAlgebra}
    (E : AnalyticCore.SourceEvaluationData A)
    {W : WeilFormSymbols} {f g : TestFunction}
    (sourceTest : PrimePowerTest.SourceTestEvaluationInterface W f g)
    (n : ℕ) :
    (ofSourceEvaluationData E sourceTest).valueAt
        (W.convolutionStar f g) (SourceInversePoint n) =
      E.valueAt (A.legacy.decode (W.convolutionStar f g))
        (SourceInversePoint n) :=
  rfl

@[simp] theorem ofSourceEvaluationData_valueAt_routeSquare_nat
    {A : AnalyticCore.SourceTestAlgebra}
    (E : AnalyticCore.SourceEvaluationData A)
    {W : WeilFormSymbols} {f g : TestFunction}
    (sourceTest : PrimePowerTest.SourceTestEvaluationInterface W f g)
    (n : ℕ) :
    (ofSourceEvaluationData E sourceTest).valueAt
        (W.convolutionStar f g) (n : ℝ) =
      E.valueAt (A.legacy.decode (W.convolutionStar f g)) (n : ℝ) :=
  rfl

@[simp] theorem ofSourceEvaluationData_valueAt_routeSquare_inv_nat
    {A : AnalyticCore.SourceTestAlgebra}
    (E : AnalyticCore.SourceEvaluationData A)
    {W : WeilFormSymbols} {f g : TestFunction}
    (sourceTest : PrimePowerTest.SourceTestEvaluationInterface W f g)
    (n : ℕ) :
    (ofSourceEvaluationData E sourceTest).valueAt
        (W.convolutionStar f g) ((n : ℝ)⁻¹) =
      E.valueAt (A.legacy.decode (W.convolutionStar f g)) ((n : ℝ)⁻¹) :=
  rfl

end SourceEvaluationFunctional

namespace ConcreteCommonPrimePowerEvaluation

noncomputable def ofSourceEvaluationData
    {A : AnalyticCore.SourceTestAlgebra}
    (E : AnalyticCore.SourceEvaluationData A)
    {W : WeilFormSymbols}
    (common : CommonSourceTest.ConcreteCommonSourceTest W) (n : ℕ) :
    ConcreteCommonPrimePowerEvaluation W common n where
  sourceEvaluator :=
    SourceEvaluationFunctional.ofSourceEvaluationData E
      common.toSourceTestEvaluationInterface
  sourceEvaluatorTestReadOff := rfl
  model := {
    sourceTest := common.toSourceTestEvaluationInterface
    sourceEvaluator :=
      SourceEvaluationFunctional.ofSourceEvaluationData E
        common.toSourceTestEvaluationInterface
    evaluatorSourceTestReadOff := rfl
    sourceConvolutionSquare := common.sourceConvolutionSquare
    convolutionSquareReadOff := rfl
    forwardPoint := SourceForwardPoint n
    inversePoint := SourceInversePoint n
    forwardPointReadOff := rfl
    inversePointReadOff := rfl }
  modelEvaluatorReadOff := rfl
  modelSourceTestReadOff := rfl

@[simp] theorem ofSourceEvaluationData_sourceEvaluator
    {A : AnalyticCore.SourceTestAlgebra}
    (E : AnalyticCore.SourceEvaluationData A)
    {W : WeilFormSymbols}
    (common : CommonSourceTest.ConcreteCommonSourceTest W) (n : ℕ) :
    (ofSourceEvaluationData E common n).sourceEvaluator =
      SourceEvaluationFunctional.ofSourceEvaluationData E
        common.toSourceTestEvaluationInterface :=
  rfl

@[simp] theorem ofSourceEvaluationData_sourceEvaluator_sourceTest
    {A : AnalyticCore.SourceTestAlgebra}
    (E : AnalyticCore.SourceEvaluationData A)
    {W : WeilFormSymbols}
    (common : CommonSourceTest.ConcreteCommonSourceTest W) (n : ℕ) :
    (ofSourceEvaluationData E common n).sourceEvaluator.sourceTest =
      common.toSourceTestEvaluationInterface :=
  rfl

@[simp] theorem ofSourceEvaluationData_sourceEvaluator_sourceSquare
    {A : AnalyticCore.SourceTestAlgebra}
    (E : AnalyticCore.SourceEvaluationData A)
    {W : WeilFormSymbols}
    (common : CommonSourceTest.ConcreteCommonSourceTest W) (n : ℕ) :
    (ofSourceEvaluationData E common n).sourceEvaluator.sourceConvolutionSquare =
      common.sourceConvolutionSquare :=
  rfl

@[simp] theorem ofSourceEvaluationData_sourceEvaluator_valueAt
    {A : AnalyticCore.SourceTestAlgebra}
    (E : AnalyticCore.SourceEvaluationData A)
    {W : WeilFormSymbols}
    (common : CommonSourceTest.ConcreteCommonSourceTest W) (n : ℕ)
    (F : TestFunction) (x : ℝ) :
    (ofSourceEvaluationData E common n).sourceEvaluator.valueAt F x =
      E.valueAt (A.legacy.decode F) x :=
  rfl

@[simp] theorem ofSourceEvaluationData_sourceEvaluator_valueAt_eq_norm
    {A : AnalyticCore.SourceTestAlgebra}
    (E : AnalyticCore.SourceEvaluationData A)
    {W : WeilFormSymbols}
    (common : CommonSourceTest.ConcreteCommonSourceTest W) (n : ℕ)
    (F : TestFunction) (x : ℝ) :
    (ofSourceEvaluationData E common n).sourceEvaluator.valueAt F x =
      ‖F x‖ := by
  change ‖A.legacy.encode (A.legacy.decode F) x‖ = ‖F x‖
  simp

@[simp] theorem ofSourceEvaluationData_sourceEvaluator_valueAt_commonSquare
    {A : AnalyticCore.SourceTestAlgebra}
    (E : AnalyticCore.SourceEvaluationData A)
    {W : WeilFormSymbols}
    (common : CommonSourceTest.ConcreteCommonSourceTest W) (n : ℕ) (x : ℝ) :
    (ofSourceEvaluationData E common n).sourceEvaluator.valueAt
        common.sourceConvolutionSquare x =
      E.valueAt (A.legacy.decode common.sourceConvolutionSquare) x :=
  rfl

@[simp] theorem ofSourceEvaluationData_model_sourceTest
    {A : AnalyticCore.SourceTestAlgebra}
    (E : AnalyticCore.SourceEvaluationData A)
    {W : WeilFormSymbols}
    (common : CommonSourceTest.ConcreteCommonSourceTest W) (n : ℕ) :
    (ofSourceEvaluationData E common n).model.sourceTest =
      common.toSourceTestEvaluationInterface :=
  rfl

@[simp] theorem ofSourceEvaluationData_model_sourceEvaluator
    {A : AnalyticCore.SourceTestAlgebra}
    (E : AnalyticCore.SourceEvaluationData A)
    {W : WeilFormSymbols}
    (common : CommonSourceTest.ConcreteCommonSourceTest W) (n : ℕ) :
    (ofSourceEvaluationData E common n).model.sourceEvaluator =
      SourceEvaluationFunctional.ofSourceEvaluationData E
        common.toSourceTestEvaluationInterface :=
  rfl

@[simp] theorem ofSourceEvaluationData_model_sourceEvaluator_valueAt
    {A : AnalyticCore.SourceTestAlgebra}
    (E : AnalyticCore.SourceEvaluationData A)
    {W : WeilFormSymbols}
    (common : CommonSourceTest.ConcreteCommonSourceTest W) (n : ℕ)
    (F : TestFunction) (x : ℝ) :
    (ofSourceEvaluationData E common n).model.sourceEvaluator.valueAt F x =
      E.valueAt (A.legacy.decode F) x :=
  rfl

@[simp] theorem ofSourceEvaluationData_model_sourceEvaluator_valueAt_eq_norm
    {A : AnalyticCore.SourceTestAlgebra}
    (E : AnalyticCore.SourceEvaluationData A)
    {W : WeilFormSymbols}
    (common : CommonSourceTest.ConcreteCommonSourceTest W) (n : ℕ)
    (F : TestFunction) (x : ℝ) :
    (ofSourceEvaluationData E common n).model.sourceEvaluator.valueAt F x =
      ‖F x‖ := by
  change ‖A.legacy.encode (A.legacy.decode F) x‖ = ‖F x‖
  simp

@[simp] theorem ofSourceEvaluationData_model_sourceConvolutionSquare
    {A : AnalyticCore.SourceTestAlgebra}
    (E : AnalyticCore.SourceEvaluationData A)
    {W : WeilFormSymbols}
    (common : CommonSourceTest.ConcreteCommonSourceTest W) (n : ℕ) :
    (ofSourceEvaluationData E common n).model.sourceConvolutionSquare =
      common.sourceConvolutionSquare :=
  rfl

@[simp] theorem ofSourceEvaluationData_model_forwardPoint
    {A : AnalyticCore.SourceTestAlgebra}
    (E : AnalyticCore.SourceEvaluationData A)
    {W : WeilFormSymbols}
    (common : CommonSourceTest.ConcreteCommonSourceTest W) (n : ℕ) :
    (ofSourceEvaluationData E common n).model.forwardPoint =
      SourceForwardPoint n :=
  rfl

@[simp] theorem ofSourceEvaluationData_model_inversePoint
    {A : AnalyticCore.SourceTestAlgebra}
    (E : AnalyticCore.SourceEvaluationData A)
    {W : WeilFormSymbols}
    (common : CommonSourceTest.ConcreteCommonSourceTest W) (n : ℕ) :
    (ofSourceEvaluationData E common n).model.inversePoint =
      SourceInversePoint n :=
  rfl

@[simp] theorem ofSourceEvaluationData_forwardValue
    {A : AnalyticCore.SourceTestAlgebra}
    (E : AnalyticCore.SourceEvaluationData A)
    {W : WeilFormSymbols}
    (common : CommonSourceTest.ConcreteCommonSourceTest W) (n : ℕ) :
    (ofSourceEvaluationData E common n).model.forwardValue =
      E.valueAt (A.legacy.decode common.sourceConvolutionSquare)
        (SourceForwardPoint n) :=
  rfl

@[simp] theorem ofSourceEvaluationData_forwardValue_eq_norm
    {A : AnalyticCore.SourceTestAlgebra}
    (E : AnalyticCore.SourceEvaluationData A)
    {W : WeilFormSymbols}
    (common : CommonSourceTest.ConcreteCommonSourceTest W) (n : ℕ) :
    (ofSourceEvaluationData E common n).model.forwardValue =
      ‖common.sourceConvolutionSquare (SourceForwardPoint n)‖ := by
  simp [ofSourceEvaluationData, SourceConvolutionEvaluationModel.forwardValue]

@[simp] theorem ofSourceEvaluationData_inverseValue
    {A : AnalyticCore.SourceTestAlgebra}
    (E : AnalyticCore.SourceEvaluationData A)
    {W : WeilFormSymbols}
    (common : CommonSourceTest.ConcreteCommonSourceTest W) (n : ℕ) :
    (ofSourceEvaluationData E common n).model.inverseValue =
      E.valueAt (A.legacy.decode common.sourceConvolutionSquare)
        (SourceInversePoint n) :=
  rfl

@[simp] theorem ofSourceEvaluationData_inverseValue_eq_norm
    {A : AnalyticCore.SourceTestAlgebra}
    (E : AnalyticCore.SourceEvaluationData A)
    {W : WeilFormSymbols}
    (common : CommonSourceTest.ConcreteCommonSourceTest W) (n : ℕ) :
    (ofSourceEvaluationData E common n).model.inverseValue =
      ‖common.sourceConvolutionSquare (SourceInversePoint n)‖ := by
  simp [ofSourceEvaluationData, SourceConvolutionEvaluationModel.inverseValue]

@[simp] theorem ofSourceEvaluationData_forwardValue_nat
    {A : AnalyticCore.SourceTestAlgebra}
    (E : AnalyticCore.SourceEvaluationData A)
    {W : WeilFormSymbols}
    (common : CommonSourceTest.ConcreteCommonSourceTest W) (n : ℕ) :
    (ofSourceEvaluationData E common n).model.forwardValue =
      E.valueAt (A.legacy.decode common.sourceConvolutionSquare) (n : ℝ) :=
  rfl

@[simp] theorem ofSourceEvaluationData_forwardValue_nat_eq_norm
    {A : AnalyticCore.SourceTestAlgebra}
    (E : AnalyticCore.SourceEvaluationData A)
    {W : WeilFormSymbols}
    (common : CommonSourceTest.ConcreteCommonSourceTest W) (n : ℕ) :
    (ofSourceEvaluationData E common n).model.forwardValue =
      ‖common.sourceConvolutionSquare (n : ℝ)‖ := by
  simp [SourceForwardPoint]

@[simp] theorem ofSourceEvaluationData_inverseValue_inv_nat
    {A : AnalyticCore.SourceTestAlgebra}
    (E : AnalyticCore.SourceEvaluationData A)
    {W : WeilFormSymbols}
    (common : CommonSourceTest.ConcreteCommonSourceTest W) (n : ℕ) :
    (ofSourceEvaluationData E common n).model.inverseValue =
      E.valueAt (A.legacy.decode common.sourceConvolutionSquare) ((n : ℝ)⁻¹) :=
  rfl

@[simp] theorem ofSourceEvaluationData_inverseValue_inv_nat_eq_norm
    {A : AnalyticCore.SourceTestAlgebra}
    (E : AnalyticCore.SourceEvaluationData A)
    {W : WeilFormSymbols}
    (common : CommonSourceTest.ConcreteCommonSourceTest W) (n : ℕ) :
    (ofSourceEvaluationData E common n).model.inverseValue =
      ‖common.sourceConvolutionSquare ((n : ℝ)⁻¹)‖ := by
  simp [SourceInversePoint]

@[simp] theorem ofSourceEvaluationData_model_forwardValue_viaEvaluator
    {A : AnalyticCore.SourceTestAlgebra}
    (E : AnalyticCore.SourceEvaluationData A)
    {W : WeilFormSymbols}
    (common : CommonSourceTest.ConcreteCommonSourceTest W) (n : ℕ) :
    (ofSourceEvaluationData E common n).model.forwardValue =
      (ofSourceEvaluationData E common n).model.sourceEvaluator.valueAt
        common.sourceConvolutionSquare (SourceForwardPoint n) :=
  rfl

@[simp] theorem ofSourceEvaluationData_model_inverseValue_viaEvaluator
    {A : AnalyticCore.SourceTestAlgebra}
    (E : AnalyticCore.SourceEvaluationData A)
    {W : WeilFormSymbols}
    (common : CommonSourceTest.ConcreteCommonSourceTest W) (n : ℕ) :
    (ofSourceEvaluationData E common n).model.inverseValue =
      (ofSourceEvaluationData E common n).model.sourceEvaluator.valueAt
        common.sourceConvolutionSquare (SourceInversePoint n) :=
  rfl

@[simp] theorem ofSourceEvaluationData_model_forwardValue_viaEvaluator_nat
    {A : AnalyticCore.SourceTestAlgebra}
    (E : AnalyticCore.SourceEvaluationData A)
    {W : WeilFormSymbols}
    (common : CommonSourceTest.ConcreteCommonSourceTest W) (n : ℕ) :
    (ofSourceEvaluationData E common n).model.forwardValue =
      (ofSourceEvaluationData E common n).model.sourceEvaluator.valueAt
        common.sourceConvolutionSquare (n : ℝ) :=
  rfl

@[simp] theorem ofSourceEvaluationData_model_inverseValue_viaEvaluator_inv_nat
    {A : AnalyticCore.SourceTestAlgebra}
    (E : AnalyticCore.SourceEvaluationData A)
    {W : WeilFormSymbols}
    (common : CommonSourceTest.ConcreteCommonSourceTest W) (n : ℕ) :
    (ofSourceEvaluationData E common n).model.inverseValue =
      (ofSourceEvaluationData E common n).model.sourceEvaluator.valueAt
        common.sourceConvolutionSquare ((n : ℝ)⁻¹) :=
  rfl

@[simp] theorem ofSourceEvaluationData_modelEvaluatorReadOff
    {A : AnalyticCore.SourceTestAlgebra}
    (E : AnalyticCore.SourceEvaluationData A)
    {W : WeilFormSymbols}
    (common : CommonSourceTest.ConcreteCommonSourceTest W) (n : ℕ) :
    (ofSourceEvaluationData E common n).model.sourceEvaluator =
      (ofSourceEvaluationData E common n).sourceEvaluator :=
  rfl

@[simp] theorem ofSourceEvaluationData_sourceEvaluator_valueAt_commonSquare_forwardPoint
    {A : AnalyticCore.SourceTestAlgebra}
    (E : AnalyticCore.SourceEvaluationData A)
    {W : WeilFormSymbols}
    (common : CommonSourceTest.ConcreteCommonSourceTest W) (n : ℕ) :
    (ofSourceEvaluationData E common n).sourceEvaluator.valueAt
        common.sourceConvolutionSquare (SourceForwardPoint n) =
      E.valueAt (A.legacy.decode common.sourceConvolutionSquare)
        (SourceForwardPoint n) :=
  rfl

@[simp] theorem ofSourceEvaluationData_sourceEvaluator_valueAt_commonSquare_inversePoint
    {A : AnalyticCore.SourceTestAlgebra}
    (E : AnalyticCore.SourceEvaluationData A)
    {W : WeilFormSymbols}
    (common : CommonSourceTest.ConcreteCommonSourceTest W) (n : ℕ) :
    (ofSourceEvaluationData E common n).sourceEvaluator.valueAt
        common.sourceConvolutionSquare (SourceInversePoint n) =
      E.valueAt (A.legacy.decode common.sourceConvolutionSquare)
        (SourceInversePoint n) :=
  rfl

@[simp] theorem ofSourceEvaluationData_sourceEvaluator_valueAt_commonSquare_nat
    {A : AnalyticCore.SourceTestAlgebra}
    (E : AnalyticCore.SourceEvaluationData A)
    {W : WeilFormSymbols}
    (common : CommonSourceTest.ConcreteCommonSourceTest W) (n : ℕ) :
    (ofSourceEvaluationData E common n).sourceEvaluator.valueAt
        common.sourceConvolutionSquare (n : ℝ) =
      E.valueAt (A.legacy.decode common.sourceConvolutionSquare) (n : ℝ) :=
  rfl

@[simp] theorem ofSourceEvaluationData_sourceEvaluator_valueAt_commonSquare_inv_nat
    {A : AnalyticCore.SourceTestAlgebra}
    (E : AnalyticCore.SourceEvaluationData A)
    {W : WeilFormSymbols}
    (common : CommonSourceTest.ConcreteCommonSourceTest W) (n : ℕ) :
    (ofSourceEvaluationData E common n).sourceEvaluator.valueAt
        common.sourceConvolutionSquare ((n : ℝ)⁻¹) =
      E.valueAt (A.legacy.decode common.sourceConvolutionSquare) ((n : ℝ)⁻¹) :=
  rfl

@[simp] theorem ofSourceEvaluationData_model_sourceEvaluator_valueAt_commonSquare_forwardPoint
    {A : AnalyticCore.SourceTestAlgebra}
    (E : AnalyticCore.SourceEvaluationData A)
    {W : WeilFormSymbols}
    (common : CommonSourceTest.ConcreteCommonSourceTest W) (n : ℕ) :
    (ofSourceEvaluationData E common n).model.sourceEvaluator.valueAt
        common.sourceConvolutionSquare (SourceForwardPoint n) =
      E.valueAt (A.legacy.decode common.sourceConvolutionSquare)
        (SourceForwardPoint n) :=
  rfl

@[simp] theorem ofSourceEvaluationData_model_sourceEvaluator_valueAt_commonSquare_inversePoint
    {A : AnalyticCore.SourceTestAlgebra}
    (E : AnalyticCore.SourceEvaluationData A)
    {W : WeilFormSymbols}
    (common : CommonSourceTest.ConcreteCommonSourceTest W) (n : ℕ) :
    (ofSourceEvaluationData E common n).model.sourceEvaluator.valueAt
        common.sourceConvolutionSquare (SourceInversePoint n) =
      E.valueAt (A.legacy.decode common.sourceConvolutionSquare)
        (SourceInversePoint n) :=
  rfl

@[simp] theorem ofSourceEvaluationData_model_sourceEvaluator_valueAt_commonSquare_nat
    {A : AnalyticCore.SourceTestAlgebra}
    (E : AnalyticCore.SourceEvaluationData A)
    {W : WeilFormSymbols}
    (common : CommonSourceTest.ConcreteCommonSourceTest W) (n : ℕ) :
    (ofSourceEvaluationData E common n).model.sourceEvaluator.valueAt
        common.sourceConvolutionSquare (n : ℝ) =
      E.valueAt (A.legacy.decode common.sourceConvolutionSquare) (n : ℝ) :=
  rfl

@[simp] theorem ofSourceEvaluationData_model_sourceEvaluator_valueAt_commonSquare_inv_nat
    {A : AnalyticCore.SourceTestAlgebra}
    (E : AnalyticCore.SourceEvaluationData A)
    {W : WeilFormSymbols}
    (common : CommonSourceTest.ConcreteCommonSourceTest W) (n : ℕ) :
    (ofSourceEvaluationData E common n).model.sourceEvaluator.valueAt
        common.sourceConvolutionSquare ((n : ℝ)⁻¹) =
      E.valueAt (A.legacy.decode common.sourceConvolutionSquare) ((n : ℝ)⁻¹) :=
  rfl

@[simp] theorem ofSourceEvaluationData_forwardValue_eq_sourceEvaluator_valueAt_commonSquare
    {A : AnalyticCore.SourceTestAlgebra}
    (E : AnalyticCore.SourceEvaluationData A)
    {W : WeilFormSymbols}
    (common : CommonSourceTest.ConcreteCommonSourceTest W) (n : ℕ) :
    (ofSourceEvaluationData E common n).model.forwardValue =
      (ofSourceEvaluationData E common n).sourceEvaluator.valueAt
        common.sourceConvolutionSquare (SourceForwardPoint n) :=
  rfl

@[simp] theorem ofSourceEvaluationData_inverseValue_eq_sourceEvaluator_valueAt_commonSquare
    {A : AnalyticCore.SourceTestAlgebra}
    (E : AnalyticCore.SourceEvaluationData A)
    {W : WeilFormSymbols}
    (common : CommonSourceTest.ConcreteCommonSourceTest W) (n : ℕ) :
    (ofSourceEvaluationData E common n).model.inverseValue =
      (ofSourceEvaluationData E common n).sourceEvaluator.valueAt
        common.sourceConvolutionSquare (SourceInversePoint n) :=
  rfl

end ConcreteCommonPrimePowerEvaluation

end PrimePowerEvaluation

namespace PrimePowerPairing

namespace ConcreteCommonPrimePowerPairingData

noncomputable def ofSourceEvaluationData
    {A : AnalyticCore.SourceTestAlgebra}
    (E : AnalyticCore.SourceEvaluationData A)
    {W : WeilFormSymbols}
    (common : CommonSourceTest.ConcreteCommonSourceTest W) (n : ℕ)
    (pairingReadOff :
      W.primePowerPairing n common.sourceTest common.sourceTest =
        (1 / Real.sqrt (n : ℝ)) *
          (E.legacyValueAt common.sourceConvolutionSquare
              (PrimePowerEvaluation.SourceForwardPoint n) +
            E.legacyValueAt common.sourceConvolutionSquare
              (PrimePowerEvaluation.SourceInversePoint n))) :
    ConcreteCommonPrimePowerPairingData W common n where
  concreteEvaluation :=
    PrimePowerEvaluation.ConcreteCommonPrimePowerEvaluation.ofSourceEvaluationData
      E common n
  model := {
    convolutionSquare := common.sourceConvolutionSquare
    sourceEvaluation :=
      (PrimePowerEvaluation.ConcreteCommonPrimePowerEvaluation.ofSourceEvaluationData
        E common n).model
    sourceForwardEvaluation :=
      E.legacyValueAt common.sourceConvolutionSquare
        (PrimePowerEvaluation.SourceForwardPoint n)
    forwardEvaluationReadOff := rfl
    sourceInverseEvaluation :=
      E.legacyValueAt common.sourceConvolutionSquare
        (PrimePowerEvaluation.SourceInversePoint n)
    inverseEvaluationReadOff := rfl
    sourceTPairing :=
      (1 / Real.sqrt (n : ℝ)) *
        (E.legacyValueAt common.sourceConvolutionSquare
            (PrimePowerEvaluation.SourceForwardPoint n) +
          E.legacyValueAt common.sourceConvolutionSquare
            (PrimePowerEvaluation.SourceInversePoint n))
    tPairingFormula := rfl }
  modelEvaluationReadOff := rfl
  pairingReadOff := pairingReadOff

@[simp] theorem ofSourceEvaluationData_concreteEvaluation
    {A : AnalyticCore.SourceTestAlgebra}
    (E : AnalyticCore.SourceEvaluationData A)
    {W : WeilFormSymbols}
    (common : CommonSourceTest.ConcreteCommonSourceTest W) (n : ℕ)
    (pairingReadOff :
      W.primePowerPairing n common.sourceTest common.sourceTest =
        (1 / Real.sqrt (n : ℝ)) *
          (E.legacyValueAt common.sourceConvolutionSquare
              (PrimePowerEvaluation.SourceForwardPoint n) +
            E.legacyValueAt common.sourceConvolutionSquare
              (PrimePowerEvaluation.SourceInversePoint n))) :
    (ofSourceEvaluationData E common n pairingReadOff).concreteEvaluation =
      PrimePowerEvaluation.ConcreteCommonPrimePowerEvaluation.ofSourceEvaluationData
        E common n :=
  rfl

@[simp] theorem ofSourceEvaluationData_model_sourceEvaluation
    {A : AnalyticCore.SourceTestAlgebra}
    (E : AnalyticCore.SourceEvaluationData A)
    {W : WeilFormSymbols}
    (common : CommonSourceTest.ConcreteCommonSourceTest W) (n : ℕ)
    (pairingReadOff :
      W.primePowerPairing n common.sourceTest common.sourceTest =
        (1 / Real.sqrt (n : ℝ)) *
          (E.legacyValueAt common.sourceConvolutionSquare
              (PrimePowerEvaluation.SourceForwardPoint n) +
            E.legacyValueAt common.sourceConvolutionSquare
              (PrimePowerEvaluation.SourceInversePoint n))) :
    (ofSourceEvaluationData E common n pairingReadOff).model.sourceEvaluation =
      (PrimePowerEvaluation.ConcreteCommonPrimePowerEvaluation.ofSourceEvaluationData
        E common n).model :=
  rfl

@[simp] theorem ofSourceEvaluationData_model_convolutionSquare
    {A : AnalyticCore.SourceTestAlgebra}
    (E : AnalyticCore.SourceEvaluationData A)
    {W : WeilFormSymbols}
    (common : CommonSourceTest.ConcreteCommonSourceTest W) (n : ℕ)
    (pairingReadOff :
      W.primePowerPairing n common.sourceTest common.sourceTest =
        (1 / Real.sqrt (n : ℝ)) *
          (E.legacyValueAt common.sourceConvolutionSquare
              (PrimePowerEvaluation.SourceForwardPoint n) +
            E.legacyValueAt common.sourceConvolutionSquare
              (PrimePowerEvaluation.SourceInversePoint n))) :
    (ofSourceEvaluationData E common n pairingReadOff).model.convolutionSquare =
      common.sourceConvolutionSquare :=
  rfl

@[simp] theorem ofSourceEvaluationData_model_sourceForwardEvaluation
    {A : AnalyticCore.SourceTestAlgebra}
    (E : AnalyticCore.SourceEvaluationData A)
    {W : WeilFormSymbols}
    (common : CommonSourceTest.ConcreteCommonSourceTest W) (n : ℕ)
    (pairingReadOff :
      W.primePowerPairing n common.sourceTest common.sourceTest =
        (1 / Real.sqrt (n : ℝ)) *
          (E.legacyValueAt common.sourceConvolutionSquare
              (PrimePowerEvaluation.SourceForwardPoint n) +
            E.legacyValueAt common.sourceConvolutionSquare
              (PrimePowerEvaluation.SourceInversePoint n))) :
    (ofSourceEvaluationData E common n pairingReadOff).model.sourceForwardEvaluation =
      E.valueAt (A.legacy.decode common.sourceConvolutionSquare)
        (PrimePowerEvaluation.SourceForwardPoint n) :=
  rfl

@[simp] theorem ofSourceEvaluationData_model_sourceInverseEvaluation
    {A : AnalyticCore.SourceTestAlgebra}
    (E : AnalyticCore.SourceEvaluationData A)
    {W : WeilFormSymbols}
    (common : CommonSourceTest.ConcreteCommonSourceTest W) (n : ℕ)
    (pairingReadOff :
      W.primePowerPairing n common.sourceTest common.sourceTest =
        (1 / Real.sqrt (n : ℝ)) *
          (E.legacyValueAt common.sourceConvolutionSquare
              (PrimePowerEvaluation.SourceForwardPoint n) +
            E.legacyValueAt common.sourceConvolutionSquare
              (PrimePowerEvaluation.SourceInversePoint n))) :
    (ofSourceEvaluationData E common n pairingReadOff).model.sourceInverseEvaluation =
      E.valueAt (A.legacy.decode common.sourceConvolutionSquare)
        (PrimePowerEvaluation.SourceInversePoint n) :=
  rfl

@[simp] theorem ofSourceEvaluationData_model_sourceForwardEvaluation_nat
    {A : AnalyticCore.SourceTestAlgebra}
    (E : AnalyticCore.SourceEvaluationData A)
    {W : WeilFormSymbols}
    (common : CommonSourceTest.ConcreteCommonSourceTest W) (n : ℕ)
    (pairingReadOff :
      W.primePowerPairing n common.sourceTest common.sourceTest =
        (1 / Real.sqrt (n : ℝ)) *
          (E.legacyValueAt common.sourceConvolutionSquare
              (PrimePowerEvaluation.SourceForwardPoint n) +
            E.legacyValueAt common.sourceConvolutionSquare
              (PrimePowerEvaluation.SourceInversePoint n))) :
    (ofSourceEvaluationData E common n pairingReadOff).model.sourceForwardEvaluation =
      E.valueAt (A.legacy.decode common.sourceConvolutionSquare) (n : ℝ) :=
  rfl

@[simp] theorem ofSourceEvaluationData_model_sourceInverseEvaluation_inv_nat
    {A : AnalyticCore.SourceTestAlgebra}
    (E : AnalyticCore.SourceEvaluationData A)
    {W : WeilFormSymbols}
    (common : CommonSourceTest.ConcreteCommonSourceTest W) (n : ℕ)
    (pairingReadOff :
      W.primePowerPairing n common.sourceTest common.sourceTest =
        (1 / Real.sqrt (n : ℝ)) *
          (E.legacyValueAt common.sourceConvolutionSquare
              (PrimePowerEvaluation.SourceForwardPoint n) +
            E.legacyValueAt common.sourceConvolutionSquare
              (PrimePowerEvaluation.SourceInversePoint n))) :
    (ofSourceEvaluationData E common n pairingReadOff).model.sourceInverseEvaluation =
      E.valueAt (A.legacy.decode common.sourceConvolutionSquare) ((n : ℝ)⁻¹) :=
  rfl

@[simp] theorem ofSourceEvaluationData_model_sourceTPairing
    {A : AnalyticCore.SourceTestAlgebra}
    (E : AnalyticCore.SourceEvaluationData A)
    {W : WeilFormSymbols}
    (common : CommonSourceTest.ConcreteCommonSourceTest W) (n : ℕ)
    (pairingReadOff :
      W.primePowerPairing n common.sourceTest common.sourceTest =
        (1 / Real.sqrt (n : ℝ)) *
          (E.legacyValueAt common.sourceConvolutionSquare
              (PrimePowerEvaluation.SourceForwardPoint n) +
            E.legacyValueAt common.sourceConvolutionSquare
              (PrimePowerEvaluation.SourceInversePoint n))) :
    (ofSourceEvaluationData E common n pairingReadOff).model.sourceTPairing =
      (1 / Real.sqrt (n : ℝ)) *
        (E.valueAt (A.legacy.decode common.sourceConvolutionSquare)
            (PrimePowerEvaluation.SourceForwardPoint n) +
          E.valueAt (A.legacy.decode common.sourceConvolutionSquare)
            (PrimePowerEvaluation.SourceInversePoint n)) :=
  rfl

@[simp] theorem ofSourceEvaluationData_model_sourceTPairing_nat
    {A : AnalyticCore.SourceTestAlgebra}
    (E : AnalyticCore.SourceEvaluationData A)
    {W : WeilFormSymbols}
    (common : CommonSourceTest.ConcreteCommonSourceTest W) (n : ℕ)
    (pairingReadOff :
      W.primePowerPairing n common.sourceTest common.sourceTest =
        (1 / Real.sqrt (n : ℝ)) *
          (E.legacyValueAt common.sourceConvolutionSquare
              (PrimePowerEvaluation.SourceForwardPoint n) +
            E.legacyValueAt common.sourceConvolutionSquare
              (PrimePowerEvaluation.SourceInversePoint n))) :
    (ofSourceEvaluationData E common n pairingReadOff).model.sourceTPairing =
      (1 / Real.sqrt (n : ℝ)) *
        (E.valueAt (A.legacy.decode common.sourceConvolutionSquare) (n : ℝ) +
          E.valueAt (A.legacy.decode common.sourceConvolutionSquare) ((n : ℝ)⁻¹)) :=
  rfl

@[simp] theorem ofSourceEvaluationData_model_sourceEvaluation_forwardValue
    {A : AnalyticCore.SourceTestAlgebra}
    (E : AnalyticCore.SourceEvaluationData A)
    {W : WeilFormSymbols}
    (common : CommonSourceTest.ConcreteCommonSourceTest W) (n : ℕ)
    (pairingReadOff :
      W.primePowerPairing n common.sourceTest common.sourceTest =
        (1 / Real.sqrt (n : ℝ)) *
          (E.legacyValueAt common.sourceConvolutionSquare
              (PrimePowerEvaluation.SourceForwardPoint n) +
            E.legacyValueAt common.sourceConvolutionSquare
              (PrimePowerEvaluation.SourceInversePoint n))) :
    (ofSourceEvaluationData E common n pairingReadOff).model.sourceEvaluation.forwardValue =
      E.valueAt (A.legacy.decode common.sourceConvolutionSquare)
        (PrimePowerEvaluation.SourceForwardPoint n) :=
  rfl

@[simp] theorem ofSourceEvaluationData_model_sourceEvaluation_inverseValue
    {A : AnalyticCore.SourceTestAlgebra}
    (E : AnalyticCore.SourceEvaluationData A)
    {W : WeilFormSymbols}
    (common : CommonSourceTest.ConcreteCommonSourceTest W) (n : ℕ)
    (pairingReadOff :
      W.primePowerPairing n common.sourceTest common.sourceTest =
        (1 / Real.sqrt (n : ℝ)) *
          (E.legacyValueAt common.sourceConvolutionSquare
              (PrimePowerEvaluation.SourceForwardPoint n) +
            E.legacyValueAt common.sourceConvolutionSquare
              (PrimePowerEvaluation.SourceInversePoint n))) :
    (ofSourceEvaluationData E common n pairingReadOff).model.sourceEvaluation.inverseValue =
      E.valueAt (A.legacy.decode common.sourceConvolutionSquare)
        (PrimePowerEvaluation.SourceInversePoint n) :=
  rfl

@[simp] theorem ofSourceEvaluationData_model_forwardEvaluationReadOff
    {A : AnalyticCore.SourceTestAlgebra}
    (E : AnalyticCore.SourceEvaluationData A)
    {W : WeilFormSymbols}
    (common : CommonSourceTest.ConcreteCommonSourceTest W) (n : ℕ)
    (pairingReadOff :
      W.primePowerPairing n common.sourceTest common.sourceTest =
        (1 / Real.sqrt (n : ℝ)) *
          (E.legacyValueAt common.sourceConvolutionSquare
              (PrimePowerEvaluation.SourceForwardPoint n) +
            E.legacyValueAt common.sourceConvolutionSquare
              (PrimePowerEvaluation.SourceInversePoint n))) :
    (ofSourceEvaluationData E common n pairingReadOff).model.sourceForwardEvaluation =
      (ofSourceEvaluationData E common n pairingReadOff).model.sourceEvaluation.forwardValue :=
  rfl

@[simp] theorem ofSourceEvaluationData_model_inverseEvaluationReadOff
    {A : AnalyticCore.SourceTestAlgebra}
    (E : AnalyticCore.SourceEvaluationData A)
    {W : WeilFormSymbols}
    (common : CommonSourceTest.ConcreteCommonSourceTest W) (n : ℕ)
    (pairingReadOff :
      W.primePowerPairing n common.sourceTest common.sourceTest =
        (1 / Real.sqrt (n : ℝ)) *
          (E.legacyValueAt common.sourceConvolutionSquare
              (PrimePowerEvaluation.SourceForwardPoint n) +
            E.legacyValueAt common.sourceConvolutionSquare
              (PrimePowerEvaluation.SourceInversePoint n))) :
    (ofSourceEvaluationData E common n pairingReadOff).model.sourceInverseEvaluation =
      (ofSourceEvaluationData E common n pairingReadOff).model.sourceEvaluation.inverseValue :=
  rfl

@[simp] theorem ofSourceEvaluationData_model_tPairingFormula
    {A : AnalyticCore.SourceTestAlgebra}
    (E : AnalyticCore.SourceEvaluationData A)
    {W : WeilFormSymbols}
    (common : CommonSourceTest.ConcreteCommonSourceTest W) (n : ℕ)
    (pairingReadOff :
      W.primePowerPairing n common.sourceTest common.sourceTest =
        (1 / Real.sqrt (n : ℝ)) *
          (E.legacyValueAt common.sourceConvolutionSquare
              (PrimePowerEvaluation.SourceForwardPoint n) +
            E.legacyValueAt common.sourceConvolutionSquare
              (PrimePowerEvaluation.SourceInversePoint n))) :
    (ofSourceEvaluationData E common n pairingReadOff).model.sourceTPairing =
      (1 / Real.sqrt (n : ℝ)) *
        ((ofSourceEvaluationData E common n pairingReadOff).model.sourceForwardEvaluation +
          (ofSourceEvaluationData E common n pairingReadOff).model.sourceInverseEvaluation) :=
  rfl

@[simp] theorem ofSourceEvaluationData_modelEvaluationReadOff
    {A : AnalyticCore.SourceTestAlgebra}
    (E : AnalyticCore.SourceEvaluationData A)
    {W : WeilFormSymbols}
    (common : CommonSourceTest.ConcreteCommonSourceTest W) (n : ℕ)
    (pairingReadOff :
      W.primePowerPairing n common.sourceTest common.sourceTest =
        (1 / Real.sqrt (n : ℝ)) *
          (E.legacyValueAt common.sourceConvolutionSquare
              (PrimePowerEvaluation.SourceForwardPoint n) +
            E.legacyValueAt common.sourceConvolutionSquare
              (PrimePowerEvaluation.SourceInversePoint n))) :
    (ofSourceEvaluationData E common n pairingReadOff).model.sourceEvaluation =
      (ofSourceEvaluationData E common n pairingReadOff).concreteEvaluation.model :=
  rfl

@[simp] theorem ofSourceEvaluationData_pairingReadOff
    {A : AnalyticCore.SourceTestAlgebra}
    (E : AnalyticCore.SourceEvaluationData A)
    {W : WeilFormSymbols}
    (common : CommonSourceTest.ConcreteCommonSourceTest W) (n : ℕ)
    (pairingReadOff :
      W.primePowerPairing n common.sourceTest common.sourceTest =
        (1 / Real.sqrt (n : ℝ)) *
          (E.legacyValueAt common.sourceConvolutionSquare
              (PrimePowerEvaluation.SourceForwardPoint n) +
            E.legacyValueAt common.sourceConvolutionSquare
              (PrimePowerEvaluation.SourceInversePoint n))) :
    W.primePowerPairing n common.sourceTest common.sourceTest =
      (ofSourceEvaluationData E common n pairingReadOff).model.sourceTPairing :=
  pairingReadOff

theorem ofSourceEvaluationData_pairing_formula
    {A : AnalyticCore.SourceTestAlgebra}
    (E : AnalyticCore.SourceEvaluationData A)
    {W : WeilFormSymbols}
    (common : CommonSourceTest.ConcreteCommonSourceTest W) (n : ℕ)
    (pairingReadOff :
      W.primePowerPairing n common.sourceTest common.sourceTest =
        (1 / Real.sqrt (n : ℝ)) *
          (E.legacyValueAt common.sourceConvolutionSquare
              (PrimePowerEvaluation.SourceForwardPoint n) +
            E.legacyValueAt common.sourceConvolutionSquare
              (PrimePowerEvaluation.SourceInversePoint n))) :
    W.primePowerPairing n common.sourceTest common.sourceTest =
      (1 / Real.sqrt (n : ℝ)) *
        (E.valueAt (A.legacy.decode common.sourceConvolutionSquare)
            (PrimePowerEvaluation.SourceForwardPoint n) +
          E.valueAt (A.legacy.decode common.sourceConvolutionSquare)
            (PrimePowerEvaluation.SourceInversePoint n)) := by
  simpa using pairingReadOff

end ConcreteCommonPrimePowerPairingData

end PrimePowerPairing

end CCM25Concrete
end Source
end ConnesWeilRH
