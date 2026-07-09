/-
Copyright (c) 2026 ConnesWeilRH contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ConnesWeilRH contributors
-/

import ConnesWeilRH.Source.CCM25Concrete.FinitePrimeSourceData
import ConnesWeilRH.Source.CCM25Concrete.PrimePowerArithmeticBridge
import ConnesWeilRH.Source.AnalyticCore

/-!
# Analytic bridge for CCM25 finite-prime source data

This module keeps the `AnalyticCore` and source-evaluation adapters downstream
of the low-level finite-prime source records.  The split prevents the source
object boundary from importing analytic bridge modules through
`FinitePrimeSourceData`.
-/

namespace ConnesWeilRH
namespace Source
namespace CCM25Concrete
namespace FinitePrimeSourceData

structure FixedLambdaSourceEvaluationVisibleArithmeticData
    {A : AnalyticCore.SourceTestAlgebra}
    (E : AnalyticCore.SourceEvaluationData A)
    (W : WeilFormSymbols)
    (common : CommonSourceTest.ConcreteCommonSourceTest W)
    (lambda : ℝ) where
  sourcePrimePowerIndex :
    ∀ n : ℕ,
      common.toSourceTestEvaluationInterface.sourceAtomVisible n →
        IsPrimePow n
  visible :
    ∀ n : ℕ,
      common.toSourceTestEvaluationInterface.sourceAtomVisible n →
        W.finitePrimeAtomVisible n
          (W.convolutionStar common.sourceTest common.sourceTest)
  pairingReadOff :
    ∀ n : ℕ,
      common.toSourceTestEvaluationInterface.sourceAtomVisible n →
        W.primePowerPairing n common.sourceTest common.sourceTest =
          (1 / Real.sqrt (n : ℝ)) *
            (E.legacyValueAt common.sourceConvolutionSquare
                (PrimePowerEvaluation.SourceForwardPoint n) +
              E.legacyValueAt common.sourceConvolutionSquare
                (PrimePowerEvaluation.SourceInversePoint n))
  weightReadOff :
    ∀ n : ℕ,
      common.toSourceTestEvaluationInterface.sourceAtomVisible n →
      W.vonMangoldtWeight n =
          ArithmeticFunction.vonMangoldt n
  termReadOff :
    ∀ n : ℕ,
      common.toSourceTestEvaluationInterface.sourceAtomVisible n →
        W.finitePrimeTerm n
            (W.convolutionStar common.sourceTest common.sourceTest) =
          ArithmeticFunction.vonMangoldt n *
            ((1 / Real.sqrt (n : ℝ)) *
              (E.legacyValueAt common.sourceConvolutionSquare
                  (PrimePowerEvaluation.SourceForwardPoint n) +
                E.legacyValueAt common.sourceConvolutionSquare
                  (PrimePowerEvaluation.SourceInversePoint n)))

namespace FixedLambdaSourceEvaluationVisibleArithmeticData

noncomputable def visibleArithmeticData
    {A : AnalyticCore.SourceTestAlgebra}
    {E : AnalyticCore.SourceEvaluationData A}
    {W : WeilFormSymbols}
    {common : CommonSourceTest.ConcreteCommonSourceTest W}
    {lambda : ℝ}
    (data :
      FixedLambdaSourceEvaluationVisibleArithmeticData E W common lambda) :
    PrimePowerArithmetic.SourceVisibleFinitePrimeArithmeticData
      W common.sourceTest common.sourceTest
      common.toSourceTestEvaluationInterface :=
  PrimePowerArithmetic.SourceVisibleFinitePrimeArithmeticData.ofSourceEvaluationData
    E common data.sourcePrimePowerIndex data.visible data.pairingReadOff
    data.weightReadOff data.termReadOff

@[simp] theorem visibleArithmeticData_atVisibleIndex
    {A : AnalyticCore.SourceTestAlgebra}
    {E : AnalyticCore.SourceEvaluationData A}
    {W : WeilFormSymbols}
    {common : CommonSourceTest.ConcreteCommonSourceTest W}
    {lambda : ℝ}
    (data :
      FixedLambdaSourceEvaluationVisibleArithmeticData E W common lambda)
    {n : ℕ}
    (hn : common.toSourceTestEvaluationInterface.sourceAtomVisible n) :
    (data.visibleArithmeticData).atVisibleIndex n hn =
      PrimePowerArithmetic.SourceFinitePrimeArithmeticData.ofSourceEvaluationData
        E common n (data.sourcePrimePowerIndex n hn) (data.visible n hn)
        (data.pairingReadOff n hn) (data.weightReadOff n hn)
        (data.termReadOff n hn) :=
  rfl

theorem pairing_formula
    {A : AnalyticCore.SourceTestAlgebra}
    {E : AnalyticCore.SourceEvaluationData A}
    {W : WeilFormSymbols}
    {common : CommonSourceTest.ConcreteCommonSourceTest W}
    {lambda : ℝ}
    (data :
      FixedLambdaSourceEvaluationVisibleArithmeticData E W common lambda)
    {n : ℕ}
    (hn : common.toSourceTestEvaluationInterface.sourceAtomVisible n) :
    W.primePowerPairing n common.sourceTest common.sourceTest =
      (1 / Real.sqrt (n : ℝ)) *
        (E.valueAt (A.legacy.decode common.sourceConvolutionSquare)
            (PrimePowerEvaluation.SourceForwardPoint n) +
          E.valueAt (A.legacy.decode common.sourceConvolutionSquare)
            (PrimePowerEvaluation.SourceInversePoint n)) :=
  PrimePowerArithmetic.SourceVisibleFinitePrimeArithmeticData.ofSourceEvaluationData_pairing_formula
    E common data.pairingReadOff hn

end FixedLambdaSourceEvaluationVisibleArithmeticData

structure FixedLambdaSourceWeilFormVisibleArithmeticData
    {A : AnalyticCore.SourceTestAlgebra}
    (W : AnalyticCore.SourceWeilFormData A)
    (common :
      CommonSourceTest.ConcreteCommonSourceTest W.toWeilFormSymbols)
    (lambda : ℝ) where
  oneLtLambda : 1 < lambda

namespace FixedLambdaSourceWeilFormVisibleArithmeticData

theorem globalExact
    {A : AnalyticCore.SourceTestAlgebra}
    {W : AnalyticCore.SourceWeilFormData A}
    {common :
      CommonSourceTest.ConcreteCommonSourceTest W.toWeilFormSymbols}
    {lambda : ℝ}
    (_data :
      FixedLambdaSourceWeilFormVisibleArithmeticData W common lambda) :
    ∀ n : ℕ,
      n ∈ W.toWeilFormSymbols.globalPrimeIndexSet ↔
        PrimePowerSupport.SourceGlobalIndexData
          W.toWeilFormSymbols common.sourceTest common.sourceTest n :=
  fun n => by
    constructor
    · intro hn
      have hExact :=
        (W.toWeilFormSymbols_globalPrimeIndex_exact
          (W.toWeilFormSymbols.convolutionStar
            common.sourceTest common.sourceTest) n).1 hn
      exact
        { primePowerIndex := hExact.1
          atomVisible := hExact.2 }
    · intro hdata
      exact
        W.toWeilFormSymbols_globalPrimeIndex_mem_of_primePower_visible
          (W.toWeilFormSymbols.convolutionStar
            common.sourceTest common.sourceTest)
          hdata.primePowerIndex
          ((common.route_visibility_iff_source_visibility n).2
            hdata.atomVisible)

theorem restrictedExact
    {A : AnalyticCore.SourceTestAlgebra}
    {W : AnalyticCore.SourceWeilFormData A}
    {common :
      CommonSourceTest.ConcreteCommonSourceTest W.toWeilFormSymbols}
    {lambda : ℝ}
    (data :
      FixedLambdaSourceWeilFormVisibleArithmeticData W common lambda) :
    ∀ n : ℕ,
      n ∈ W.toWeilFormSymbols.restrictedPrimeIndexSet lambda ↔
        PrimePowerSupport.SourceRestrictedIndexData
          W.toWeilFormSymbols common.sourceTest common.sourceTest lambda n :=
  fun n => by
    constructor
    · intro hn
      have hExact :=
        (W.toWeilFormSymbols_restrictedPrimeIndex_exact lambda
          (W.toWeilFormSymbols.convolutionStar
            common.sourceTest common.sourceTest) n).1 hn
      exact
        { primePowerIndex := hExact.1
          atomVisible := hExact.2.1
          lambdaCut := hExact.2.2 }
    · intro hdata
      exact
        W.toWeilFormSymbols_restrictedPrimeIndex_mem_of_visible
          lambda
          data.oneLtLambda
          (W.toWeilFormSymbols.convolutionStar
            common.sourceTest common.sourceTest)
          hdata.atomVisible
          hdata.lambdaCut.1 hdata.lambdaCut.2

theorem visible
    {A : AnalyticCore.SourceTestAlgebra}
    {W : AnalyticCore.SourceWeilFormData A}
    {common :
      CommonSourceTest.ConcreteCommonSourceTest W.toWeilFormSymbols}
    {lambda : ℝ}
    (_data :
      FixedLambdaSourceWeilFormVisibleArithmeticData W common lambda)
    (n : ℕ)
    (hn : common.toSourceTestEvaluationInterface.sourceAtomVisible n) :
    W.toWeilFormSymbols.finitePrimeAtomVisible n
      (W.toWeilFormSymbols.convolutionStar
        common.sourceTest common.sourceTest) :=
  (CommonSourceTest.ConcreteCommonSourceTest.route_visibility_iff_source_visibility
    common n).2 hn

theorem mathlibSourcePrimePowerIndex
    {A : AnalyticCore.SourceTestAlgebra}
    {W : AnalyticCore.SourceWeilFormData A}
    {common :
      CommonSourceTest.ConcreteCommonSourceTest W.toWeilFormSymbols}
    {lambda : ℝ}
    (data :
      FixedLambdaSourceWeilFormVisibleArithmeticData W common lambda)
    (n : ℕ)
    (hn : common.toSourceTestEvaluationInterface.sourceAtomVisible n) :
    IsPrimePow n :=
  AnalyticCore.SourceWeilFormData.toWeilFormSymbols_finitePrimeAtomVisible_primePower
    W (W.toWeilFormSymbols.convolutionStar common.sourceTest common.sourceTest)
    (data.visible n hn)

theorem sourcePrimePowerIndex
    {A : AnalyticCore.SourceTestAlgebra}
    {W : AnalyticCore.SourceWeilFormData A}
    {common :
      CommonSourceTest.ConcreteCommonSourceTest W.toWeilFormSymbols}
    {lambda : ℝ}
    (data :
      FixedLambdaSourceWeilFormVisibleArithmeticData W common lambda)
    (n : ℕ)
    (hn : common.toSourceTestEvaluationInterface.sourceAtomVisible n) :
    IsPrimePow n :=
  data.mathlibSourcePrimePowerIndex n hn

theorem weightReadOff
    {A : AnalyticCore.SourceTestAlgebra}
    {W : AnalyticCore.SourceWeilFormData A}
    {common :
      CommonSourceTest.ConcreteCommonSourceTest W.toWeilFormSymbols}
    {lambda : ℝ}
    (_data :
      FixedLambdaSourceWeilFormVisibleArithmeticData W common lambda)
    (n : ℕ)
    (_hn : common.toSourceTestEvaluationInterface.sourceAtomVisible n) :
    W.toWeilFormSymbols.vonMangoldtWeight n =
      ArithmeticFunction.vonMangoldt n :=
  AnalyticCore.SourceWeilFormData.toWeilFormSymbols_vonMangoldtWeight_eq_arithmetic
    W n

theorem pairingReadOff
    {A : AnalyticCore.SourceTestAlgebra}
    {W : AnalyticCore.SourceWeilFormData A}
    {common :
      CommonSourceTest.ConcreteCommonSourceTest W.toWeilFormSymbols}
    {lambda : ℝ}
    (_data :
      FixedLambdaSourceWeilFormVisibleArithmeticData W common lambda)
    (n : ℕ)
    (_hn : common.toSourceTestEvaluationInterface.sourceAtomVisible n) :
    W.toWeilFormSymbols.primePowerPairing n
        common.sourceTest common.sourceTest =
      (1 / Real.sqrt (n : ℝ)) *
        (W.evaluation.legacyValueAt common.sourceConvolutionSquare
            (PrimePowerEvaluation.SourceForwardPoint n) +
          W.evaluation.legacyValueAt common.sourceConvolutionSquare
            (PrimePowerEvaluation.SourceInversePoint n)) := by
  rw [AnalyticCore.SourceWeilFormData.toWeilFormSymbols_primePowerPairing,
    AnalyticCore.SourceFinitePrimeData.primePowerPairing_eq_evaluation,
    AnalyticCore.SourceEvaluationData.sourcePrimePowerPairing_eq_valueAt,
    PrimePowerEvaluation.source_forward_point_eq_nat_cast,
    PrimePowerEvaluation.source_inverse_point_eq_inv_nat_cast,
    common.source_convolution_square_read_off,
    AnalyticCore.SourceWeilFormData.toWeilFormSymbols_convolutionStar]
  simp [AnalyticCore.SourceEvaluationData.legacyValueAt]

theorem termReadOff
    {A : AnalyticCore.SourceTestAlgebra}
    {W : AnalyticCore.SourceWeilFormData A}
    {common :
      CommonSourceTest.ConcreteCommonSourceTest W.toWeilFormSymbols}
    {lambda : ℝ}
    (data :
      FixedLambdaSourceWeilFormVisibleArithmeticData W common lambda)
    (n : ℕ)
    (hn : common.toSourceTestEvaluationInterface.sourceAtomVisible n) :
    W.toWeilFormSymbols.finitePrimeTerm n
        (W.toWeilFormSymbols.convolutionStar
          common.sourceTest common.sourceTest) =
      ArithmeticFunction.vonMangoldt n *
        ((1 / Real.sqrt (n : ℝ)) *
          (W.evaluation.legacyValueAt common.sourceConvolutionSquare
              (PrimePowerEvaluation.SourceForwardPoint n) +
            W.evaluation.legacyValueAt common.sourceConvolutionSquare
              (PrimePowerEvaluation.SourceInversePoint n))) := by
  rw [AnalyticCore.SourceWeilFormData.toWeilFormSymbols_finitePrimeTerm_convolutionStar,
    data.weightReadOff n hn, data.pairingReadOff n hn]

noncomputable def toSourceEvaluationVisibleArithmeticData
    {A : AnalyticCore.SourceTestAlgebra}
    {W : AnalyticCore.SourceWeilFormData A}
    {common :
      CommonSourceTest.ConcreteCommonSourceTest W.toWeilFormSymbols}
    {lambda : ℝ}
    (data :
      FixedLambdaSourceWeilFormVisibleArithmeticData W common lambda) :
    FixedLambdaSourceEvaluationVisibleArithmeticData
      W.evaluation W.toWeilFormSymbols common lambda where
  sourcePrimePowerIndex := data.sourcePrimePowerIndex
  visible := data.visible
  pairingReadOff := data.pairingReadOff
  weightReadOff := data.weightReadOff
  termReadOff := data.termReadOff

@[simp] theorem toSourceEvaluationVisibleArithmeticData_weightReadOff
    {A : AnalyticCore.SourceTestAlgebra}
    {W : AnalyticCore.SourceWeilFormData A}
    {common :
      CommonSourceTest.ConcreteCommonSourceTest W.toWeilFormSymbols}
    {lambda : ℝ}
    (data :
      FixedLambdaSourceWeilFormVisibleArithmeticData W common lambda)
    {n : ℕ}
    (hn : common.toSourceTestEvaluationInterface.sourceAtomVisible n) :
    (data.toSourceEvaluationVisibleArithmeticData).weightReadOff n hn =
      data.weightReadOff n hn :=
  rfl

end FixedLambdaSourceWeilFormVisibleArithmeticData

namespace FixedLambdaArithmeticCertificateSourceTestData

noncomputable def ofSourceEvaluationVisibleData
    {A : AnalyticCore.SourceTestAlgebra}
    {E : AnalyticCore.SourceEvaluationData A}
    {W : WeilFormSymbols}
    {common : CommonSourceTest.ConcreteCommonSourceTest W}
    {lambda : ℝ}
    (supportData :
      FixedLambdaCommonFinitePrimeSupportData W common lambda)
    (visibleData :
      FixedLambdaSourceEvaluationVisibleArithmeticData E W common lambda)
    (atoms :
      PrimePowerArithmetic.SourceFinitePrimeArithmeticNormalizationForSourceTest
        W common.sourceTest common.sourceTest
        common.toSourceTestEvaluationInterface) :
    FixedLambdaArithmeticCertificateSourceTestData
      W common.sourceTest common.sourceTest lambda
      common.toSourceTestEvaluationInterface where
  globalIndexData := by
    intro n hn
    exact supportData.globalIndexData n hn
  routeVisibleGlobalIndex := by
    intro n hvisible
    exact supportData.routeVisibleGlobalIndex n hvisible
  restrictedIndexData := by
    intro n hn
    exact supportData.restrictedIndexData n hn
  routeVisibleRestrictedIndex := by
    intro n hvisible hOne hCutoff
    exact supportData.routeVisibleRestrictedIndex n hvisible hOne hCutoff
  visibleArithmeticData := visibleData.visibleArithmeticData
  atoms := atoms

@[simp] theorem ofSourceEvaluationVisibleData_sourceVisibleArithmeticData
    {A : AnalyticCore.SourceTestAlgebra}
    {E : AnalyticCore.SourceEvaluationData A}
    {W : WeilFormSymbols}
    {common : CommonSourceTest.ConcreteCommonSourceTest W}
    {lambda : ℝ}
    (supportData :
      FixedLambdaCommonFinitePrimeSupportData W common lambda)
    (visibleData :
      FixedLambdaSourceEvaluationVisibleArithmeticData E W common lambda)
    (atoms :
      PrimePowerArithmetic.SourceFinitePrimeArithmeticNormalizationForSourceTest
        W common.sourceTest common.sourceTest
        common.toSourceTestEvaluationInterface)
    {n : ℕ}
    (hn : common.toSourceTestEvaluationInterface.sourceAtomVisible n) :
    ((ofSourceEvaluationVisibleData supportData visibleData atoms).sourceVisibleArithmeticData
      n hn) =
      PrimePowerArithmetic.SourceFinitePrimeArithmeticData.ofSourceEvaluationData
        E common n (visibleData.sourcePrimePowerIndex n hn)
        (visibleData.visible n hn) (visibleData.pairingReadOff n hn)
        (visibleData.weightReadOff n hn) (visibleData.termReadOff n hn) :=
  rfl

noncomputable def ofSourceWeilFormVisibleData
    {A : AnalyticCore.SourceTestAlgebra}
    {W : AnalyticCore.SourceWeilFormData A}
    {common : CommonSourceTest.ConcreteCommonSourceTest W.toWeilFormSymbols}
    {lambda : ℝ}
    (supportData :
      FixedLambdaCommonFinitePrimeSupportData W.toWeilFormSymbols common lambda)
    (visibleData :
      FixedLambdaSourceWeilFormVisibleArithmeticData W common lambda)
    (atoms :
      PrimePowerArithmetic.SourceFinitePrimeArithmeticNormalizationForSourceTest
        W.toWeilFormSymbols common.sourceTest common.sourceTest
        common.toSourceTestEvaluationInterface) :
    FixedLambdaArithmeticCertificateSourceTestData
      W.toWeilFormSymbols common.sourceTest common.sourceTest lambda
      common.toSourceTestEvaluationInterface :=
  ofSourceEvaluationVisibleData supportData
    visibleData.toSourceEvaluationVisibleArithmeticData atoms

@[simp] theorem ofSourceWeilFormVisibleData_sourceVisibleArithmeticData
    {A : AnalyticCore.SourceTestAlgebra}
    {W : AnalyticCore.SourceWeilFormData A}
    {common : CommonSourceTest.ConcreteCommonSourceTest W.toWeilFormSymbols}
    {lambda : ℝ}
    (supportData :
      FixedLambdaCommonFinitePrimeSupportData W.toWeilFormSymbols common lambda)
    (visibleData :
      FixedLambdaSourceWeilFormVisibleArithmeticData W common lambda)
    (atoms :
      PrimePowerArithmetic.SourceFinitePrimeArithmeticNormalizationForSourceTest
        W.toWeilFormSymbols common.sourceTest common.sourceTest
        common.toSourceTestEvaluationInterface)
    {n : ℕ}
    (hn : common.toSourceTestEvaluationInterface.sourceAtomVisible n) :
    ((ofSourceWeilFormVisibleData supportData visibleData atoms).sourceVisibleArithmeticData
      n hn) =
      PrimePowerArithmetic.SourceFinitePrimeArithmeticData.ofSourceEvaluationData
        W.evaluation common n (visibleData.sourcePrimePowerIndex n hn)
        (visibleData.visible n hn) (visibleData.pairingReadOff n hn)
        (visibleData.weightReadOff n hn) (visibleData.termReadOff n hn) :=
  rfl

theorem ofSourceWeilFormVisibleData_sourceVisibleArithmeticData_mathlibIndex
    {A : AnalyticCore.SourceTestAlgebra}
    {W : AnalyticCore.SourceWeilFormData A}
    {common : CommonSourceTest.ConcreteCommonSourceTest W.toWeilFormSymbols}
    {lambda : ℝ}
    (supportData :
      FixedLambdaCommonFinitePrimeSupportData W.toWeilFormSymbols common lambda)
    (visibleData :
      FixedLambdaSourceWeilFormVisibleArithmeticData W common lambda)
    (atoms :
      PrimePowerArithmetic.SourceFinitePrimeArithmeticNormalizationForSourceTest
        W.toWeilFormSymbols common.sourceTest common.sourceTest
        common.toSourceTestEvaluationInterface)
    {n : ℕ}
    (hn : common.toSourceTestEvaluationInterface.sourceAtomVisible n) :
    ((ofSourceWeilFormVisibleData supportData visibleData atoms).sourceVisibleArithmeticData
      n hn) =
      PrimePowerArithmetic.SourceFinitePrimeArithmeticData.ofSourceEvaluationData
        W.evaluation common n
        (visibleData.mathlibSourcePrimePowerIndex n hn)
        (visibleData.visible n hn) (visibleData.pairingReadOff n hn)
        (visibleData.weightReadOff n hn) (visibleData.termReadOff n hn) :=
  rfl

end FixedLambdaArithmeticCertificateSourceTestData

end FinitePrimeSourceData
end CCM25Concrete
end Source
end ConnesWeilRH
