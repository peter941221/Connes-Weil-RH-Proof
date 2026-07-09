/-
Copyright (c) 2026 ConnesWeilRH contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ConnesWeilRH contributors
-/

import ConnesWeilRH.Source.CCM25Concrete.FinitePrimeSourceData
import ConnesWeilRH.Source.CCM25Concrete.PrimePowerArithmeticBridge
import ConnesWeilRH.Source.AnalyticCore
import ConnesWeilRH.Source.CC20ConcreteTestSpace

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

noncomputable def toSupportData
    {A : AnalyticCore.SourceTestAlgebra}
    {W : AnalyticCore.SourceWeilFormData A}
    {common :
      CommonSourceTest.ConcreteCommonSourceTest W.toWeilFormSymbols}
    {lambda : ℝ}
    (data :
      FixedLambdaSourceWeilFormVisibleArithmeticData W common lambda) :
    FixedLambdaCommonFinitePrimeSupportData W.toWeilFormSymbols common lambda where
  globalIndexData := fun n hn => (data.globalExact n).1 hn
  routeVisibleGlobalIndex := by
    intro n hvisible
    have hsourceVisible :
        common.toSourceTestEvaluationInterface.sourceAtomVisible n :=
      (common.route_visibility_iff_source_visibility n).1 hvisible
    exact
      (data.globalExact n).2
        { primePowerIndex :=
            data.mathlibSourcePrimePowerIndex n hsourceVisible
          atomVisible := hsourceVisible }
  restrictedIndexData := fun n hn => (data.restrictedExact n).1 hn
  routeVisibleRestrictedIndex := by
    intro n hvisible hOne hCutoff
    have hsourceVisible :
        common.toSourceTestEvaluationInterface.sourceAtomVisible n :=
      (common.route_visibility_iff_source_visibility n).1 hvisible
    exact
      (data.restrictedExact n).2
        { primePowerIndex :=
            data.mathlibSourcePrimePowerIndex n hsourceVisible
          atomVisible := hsourceVisible
          lambdaCut := ⟨hOne, hCutoff⟩ }

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

@[simp] theorem ofSourceEvaluationVisibleData_visibleArithmeticData
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
    (ofSourceEvaluationVisibleData supportData visibleData atoms).visibleArithmeticData =
      visibleData.visibleArithmeticData :=
  rfl

@[simp] theorem ofSourceEvaluationVisibleData_atoms
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
    (ofSourceEvaluationVisibleData supportData visibleData atoms).atoms = atoms :=
  rfl

structure FixedLambdaSourceEvaluationCanonicalAtomNormalization
    {A : AnalyticCore.SourceTestAlgebra}
    {E : AnalyticCore.SourceEvaluationData A}
    {W : WeilFormSymbols}
    {common : CommonSourceTest.ConcreteCommonSourceTest W}
    {lambda : ℝ}
    (visibleData :
      FixedLambdaSourceEvaluationVisibleArithmeticData E W common lambda) where
  atoms :
    PrimePowerArithmetic.SourceFinitePrimeArithmeticNormalizationForSourceTest
      W common.sourceTest common.sourceTest
      common.toSourceTestEvaluationInterface
  visibleReadOff :
    (fun n hn => (atoms.atIndex n).data) =
      (fun n hn => visibleData.visibleArithmeticData.atVisibleIndex n hn)

noncomputable def ofSourceEvaluationVisibleCanonicalData
    {A : AnalyticCore.SourceTestAlgebra}
    {E : AnalyticCore.SourceEvaluationData A}
    {W : WeilFormSymbols}
    {common : CommonSourceTest.ConcreteCommonSourceTest W}
    {lambda : ℝ}
    (supportData :
      FixedLambdaCommonFinitePrimeSupportData W common lambda)
    (visibleData :
      FixedLambdaSourceEvaluationVisibleArithmeticData E W common lambda)
    (canonicalAtoms :
      FixedLambdaSourceEvaluationCanonicalAtomNormalization visibleData) :
    FixedLambdaArithmeticCertificateSourceTestData
      W common.sourceTest common.sourceTest lambda
      common.toSourceTestEvaluationInterface :=
  ofSourceEvaluationVisibleData supportData visibleData canonicalAtoms.atoms

@[simp] theorem ofSourceEvaluationVisibleCanonicalData_visibleArithmeticData
    {A : AnalyticCore.SourceTestAlgebra}
    {E : AnalyticCore.SourceEvaluationData A}
    {W : WeilFormSymbols}
    {common : CommonSourceTest.ConcreteCommonSourceTest W}
    {lambda : ℝ}
    (supportData :
      FixedLambdaCommonFinitePrimeSupportData W common lambda)
    (visibleData :
      FixedLambdaSourceEvaluationVisibleArithmeticData E W common lambda)
    (canonicalAtoms :
      FixedLambdaSourceEvaluationCanonicalAtomNormalization visibleData) :
    (ofSourceEvaluationVisibleCanonicalData supportData visibleData
        canonicalAtoms).visibleArithmeticData =
      visibleData.visibleArithmeticData :=
  rfl

@[simp] theorem ofSourceEvaluationVisibleCanonicalData_atoms
    {A : AnalyticCore.SourceTestAlgebra}
    {E : AnalyticCore.SourceEvaluationData A}
    {W : WeilFormSymbols}
    {common : CommonSourceTest.ConcreteCommonSourceTest W}
    {lambda : ℝ}
    (supportData :
      FixedLambdaCommonFinitePrimeSupportData W common lambda)
    (visibleData :
      FixedLambdaSourceEvaluationVisibleArithmeticData E W common lambda)
    (canonicalAtoms :
      FixedLambdaSourceEvaluationCanonicalAtomNormalization visibleData) :
    (ofSourceEvaluationVisibleCanonicalData supportData visibleData
        canonicalAtoms).atoms =
      canonicalAtoms.atoms :=
  rfl

theorem ofSourceEvaluationVisibleCanonicalData_directAtomVisibleFunctionReadOff
    {A : AnalyticCore.SourceTestAlgebra}
    {E : AnalyticCore.SourceEvaluationData A}
    {W : WeilFormSymbols}
    {common : CommonSourceTest.ConcreteCommonSourceTest W}
    {lambda : ℝ}
    (supportData :
      FixedLambdaCommonFinitePrimeSupportData W common lambda)
    (visibleData :
      FixedLambdaSourceEvaluationVisibleArithmeticData E W common lambda)
    (canonicalAtoms :
      FixedLambdaSourceEvaluationCanonicalAtomNormalization visibleData) :
    FixedLambdaArithmeticCertificateSourceTestData.DirectAtomVisibleFunctionReadOff
      (ofSourceEvaluationVisibleCanonicalData supportData visibleData
        canonicalAtoms) :=
  canonicalAtoms.visibleReadOff

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

@[simp] theorem ofSourceWeilFormVisibleData_visibleArithmeticData
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
    (ofSourceWeilFormVisibleData supportData visibleData atoms).visibleArithmeticData =
      visibleData.toSourceEvaluationVisibleArithmeticData.visibleArithmeticData :=
  rfl

@[simp] theorem ofSourceWeilFormVisibleData_atoms
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
    (ofSourceWeilFormVisibleData supportData visibleData atoms).atoms = atoms :=
  rfl

abbrev FixedLambdaSourceWeilFormCanonicalAtomNormalization
    {A : AnalyticCore.SourceTestAlgebra}
    {W : AnalyticCore.SourceWeilFormData A}
    {common : CommonSourceTest.ConcreteCommonSourceTest W.toWeilFormSymbols}
    {lambda : ℝ}
    (visibleData :
      FixedLambdaSourceWeilFormVisibleArithmeticData W common lambda) :=
  FixedLambdaSourceEvaluationCanonicalAtomNormalization
    visibleData.toSourceEvaluationVisibleArithmeticData

noncomputable def ofSourceWeilFormVisibleCanonicalData
    {A : AnalyticCore.SourceTestAlgebra}
    {W : AnalyticCore.SourceWeilFormData A}
    {common : CommonSourceTest.ConcreteCommonSourceTest W.toWeilFormSymbols}
    {lambda : ℝ}
    (supportData :
      FixedLambdaCommonFinitePrimeSupportData W.toWeilFormSymbols common lambda)
    (visibleData :
      FixedLambdaSourceWeilFormVisibleArithmeticData W common lambda)
    (canonicalAtoms :
      FixedLambdaSourceWeilFormCanonicalAtomNormalization visibleData) :
    FixedLambdaArithmeticCertificateSourceTestData
      W.toWeilFormSymbols common.sourceTest common.sourceTest lambda
      common.toSourceTestEvaluationInterface :=
  ofSourceEvaluationVisibleCanonicalData supportData
    visibleData.toSourceEvaluationVisibleArithmeticData canonicalAtoms

@[simp] theorem ofSourceWeilFormVisibleCanonicalData_visibleArithmeticData
    {A : AnalyticCore.SourceTestAlgebra}
    {W : AnalyticCore.SourceWeilFormData A}
    {common : CommonSourceTest.ConcreteCommonSourceTest W.toWeilFormSymbols}
    {lambda : ℝ}
    (supportData :
      FixedLambdaCommonFinitePrimeSupportData W.toWeilFormSymbols common lambda)
    (visibleData :
      FixedLambdaSourceWeilFormVisibleArithmeticData W common lambda)
    (canonicalAtoms :
      FixedLambdaSourceWeilFormCanonicalAtomNormalization visibleData) :
    (ofSourceWeilFormVisibleCanonicalData supportData visibleData
        canonicalAtoms).visibleArithmeticData =
      visibleData.toSourceEvaluationVisibleArithmeticData.visibleArithmeticData :=
  rfl

@[simp] theorem ofSourceWeilFormVisibleCanonicalData_atoms
    {A : AnalyticCore.SourceTestAlgebra}
    {W : AnalyticCore.SourceWeilFormData A}
    {common : CommonSourceTest.ConcreteCommonSourceTest W.toWeilFormSymbols}
    {lambda : ℝ}
    (supportData :
      FixedLambdaCommonFinitePrimeSupportData W.toWeilFormSymbols common lambda)
    (visibleData :
      FixedLambdaSourceWeilFormVisibleArithmeticData W common lambda)
    (canonicalAtoms :
      FixedLambdaSourceWeilFormCanonicalAtomNormalization visibleData) :
    (ofSourceWeilFormVisibleCanonicalData supportData visibleData
        canonicalAtoms).atoms =
      canonicalAtoms.atoms :=
  rfl

theorem ofSourceWeilFormVisibleCanonicalData_directAtomVisibleFunctionReadOff
    {A : AnalyticCore.SourceTestAlgebra}
    {W : AnalyticCore.SourceWeilFormData A}
    {common : CommonSourceTest.ConcreteCommonSourceTest W.toWeilFormSymbols}
    {lambda : ℝ}
    (supportData :
      FixedLambdaCommonFinitePrimeSupportData W.toWeilFormSymbols common lambda)
    (visibleData :
      FixedLambdaSourceWeilFormVisibleArithmeticData W common lambda)
    (canonicalAtoms :
      FixedLambdaSourceWeilFormCanonicalAtomNormalization visibleData) :
    FixedLambdaArithmeticCertificateSourceTestData.DirectAtomVisibleFunctionReadOff
      (ofSourceWeilFormVisibleCanonicalData supportData visibleData
        canonicalAtoms) :=
  canonicalAtoms.visibleReadOff

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

/-- Data-bearing source owner for route-common finite-prime certificates.

This wrapper does not claim that every `(f,g)` certificate in the underlying
source-data owner is canonical.  It records the sharper provenance needed by
the square route: for the selected common test, each fixed-lambda certificate
is generated from same-symbol source-Weil-form visible data and a full
canonical atom normalization. -/
structure CanonicalSourceWeilFormSourceDataOwner
    (W : WeilFormSymbols) (commonTestFunction : TestFunction) where
  sourceDataOwner : CommonFinitePrimeArithmeticSourceData W
  sourceDataOwner_commonTestFunction :
    sourceDataOwner.commonTestFunction = commonTestFunction
  A : AnalyticCore.SourceTestAlgebra
  sourceWeilForm : AnalyticCore.SourceWeilFormData A
  sameSymbols : W = sourceWeilForm.toWeilFormSymbols
  supportData :
    ∀ lambda : ℝ, 1 < lambda →
      FixedLambdaCommonFinitePrimeSupportData W
        (CommonSourceTest.concreteCommonSourceTest W commonTestFunction)
        lambda
  visibleData :
    ∀ lambda : ℝ, 1 < lambda →
      FixedLambdaSourceEvaluationVisibleArithmeticData
        sourceWeilForm.evaluation W
        (CommonSourceTest.concreteCommonSourceTest W commonTestFunction)
        lambda
  canonicalAtoms :
    ∀ lambda : ℝ, ∀ hlambda : 1 < lambda,
      FixedLambdaArithmeticCertificateSourceTestData.FixedLambdaSourceEvaluationCanonicalAtomNormalization
        (visibleData lambda hlambda)
  certificateData :
    ∀ lambda : ℝ, ∀ hlambda : 1 < lambda,
      HEq
        (sourceDataOwner.finitePrimeData.certificateData
          commonTestFunction commonTestFunction lambda hlambda)
        (FixedLambdaArithmeticCertificateSourceTestData.ofSourceEvaluationVisibleCanonicalData
          (supportData lambda hlambda)
          (visibleData lambda hlambda)
          (canonicalAtoms lambda hlambda))

namespace CanonicalSourceWeilFormSourceDataOwner

noncomputable def ofSourceWeilFormVisibleCanonicalData
    {W : WeilFormSymbols} {commonTestFunction : TestFunction}
    (sourceDataOwner : CommonFinitePrimeArithmeticSourceData W)
    (sourceDataOwner_commonTestFunction :
      sourceDataOwner.commonTestFunction = commonTestFunction)
    {A : AnalyticCore.SourceTestAlgebra}
    (sourceWeilForm : AnalyticCore.SourceWeilFormData A)
    (sameSymbols : W = sourceWeilForm.toWeilFormSymbols)
    (supportData :
      ∀ lambda : ℝ, 1 < lambda →
        FixedLambdaCommonFinitePrimeSupportData W
          (CommonSourceTest.concreteCommonSourceTest W commonTestFunction)
          lambda)
    (visibleData :
      ∀ lambda : ℝ, 1 < lambda →
        FixedLambdaSourceEvaluationVisibleArithmeticData
          sourceWeilForm.evaluation W
          (CommonSourceTest.concreteCommonSourceTest W commonTestFunction)
          lambda)
    (canonicalAtoms :
      ∀ lambda : ℝ, ∀ hlambda : 1 < lambda,
        FixedLambdaArithmeticCertificateSourceTestData.FixedLambdaSourceEvaluationCanonicalAtomNormalization
          (visibleData lambda hlambda))
    (certificateData :
      ∀ lambda : ℝ, ∀ hlambda : 1 < lambda,
        HEq
          (sourceDataOwner.finitePrimeData.certificateData
            commonTestFunction commonTestFunction lambda hlambda)
          (FixedLambdaArithmeticCertificateSourceTestData.ofSourceEvaluationVisibleCanonicalData
            (supportData lambda hlambda)
            (visibleData lambda hlambda)
            (canonicalAtoms lambda hlambda))) :
    CanonicalSourceWeilFormSourceDataOwner W commonTestFunction where
  sourceDataOwner := sourceDataOwner
  sourceDataOwner_commonTestFunction := sourceDataOwner_commonTestFunction
  A := A
  sourceWeilForm := sourceWeilForm
  sameSymbols := sameSymbols
  supportData := supportData
  visibleData := visibleData
  canonicalAtoms := canonicalAtoms
  certificateData := certificateData

@[simp] theorem ofSourceWeilFormVisibleCanonicalData_sourceWeilForm
    {W : WeilFormSymbols} {commonTestFunction : TestFunction}
    (sourceDataOwner : CommonFinitePrimeArithmeticSourceData W)
    (sourceDataOwner_commonTestFunction :
      sourceDataOwner.commonTestFunction = commonTestFunction)
    {A : AnalyticCore.SourceTestAlgebra}
    (sourceWeilForm : AnalyticCore.SourceWeilFormData A)
    (sameSymbols : W = sourceWeilForm.toWeilFormSymbols)
    (supportData :
      ∀ lambda : ℝ, 1 < lambda →
        FixedLambdaCommonFinitePrimeSupportData W
          (CommonSourceTest.concreteCommonSourceTest W commonTestFunction)
          lambda)
    (visibleData :
      ∀ lambda : ℝ, 1 < lambda →
        FixedLambdaSourceEvaluationVisibleArithmeticData
          sourceWeilForm.evaluation W
          (CommonSourceTest.concreteCommonSourceTest W commonTestFunction)
          lambda)
    (canonicalAtoms :
      ∀ lambda : ℝ, ∀ hlambda : 1 < lambda,
        FixedLambdaArithmeticCertificateSourceTestData.FixedLambdaSourceEvaluationCanonicalAtomNormalization
          (visibleData lambda hlambda))
    (certificateData :
      ∀ lambda : ℝ, ∀ hlambda : 1 < lambda,
        HEq
          (sourceDataOwner.finitePrimeData.certificateData
            commonTestFunction commonTestFunction lambda hlambda)
          (FixedLambdaArithmeticCertificateSourceTestData.ofSourceEvaluationVisibleCanonicalData
            (supportData lambda hlambda)
            (visibleData lambda hlambda)
            (canonicalAtoms lambda hlambda))) :
    (ofSourceWeilFormVisibleCanonicalData
      sourceDataOwner sourceDataOwner_commonTestFunction sourceWeilForm
      sameSymbols supportData visibleData canonicalAtoms certificateData).sourceWeilForm =
      sourceWeilForm :=
  rfl

@[simp] theorem ofSourceWeilFormVisibleCanonicalData_sameSymbols
    {W : WeilFormSymbols} {commonTestFunction : TestFunction}
    (sourceDataOwner : CommonFinitePrimeArithmeticSourceData W)
    (sourceDataOwner_commonTestFunction :
      sourceDataOwner.commonTestFunction = commonTestFunction)
    {A : AnalyticCore.SourceTestAlgebra}
    (sourceWeilForm : AnalyticCore.SourceWeilFormData A)
    (sameSymbols : W = sourceWeilForm.toWeilFormSymbols)
    (supportData :
      ∀ lambda : ℝ, 1 < lambda →
        FixedLambdaCommonFinitePrimeSupportData W
          (CommonSourceTest.concreteCommonSourceTest W commonTestFunction)
          lambda)
    (visibleData :
      ∀ lambda : ℝ, 1 < lambda →
        FixedLambdaSourceEvaluationVisibleArithmeticData
          sourceWeilForm.evaluation W
          (CommonSourceTest.concreteCommonSourceTest W commonTestFunction)
          lambda)
    (canonicalAtoms :
      ∀ lambda : ℝ, ∀ hlambda : 1 < lambda,
        FixedLambdaArithmeticCertificateSourceTestData.FixedLambdaSourceEvaluationCanonicalAtomNormalization
          (visibleData lambda hlambda))
    (certificateData :
      ∀ lambda : ℝ, ∀ hlambda : 1 < lambda,
        HEq
          (sourceDataOwner.finitePrimeData.certificateData
            commonTestFunction commonTestFunction lambda hlambda)
          (FixedLambdaArithmeticCertificateSourceTestData.ofSourceEvaluationVisibleCanonicalData
            (supportData lambda hlambda)
            (visibleData lambda hlambda)
            (canonicalAtoms lambda hlambda))) :
    (ofSourceWeilFormVisibleCanonicalData
      sourceDataOwner sourceDataOwner_commonTestFunction sourceWeilForm
      sameSymbols supportData visibleData canonicalAtoms certificateData).sameSymbols =
      sameSymbols :=
  rfl

@[simp] theorem ofSourceWeilFormVisibleCanonicalData_supportData
    {W : WeilFormSymbols} {commonTestFunction : TestFunction}
    (sourceDataOwner : CommonFinitePrimeArithmeticSourceData W)
    (sourceDataOwner_commonTestFunction :
      sourceDataOwner.commonTestFunction = commonTestFunction)
    {A : AnalyticCore.SourceTestAlgebra}
    (sourceWeilForm : AnalyticCore.SourceWeilFormData A)
    (sameSymbols : W = sourceWeilForm.toWeilFormSymbols)
    (supportData :
      ∀ lambda : ℝ, 1 < lambda →
        FixedLambdaCommonFinitePrimeSupportData W
          (CommonSourceTest.concreteCommonSourceTest W commonTestFunction)
          lambda)
    (visibleData :
      ∀ lambda : ℝ, 1 < lambda →
        FixedLambdaSourceEvaluationVisibleArithmeticData
          sourceWeilForm.evaluation W
          (CommonSourceTest.concreteCommonSourceTest W commonTestFunction)
          lambda)
    (canonicalAtoms :
      ∀ lambda : ℝ, ∀ hlambda : 1 < lambda,
        FixedLambdaArithmeticCertificateSourceTestData.FixedLambdaSourceEvaluationCanonicalAtomNormalization
          (visibleData lambda hlambda))
    (certificateData :
      ∀ lambda : ℝ, ∀ hlambda : 1 < lambda,
        HEq
          (sourceDataOwner.finitePrimeData.certificateData
            commonTestFunction commonTestFunction lambda hlambda)
          (FixedLambdaArithmeticCertificateSourceTestData.ofSourceEvaluationVisibleCanonicalData
            (supportData lambda hlambda)
            (visibleData lambda hlambda)
            (canonicalAtoms lambda hlambda)))
    (lambda : ℝ) (hlambda : 1 < lambda) :
    (ofSourceWeilFormVisibleCanonicalData
      sourceDataOwner sourceDataOwner_commonTestFunction sourceWeilForm
      sameSymbols supportData visibleData canonicalAtoms certificateData).supportData
        lambda hlambda =
      supportData lambda hlambda :=
  rfl

@[simp] theorem ofSourceWeilFormVisibleCanonicalData_visibleData
    {W : WeilFormSymbols} {commonTestFunction : TestFunction}
    (sourceDataOwner : CommonFinitePrimeArithmeticSourceData W)
    (sourceDataOwner_commonTestFunction :
      sourceDataOwner.commonTestFunction = commonTestFunction)
    {A : AnalyticCore.SourceTestAlgebra}
    (sourceWeilForm : AnalyticCore.SourceWeilFormData A)
    (sameSymbols : W = sourceWeilForm.toWeilFormSymbols)
    (supportData :
      ∀ lambda : ℝ, 1 < lambda →
        FixedLambdaCommonFinitePrimeSupportData W
          (CommonSourceTest.concreteCommonSourceTest W commonTestFunction)
          lambda)
    (visibleData :
      ∀ lambda : ℝ, 1 < lambda →
        FixedLambdaSourceEvaluationVisibleArithmeticData
          sourceWeilForm.evaluation W
          (CommonSourceTest.concreteCommonSourceTest W commonTestFunction)
          lambda)
    (canonicalAtoms :
      ∀ lambda : ℝ, ∀ hlambda : 1 < lambda,
        FixedLambdaArithmeticCertificateSourceTestData.FixedLambdaSourceEvaluationCanonicalAtomNormalization
          (visibleData lambda hlambda))
    (certificateData :
      ∀ lambda : ℝ, ∀ hlambda : 1 < lambda,
        HEq
          (sourceDataOwner.finitePrimeData.certificateData
            commonTestFunction commonTestFunction lambda hlambda)
          (FixedLambdaArithmeticCertificateSourceTestData.ofSourceEvaluationVisibleCanonicalData
            (supportData lambda hlambda)
            (visibleData lambda hlambda)
            (canonicalAtoms lambda hlambda)))
    (lambda : ℝ) (hlambda : 1 < lambda) :
    (ofSourceWeilFormVisibleCanonicalData
      sourceDataOwner sourceDataOwner_commonTestFunction sourceWeilForm
      sameSymbols supportData visibleData canonicalAtoms certificateData).visibleData
        lambda hlambda =
      visibleData lambda hlambda :=
  rfl

theorem certificateData_eq
    {W : WeilFormSymbols} {commonTestFunction : TestFunction}
    (owner : CanonicalSourceWeilFormSourceDataOwner W commonTestFunction)
    (lambda : ℝ) (hlambda : 1 < lambda) :
    HEq
      (owner.sourceDataOwner.finitePrimeData.certificateData
        commonTestFunction commonTestFunction lambda hlambda)
      (FixedLambdaArithmeticCertificateSourceTestData.ofSourceEvaluationVisibleCanonicalData
        (owner.supportData lambda hlambda)
        (owner.visibleData lambda hlambda)
        (owner.canonicalAtoms lambda hlambda)) :=
  owner.certificateData lambda hlambda

theorem canonicalAtoms_visibleReadOff
    {W : WeilFormSymbols} {commonTestFunction : TestFunction}
    (owner : CanonicalSourceWeilFormSourceDataOwner W commonTestFunction)
    (lambda : ℝ) (hlambda : 1 < lambda) :
    (fun n hn => ((owner.canonicalAtoms lambda hlambda).atoms.atIndex n).data) =
      (fun n hn =>
        (owner.visibleData lambda hlambda).visibleArithmeticData.atVisibleIndex
          n hn) :=
  (owner.canonicalAtoms lambda hlambda).visibleReadOff

end CanonicalSourceWeilFormSourceDataOwner

/-- Concrete source-Weil-form provenance for the canonical finite-prime
source-data owner.  This is the source-layer owner required by the normalized
CC20 square route's B1 transport: the owner-selected source-Weil-form symbols
must have a representative over the normalized concrete CC20 source algebra,
and that representative must use the normalized concrete source-evaluation
object. -/
structure ConcreteCanonicalSourceWeilFormSourceDataOwner
    (W : WeilFormSymbols) (commonTestFunction : TestFunction) where
  owner : CanonicalSourceWeilFormSourceDataOwner W commonTestFunction
  concreteSourceWeilForm :
    AnalyticCore.SourceWeilFormData normalizedCC20ConcreteTestAlgebra
  owner_algebra_eq :
    owner.A = normalizedCC20ConcreteTestAlgebra
  owner_sourceWeilForm_heq :
    HEq owner.sourceWeilForm concreteSourceWeilForm
  owner_sourceWeilForm_eq :
    cast (by rw [owner_algebra_eq]) owner.sourceWeilForm =
      concreteSourceWeilForm
  owner_sourceWeilForm_evaluation_heq :
    HEq owner.sourceWeilForm.evaluation concreteSourceWeilForm.evaluation
  owner_sourceWeilForm_evaluation_eq :
    cast (by rw [owner_algebra_eq]) owner.sourceWeilForm.evaluation =
      concreteSourceWeilForm.evaluation
  concreteEvaluation_eq :
    concreteSourceWeilForm.evaluation = normalizedCC20ConcreteEvaluationData
  owner_sourceWeilForm_symbols_eq :
    owner.sourceWeilForm.toWeilFormSymbols =
      concreteSourceWeilForm.toWeilFormSymbols

namespace ConcreteCanonicalSourceWeilFormSourceDataOwner

noncomputable def ofConcreteSourceWeilFormVisibleCanonicalData
    {W : WeilFormSymbols} {commonTestFunction : TestFunction}
    (sourceDataOwner : CommonFinitePrimeArithmeticSourceData W)
    (sourceDataOwner_commonTestFunction :
      sourceDataOwner.commonTestFunction = commonTestFunction)
    (sourceWeilForm :
      AnalyticCore.SourceWeilFormData normalizedCC20ConcreteTestAlgebra)
    (concreteEvaluation_eq :
      sourceWeilForm.evaluation = normalizedCC20ConcreteEvaluationData)
    (sameSymbols : W = sourceWeilForm.toWeilFormSymbols)
    (supportData :
      ∀ lambda : ℝ, 1 < lambda →
        FixedLambdaCommonFinitePrimeSupportData W
          (CommonSourceTest.concreteCommonSourceTest W commonTestFunction)
          lambda)
    (visibleData :
      ∀ lambda : ℝ, 1 < lambda →
        FixedLambdaSourceEvaluationVisibleArithmeticData
          sourceWeilForm.evaluation W
          (CommonSourceTest.concreteCommonSourceTest W commonTestFunction)
          lambda)
    (canonicalAtoms :
      ∀ lambda : ℝ, ∀ hlambda : 1 < lambda,
        FixedLambdaArithmeticCertificateSourceTestData.FixedLambdaSourceEvaluationCanonicalAtomNormalization
          (visibleData lambda hlambda))
    (certificateData :
      ∀ lambda : ℝ, ∀ hlambda : 1 < lambda,
        HEq
          (sourceDataOwner.finitePrimeData.certificateData
            commonTestFunction commonTestFunction lambda hlambda)
          (FixedLambdaArithmeticCertificateSourceTestData.ofSourceEvaluationVisibleCanonicalData
            (supportData lambda hlambda)
            (visibleData lambda hlambda)
            (canonicalAtoms lambda hlambda))) :
    ConcreteCanonicalSourceWeilFormSourceDataOwner W commonTestFunction where
  owner :=
    CanonicalSourceWeilFormSourceDataOwner.ofSourceWeilFormVisibleCanonicalData
      sourceDataOwner sourceDataOwner_commonTestFunction sourceWeilForm
      sameSymbols supportData visibleData canonicalAtoms certificateData
  concreteSourceWeilForm := sourceWeilForm
  owner_algebra_eq := rfl
  owner_sourceWeilForm_heq := HEq.rfl
  owner_sourceWeilForm_eq := rfl
  owner_sourceWeilForm_evaluation_heq := HEq.rfl
  owner_sourceWeilForm_evaluation_eq := rfl
  concreteEvaluation_eq := concreteEvaluation_eq
  owner_sourceWeilForm_symbols_eq := rfl

@[simp] theorem ofConcreteSourceWeilFormVisibleCanonicalData_owner
    {W : WeilFormSymbols} {commonTestFunction : TestFunction}
    (sourceDataOwner : CommonFinitePrimeArithmeticSourceData W)
    (sourceDataOwner_commonTestFunction :
      sourceDataOwner.commonTestFunction = commonTestFunction)
    (sourceWeilForm :
      AnalyticCore.SourceWeilFormData normalizedCC20ConcreteTestAlgebra)
    (concreteEvaluation_eq :
      sourceWeilForm.evaluation = normalizedCC20ConcreteEvaluationData)
    (sameSymbols : W = sourceWeilForm.toWeilFormSymbols)
    (supportData :
      ∀ lambda : ℝ, 1 < lambda →
        FixedLambdaCommonFinitePrimeSupportData W
          (CommonSourceTest.concreteCommonSourceTest W commonTestFunction)
          lambda)
    (visibleData :
      ∀ lambda : ℝ, 1 < lambda →
        FixedLambdaSourceEvaluationVisibleArithmeticData
          sourceWeilForm.evaluation W
          (CommonSourceTest.concreteCommonSourceTest W commonTestFunction)
          lambda)
    (canonicalAtoms :
      ∀ lambda : ℝ, ∀ hlambda : 1 < lambda,
        FixedLambdaArithmeticCertificateSourceTestData.FixedLambdaSourceEvaluationCanonicalAtomNormalization
          (visibleData lambda hlambda))
    (certificateData :
      ∀ lambda : ℝ, ∀ hlambda : 1 < lambda,
        HEq
          (sourceDataOwner.finitePrimeData.certificateData
            commonTestFunction commonTestFunction lambda hlambda)
          (FixedLambdaArithmeticCertificateSourceTestData.ofSourceEvaluationVisibleCanonicalData
            (supportData lambda hlambda)
            (visibleData lambda hlambda)
            (canonicalAtoms lambda hlambda))) :
    (ofConcreteSourceWeilFormVisibleCanonicalData
      sourceDataOwner sourceDataOwner_commonTestFunction sourceWeilForm
      concreteEvaluation_eq sameSymbols supportData visibleData canonicalAtoms
      certificateData).owner =
      CanonicalSourceWeilFormSourceDataOwner.ofSourceWeilFormVisibleCanonicalData
        sourceDataOwner sourceDataOwner_commonTestFunction sourceWeilForm
        sameSymbols supportData visibleData canonicalAtoms certificateData :=
  rfl

@[simp] theorem ofConcreteSourceWeilFormVisibleCanonicalData_concreteSourceWeilForm
    {W : WeilFormSymbols} {commonTestFunction : TestFunction}
    (sourceDataOwner : CommonFinitePrimeArithmeticSourceData W)
    (sourceDataOwner_commonTestFunction :
      sourceDataOwner.commonTestFunction = commonTestFunction)
    (sourceWeilForm :
      AnalyticCore.SourceWeilFormData normalizedCC20ConcreteTestAlgebra)
    (concreteEvaluation_eq :
      sourceWeilForm.evaluation = normalizedCC20ConcreteEvaluationData)
    (sameSymbols : W = sourceWeilForm.toWeilFormSymbols)
    (supportData :
      ∀ lambda : ℝ, 1 < lambda →
        FixedLambdaCommonFinitePrimeSupportData W
          (CommonSourceTest.concreteCommonSourceTest W commonTestFunction)
          lambda)
    (visibleData :
      ∀ lambda : ℝ, 1 < lambda →
        FixedLambdaSourceEvaluationVisibleArithmeticData
          sourceWeilForm.evaluation W
          (CommonSourceTest.concreteCommonSourceTest W commonTestFunction)
          lambda)
    (canonicalAtoms :
      ∀ lambda : ℝ, ∀ hlambda : 1 < lambda,
        FixedLambdaArithmeticCertificateSourceTestData.FixedLambdaSourceEvaluationCanonicalAtomNormalization
          (visibleData lambda hlambda))
    (certificateData :
      ∀ lambda : ℝ, ∀ hlambda : 1 < lambda,
        HEq
          (sourceDataOwner.finitePrimeData.certificateData
            commonTestFunction commonTestFunction lambda hlambda)
          (FixedLambdaArithmeticCertificateSourceTestData.ofSourceEvaluationVisibleCanonicalData
            (supportData lambda hlambda)
            (visibleData lambda hlambda)
            (canonicalAtoms lambda hlambda))) :
    (ofConcreteSourceWeilFormVisibleCanonicalData
      sourceDataOwner sourceDataOwner_commonTestFunction sourceWeilForm
      concreteEvaluation_eq sameSymbols supportData visibleData canonicalAtoms
      certificateData).concreteSourceWeilForm =
      sourceWeilForm :=
  rfl

@[simp] theorem ofConcreteSourceWeilFormVisibleCanonicalData_owner_algebra_eq
    {W : WeilFormSymbols} {commonTestFunction : TestFunction}
    (sourceDataOwner : CommonFinitePrimeArithmeticSourceData W)
    (sourceDataOwner_commonTestFunction :
      sourceDataOwner.commonTestFunction = commonTestFunction)
    (sourceWeilForm :
      AnalyticCore.SourceWeilFormData normalizedCC20ConcreteTestAlgebra)
    (concreteEvaluation_eq :
      sourceWeilForm.evaluation = normalizedCC20ConcreteEvaluationData)
    (sameSymbols : W = sourceWeilForm.toWeilFormSymbols)
    (supportData :
      ∀ lambda : ℝ, 1 < lambda →
        FixedLambdaCommonFinitePrimeSupportData W
          (CommonSourceTest.concreteCommonSourceTest W commonTestFunction)
          lambda)
    (visibleData :
      ∀ lambda : ℝ, 1 < lambda →
        FixedLambdaSourceEvaluationVisibleArithmeticData
          sourceWeilForm.evaluation W
          (CommonSourceTest.concreteCommonSourceTest W commonTestFunction)
          lambda)
    (canonicalAtoms :
      ∀ lambda : ℝ, ∀ hlambda : 1 < lambda,
        FixedLambdaArithmeticCertificateSourceTestData.FixedLambdaSourceEvaluationCanonicalAtomNormalization
          (visibleData lambda hlambda))
    (certificateData :
      ∀ lambda : ℝ, ∀ hlambda : 1 < lambda,
        HEq
          (sourceDataOwner.finitePrimeData.certificateData
            commonTestFunction commonTestFunction lambda hlambda)
          (FixedLambdaArithmeticCertificateSourceTestData.ofSourceEvaluationVisibleCanonicalData
            (supportData lambda hlambda)
            (visibleData lambda hlambda)
            (canonicalAtoms lambda hlambda))) :
    (ofConcreteSourceWeilFormVisibleCanonicalData
      sourceDataOwner sourceDataOwner_commonTestFunction sourceWeilForm
      concreteEvaluation_eq sameSymbols supportData visibleData canonicalAtoms
      certificateData).owner_algebra_eq =
      rfl :=
  rfl

@[simp] theorem ofConcreteSourceWeilFormVisibleCanonicalData_owner_sourceWeilForm_heq
    {W : WeilFormSymbols} {commonTestFunction : TestFunction}
    (sourceDataOwner : CommonFinitePrimeArithmeticSourceData W)
    (sourceDataOwner_commonTestFunction :
      sourceDataOwner.commonTestFunction = commonTestFunction)
    (sourceWeilForm :
      AnalyticCore.SourceWeilFormData normalizedCC20ConcreteTestAlgebra)
    (concreteEvaluation_eq :
      sourceWeilForm.evaluation = normalizedCC20ConcreteEvaluationData)
    (sameSymbols : W = sourceWeilForm.toWeilFormSymbols)
    (supportData :
      ∀ lambda : ℝ, 1 < lambda →
        FixedLambdaCommonFinitePrimeSupportData W
          (CommonSourceTest.concreteCommonSourceTest W commonTestFunction)
          lambda)
    (visibleData :
      ∀ lambda : ℝ, 1 < lambda →
        FixedLambdaSourceEvaluationVisibleArithmeticData
          sourceWeilForm.evaluation W
          (CommonSourceTest.concreteCommonSourceTest W commonTestFunction)
          lambda)
    (canonicalAtoms :
      ∀ lambda : ℝ, ∀ hlambda : 1 < lambda,
        FixedLambdaArithmeticCertificateSourceTestData.FixedLambdaSourceEvaluationCanonicalAtomNormalization
          (visibleData lambda hlambda))
    (certificateData :
      ∀ lambda : ℝ, ∀ hlambda : 1 < lambda,
        HEq
          (sourceDataOwner.finitePrimeData.certificateData
            commonTestFunction commonTestFunction lambda hlambda)
          (FixedLambdaArithmeticCertificateSourceTestData.ofSourceEvaluationVisibleCanonicalData
            (supportData lambda hlambda)
            (visibleData lambda hlambda)
            (canonicalAtoms lambda hlambda))) :
    (ofConcreteSourceWeilFormVisibleCanonicalData
      sourceDataOwner sourceDataOwner_commonTestFunction sourceWeilForm
      concreteEvaluation_eq sameSymbols supportData visibleData canonicalAtoms
      certificateData).owner_sourceWeilForm_heq =
      HEq.rfl :=
  rfl

@[simp] theorem ofConcreteSourceWeilFormVisibleCanonicalData_owner_sourceWeilForm_eq
    {W : WeilFormSymbols} {commonTestFunction : TestFunction}
    (sourceDataOwner : CommonFinitePrimeArithmeticSourceData W)
    (sourceDataOwner_commonTestFunction :
      sourceDataOwner.commonTestFunction = commonTestFunction)
    (sourceWeilForm :
      AnalyticCore.SourceWeilFormData normalizedCC20ConcreteTestAlgebra)
    (concreteEvaluation_eq :
      sourceWeilForm.evaluation = normalizedCC20ConcreteEvaluationData)
    (sameSymbols : W = sourceWeilForm.toWeilFormSymbols)
    (supportData :
      ∀ lambda : ℝ, 1 < lambda →
        FixedLambdaCommonFinitePrimeSupportData W
          (CommonSourceTest.concreteCommonSourceTest W commonTestFunction)
          lambda)
    (visibleData :
      ∀ lambda : ℝ, 1 < lambda →
        FixedLambdaSourceEvaluationVisibleArithmeticData
          sourceWeilForm.evaluation W
          (CommonSourceTest.concreteCommonSourceTest W commonTestFunction)
          lambda)
    (canonicalAtoms :
      ∀ lambda : ℝ, ∀ hlambda : 1 < lambda,
        FixedLambdaArithmeticCertificateSourceTestData.FixedLambdaSourceEvaluationCanonicalAtomNormalization
          (visibleData lambda hlambda))
    (certificateData :
      ∀ lambda : ℝ, ∀ hlambda : 1 < lambda,
        HEq
          (sourceDataOwner.finitePrimeData.certificateData
            commonTestFunction commonTestFunction lambda hlambda)
          (FixedLambdaArithmeticCertificateSourceTestData.ofSourceEvaluationVisibleCanonicalData
            (supportData lambda hlambda)
            (visibleData lambda hlambda)
            (canonicalAtoms lambda hlambda))) :
    (ofConcreteSourceWeilFormVisibleCanonicalData
      sourceDataOwner sourceDataOwner_commonTestFunction sourceWeilForm
      concreteEvaluation_eq sameSymbols supportData visibleData canonicalAtoms
      certificateData).owner_sourceWeilForm_eq =
      rfl :=
  rfl

@[simp] theorem ofConcreteSourceWeilFormVisibleCanonicalData_owner_sourceWeilForm_evaluation_heq
    {W : WeilFormSymbols} {commonTestFunction : TestFunction}
    (sourceDataOwner : CommonFinitePrimeArithmeticSourceData W)
    (sourceDataOwner_commonTestFunction :
      sourceDataOwner.commonTestFunction = commonTestFunction)
    (sourceWeilForm :
      AnalyticCore.SourceWeilFormData normalizedCC20ConcreteTestAlgebra)
    (concreteEvaluation_eq :
      sourceWeilForm.evaluation = normalizedCC20ConcreteEvaluationData)
    (sameSymbols : W = sourceWeilForm.toWeilFormSymbols)
    (supportData :
      ∀ lambda : ℝ, 1 < lambda →
        FixedLambdaCommonFinitePrimeSupportData W
          (CommonSourceTest.concreteCommonSourceTest W commonTestFunction)
          lambda)
    (visibleData :
      ∀ lambda : ℝ, 1 < lambda →
        FixedLambdaSourceEvaluationVisibleArithmeticData
          sourceWeilForm.evaluation W
          (CommonSourceTest.concreteCommonSourceTest W commonTestFunction)
          lambda)
    (canonicalAtoms :
      ∀ lambda : ℝ, ∀ hlambda : 1 < lambda,
        FixedLambdaArithmeticCertificateSourceTestData.FixedLambdaSourceEvaluationCanonicalAtomNormalization
          (visibleData lambda hlambda))
    (certificateData :
      ∀ lambda : ℝ, ∀ hlambda : 1 < lambda,
        HEq
          (sourceDataOwner.finitePrimeData.certificateData
            commonTestFunction commonTestFunction lambda hlambda)
          (FixedLambdaArithmeticCertificateSourceTestData.ofSourceEvaluationVisibleCanonicalData
            (supportData lambda hlambda)
            (visibleData lambda hlambda)
            (canonicalAtoms lambda hlambda))) :
    (ofConcreteSourceWeilFormVisibleCanonicalData
      sourceDataOwner sourceDataOwner_commonTestFunction sourceWeilForm
      concreteEvaluation_eq sameSymbols supportData visibleData canonicalAtoms
      certificateData).owner_sourceWeilForm_evaluation_heq =
      HEq.rfl :=
  rfl

@[simp] theorem ofConcreteSourceWeilFormVisibleCanonicalData_owner_sourceWeilForm_evaluation_eq
    {W : WeilFormSymbols} {commonTestFunction : TestFunction}
    (sourceDataOwner : CommonFinitePrimeArithmeticSourceData W)
    (sourceDataOwner_commonTestFunction :
      sourceDataOwner.commonTestFunction = commonTestFunction)
    (sourceWeilForm :
      AnalyticCore.SourceWeilFormData normalizedCC20ConcreteTestAlgebra)
    (concreteEvaluation_eq :
      sourceWeilForm.evaluation = normalizedCC20ConcreteEvaluationData)
    (sameSymbols : W = sourceWeilForm.toWeilFormSymbols)
    (supportData :
      ∀ lambda : ℝ, 1 < lambda →
        FixedLambdaCommonFinitePrimeSupportData W
          (CommonSourceTest.concreteCommonSourceTest W commonTestFunction)
          lambda)
    (visibleData :
      ∀ lambda : ℝ, 1 < lambda →
        FixedLambdaSourceEvaluationVisibleArithmeticData
          sourceWeilForm.evaluation W
          (CommonSourceTest.concreteCommonSourceTest W commonTestFunction)
          lambda)
    (canonicalAtoms :
      ∀ lambda : ℝ, ∀ hlambda : 1 < lambda,
        FixedLambdaArithmeticCertificateSourceTestData.FixedLambdaSourceEvaluationCanonicalAtomNormalization
          (visibleData lambda hlambda))
    (certificateData :
      ∀ lambda : ℝ, ∀ hlambda : 1 < lambda,
        HEq
          (sourceDataOwner.finitePrimeData.certificateData
            commonTestFunction commonTestFunction lambda hlambda)
          (FixedLambdaArithmeticCertificateSourceTestData.ofSourceEvaluationVisibleCanonicalData
            (supportData lambda hlambda)
            (visibleData lambda hlambda)
            (canonicalAtoms lambda hlambda))) :
    (ofConcreteSourceWeilFormVisibleCanonicalData
      sourceDataOwner sourceDataOwner_commonTestFunction sourceWeilForm
      concreteEvaluation_eq sameSymbols supportData visibleData canonicalAtoms
      certificateData).owner_sourceWeilForm_evaluation_eq =
      rfl :=
  rfl

@[simp] theorem ofConcreteSourceWeilFormVisibleCanonicalData_concreteEvaluation_eq
    {W : WeilFormSymbols} {commonTestFunction : TestFunction}
    (sourceDataOwner : CommonFinitePrimeArithmeticSourceData W)
    (sourceDataOwner_commonTestFunction :
      sourceDataOwner.commonTestFunction = commonTestFunction)
    (sourceWeilForm :
      AnalyticCore.SourceWeilFormData normalizedCC20ConcreteTestAlgebra)
    (concreteEvaluation_eq :
      sourceWeilForm.evaluation = normalizedCC20ConcreteEvaluationData)
    (sameSymbols : W = sourceWeilForm.toWeilFormSymbols)
    (supportData :
      ∀ lambda : ℝ, 1 < lambda →
        FixedLambdaCommonFinitePrimeSupportData W
          (CommonSourceTest.concreteCommonSourceTest W commonTestFunction)
          lambda)
    (visibleData :
      ∀ lambda : ℝ, 1 < lambda →
        FixedLambdaSourceEvaluationVisibleArithmeticData
          sourceWeilForm.evaluation W
          (CommonSourceTest.concreteCommonSourceTest W commonTestFunction)
          lambda)
    (canonicalAtoms :
      ∀ lambda : ℝ, ∀ hlambda : 1 < lambda,
        FixedLambdaArithmeticCertificateSourceTestData.FixedLambdaSourceEvaluationCanonicalAtomNormalization
          (visibleData lambda hlambda))
    (certificateData :
      ∀ lambda : ℝ, ∀ hlambda : 1 < lambda,
        HEq
          (sourceDataOwner.finitePrimeData.certificateData
            commonTestFunction commonTestFunction lambda hlambda)
          (FixedLambdaArithmeticCertificateSourceTestData.ofSourceEvaluationVisibleCanonicalData
            (supportData lambda hlambda)
            (visibleData lambda hlambda)
            (canonicalAtoms lambda hlambda))) :
    (ofConcreteSourceWeilFormVisibleCanonicalData
      sourceDataOwner sourceDataOwner_commonTestFunction sourceWeilForm
      concreteEvaluation_eq sameSymbols supportData visibleData canonicalAtoms
      certificateData).concreteEvaluation_eq =
      concreteEvaluation_eq :=
  rfl

@[simp] theorem ofConcreteSourceWeilFormVisibleCanonicalData_symbols_eq
    {W : WeilFormSymbols} {commonTestFunction : TestFunction}
    (sourceDataOwner : CommonFinitePrimeArithmeticSourceData W)
    (sourceDataOwner_commonTestFunction :
      sourceDataOwner.commonTestFunction = commonTestFunction)
    (sourceWeilForm :
      AnalyticCore.SourceWeilFormData normalizedCC20ConcreteTestAlgebra)
    (concreteEvaluation_eq :
      sourceWeilForm.evaluation = normalizedCC20ConcreteEvaluationData)
    (sameSymbols : W = sourceWeilForm.toWeilFormSymbols)
    (supportData :
      ∀ lambda : ℝ, 1 < lambda →
        FixedLambdaCommonFinitePrimeSupportData W
          (CommonSourceTest.concreteCommonSourceTest W commonTestFunction)
          lambda)
    (visibleData :
      ∀ lambda : ℝ, 1 < lambda →
        FixedLambdaSourceEvaluationVisibleArithmeticData
          sourceWeilForm.evaluation W
          (CommonSourceTest.concreteCommonSourceTest W commonTestFunction)
          lambda)
    (canonicalAtoms :
      ∀ lambda : ℝ, ∀ hlambda : 1 < lambda,
        FixedLambdaArithmeticCertificateSourceTestData.FixedLambdaSourceEvaluationCanonicalAtomNormalization
          (visibleData lambda hlambda))
    (certificateData :
      ∀ lambda : ℝ, ∀ hlambda : 1 < lambda,
        HEq
          (sourceDataOwner.finitePrimeData.certificateData
            commonTestFunction commonTestFunction lambda hlambda)
          (FixedLambdaArithmeticCertificateSourceTestData.ofSourceEvaluationVisibleCanonicalData
            (supportData lambda hlambda)
            (visibleData lambda hlambda)
            (canonicalAtoms lambda hlambda))) :
    (ofConcreteSourceWeilFormVisibleCanonicalData
      sourceDataOwner sourceDataOwner_commonTestFunction sourceWeilForm
      concreteEvaluation_eq sameSymbols supportData visibleData canonicalAtoms
      certificateData).owner_sourceWeilForm_symbols_eq =
      rfl :=
  rfl

end ConcreteCanonicalSourceWeilFormSourceDataOwner

end FinitePrimeSourceData
end CCM25Concrete
end Source
end ConnesWeilRH
