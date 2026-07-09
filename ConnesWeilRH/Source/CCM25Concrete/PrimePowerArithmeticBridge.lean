/-
Copyright (c) 2026 ConnesWeilRH contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ConnesWeilRH contributors
-/

import ConnesWeilRH.Source.CCM25Concrete.PrimePowerArithmetic
import ConnesWeilRH.Source.CCM25Concrete.PrimePowerEvaluationBridge

/-!
# Bridge from source evaluation data to CCM25 prime-power arithmetic

This module is downstream of the CCM25 arithmetic boundary.  It constructs a
finite-prime arithmetic atom whose evaluation leg is forced through
`SourceEvaluationData`, while still requiring the real pairing and term
read-offs from the caller.
-/

namespace ConnesWeilRH
namespace Source
namespace CCM25Concrete
namespace PrimePowerArithmetic

noncomputable def SourceFinitePrimeArithmeticData.ofSourceEvaluationData
    {A : AnalyticCore.SourceTestAlgebra}
    (E : AnalyticCore.SourceEvaluationData A)
    {W : WeilFormSymbols}
    (common : CommonSourceTest.ConcreteCommonSourceTest W) (n : ℕ)
    (sourcePrimePowerIndex : IsPrimePow n)
    (visible :
      W.finitePrimeAtomVisible n
        (W.convolutionStar common.sourceTest common.sourceTest))
    (pairingReadOff :
      W.primePowerPairing n common.sourceTest common.sourceTest =
        (1 / Real.sqrt (n : ℝ)) *
          (E.legacyValueAt common.sourceConvolutionSquare
              (PrimePowerEvaluation.SourceForwardPoint n) +
            E.legacyValueAt common.sourceConvolutionSquare
              (PrimePowerEvaluation.SourceInversePoint n)))
    (weightReadOff :
      W.vonMangoldtWeight n = ArithmeticFunction.vonMangoldt n)
    (termReadOff :
      W.finitePrimeTerm n
          (W.convolutionStar common.sourceTest common.sourceTest) =
        ArithmeticFunction.vonMangoldt n *
      ((1 / Real.sqrt (n : ℝ)) *
        (E.legacyValueAt common.sourceConvolutionSquare
            (PrimePowerEvaluation.SourceForwardPoint n) +
          E.legacyValueAt common.sourceConvolutionSquare
            (PrimePowerEvaluation.SourceInversePoint n)))) :
    SourceFinitePrimeArithmeticData W common.sourceTest common.sourceTest n where
  indexData :=
    { sourcePrimePowerIndex := sourcePrimePowerIndex
      sourceTest := common.toSourceTestEvaluationInterface
      sourceAtomVisible := visible }
  pairingData :=
    { sourcePairing :=
        (PrimePowerPairing.ConcreteCommonPrimePowerPairingData.ofSourceEvaluationData
          E common n pairingReadOff).toSourcePrimePowerPairingData
      pairingSourceTestReadOff := rfl
      sourcePrimePowerPairing :=
        (1 / Real.sqrt (n : ℝ)) *
          (E.legacyValueAt common.sourceConvolutionSquare
              (PrimePowerEvaluation.SourceForwardPoint n) +
            E.legacyValueAt common.sourceConvolutionSquare
              (PrimePowerEvaluation.SourceInversePoint n))
      pairingReadOff := pairingReadOff }
  formulaData :=
    { weightReadOff := weightReadOff
      termReadOff := termReadOff }

@[simp] theorem SourceFinitePrimeArithmeticData.ofSourceEvaluationData_sourcePrimePowerIndex
    {A : AnalyticCore.SourceTestAlgebra}
    (E : AnalyticCore.SourceEvaluationData A)
    {W : WeilFormSymbols}
    (common : CommonSourceTest.ConcreteCommonSourceTest W) (n : ℕ)
    (sourcePrimePowerIndex : IsPrimePow n)
    (visible :
      W.finitePrimeAtomVisible n
        (W.convolutionStar common.sourceTest common.sourceTest))
    (pairingReadOff :
      W.primePowerPairing n common.sourceTest common.sourceTest =
        (1 / Real.sqrt (n : ℝ)) *
          (E.legacyValueAt common.sourceConvolutionSquare
              (PrimePowerEvaluation.SourceForwardPoint n) +
            E.legacyValueAt common.sourceConvolutionSquare
              (PrimePowerEvaluation.SourceInversePoint n)))
    (weightReadOff :
      W.vonMangoldtWeight n = ArithmeticFunction.vonMangoldt n)
    (termReadOff :
      W.finitePrimeTerm n
          (W.convolutionStar common.sourceTest common.sourceTest) =
        ArithmeticFunction.vonMangoldt n *
          ((1 / Real.sqrt (n : ℝ)) *
            (E.legacyValueAt common.sourceConvolutionSquare
                (PrimePowerEvaluation.SourceForwardPoint n) +
              E.legacyValueAt common.sourceConvolutionSquare
                (PrimePowerEvaluation.SourceInversePoint n)))) :
    (SourceFinitePrimeArithmeticData.ofSourceEvaluationData E common n
      sourcePrimePowerIndex visible pairingReadOff weightReadOff
      termReadOff).sourcePrimePowerIndex = sourcePrimePowerIndex :=
  rfl

@[simp] theorem SourceFinitePrimeArithmeticData.ofSourceEvaluationData_sourceTest
    {A : AnalyticCore.SourceTestAlgebra}
    (E : AnalyticCore.SourceEvaluationData A)
    {W : WeilFormSymbols}
    (common : CommonSourceTest.ConcreteCommonSourceTest W) (n : ℕ)
    (sourcePrimePowerIndex : IsPrimePow n)
    (visible :
      W.finitePrimeAtomVisible n
        (W.convolutionStar common.sourceTest common.sourceTest))
    (pairingReadOff :
      W.primePowerPairing n common.sourceTest common.sourceTest =
        (1 / Real.sqrt (n : ℝ)) *
          (E.legacyValueAt common.sourceConvolutionSquare
              (PrimePowerEvaluation.SourceForwardPoint n) +
            E.legacyValueAt common.sourceConvolutionSquare
              (PrimePowerEvaluation.SourceInversePoint n)))
    (weightReadOff :
      W.vonMangoldtWeight n = ArithmeticFunction.vonMangoldt n)
    (termReadOff :
      W.finitePrimeTerm n
          (W.convolutionStar common.sourceTest common.sourceTest) =
        ArithmeticFunction.vonMangoldt n *
          ((1 / Real.sqrt (n : ℝ)) *
            (E.legacyValueAt common.sourceConvolutionSquare
                (PrimePowerEvaluation.SourceForwardPoint n) +
              E.legacyValueAt common.sourceConvolutionSquare
                (PrimePowerEvaluation.SourceInversePoint n)))) :
    (SourceFinitePrimeArithmeticData.ofSourceEvaluationData E common n
      sourcePrimePowerIndex visible pairingReadOff weightReadOff
      termReadOff).sourceTest = common.toSourceTestEvaluationInterface :=
  rfl

@[simp] theorem SourceFinitePrimeArithmeticData.ofSourceEvaluationData_sourceAtomVisible
    {A : AnalyticCore.SourceTestAlgebra}
    (E : AnalyticCore.SourceEvaluationData A)
    {W : WeilFormSymbols}
    (common : CommonSourceTest.ConcreteCommonSourceTest W) (n : ℕ)
    (sourcePrimePowerIndex : IsPrimePow n)
    (visible :
      W.finitePrimeAtomVisible n
        (W.convolutionStar common.sourceTest common.sourceTest))
    (pairingReadOff :
      W.primePowerPairing n common.sourceTest common.sourceTest =
        (1 / Real.sqrt (n : ℝ)) *
          (E.legacyValueAt common.sourceConvolutionSquare
              (PrimePowerEvaluation.SourceForwardPoint n) +
            E.legacyValueAt common.sourceConvolutionSquare
              (PrimePowerEvaluation.SourceInversePoint n)))
    (weightReadOff :
      W.vonMangoldtWeight n = ArithmeticFunction.vonMangoldt n)
    (termReadOff :
      W.finitePrimeTerm n
          (W.convolutionStar common.sourceTest common.sourceTest) =
        ArithmeticFunction.vonMangoldt n *
          ((1 / Real.sqrt (n : ℝ)) *
            (E.legacyValueAt common.sourceConvolutionSquare
                (PrimePowerEvaluation.SourceForwardPoint n) +
              E.legacyValueAt common.sourceConvolutionSquare
                (PrimePowerEvaluation.SourceInversePoint n)))) :
    (SourceFinitePrimeArithmeticData.ofSourceEvaluationData E common n
      sourcePrimePowerIndex visible pairingReadOff weightReadOff
      termReadOff).sourceAtomVisible = visible :=
  rfl

@[simp] theorem SourceFinitePrimeArithmeticData.ofSourceEvaluationData_sourcePrimePowerPairing
    {A : AnalyticCore.SourceTestAlgebra}
    (E : AnalyticCore.SourceEvaluationData A)
    {W : WeilFormSymbols}
    (common : CommonSourceTest.ConcreteCommonSourceTest W) (n : ℕ)
    (sourcePrimePowerIndex : IsPrimePow n)
    (visible :
      W.finitePrimeAtomVisible n
        (W.convolutionStar common.sourceTest common.sourceTest))
    (pairingReadOff :
      W.primePowerPairing n common.sourceTest common.sourceTest =
        (1 / Real.sqrt (n : ℝ)) *
          (E.legacyValueAt common.sourceConvolutionSquare
              (PrimePowerEvaluation.SourceForwardPoint n) +
            E.legacyValueAt common.sourceConvolutionSquare
              (PrimePowerEvaluation.SourceInversePoint n)))
    (weightReadOff :
      W.vonMangoldtWeight n = ArithmeticFunction.vonMangoldt n)
    (termReadOff :
      W.finitePrimeTerm n
          (W.convolutionStar common.sourceTest common.sourceTest) =
        ArithmeticFunction.vonMangoldt n *
          ((1 / Real.sqrt (n : ℝ)) *
            (E.legacyValueAt common.sourceConvolutionSquare
                (PrimePowerEvaluation.SourceForwardPoint n) +
              E.legacyValueAt common.sourceConvolutionSquare
                (PrimePowerEvaluation.SourceInversePoint n)))) :
    (SourceFinitePrimeArithmeticData.ofSourceEvaluationData E common n
      sourcePrimePowerIndex visible pairingReadOff weightReadOff
      termReadOff).sourcePrimePowerPairing =
      (1 / Real.sqrt (n : ℝ)) *
        (E.valueAt (A.legacy.decode common.sourceConvolutionSquare)
            (PrimePowerEvaluation.SourceForwardPoint n) +
          E.valueAt (A.legacy.decode common.sourceConvolutionSquare)
            (PrimePowerEvaluation.SourceInversePoint n)) :=
  rfl

@[simp] theorem SourceFinitePrimeArithmeticData.ofSourceEvaluationData_sourcePairing_forwardValue
    {A : AnalyticCore.SourceTestAlgebra}
    (E : AnalyticCore.SourceEvaluationData A)
    {W : WeilFormSymbols}
    (common : CommonSourceTest.ConcreteCommonSourceTest W) (n : ℕ)
    (sourcePrimePowerIndex : IsPrimePow n)
    (visible :
      W.finitePrimeAtomVisible n
        (W.convolutionStar common.sourceTest common.sourceTest))
    (pairingReadOff :
      W.primePowerPairing n common.sourceTest common.sourceTest =
        (1 / Real.sqrt (n : ℝ)) *
          (E.legacyValueAt common.sourceConvolutionSquare
              (PrimePowerEvaluation.SourceForwardPoint n) +
            E.legacyValueAt common.sourceConvolutionSquare
              (PrimePowerEvaluation.SourceInversePoint n)))
    (weightReadOff :
      W.vonMangoldtWeight n = ArithmeticFunction.vonMangoldt n)
    (termReadOff :
      W.finitePrimeTerm n
          (W.convolutionStar common.sourceTest common.sourceTest) =
        ArithmeticFunction.vonMangoldt n *
          ((1 / Real.sqrt (n : ℝ)) *
            (E.legacyValueAt common.sourceConvolutionSquare
                (PrimePowerEvaluation.SourceForwardPoint n) +
              E.legacyValueAt common.sourceConvolutionSquare
                (PrimePowerEvaluation.SourceInversePoint n)))) :
    (SourceFinitePrimeArithmeticData.ofSourceEvaluationData E common n
      sourcePrimePowerIndex visible pairingReadOff weightReadOff termReadOff
        ).sourcePairing.model.sourceEvaluation.forwardValue =
      E.valueAt (A.legacy.decode common.sourceConvolutionSquare)
        (PrimePowerEvaluation.SourceForwardPoint n) :=
  rfl

@[simp] theorem
    SourceFinitePrimeArithmeticData.ofSourceEvaluationData_sourcePairing_forwardValue_nat
    {A : AnalyticCore.SourceTestAlgebra}
    (E : AnalyticCore.SourceEvaluationData A)
    {W : WeilFormSymbols}
    (common : CommonSourceTest.ConcreteCommonSourceTest W) (n : ℕ)
    (sourcePrimePowerIndex : IsPrimePow n)
    (visible :
      W.finitePrimeAtomVisible n
        (W.convolutionStar common.sourceTest common.sourceTest))
    (pairingReadOff :
      W.primePowerPairing n common.sourceTest common.sourceTest =
        (1 / Real.sqrt (n : ℝ)) *
          (E.legacyValueAt common.sourceConvolutionSquare
              (PrimePowerEvaluation.SourceForwardPoint n) +
            E.legacyValueAt common.sourceConvolutionSquare
              (PrimePowerEvaluation.SourceInversePoint n)))
    (weightReadOff :
      W.vonMangoldtWeight n = ArithmeticFunction.vonMangoldt n)
    (termReadOff :
      W.finitePrimeTerm n
          (W.convolutionStar common.sourceTest common.sourceTest) =
        ArithmeticFunction.vonMangoldt n *
          ((1 / Real.sqrt (n : ℝ)) *
            (E.legacyValueAt common.sourceConvolutionSquare
                (PrimePowerEvaluation.SourceForwardPoint n) +
              E.legacyValueAt common.sourceConvolutionSquare
                (PrimePowerEvaluation.SourceInversePoint n)))) :
    (SourceFinitePrimeArithmeticData.ofSourceEvaluationData E common n
      sourcePrimePowerIndex visible pairingReadOff weightReadOff termReadOff
        ).sourcePairing.model.sourceEvaluation.forwardValue =
      E.valueAt (A.legacy.decode common.sourceConvolutionSquare) (n : ℝ) :=
  rfl

@[simp] theorem SourceFinitePrimeArithmeticData.ofSourceEvaluationData_sourcePairing_inverseValue
    {A : AnalyticCore.SourceTestAlgebra}
    (E : AnalyticCore.SourceEvaluationData A)
    {W : WeilFormSymbols}
    (common : CommonSourceTest.ConcreteCommonSourceTest W) (n : ℕ)
    (sourcePrimePowerIndex : IsPrimePow n)
    (visible :
      W.finitePrimeAtomVisible n
        (W.convolutionStar common.sourceTest common.sourceTest))
    (pairingReadOff :
      W.primePowerPairing n common.sourceTest common.sourceTest =
        (1 / Real.sqrt (n : ℝ)) *
          (E.legacyValueAt common.sourceConvolutionSquare
              (PrimePowerEvaluation.SourceForwardPoint n) +
            E.legacyValueAt common.sourceConvolutionSquare
              (PrimePowerEvaluation.SourceInversePoint n)))
    (weightReadOff :
      W.vonMangoldtWeight n = ArithmeticFunction.vonMangoldt n)
    (termReadOff :
      W.finitePrimeTerm n
          (W.convolutionStar common.sourceTest common.sourceTest) =
        ArithmeticFunction.vonMangoldt n *
          ((1 / Real.sqrt (n : ℝ)) *
            (E.legacyValueAt common.sourceConvolutionSquare
                (PrimePowerEvaluation.SourceForwardPoint n) +
              E.legacyValueAt common.sourceConvolutionSquare
                (PrimePowerEvaluation.SourceInversePoint n)))) :
    (SourceFinitePrimeArithmeticData.ofSourceEvaluationData E common n
      sourcePrimePowerIndex visible pairingReadOff weightReadOff termReadOff
        ).sourcePairing.model.sourceEvaluation.inverseValue =
      E.valueAt (A.legacy.decode common.sourceConvolutionSquare)
        (PrimePowerEvaluation.SourceInversePoint n) :=
  rfl

@[simp] theorem
    SourceFinitePrimeArithmeticData.ofSourceEvaluationData_sourcePairing_inverseValue_inv_nat
    {A : AnalyticCore.SourceTestAlgebra}
    (E : AnalyticCore.SourceEvaluationData A)
    {W : WeilFormSymbols}
    (common : CommonSourceTest.ConcreteCommonSourceTest W) (n : ℕ)
    (sourcePrimePowerIndex : IsPrimePow n)
    (visible :
      W.finitePrimeAtomVisible n
        (W.convolutionStar common.sourceTest common.sourceTest))
    (pairingReadOff :
      W.primePowerPairing n common.sourceTest common.sourceTest =
        (1 / Real.sqrt (n : ℝ)) *
          (E.legacyValueAt common.sourceConvolutionSquare
              (PrimePowerEvaluation.SourceForwardPoint n) +
            E.legacyValueAt common.sourceConvolutionSquare
              (PrimePowerEvaluation.SourceInversePoint n)))
    (weightReadOff :
      W.vonMangoldtWeight n = ArithmeticFunction.vonMangoldt n)
    (termReadOff :
      W.finitePrimeTerm n
          (W.convolutionStar common.sourceTest common.sourceTest) =
        ArithmeticFunction.vonMangoldt n *
          ((1 / Real.sqrt (n : ℝ)) *
            (E.legacyValueAt common.sourceConvolutionSquare
                (PrimePowerEvaluation.SourceForwardPoint n) +
              E.legacyValueAt common.sourceConvolutionSquare
                (PrimePowerEvaluation.SourceInversePoint n)))) :
    (SourceFinitePrimeArithmeticData.ofSourceEvaluationData E common n
      sourcePrimePowerIndex visible pairingReadOff weightReadOff termReadOff
        ).sourcePairing.model.sourceEvaluation.inverseValue =
      E.valueAt (A.legacy.decode common.sourceConvolutionSquare) ((n : ℝ)⁻¹) :=
  rfl

@[simp] theorem
    SourceFinitePrimeArithmeticData.ofSourceEvaluationData_sourceEvaluator_valueAt_forwardPoint
    {A : AnalyticCore.SourceTestAlgebra}
    (E : AnalyticCore.SourceEvaluationData A)
    {W : WeilFormSymbols}
    (common : CommonSourceTest.ConcreteCommonSourceTest W) (n : ℕ)
    (sourcePrimePowerIndex : IsPrimePow n)
    (visible :
      W.finitePrimeAtomVisible n
        (W.convolutionStar common.sourceTest common.sourceTest))
    (pairingReadOff :
      W.primePowerPairing n common.sourceTest common.sourceTest =
        (1 / Real.sqrt (n : ℝ)) *
          (E.legacyValueAt common.sourceConvolutionSquare
              (PrimePowerEvaluation.SourceForwardPoint n) +
            E.legacyValueAt common.sourceConvolutionSquare
              (PrimePowerEvaluation.SourceInversePoint n)))
    (weightReadOff :
      W.vonMangoldtWeight n = ArithmeticFunction.vonMangoldt n)
    (termReadOff :
      W.finitePrimeTerm n
          (W.convolutionStar common.sourceTest common.sourceTest) =
        ArithmeticFunction.vonMangoldt n *
          ((1 / Real.sqrt (n : ℝ)) *
            (E.legacyValueAt common.sourceConvolutionSquare
                (PrimePowerEvaluation.SourceForwardPoint n) +
              E.legacyValueAt common.sourceConvolutionSquare
                (PrimePowerEvaluation.SourceInversePoint n)))) :
    (SourceFinitePrimeArithmeticData.ofSourceEvaluationData E common n
      sourcePrimePowerIndex visible pairingReadOff weightReadOff termReadOff
        ).sourcePairing.model.sourceEvaluation.sourceEvaluator.valueAt
          common.sourceConvolutionSquare (PrimePowerEvaluation.SourceForwardPoint n) =
      E.valueAt (A.legacy.decode common.sourceConvolutionSquare)
        (PrimePowerEvaluation.SourceForwardPoint n) :=
  rfl

@[simp] theorem
    SourceFinitePrimeArithmeticData.ofSourceEvaluationData_sourceEvaluator_valueAt_inversePoint
    {A : AnalyticCore.SourceTestAlgebra}
    (E : AnalyticCore.SourceEvaluationData A)
    {W : WeilFormSymbols}
    (common : CommonSourceTest.ConcreteCommonSourceTest W) (n : ℕ)
    (sourcePrimePowerIndex : IsPrimePow n)
    (visible :
      W.finitePrimeAtomVisible n
        (W.convolutionStar common.sourceTest common.sourceTest))
    (pairingReadOff :
      W.primePowerPairing n common.sourceTest common.sourceTest =
        (1 / Real.sqrt (n : ℝ)) *
          (E.legacyValueAt common.sourceConvolutionSquare
              (PrimePowerEvaluation.SourceForwardPoint n) +
            E.legacyValueAt common.sourceConvolutionSquare
              (PrimePowerEvaluation.SourceInversePoint n)))
    (weightReadOff :
      W.vonMangoldtWeight n = ArithmeticFunction.vonMangoldt n)
    (termReadOff :
      W.finitePrimeTerm n
          (W.convolutionStar common.sourceTest common.sourceTest) =
        ArithmeticFunction.vonMangoldt n *
          ((1 / Real.sqrt (n : ℝ)) *
            (E.legacyValueAt common.sourceConvolutionSquare
                (PrimePowerEvaluation.SourceForwardPoint n) +
              E.legacyValueAt common.sourceConvolutionSquare
                (PrimePowerEvaluation.SourceInversePoint n)))) :
    (SourceFinitePrimeArithmeticData.ofSourceEvaluationData E common n
      sourcePrimePowerIndex visible pairingReadOff weightReadOff termReadOff
        ).sourcePairing.model.sourceEvaluation.sourceEvaluator.valueAt
          common.sourceConvolutionSquare (PrimePowerEvaluation.SourceInversePoint n) =
      E.valueAt (A.legacy.decode common.sourceConvolutionSquare)
        (PrimePowerEvaluation.SourceInversePoint n) :=
  rfl

@[simp] theorem SourceFinitePrimeArithmeticData.ofSourceEvaluationData_sourceEvaluator_valueAt_nat
    {A : AnalyticCore.SourceTestAlgebra}
    (E : AnalyticCore.SourceEvaluationData A)
    {W : WeilFormSymbols}
    (common : CommonSourceTest.ConcreteCommonSourceTest W) (n : ℕ)
    (sourcePrimePowerIndex : IsPrimePow n)
    (visible :
      W.finitePrimeAtomVisible n
        (W.convolutionStar common.sourceTest common.sourceTest))
    (pairingReadOff :
      W.primePowerPairing n common.sourceTest common.sourceTest =
        (1 / Real.sqrt (n : ℝ)) *
          (E.legacyValueAt common.sourceConvolutionSquare
              (PrimePowerEvaluation.SourceForwardPoint n) +
            E.legacyValueAt common.sourceConvolutionSquare
              (PrimePowerEvaluation.SourceInversePoint n)))
    (weightReadOff :
      W.vonMangoldtWeight n = ArithmeticFunction.vonMangoldt n)
    (termReadOff :
      W.finitePrimeTerm n
          (W.convolutionStar common.sourceTest common.sourceTest) =
        ArithmeticFunction.vonMangoldt n *
          ((1 / Real.sqrt (n : ℝ)) *
            (E.legacyValueAt common.sourceConvolutionSquare
                (PrimePowerEvaluation.SourceForwardPoint n) +
              E.legacyValueAt common.sourceConvolutionSquare
                (PrimePowerEvaluation.SourceInversePoint n)))) :
    (SourceFinitePrimeArithmeticData.ofSourceEvaluationData E common n
      sourcePrimePowerIndex visible pairingReadOff weightReadOff termReadOff
        ).sourcePairing.model.sourceEvaluation.sourceEvaluator.valueAt
          common.sourceConvolutionSquare (n : ℝ) =
      E.valueAt (A.legacy.decode common.sourceConvolutionSquare) (n : ℝ) :=
  rfl

@[simp] theorem
    SourceFinitePrimeArithmeticData.ofSourceEvaluationData_sourceEvaluator_valueAt_inv_nat
    {A : AnalyticCore.SourceTestAlgebra}
    (E : AnalyticCore.SourceEvaluationData A)
    {W : WeilFormSymbols}
    (common : CommonSourceTest.ConcreteCommonSourceTest W) (n : ℕ)
    (sourcePrimePowerIndex : IsPrimePow n)
    (visible :
      W.finitePrimeAtomVisible n
        (W.convolutionStar common.sourceTest common.sourceTest))
    (pairingReadOff :
      W.primePowerPairing n common.sourceTest common.sourceTest =
        (1 / Real.sqrt (n : ℝ)) *
          (E.legacyValueAt common.sourceConvolutionSquare
              (PrimePowerEvaluation.SourceForwardPoint n) +
            E.legacyValueAt common.sourceConvolutionSquare
              (PrimePowerEvaluation.SourceInversePoint n)))
    (weightReadOff :
      W.vonMangoldtWeight n = ArithmeticFunction.vonMangoldt n)
    (termReadOff :
      W.finitePrimeTerm n
          (W.convolutionStar common.sourceTest common.sourceTest) =
        ArithmeticFunction.vonMangoldt n *
          ((1 / Real.sqrt (n : ℝ)) *
            (E.legacyValueAt common.sourceConvolutionSquare
                (PrimePowerEvaluation.SourceForwardPoint n) +
              E.legacyValueAt common.sourceConvolutionSquare
                (PrimePowerEvaluation.SourceInversePoint n)))) :
    (SourceFinitePrimeArithmeticData.ofSourceEvaluationData E common n
      sourcePrimePowerIndex visible pairingReadOff weightReadOff termReadOff
        ).sourcePairing.model.sourceEvaluation.sourceEvaluator.valueAt
          common.sourceConvolutionSquare ((n : ℝ)⁻¹) =
      E.valueAt (A.legacy.decode common.sourceConvolutionSquare) ((n : ℝ)⁻¹) :=
  rfl

theorem SourceFinitePrimeArithmeticData.ofSourceEvaluationData_pairing_formula
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
  simpa using
    PrimePowerPairing.ConcreteCommonPrimePowerPairingData.ofSourceEvaluationData_pairing_formula
      E common n pairingReadOff

noncomputable def SourceFinitePrimeArithmeticDataOnIndexSet.ofSourceEvaluationData
    {A : AnalyticCore.SourceTestAlgebra}
    (E : AnalyticCore.SourceEvaluationData A)
    {W : WeilFormSymbols}
    (common : CommonSourceTest.ConcreteCommonSourceTest W)
    (indexSet : Finset ℕ)
    (sourcePrimePowerIndex :
      ∀ n : ℕ, n ∈ indexSet → IsPrimePow n)
    (visible :
      ∀ n : ℕ, n ∈ indexSet →
        W.finitePrimeAtomVisible n
          (W.convolutionStar common.sourceTest common.sourceTest))
    (pairingReadOff :
      ∀ n : ℕ, n ∈ indexSet →
        W.primePowerPairing n common.sourceTest common.sourceTest =
          (1 / Real.sqrt (n : ℝ)) *
            (E.legacyValueAt common.sourceConvolutionSquare
                (PrimePowerEvaluation.SourceForwardPoint n) +
              E.legacyValueAt common.sourceConvolutionSquare
                (PrimePowerEvaluation.SourceInversePoint n)))
    (weightReadOff :
      ∀ n : ℕ, n ∈ indexSet →
        W.vonMangoldtWeight n = ArithmeticFunction.vonMangoldt n)
    (termReadOff :
      ∀ n : ℕ, n ∈ indexSet →
        W.finitePrimeTerm n
            (W.convolutionStar common.sourceTest common.sourceTest) =
          ArithmeticFunction.vonMangoldt n *
            ((1 / Real.sqrt (n : ℝ)) *
              (E.legacyValueAt common.sourceConvolutionSquare
                  (PrimePowerEvaluation.SourceForwardPoint n) +
                E.legacyValueAt common.sourceConvolutionSquare
                  (PrimePowerEvaluation.SourceInversePoint n)))) :
    SourceFinitePrimeArithmeticDataOnIndexSet
      W common.sourceTest common.sourceTest indexSet where
  atIndex := fun n hn =>
    SourceFinitePrimeArithmeticData.ofSourceEvaluationData
      E common n (sourcePrimePowerIndex n hn) (visible n hn)
      (pairingReadOff n hn) (weightReadOff n hn) (termReadOff n hn)

theorem SourceFinitePrimeArithmeticDataOnIndexSet.ofSourceEvaluationData_pairing_formula
    {A : AnalyticCore.SourceTestAlgebra}
    (E : AnalyticCore.SourceEvaluationData A)
    {W : WeilFormSymbols}
    (common : CommonSourceTest.ConcreteCommonSourceTest W)
    (indexSet : Finset ℕ)
    (pairingReadOff :
      ∀ n : ℕ, n ∈ indexSet →
        W.primePowerPairing n common.sourceTest common.sourceTest =
          (1 / Real.sqrt (n : ℝ)) *
            (E.legacyValueAt common.sourceConvolutionSquare
                (PrimePowerEvaluation.SourceForwardPoint n) +
              E.legacyValueAt common.sourceConvolutionSquare
                (PrimePowerEvaluation.SourceInversePoint n)))
    {n : ℕ} (hn : n ∈ indexSet) :
    W.primePowerPairing n common.sourceTest common.sourceTest =
      (1 / Real.sqrt (n : ℝ)) *
        (E.valueAt (A.legacy.decode common.sourceConvolutionSquare)
            (PrimePowerEvaluation.SourceForwardPoint n) +
          E.valueAt (A.legacy.decode common.sourceConvolutionSquare)
            (PrimePowerEvaluation.SourceInversePoint n)) := by
  exact SourceFinitePrimeArithmeticData.ofSourceEvaluationData_pairing_formula
    E common n (pairingReadOff n hn)

noncomputable def SourceVisibleFinitePrimeArithmeticData.ofSourceEvaluationData
    {A : AnalyticCore.SourceTestAlgebra}
    (E : AnalyticCore.SourceEvaluationData A)
    {W : WeilFormSymbols}
    (common : CommonSourceTest.ConcreteCommonSourceTest W)
    (sourcePrimePowerIndex :
      ∀ n : ℕ, common.toSourceTestEvaluationInterface.sourceAtomVisible n →
        IsPrimePow n)
    (visible :
      ∀ n : ℕ, common.toSourceTestEvaluationInterface.sourceAtomVisible n →
        W.finitePrimeAtomVisible n
          (W.convolutionStar common.sourceTest common.sourceTest))
    (pairingReadOff :
      ∀ n : ℕ, common.toSourceTestEvaluationInterface.sourceAtomVisible n →
        W.primePowerPairing n common.sourceTest common.sourceTest =
          (1 / Real.sqrt (n : ℝ)) *
            (E.legacyValueAt common.sourceConvolutionSquare
                (PrimePowerEvaluation.SourceForwardPoint n) +
              E.legacyValueAt common.sourceConvolutionSquare
                (PrimePowerEvaluation.SourceInversePoint n)))
    (weightReadOff :
      ∀ n : ℕ, common.toSourceTestEvaluationInterface.sourceAtomVisible n →
        W.vonMangoldtWeight n = ArithmeticFunction.vonMangoldt n)
    (termReadOff :
      ∀ n : ℕ, common.toSourceTestEvaluationInterface.sourceAtomVisible n →
        W.finitePrimeTerm n
            (W.convolutionStar common.sourceTest common.sourceTest) =
          ArithmeticFunction.vonMangoldt n *
            ((1 / Real.sqrt (n : ℝ)) *
              (E.legacyValueAt common.sourceConvolutionSquare
                  (PrimePowerEvaluation.SourceForwardPoint n) +
                E.legacyValueAt common.sourceConvolutionSquare
                  (PrimePowerEvaluation.SourceInversePoint n)))) :
    SourceVisibleFinitePrimeArithmeticData
      W common.sourceTest common.sourceTest
      common.toSourceTestEvaluationInterface where
  atVisibleIndex := fun n hn =>
    SourceFinitePrimeArithmeticData.ofSourceEvaluationData
      E common n (sourcePrimePowerIndex n hn) (visible n hn)
      (pairingReadOff n hn) (weightReadOff n hn) (termReadOff n hn)

@[simp] theorem SourceVisibleFinitePrimeArithmeticData.ofSourceEvaluationData_atVisibleIndex
    {A : AnalyticCore.SourceTestAlgebra}
    (E : AnalyticCore.SourceEvaluationData A)
    {W : WeilFormSymbols}
    (common : CommonSourceTest.ConcreteCommonSourceTest W)
    (sourcePrimePowerIndex :
      ∀ n : ℕ, common.toSourceTestEvaluationInterface.sourceAtomVisible n →
        IsPrimePow n)
    (visible :
      ∀ n : ℕ, common.toSourceTestEvaluationInterface.sourceAtomVisible n →
        W.finitePrimeAtomVisible n
          (W.convolutionStar common.sourceTest common.sourceTest))
    (pairingReadOff :
      ∀ n : ℕ, common.toSourceTestEvaluationInterface.sourceAtomVisible n →
        W.primePowerPairing n common.sourceTest common.sourceTest =
          (1 / Real.sqrt (n : ℝ)) *
            (E.legacyValueAt common.sourceConvolutionSquare
                (PrimePowerEvaluation.SourceForwardPoint n) +
              E.legacyValueAt common.sourceConvolutionSquare
                (PrimePowerEvaluation.SourceInversePoint n)))
    (weightReadOff :
      ∀ n : ℕ, common.toSourceTestEvaluationInterface.sourceAtomVisible n →
        W.vonMangoldtWeight n = ArithmeticFunction.vonMangoldt n)
    (termReadOff :
      ∀ n : ℕ, common.toSourceTestEvaluationInterface.sourceAtomVisible n →
        W.finitePrimeTerm n
            (W.convolutionStar common.sourceTest common.sourceTest) =
          ArithmeticFunction.vonMangoldt n *
            ((1 / Real.sqrt (n : ℝ)) *
              (E.legacyValueAt common.sourceConvolutionSquare
                  (PrimePowerEvaluation.SourceForwardPoint n) +
                E.legacyValueAt common.sourceConvolutionSquare
                  (PrimePowerEvaluation.SourceInversePoint n))))
    {n : ℕ}
    (hn : common.toSourceTestEvaluationInterface.sourceAtomVisible n) :
    (SourceVisibleFinitePrimeArithmeticData.ofSourceEvaluationData E common
      sourcePrimePowerIndex visible pairingReadOff weightReadOff
      termReadOff).atVisibleIndex n hn =
      SourceFinitePrimeArithmeticData.ofSourceEvaluationData E common n
        (sourcePrimePowerIndex n hn) (visible n hn) (pairingReadOff n hn)
        (weightReadOff n hn) (termReadOff n hn) :=
  rfl

theorem SourceVisibleFinitePrimeArithmeticData.ofSourceEvaluationData_pairing_formula
    {A : AnalyticCore.SourceTestAlgebra}
    (E : AnalyticCore.SourceEvaluationData A)
    {W : WeilFormSymbols}
    (common : CommonSourceTest.ConcreteCommonSourceTest W)
    (pairingReadOff :
      ∀ n : ℕ, common.toSourceTestEvaluationInterface.sourceAtomVisible n →
        W.primePowerPairing n common.sourceTest common.sourceTest =
          (1 / Real.sqrt (n : ℝ)) *
            (E.legacyValueAt common.sourceConvolutionSquare
                (PrimePowerEvaluation.SourceForwardPoint n) +
              E.legacyValueAt common.sourceConvolutionSquare
                (PrimePowerEvaluation.SourceInversePoint n)))
    {n : ℕ}
    (hn : common.toSourceTestEvaluationInterface.sourceAtomVisible n) :
    W.primePowerPairing n common.sourceTest common.sourceTest =
      (1 / Real.sqrt (n : ℝ)) *
        (E.valueAt (A.legacy.decode common.sourceConvolutionSquare)
            (PrimePowerEvaluation.SourceForwardPoint n) +
          E.valueAt (A.legacy.decode common.sourceConvolutionSquare)
            (PrimePowerEvaluation.SourceInversePoint n)) := by
  exact SourceFinitePrimeArithmeticData.ofSourceEvaluationData_pairing_formula
    E common n (pairingReadOff n hn)

section SourceEvaluationDataOnIndexSet

variable {A : AnalyticCore.SourceTestAlgebra}
variable (E : AnalyticCore.SourceEvaluationData A)
variable {W : WeilFormSymbols}
variable (common : CommonSourceTest.ConcreteCommonSourceTest W)
variable (indexSet : Finset ℕ)
variable (sourcePrimePowerIndex :
  ∀ n : ℕ, n ∈ indexSet → IsPrimePow n)
variable (visible :
  ∀ n : ℕ, n ∈ indexSet →
    W.finitePrimeAtomVisible n
      (W.convolutionStar common.sourceTest common.sourceTest))
variable (pairingReadOff :
  ∀ n : ℕ, n ∈ indexSet →
    W.primePowerPairing n common.sourceTest common.sourceTest =
      (1 / Real.sqrt (n : ℝ)) *
        (E.legacyValueAt common.sourceConvolutionSquare
            (PrimePowerEvaluation.SourceForwardPoint n) +
          E.legacyValueAt common.sourceConvolutionSquare
            (PrimePowerEvaluation.SourceInversePoint n)))
variable (weightReadOff :
  ∀ n : ℕ, n ∈ indexSet →
    W.vonMangoldtWeight n = ArithmeticFunction.vonMangoldt n)
variable (termReadOff :
  ∀ n : ℕ, n ∈ indexSet →
    W.finitePrimeTerm n
        (W.convolutionStar common.sourceTest common.sourceTest) =
      ArithmeticFunction.vonMangoldt n *
        ((1 / Real.sqrt (n : ℝ)) *
          (E.legacyValueAt common.sourceConvolutionSquare
              (PrimePowerEvaluation.SourceForwardPoint n) +
            E.legacyValueAt common.sourceConvolutionSquare
              (PrimePowerEvaluation.SourceInversePoint n))))

namespace SourceFinitePrimeArithmeticDataOnIndexSet

@[simp] theorem ofSourceEvaluationData_atIndex
    {n : ℕ} (hn : n ∈ indexSet) :
    (SourceFinitePrimeArithmeticDataOnIndexSet.ofSourceEvaluationData E common
      indexSet sourcePrimePowerIndex visible pairingReadOff weightReadOff
      termReadOff).atIndex n hn =
      SourceFinitePrimeArithmeticData.ofSourceEvaluationData E common n
        (sourcePrimePowerIndex n hn) (visible n hn) (pairingReadOff n hn)
        (weightReadOff n hn) (termReadOff n hn) :=
  rfl

@[simp] theorem ofSourceEvaluationData_sourcePrimePowerIndex
    {n : ℕ} (hn : n ∈ indexSet) :
    ((SourceFinitePrimeArithmeticDataOnIndexSet.ofSourceEvaluationData E common
      indexSet sourcePrimePowerIndex visible pairingReadOff weightReadOff
      termReadOff).atIndex n hn).sourcePrimePowerIndex =
      sourcePrimePowerIndex n hn :=
  rfl

@[simp] theorem ofSourceEvaluationData_sourceTest
    {n : ℕ} (hn : n ∈ indexSet) :
    ((SourceFinitePrimeArithmeticDataOnIndexSet.ofSourceEvaluationData E common
      indexSet sourcePrimePowerIndex visible pairingReadOff weightReadOff
      termReadOff).atIndex n hn).sourceTest =
      common.toSourceTestEvaluationInterface :=
  rfl

@[simp] theorem ofSourceEvaluationData_sourceAtomVisible
    {n : ℕ} (hn : n ∈ indexSet) :
    ((SourceFinitePrimeArithmeticDataOnIndexSet.ofSourceEvaluationData E common
      indexSet sourcePrimePowerIndex visible pairingReadOff weightReadOff
      termReadOff).atIndex n hn).sourceAtomVisible =
      visible n hn :=
  rfl

@[simp] theorem ofSourceEvaluationData_sourcePrimePowerPairing
    {n : ℕ} (hn : n ∈ indexSet) :
    ((SourceFinitePrimeArithmeticDataOnIndexSet.ofSourceEvaluationData E common
      indexSet sourcePrimePowerIndex visible pairingReadOff weightReadOff
      termReadOff).atIndex n hn).sourcePrimePowerPairing =
      (1 / Real.sqrt (n : ℝ)) *
        (E.valueAt (A.legacy.decode common.sourceConvolutionSquare)
            (PrimePowerEvaluation.SourceForwardPoint n) +
          E.valueAt (A.legacy.decode common.sourceConvolutionSquare)
            (PrimePowerEvaluation.SourceInversePoint n)) :=
  rfl

@[simp] theorem ofSourceEvaluationData_sourcePairing_forwardValue
    {n : ℕ} (hn : n ∈ indexSet) :
    ((SourceFinitePrimeArithmeticDataOnIndexSet.ofSourceEvaluationData E common
      indexSet sourcePrimePowerIndex visible pairingReadOff weightReadOff
      termReadOff).atIndex n hn).sourcePairing.model.sourceEvaluation.forwardValue =
      E.valueAt (A.legacy.decode common.sourceConvolutionSquare)
        (PrimePowerEvaluation.SourceForwardPoint n) :=
  rfl

@[simp] theorem ofSourceEvaluationData_sourcePairing_forwardValue_nat
    {n : ℕ} (hn : n ∈ indexSet) :
    ((SourceFinitePrimeArithmeticDataOnIndexSet.ofSourceEvaluationData E common
      indexSet sourcePrimePowerIndex visible pairingReadOff weightReadOff
      termReadOff).atIndex n hn).sourcePairing.model.sourceEvaluation.forwardValue =
      E.valueAt (A.legacy.decode common.sourceConvolutionSquare) (n : ℝ) :=
  rfl

@[simp] theorem ofSourceEvaluationData_sourcePairing_inverseValue
    {n : ℕ} (hn : n ∈ indexSet) :
    ((SourceFinitePrimeArithmeticDataOnIndexSet.ofSourceEvaluationData E common
      indexSet sourcePrimePowerIndex visible pairingReadOff weightReadOff
      termReadOff).atIndex n hn).sourcePairing.model.sourceEvaluation.inverseValue =
      E.valueAt (A.legacy.decode common.sourceConvolutionSquare)
        (PrimePowerEvaluation.SourceInversePoint n) :=
  rfl

@[simp] theorem ofSourceEvaluationData_sourcePairing_inverseValue_inv_nat
    {n : ℕ} (hn : n ∈ indexSet) :
    ((SourceFinitePrimeArithmeticDataOnIndexSet.ofSourceEvaluationData E common
      indexSet sourcePrimePowerIndex visible pairingReadOff weightReadOff
      termReadOff).atIndex n hn).sourcePairing.model.sourceEvaluation.inverseValue =
      E.valueAt (A.legacy.decode common.sourceConvolutionSquare) ((n : ℝ)⁻¹) :=
  rfl

@[simp] theorem ofSourceEvaluationData_sourceEvaluator_valueAt_forwardPoint
    {n : ℕ} (hn : n ∈ indexSet) :
    ((SourceFinitePrimeArithmeticDataOnIndexSet.ofSourceEvaluationData E common
      indexSet sourcePrimePowerIndex visible pairingReadOff weightReadOff
      termReadOff).atIndex n hn).sourcePairing.model.sourceEvaluation.sourceEvaluator.valueAt
        common.sourceConvolutionSquare (PrimePowerEvaluation.SourceForwardPoint n) =
      E.valueAt (A.legacy.decode common.sourceConvolutionSquare)
        (PrimePowerEvaluation.SourceForwardPoint n) :=
  rfl

@[simp] theorem ofSourceEvaluationData_sourceEvaluator_valueAt_inversePoint
    {n : ℕ} (hn : n ∈ indexSet) :
    ((SourceFinitePrimeArithmeticDataOnIndexSet.ofSourceEvaluationData E common
      indexSet sourcePrimePowerIndex visible pairingReadOff weightReadOff
      termReadOff).atIndex n hn).sourcePairing.model.sourceEvaluation.sourceEvaluator.valueAt
        common.sourceConvolutionSquare (PrimePowerEvaluation.SourceInversePoint n) =
      E.valueAt (A.legacy.decode common.sourceConvolutionSquare)
        (PrimePowerEvaluation.SourceInversePoint n) :=
  rfl

@[simp] theorem ofSourceEvaluationData_sourceEvaluator_valueAt_nat
    {n : ℕ} (hn : n ∈ indexSet) :
    ((SourceFinitePrimeArithmeticDataOnIndexSet.ofSourceEvaluationData E common
      indexSet sourcePrimePowerIndex visible pairingReadOff weightReadOff
      termReadOff).atIndex n hn).sourcePairing.model.sourceEvaluation.sourceEvaluator.valueAt
        common.sourceConvolutionSquare (n : ℝ) =
      E.valueAt (A.legacy.decode common.sourceConvolutionSquare) (n : ℝ) :=
  rfl

@[simp] theorem ofSourceEvaluationData_sourceEvaluator_valueAt_inv_nat
    {n : ℕ} (hn : n ∈ indexSet) :
    ((SourceFinitePrimeArithmeticDataOnIndexSet.ofSourceEvaluationData E common
      indexSet sourcePrimePowerIndex visible pairingReadOff weightReadOff
      termReadOff).atIndex n hn).sourcePairing.model.sourceEvaluation.sourceEvaluator.valueAt
        common.sourceConvolutionSquare ((n : ℝ)⁻¹) =
      E.valueAt (A.legacy.decode common.sourceConvolutionSquare) ((n : ℝ)⁻¹) :=
  rfl

include termReadOff in
theorem ofSourceEvaluationData_term_formula
    {n : ℕ} (hn : n ∈ indexSet) :
    W.finitePrimeTerm n
        (W.convolutionStar common.sourceTest common.sourceTest) =
      ArithmeticFunction.vonMangoldt n *
        ((1 / Real.sqrt (n : ℝ)) *
          (E.valueAt (A.legacy.decode common.sourceConvolutionSquare)
              (PrimePowerEvaluation.SourceForwardPoint n) +
            E.valueAt (A.legacy.decode common.sourceConvolutionSquare)
              (PrimePowerEvaluation.SourceInversePoint n))) := by
  simpa using termReadOff n hn

include weightReadOff in
theorem ofSourceEvaluationData_weight_read_off
    {n : ℕ} (hn : n ∈ indexSet) :
    W.vonMangoldtWeight n = ArithmeticFunction.vonMangoldt n :=
  weightReadOff n hn

end SourceFinitePrimeArithmeticDataOnIndexSet

end SourceEvaluationDataOnIndexSet

end PrimePowerArithmetic
end CCM25Concrete
end Source
end ConnesWeilRH
