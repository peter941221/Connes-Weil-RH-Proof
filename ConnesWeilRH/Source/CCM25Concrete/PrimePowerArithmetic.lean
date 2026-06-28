/-
Copyright (c) 2026 ConnesWeilRH contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ConnesWeilRH contributors
-/

import ConnesWeilRH.Basic
import ConnesWeilRH.Source.CCM25Concrete.PrimePowerPairing
import Mathlib.NumberTheory.ArithmeticFunction.VonMangoldt

/-!
# CCM25 prime-power arithmetic boundary

This module ties the CCM25 finite-prime arithmetic names to Mathlib's
prime-power predicate and von Mangoldt function.  The pairing
`<g | T(n) g>` remains a source read-off datum because the current phase-1
`TestFunction` boundary has no evaluation or operator model.
-/

namespace ConnesWeilRH
namespace Source
namespace CCM25Concrete
namespace PrimePowerArithmetic

open scoped ArithmeticFunction

def SourcePrimePowerIndex (n : ℕ) : Prop :=
  IsPrimePow n

noncomputable def SourceVonMangoldtWeight (n : ℕ) : ℝ :=
  ArithmeticFunction.vonMangoldt n

theorem source_prime_power_index_iff_mathlib
    {n : ℕ} :
    SourcePrimePowerIndex n ↔ IsPrimePow n :=
  Iff.rfl

theorem source_prime_power_index_factorization
    {n : ℕ} (h : SourcePrimePowerIndex n) :
    ∃ p k : ℕ, Nat.Prime p ∧ 0 < k ∧ p ^ k = n :=
  (isPrimePow_nat_iff n).1 h

theorem source_prime_power_index_one_lt
    {n : ℕ} (h : SourcePrimePowerIndex n) :
    1 < n :=
  IsPrimePow.one_lt h

theorem source_von_mangoldt_weight_eq_mathlib
    {n : ℕ} :
    SourceVonMangoldtWeight n = ArithmeticFunction.vonMangoldt n :=
  rfl

theorem source_von_mangoldt_weight_apply
    {n : ℕ} :
    SourceVonMangoldtWeight n =
      if IsPrimePow n then Real.log (Nat.minFac n) else 0 :=
  ArithmeticFunction.vonMangoldt_apply

theorem source_von_mangoldt_weight_prime
    {p : ℕ} (hp : p.Prime) :
    SourceVonMangoldtWeight p = Real.log p :=
  ArithmeticFunction.vonMangoldt_apply_prime hp

structure SourceFinitePrimeArithmeticData
    (W : WeilFormSymbols) (f g : TestFunction) (n : ℕ) where
  sourceTest : PrimePowerTest.SourceTestEvaluationInterface W f g
  sourceAtomVisible :
    W.finitePrimeAtomVisible n (W.convolutionStar f g)
  sourcePairing :
    PrimePowerPairing.SourcePrimePowerPairingData W f g n
  pairingSourceTestReadOff :
    sourcePairing.model.sourceEvaluation.sourceTest = sourceTest
  sourcePrimePowerPairing : ℝ
  weightReadOff :
    W.vonMangoldtWeight n = SourceVonMangoldtWeight n
  pairingReadOff :
    W.primePowerPairing n f g = sourcePrimePowerPairing
  termReadOff :
    W.finitePrimeTerm n (W.convolutionStar f g) =
      SourceVonMangoldtWeight n * sourcePrimePowerPairing

noncomputable def SourceFinitePrimeEvaluatorAtom
    (W : WeilFormSymbols) (f g : TestFunction) (n : ℕ)
    (h : SourceFinitePrimeArithmeticData W f g n) : ℝ :=
  SourceVonMangoldtWeight n *
    ((1 / Real.sqrt (n : ℝ)) *
      (h.sourcePairing.model.sourceEvaluation.sourceEvaluator.valueAt
          (W.convolutionStar f g) (n : ℝ) +
        h.sourcePairing.model.sourceEvaluation.sourceEvaluator.valueAt
          (W.convolutionStar f g) ((n : ℝ)⁻¹)))

def source_arithmetic_data_of_pairing_data
    {W : WeilFormSymbols} {f g : TestFunction} {n : ℕ}
    (sourceTest : PrimePowerTest.SourceTestEvaluationInterface W f g)
    (visible :
      W.finitePrimeAtomVisible n (W.convolutionStar f g))
    (pairing :
      PrimePowerPairing.SourcePrimePowerPairingData W f g n)
    (pairingSourceTestReadOff :
      pairing.model.sourceEvaluation.sourceTest = sourceTest)
    (weightReadOff :
      W.vonMangoldtWeight n = SourceVonMangoldtWeight n)
    (termReadOff :
      W.finitePrimeTerm n (W.convolutionStar f g) =
        SourceVonMangoldtWeight n * pairing.model.sourceTPairing) :
    SourceFinitePrimeArithmeticData W f g n where
  sourceTest := sourceTest
  sourceAtomVisible := visible
  sourcePairing := pairing
  pairingSourceTestReadOff := pairingSourceTestReadOff
  sourcePrimePowerPairing := pairing.model.sourceTPairing
  weightReadOff := weightReadOff
  pairingReadOff := pairing.pairingReadOff
  termReadOff := termReadOff

structure SourceFinitePrimeArithmeticNormalization
    (W : WeilFormSymbols) (f g : TestFunction) where
  atIndex : ∀ n : ℕ, SourceFinitePrimeArithmeticData W f g n

noncomputable def SourceFinitePrimeEvaluatorSum
    (W : WeilFormSymbols) (f g : TestFunction) (indexSet : Finset ℕ)
    (h : SourceFinitePrimeArithmeticNormalization W f g) : ℝ :=
  ∑ n ∈ indexSet, SourceFinitePrimeEvaluatorAtom W f g n (h.atIndex n)

noncomputable def SourceGlobalFinitePrimeEvaluatorSum
    (W : WeilFormSymbols) (f g : TestFunction)
    (h : SourceFinitePrimeArithmeticNormalization W f g) : ℝ :=
  SourceFinitePrimeEvaluatorSum W f g W.globalPrimeIndexSet h

noncomputable def SourceRestrictedFinitePrimeEvaluatorSum
    (W : WeilFormSymbols) (f g : TestFunction) (lambda : ℝ)
    (h : SourceFinitePrimeArithmeticNormalization W f g) : ℝ :=
  SourceFinitePrimeEvaluatorSum W f g (W.restrictedPrimeIndexSet lambda) h

def UsesSourceTest
    {W : WeilFormSymbols} {f g : TestFunction}
    (h : SourceFinitePrimeArithmeticNormalization W f g)
    (sourceTest : PrimePowerTest.SourceTestEvaluationInterface W f g) :
    Prop :=
  ∀ n : ℕ, (h.atIndex n).sourceTest = sourceTest

theorem source_weight_read_off
    {W : WeilFormSymbols} {f g : TestFunction} {n : ℕ}
    (h : SourceFinitePrimeArithmeticData W f g n) :
    W.vonMangoldtWeight n = SourceVonMangoldtWeight n :=
  h.weightReadOff

theorem source_pairing_read_off
    {W : WeilFormSymbols} {f g : TestFunction} {n : ℕ}
    (h : SourceFinitePrimeArithmeticData W f g n) :
    W.primePowerPairing n f g = h.sourcePrimePowerPairing :=
  h.pairingReadOff

theorem source_pairing_evaluation_source_test_read_off
    {W : WeilFormSymbols} {f g : TestFunction} {n : ℕ}
    (h : SourceFinitePrimeArithmeticData W f g n) :
    h.sourcePairing.model.sourceEvaluation.sourceTest = h.sourceTest :=
  h.pairingSourceTestReadOff

theorem source_pairing_evaluation_uses_normalization_source_test
    {W : WeilFormSymbols} {f g : TestFunction}
    {h : SourceFinitePrimeArithmeticNormalization W f g}
    {sourceTest : PrimePowerTest.SourceTestEvaluationInterface W f g}
    (huses : UsesSourceTest h sourceTest) (n : ℕ) :
    (h.atIndex n).sourcePairing.model.sourceEvaluation.sourceTest =
      sourceTest := by
  rw [source_pairing_evaluation_source_test_read_off (h.atIndex n),
    huses n]

theorem source_pairing_formula
    {W : WeilFormSymbols} {f g : TestFunction} {n : ℕ}
    (h : SourceFinitePrimeArithmeticData W f g n) :
    W.primePowerPairing n f g =
      h.sourcePairing.model.sourceNormalizationFactor *
        (h.sourcePairing.model.sourceForwardEvaluation +
          h.sourcePairing.model.sourceInverseEvaluation) :=
  PrimePowerPairing.source_prime_power_pairing_formula h.sourcePairing

theorem source_pairing_formula_inv_sqrt
    {W : WeilFormSymbols} {f g : TestFunction} {n : ℕ}
    (h : SourceFinitePrimeArithmeticData W f g n) :
    W.primePowerPairing n f g =
      PrimePowerPairing.SourceNormalizationFactor n *
        (h.sourcePairing.model.sourceForwardEvaluation +
          h.sourcePairing.model.sourceInverseEvaluation) :=
  PrimePowerPairing.source_prime_power_pairing_formula_inv_sqrt
    h.sourcePairing

theorem source_pairing_formula_real_sqrt
    {W : WeilFormSymbols} {f g : TestFunction} {n : ℕ}
    (h : SourceFinitePrimeArithmeticData W f g n) :
    W.primePowerPairing n f g =
      (1 / Real.sqrt (n : ℝ)) *
        (h.sourcePairing.model.sourceForwardEvaluation +
          h.sourcePairing.model.sourceInverseEvaluation) :=
  PrimePowerPairing.source_prime_power_pairing_formula_real_sqrt
    h.sourcePairing

theorem source_pairing_formula_source_evaluations
    {W : WeilFormSymbols} {f g : TestFunction} {n : ℕ}
    (h : SourceFinitePrimeArithmeticData W f g n) :
    W.primePowerPairing n f g =
      (1 / Real.sqrt (n : ℝ)) *
        (h.sourcePairing.model.sourceEvaluation.forwardValue +
          h.sourcePairing.model.sourceEvaluation.inverseValue) :=
  PrimePowerPairing.source_prime_power_pairing_formula_source_evaluations
    h.sourcePairing

theorem source_pairing_formula_source_evaluator
    {W : WeilFormSymbols} {f g : TestFunction} {n : ℕ}
    (h : SourceFinitePrimeArithmeticData W f g n) :
    W.primePowerPairing n f g =
      (1 / Real.sqrt (n : ℝ)) *
        (h.sourcePairing.model.sourceEvaluation.sourceEvaluator.valueAt
            (W.convolutionStar f g) (n : ℝ) +
          h.sourcePairing.model.sourceEvaluation.sourceEvaluator.valueAt
            (W.convolutionStar f g) ((n : ℝ)⁻¹)) :=
  PrimePowerPairing.source_prime_power_pairing_formula_source_evaluator
    h.sourcePairing

theorem source_finite_prime_term_read_off
    {W : WeilFormSymbols} {f g : TestFunction} {n : ℕ}
    (h : SourceFinitePrimeArithmeticData W f g n) :
    W.finitePrimeTerm n (W.convolutionStar f g) =
      SourceVonMangoldtWeight n * h.sourcePrimePowerPairing :=
  h.termReadOff

theorem source_finite_prime_term_formula_source_evaluator
    {W : WeilFormSymbols} {f g : TestFunction} {n : ℕ}
    (h : SourceFinitePrimeArithmeticData W f g n) :
    W.finitePrimeTerm n (W.convolutionStar f g) =
      SourceFinitePrimeEvaluatorAtom W f g n h := by
  dsimp [SourceFinitePrimeEvaluatorAtom]
  rw [h.termReadOff]
  congr 1
  rw [← h.pairingReadOff]
  exact source_pairing_formula_source_evaluator h

end PrimePowerArithmetic
end CCM25Concrete
end Source
end ConnesWeilRH
