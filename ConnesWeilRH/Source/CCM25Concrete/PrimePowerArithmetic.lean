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

structure SourceFinitePrimeArithmeticIndexData
    (W : WeilFormSymbols) (f g : TestFunction) (n : ℕ) where
  sourcePrimePowerIndex : IsPrimePow n
  sourceTest : PrimePowerTest.SourceTestEvaluationInterface W f g
  sourceAtomVisible :
    W.finitePrimeAtomVisible n (W.convolutionStar f g)

structure SourceFinitePrimeArithmeticPairingData
    (W : WeilFormSymbols) (f g : TestFunction) (n : ℕ)
    (indexData : SourceFinitePrimeArithmeticIndexData W f g n) where
  sourcePairing :
    PrimePowerPairing.SourcePrimePowerPairingData W f g n
  pairingSourceTestReadOff :
    sourcePairing.model.sourceEvaluation.sourceTest = indexData.sourceTest
  sourcePrimePowerPairing : ℝ
  pairingReadOff :
    W.primePowerPairing n f g = sourcePrimePowerPairing

structure SourceFinitePrimeArithmeticFormulaData
    (W : WeilFormSymbols) (f g : TestFunction) (n : ℕ)
    (indexData : SourceFinitePrimeArithmeticIndexData W f g n)
    (pairingData :
      SourceFinitePrimeArithmeticPairingData W f g n indexData) where
  weightReadOff :
    W.vonMangoldtWeight n = ArithmeticFunction.vonMangoldt n
  termReadOff :
    W.finitePrimeTerm n (W.convolutionStar f g) =
      ArithmeticFunction.vonMangoldt n * pairingData.sourcePrimePowerPairing

structure SourceFinitePrimeArithmeticData
    (W : WeilFormSymbols) (f g : TestFunction) (n : ℕ) where
  indexData : SourceFinitePrimeArithmeticIndexData W f g n
  pairingData :
    SourceFinitePrimeArithmeticPairingData W f g n indexData
  formulaData :
    SourceFinitePrimeArithmeticFormulaData W f g n indexData pairingData

namespace SourceFinitePrimeArithmeticData

def sourcePrimePowerIndex
    {W : WeilFormSymbols} {f g : TestFunction} {n : ℕ}
    (h : SourceFinitePrimeArithmeticData W f g n) :
    IsPrimePow n :=
  h.indexData.sourcePrimePowerIndex

def sourceTest
    {W : WeilFormSymbols} {f g : TestFunction} {n : ℕ}
    (h : SourceFinitePrimeArithmeticData W f g n) :
    PrimePowerTest.SourceTestEvaluationInterface W f g :=
  h.indexData.sourceTest

theorem sourceAtomVisible
    {W : WeilFormSymbols} {f g : TestFunction} {n : ℕ}
    (h : SourceFinitePrimeArithmeticData W f g n) :
    W.finitePrimeAtomVisible n (W.convolutionStar f g) :=
  h.indexData.sourceAtomVisible

def sourcePairing
    {W : WeilFormSymbols} {f g : TestFunction} {n : ℕ}
    (h : SourceFinitePrimeArithmeticData W f g n) :
    PrimePowerPairing.SourcePrimePowerPairingData W f g n :=
  h.pairingData.sourcePairing

theorem pairingSourceTestReadOff
    {W : WeilFormSymbols} {f g : TestFunction} {n : ℕ}
    (h : SourceFinitePrimeArithmeticData W f g n) :
    h.sourcePairing.model.sourceEvaluation.sourceTest = h.sourceTest :=
  h.pairingData.pairingSourceTestReadOff

def sourcePrimePowerPairing
    {W : WeilFormSymbols} {f g : TestFunction} {n : ℕ}
    (h : SourceFinitePrimeArithmeticData W f g n) : ℝ :=
  h.pairingData.sourcePrimePowerPairing

theorem weightReadOff
    {W : WeilFormSymbols} {f g : TestFunction} {n : ℕ}
    (h : SourceFinitePrimeArithmeticData W f g n) :
    W.vonMangoldtWeight n = ArithmeticFunction.vonMangoldt n :=
  h.formulaData.weightReadOff

theorem pairingReadOff
    {W : WeilFormSymbols} {f g : TestFunction} {n : ℕ}
    (h : SourceFinitePrimeArithmeticData W f g n) :
    W.primePowerPairing n f g = h.sourcePrimePowerPairing :=
  h.pairingData.pairingReadOff

theorem termReadOff
    {W : WeilFormSymbols} {f g : TestFunction} {n : ℕ}
    (h : SourceFinitePrimeArithmeticData W f g n) :
    W.finitePrimeTerm n (W.convolutionStar f g) =
      ArithmeticFunction.vonMangoldt n * h.sourcePrimePowerPairing :=
  h.formulaData.termReadOff

end SourceFinitePrimeArithmeticData

noncomputable def SourceFinitePrimeEvaluatorAtom
    (W : WeilFormSymbols) (f g : TestFunction) (n : ℕ)
    (h : SourceFinitePrimeArithmeticData W f g n) : ℝ :=
  ArithmeticFunction.vonMangoldt n *
    ((1 / Real.sqrt (n : ℝ)) *
      (h.sourcePairing.model.sourceEvaluation.forwardValue +
        h.sourcePairing.model.sourceEvaluation.inverseValue))

noncomputable def MathlibFinitePrimeEvaluatorAtom
    (W : WeilFormSymbols) (f g : TestFunction) (n : ℕ)
    (h : SourceFinitePrimeArithmeticData W f g n) : ℝ :=
  ArithmeticFunction.vonMangoldt n *
    ((1 / Real.sqrt (n : ℝ)) *
      (h.sourcePairing.model.sourceEvaluation.forwardValue +
        h.sourcePairing.model.sourceEvaluation.inverseValue))

theorem source_finite_prime_evaluator_atom_eq_source_evaluations
    {W : WeilFormSymbols} {f g : TestFunction} {n : ℕ}
    (h : SourceFinitePrimeArithmeticData W f g n) :
    SourceFinitePrimeEvaluatorAtom W f g n h =
      ArithmeticFunction.vonMangoldt n *
        ((1 / Real.sqrt (n : ℝ)) *
          (h.sourcePairing.model.sourceEvaluation.forwardValue +
            h.sourcePairing.model.sourceEvaluation.inverseValue)) :=
  rfl

theorem mathlib_finite_prime_evaluator_atom_eq_source_evaluations
    {W : WeilFormSymbols} {f g : TestFunction} {n : ℕ}
    (h : SourceFinitePrimeArithmeticData W f g n) :
    MathlibFinitePrimeEvaluatorAtom W f g n h =
      ArithmeticFunction.vonMangoldt n *
        ((1 / Real.sqrt (n : ℝ)) *
          (h.sourcePairing.model.sourceEvaluation.forwardValue +
            h.sourcePairing.model.sourceEvaluation.inverseValue)) :=
  rfl

theorem source_finite_prime_evaluator_atom_eq_source_evaluator
    {W : WeilFormSymbols} {f g : TestFunction} {n : ℕ}
    (h : SourceFinitePrimeArithmeticData W f g n) :
    SourceFinitePrimeEvaluatorAtom W f g n h =
      ArithmeticFunction.vonMangoldt n *
        ((1 / Real.sqrt (n : ℝ)) *
          (h.sourcePairing.model.sourceEvaluation.sourceEvaluator.valueAt
              (W.convolutionStar f g) (n : ℝ) +
            h.sourcePairing.model.sourceEvaluation.sourceEvaluator.valueAt
              (W.convolutionStar f g) ((n : ℝ)⁻¹))) := by
  rw [source_finite_prime_evaluator_atom_eq_source_evaluations h,
    PrimePowerEvaluation.source_forward_value_at_source_points
      h.sourcePairing.model.sourceEvaluation,
    PrimePowerEvaluation.source_inverse_value_at_source_points
      h.sourcePairing.model.sourceEvaluation]

theorem mathlib_finite_prime_evaluator_atom_eq_source_evaluator
    {W : WeilFormSymbols} {f g : TestFunction} {n : ℕ}
    (h : SourceFinitePrimeArithmeticData W f g n) :
    MathlibFinitePrimeEvaluatorAtom W f g n h =
      ArithmeticFunction.vonMangoldt n *
        ((1 / Real.sqrt (n : ℝ)) *
          (h.sourcePairing.model.sourceEvaluation.sourceEvaluator.valueAt
              (W.convolutionStar f g) (n : ℝ) +
            h.sourcePairing.model.sourceEvaluation.sourceEvaluator.valueAt
              (W.convolutionStar f g) ((n : ℝ)⁻¹))) := by
  rw [mathlib_finite_prime_evaluator_atom_eq_source_evaluations h,
    PrimePowerEvaluation.source_forward_value_at_source_points
      h.sourcePairing.model.sourceEvaluation,
    PrimePowerEvaluation.source_inverse_value_at_source_points
      h.sourcePairing.model.sourceEvaluation]

theorem source_finite_prime_evaluator_atom_eq_mathlib
    {W : WeilFormSymbols} {f g : TestFunction} {n : ℕ}
    (h : SourceFinitePrimeArithmeticData W f g n) :
    SourceFinitePrimeEvaluatorAtom W f g n h =
      MathlibFinitePrimeEvaluatorAtom W f g n h :=
  rfl

theorem mathlib_finite_prime_evaluator_atom_eq_zero_of_not_prime_power
    {W : WeilFormSymbols} {f g : TestFunction} {n : ℕ}
    (h : SourceFinitePrimeArithmeticData W f g n) (hn : ¬ IsPrimePow n) :
    MathlibFinitePrimeEvaluatorAtom W f g n h = 0 := by
  simp [MathlibFinitePrimeEvaluatorAtom, ArithmeticFunction.vonMangoldt_apply, hn]

theorem source_finite_prime_evaluator_atom_eq_zero_of_not_prime_power
    {W : WeilFormSymbols} {f g : TestFunction} {n : ℕ}
    (h : SourceFinitePrimeArithmeticData W f g n) (hn : ¬ IsPrimePow n) :
    SourceFinitePrimeEvaluatorAtom W f g n h = 0 := by
  rw [source_finite_prime_evaluator_atom_eq_mathlib h]
  exact mathlib_finite_prime_evaluator_atom_eq_zero_of_not_prime_power h hn

structure SourceFinitePrimeLocalFormulaData
    (W : WeilFormSymbols) (f g : TestFunction) (n : ℕ)
    (h : SourceFinitePrimeArithmeticData W f g n) where
  weightReadOff :
    W.vonMangoldtWeight n = ArithmeticFunction.vonMangoldt n
  pairingFormulaSourceEvaluator :
    W.primePowerPairing n f g =
      (1 / Real.sqrt (n : ℝ)) *
        (h.sourcePairing.model.sourceEvaluation.sourceEvaluator.valueAt
            (W.convolutionStar f g) (n : ℝ) +
          h.sourcePairing.model.sourceEvaluation.sourceEvaluator.valueAt
            (W.convolutionStar f g) ((n : ℝ)⁻¹))
  termFormulaSourceEvaluator :
    W.finitePrimeTerm n (W.convolutionStar f g) =
      SourceFinitePrimeEvaluatorAtom W f g n h

def source_arithmetic_data_of_pairing_data
    {W : WeilFormSymbols} {f g : TestFunction} {n : ℕ}
    (sourcePrimePowerIndex : IsPrimePow n)
    (sourceTest : PrimePowerTest.SourceTestEvaluationInterface W f g)
    (visible :
      W.finitePrimeAtomVisible n (W.convolutionStar f g))
    (pairing :
      PrimePowerPairing.SourcePrimePowerPairingData W f g n)
    (pairingSourceTestReadOff :
      pairing.model.sourceEvaluation.sourceTest = sourceTest)
    (weightReadOff :
      W.vonMangoldtWeight n = ArithmeticFunction.vonMangoldt n)
    (termReadOff :
      W.finitePrimeTerm n (W.convolutionStar f g) =
        ArithmeticFunction.vonMangoldt n * pairing.model.sourceTPairing) :
    SourceFinitePrimeArithmeticData W f g n where
  indexData :=
    { sourcePrimePowerIndex := sourcePrimePowerIndex
      sourceTest := sourceTest
      sourceAtomVisible := visible }
  pairingData :=
    { sourcePairing := pairing
      pairingSourceTestReadOff := pairingSourceTestReadOff
      sourcePrimePowerPairing := pairing.model.sourceTPairing
      pairingReadOff := pairing.pairingReadOff }
  formulaData :=
    { weightReadOff := weightReadOff
      termReadOff := termReadOff }

structure SourceFinitePrimeArithmeticNormalization
    (W : WeilFormSymbols) (f g : TestFunction) where
  atIndex : ∀ n : ℕ, SourceFinitePrimeArithmeticData W f g n

structure SourceFinitePrimeArithmeticDataForSourceTest
    (W : WeilFormSymbols) (f g : TestFunction)
    (sourceTest : PrimePowerTest.SourceTestEvaluationInterface W f g)
    (n : ℕ) where
  data : SourceFinitePrimeArithmeticData W f g n
  sourceTestReadOff : data.sourceTest = sourceTest

namespace SourceFinitePrimeArithmeticDataForSourceTest

def ofArithmeticData
    {W : WeilFormSymbols} {f g : TestFunction}
    {sourceTest : PrimePowerTest.SourceTestEvaluationInterface W f g}
    {n : ℕ}
    (data : SourceFinitePrimeArithmeticData W f g n)
    (sourceTestReadOff : data.sourceTest = sourceTest) :
    SourceFinitePrimeArithmeticDataForSourceTest W f g sourceTest n where
  data := data
  sourceTestReadOff := sourceTestReadOff

theorem ext_data
    {W : WeilFormSymbols} {f g : TestFunction}
    {sourceTest : PrimePowerTest.SourceTestEvaluationInterface W f g}
    {n : ℕ}
    {a b : SourceFinitePrimeArithmeticDataForSourceTest W f g sourceTest n}
    (h : a.data = b.data) : a = b := by
  cases a with
  | mk adata areadOff =>
  cases b with
  | mk bdata breadOff =>
  cases h
  congr

end SourceFinitePrimeArithmeticDataForSourceTest

structure SourceFinitePrimeArithmeticNormalizationForSourceTest
    (W : WeilFormSymbols) (f g : TestFunction)
    (sourceTest : PrimePowerTest.SourceTestEvaluationInterface W f g) where
  atIndex :
    ∀ n : ℕ,
      SourceFinitePrimeArithmeticDataForSourceTest W f g sourceTest n

namespace SourceFinitePrimeArithmeticNormalizationForSourceTest

def toNormalization
    {W : WeilFormSymbols} {f g : TestFunction}
    {sourceTest : PrimePowerTest.SourceTestEvaluationInterface W f g}
    (h :
      SourceFinitePrimeArithmeticNormalizationForSourceTest W f g sourceTest) :
    SourceFinitePrimeArithmeticNormalization W f g where
  atIndex := fun n => (h.atIndex n).data

def ofNormalization
    {W : WeilFormSymbols} {f g : TestFunction}
    {sourceTest : PrimePowerTest.SourceTestEvaluationInterface W f g}
    (h : SourceFinitePrimeArithmeticNormalization W f g)
    (hUse : ∀ n : ℕ, (h.atIndex n).sourceTest = sourceTest) :
    SourceFinitePrimeArithmeticNormalizationForSourceTest W f g sourceTest where
  atIndex := fun n =>
    SourceFinitePrimeArithmeticDataForSourceTest.ofArithmeticData
      (h.atIndex n) (hUse n)

theorem ext_atIndex
    {W : WeilFormSymbols} {f g : TestFunction}
    {sourceTest : PrimePowerTest.SourceTestEvaluationInterface W f g}
    {a b : SourceFinitePrimeArithmeticNormalizationForSourceTest W f g sourceTest}
    (h : ∀ n : ℕ, a.atIndex n = b.atIndex n) : a = b := by
  cases a with
  | mk aAt =>
  cases b with
  | mk bAt =>
  congr
  funext n
  exact h n

theorem toNormalization_uses_sourceTest
    {W : WeilFormSymbols} {f g : TestFunction}
    {sourceTest : PrimePowerTest.SourceTestEvaluationInterface W f g}
    (h :
      SourceFinitePrimeArithmeticNormalizationForSourceTest W f g sourceTest) :
    ∀ n : ℕ, ((h.toNormalization).atIndex n).sourceTest = sourceTest :=
  fun n => (h.atIndex n).sourceTestReadOff

end SourceFinitePrimeArithmeticNormalizationForSourceTest

def UsesSourceTest
    {W : WeilFormSymbols} {f g : TestFunction}
    (h : SourceFinitePrimeArithmeticNormalization W f g)
    (sourceTest : PrimePowerTest.SourceTestEvaluationInterface W f g) :
    Prop :=
  ∀ n : ℕ, (h.atIndex n).sourceTest = sourceTest

structure SourceFinitePrimeArithmeticDataOnIndexSet
    (W : WeilFormSymbols) (f g : TestFunction) (indexSet : Finset ℕ) where
  atIndex :
    ∀ n : ℕ, n ∈ indexSet → SourceFinitePrimeArithmeticData W f g n

structure SourceVisibleFinitePrimeArithmeticData
    (W : WeilFormSymbols) (f g : TestFunction)
    (sourceTest : PrimePowerTest.SourceTestEvaluationInterface W f g) where
  atVisibleIndex :
    ∀ n : ℕ,
      sourceTest.sourceAtomVisible n →
        SourceFinitePrimeArithmeticData W f g n

namespace SourceVisibleFinitePrimeArithmeticData

def ofGlobalNormalization
    {W : WeilFormSymbols} {f g : TestFunction}
    {sourceTest : PrimePowerTest.SourceTestEvaluationInterface W f g}
    (h : SourceFinitePrimeArithmeticNormalization W f g)
    (_hUse : UsesSourceTest h sourceTest) :
    SourceVisibleFinitePrimeArithmeticData W f g sourceTest where
  atVisibleIndex := fun n _ => h.atIndex n

@[simp] theorem ofGlobalNormalization_atVisibleIndex
    {W : WeilFormSymbols} {f g : TestFunction}
    {sourceTest : PrimePowerTest.SourceTestEvaluationInterface W f g}
    (h : SourceFinitePrimeArithmeticNormalization W f g)
    (hUse : UsesSourceTest h sourceTest)
    {n : ℕ} (hn : sourceTest.sourceAtomVisible n) :
    (ofGlobalNormalization h hUse).atVisibleIndex n hn = h.atIndex n :=
  rfl

end SourceVisibleFinitePrimeArithmeticData

noncomputable def SourceFinitePrimeEvaluatorSum
    (W : WeilFormSymbols) (f g : TestFunction) (indexSet : Finset ℕ)
    (h : SourceFinitePrimeArithmeticNormalization W f g) : ℝ :=
  ∑ n ∈ indexSet, SourceFinitePrimeEvaluatorAtom W f g n (h.atIndex n)

noncomputable def SourceFinitePrimeEvaluatorSumOnIndexSet
    (W : WeilFormSymbols) (f g : TestFunction) (indexSet : Finset ℕ)
    (h : SourceFinitePrimeArithmeticDataOnIndexSet W f g indexSet) : ℝ :=
  ∑ n ∈ indexSet,
    if hn : n ∈ indexSet then
      SourceFinitePrimeEvaluatorAtom W f g n (h.atIndex n hn)
    else 0

noncomputable def MathlibFinitePrimeEvaluatorSumOnIndexSet
    (W : WeilFormSymbols) (f g : TestFunction) (indexSet : Finset ℕ)
    (h : SourceFinitePrimeArithmeticDataOnIndexSet W f g indexSet) : ℝ :=
  ∑ n ∈ indexSet,
    if hn : n ∈ indexSet then
      MathlibFinitePrimeEvaluatorAtom W f g n (h.atIndex n hn)
    else 0

theorem source_finite_prime_evaluator_sum_on_index_set_eq_mathlib
    {W : WeilFormSymbols} {f g : TestFunction} {indexSet : Finset ℕ}
    (h : SourceFinitePrimeArithmeticDataOnIndexSet W f g indexSet) :
    SourceFinitePrimeEvaluatorSumOnIndexSet W f g indexSet h =
      MathlibFinitePrimeEvaluatorSumOnIndexSet W f g indexSet h := by
  simp [SourceFinitePrimeEvaluatorSumOnIndexSet,
    MathlibFinitePrimeEvaluatorSumOnIndexSet,
    source_finite_prime_evaluator_atom_eq_mathlib]

theorem mathlib_finite_prime_evaluator_sum_on_index_set_eq_prime_power_filter
    {W : WeilFormSymbols} {f g : TestFunction} {indexSet : Finset ℕ}
    (h : SourceFinitePrimeArithmeticDataOnIndexSet W f g indexSet) :
    MathlibFinitePrimeEvaluatorSumOnIndexSet W f g indexSet h =
      ∑ n ∈ indexSet.filter IsPrimePow,
        if hn : n ∈ indexSet then
          MathlibFinitePrimeEvaluatorAtom W f g n (h.atIndex n hn)
        else
          0 := by
  rw [MathlibFinitePrimeEvaluatorSumOnIndexSet, Finset.sum_filter]
  refine Finset.sum_congr rfl ?_
  intro n hn
  by_cases hPrime : IsPrimePow n
  · simp [hPrime, hn]
  · simp [hPrime, hn,
      mathlib_finite_prime_evaluator_atom_eq_zero_of_not_prime_power
        (h.atIndex n hn) hPrime]

theorem source_finite_prime_evaluator_sum_on_index_set_eq_prime_power_filter
    {W : WeilFormSymbols} {f g : TestFunction} {indexSet : Finset ℕ}
    (h : SourceFinitePrimeArithmeticDataOnIndexSet W f g indexSet) :
    SourceFinitePrimeEvaluatorSumOnIndexSet W f g indexSet h =
      ∑ n ∈ indexSet.filter IsPrimePow,
        if hn : n ∈ indexSet then
          MathlibFinitePrimeEvaluatorAtom W f g n (h.atIndex n hn)
        else
          0 := by
  rw [source_finite_prime_evaluator_sum_on_index_set_eq_mathlib h]
  exact mathlib_finite_prime_evaluator_sum_on_index_set_eq_prime_power_filter h

def SourceFinitePrimeArithmeticDataOnIndexSet.ofGlobalNormalization
    {W : WeilFormSymbols} {f g : TestFunction} {indexSet : Finset ℕ}
    (h : SourceFinitePrimeArithmeticNormalization W f g) :
    SourceFinitePrimeArithmeticDataOnIndexSet W f g indexSet where
  atIndex := fun n _ => h.atIndex n

theorem source_finite_prime_evaluator_sum_on_index_set_of_global
    {W : WeilFormSymbols} {f g : TestFunction} {indexSet : Finset ℕ}
    (h : SourceFinitePrimeArithmeticNormalization W f g) :
    SourceFinitePrimeEvaluatorSumOnIndexSet W f g indexSet
        (SourceFinitePrimeArithmeticDataOnIndexSet.ofGlobalNormalization h) =
      SourceFinitePrimeEvaluatorSum W f g indexSet h := by
  simp [SourceFinitePrimeEvaluatorSumOnIndexSet,
    SourceFinitePrimeArithmeticDataOnIndexSet.ofGlobalNormalization,
    SourceFinitePrimeEvaluatorSum]

noncomputable def SourceGlobalFinitePrimeEvaluatorSum
    (W : WeilFormSymbols) (f g : TestFunction)
    (h : SourceFinitePrimeArithmeticNormalization W f g) : ℝ :=
  SourceFinitePrimeEvaluatorSum W f g W.globalPrimeIndexSet h

noncomputable def SourceRestrictedFinitePrimeEvaluatorSum
    (W : WeilFormSymbols) (f g : TestFunction) (lambda : ℝ)
    (h : SourceFinitePrimeArithmeticNormalization W f g) : ℝ :=
  SourceFinitePrimeEvaluatorSum W f g (W.restrictedPrimeIndexSet lambda) h

abbrev SourceGlobalFinitePrimeArithmeticData
    (W : WeilFormSymbols) (f g : TestFunction) :=
  SourceFinitePrimeArithmeticDataOnIndexSet W f g W.globalPrimeIndexSet

abbrev SourceRestrictedFinitePrimeArithmeticData
    (W : WeilFormSymbols) (f g : TestFunction) (lambda : ℝ) :=
  SourceFinitePrimeArithmeticDataOnIndexSet W f g
    (W.restrictedPrimeIndexSet lambda)

noncomputable def SourceGlobalFinitePrimeEvaluatorSumOnIndexSet
    (W : WeilFormSymbols) (f g : TestFunction)
    (h : SourceGlobalFinitePrimeArithmeticData W f g) : ℝ :=
  SourceFinitePrimeEvaluatorSumOnIndexSet W f g W.globalPrimeIndexSet h

noncomputable def SourceRestrictedFinitePrimeEvaluatorSumOnIndexSet
    (W : WeilFormSymbols) (f g : TestFunction) (lambda : ℝ)
    (h : SourceRestrictedFinitePrimeArithmeticData W f g lambda) : ℝ :=
  SourceFinitePrimeEvaluatorSumOnIndexSet W f g
    (W.restrictedPrimeIndexSet lambda) h

noncomputable def MathlibGlobalFinitePrimeEvaluatorSumOnIndexSet
    (W : WeilFormSymbols) (f g : TestFunction)
    (h : SourceGlobalFinitePrimeArithmeticData W f g) : ℝ :=
  MathlibFinitePrimeEvaluatorSumOnIndexSet W f g W.globalPrimeIndexSet h

noncomputable def MathlibRestrictedFinitePrimeEvaluatorSumOnIndexSet
    (W : WeilFormSymbols) (f g : TestFunction) (lambda : ℝ)
    (h : SourceRestrictedFinitePrimeArithmeticData W f g lambda) : ℝ :=
  MathlibFinitePrimeEvaluatorSumOnIndexSet W f g
    (W.restrictedPrimeIndexSet lambda) h

theorem source_global_finite_prime_evaluator_sum_on_index_set_eq_mathlib
    {W : WeilFormSymbols} {f g : TestFunction}
    (h : SourceGlobalFinitePrimeArithmeticData W f g) :
    SourceGlobalFinitePrimeEvaluatorSumOnIndexSet W f g h =
      MathlibGlobalFinitePrimeEvaluatorSumOnIndexSet W f g h :=
  source_finite_prime_evaluator_sum_on_index_set_eq_mathlib h

theorem source_restricted_finite_prime_evaluator_sum_on_index_set_eq_mathlib
    {W : WeilFormSymbols} {f g : TestFunction} {lambda : ℝ}
    (h : SourceRestrictedFinitePrimeArithmeticData W f g lambda) :
    SourceRestrictedFinitePrimeEvaluatorSumOnIndexSet W f g lambda h =
      MathlibRestrictedFinitePrimeEvaluatorSumOnIndexSet W f g lambda h :=
  source_finite_prime_evaluator_sum_on_index_set_eq_mathlib h

theorem mathlib_global_finite_prime_evaluator_sum_on_index_set_eq_prime_power_filter
    {W : WeilFormSymbols} {f g : TestFunction}
    (h : SourceGlobalFinitePrimeArithmeticData W f g) :
    MathlibGlobalFinitePrimeEvaluatorSumOnIndexSet W f g h =
      ∑ n ∈ W.globalPrimeIndexSet.filter IsPrimePow,
        if hn : n ∈ W.globalPrimeIndexSet then
          MathlibFinitePrimeEvaluatorAtom W f g n (h.atIndex n hn)
        else
          0 :=
  mathlib_finite_prime_evaluator_sum_on_index_set_eq_prime_power_filter h

theorem mathlib_restricted_finite_prime_evaluator_sum_on_index_set_eq_prime_power_filter
    {W : WeilFormSymbols} {f g : TestFunction} {lambda : ℝ}
    (h : SourceRestrictedFinitePrimeArithmeticData W f g lambda) :
    MathlibRestrictedFinitePrimeEvaluatorSumOnIndexSet W f g lambda h =
      ∑ n ∈ (W.restrictedPrimeIndexSet lambda).filter IsPrimePow,
        if hn : n ∈ W.restrictedPrimeIndexSet lambda then
          MathlibFinitePrimeEvaluatorAtom W f g n (h.atIndex n hn)
        else
          0 :=
  mathlib_finite_prime_evaluator_sum_on_index_set_eq_prime_power_filter h

theorem source_global_finite_prime_evaluator_sum_on_index_set_eq_prime_power_filter
    {W : WeilFormSymbols} {f g : TestFunction}
    (h : SourceGlobalFinitePrimeArithmeticData W f g) :
    SourceGlobalFinitePrimeEvaluatorSumOnIndexSet W f g h =
      ∑ n ∈ W.globalPrimeIndexSet.filter IsPrimePow,
        if hn : n ∈ W.globalPrimeIndexSet then
          MathlibFinitePrimeEvaluatorAtom W f g n (h.atIndex n hn)
        else
          0 := by
  rw [source_global_finite_prime_evaluator_sum_on_index_set_eq_mathlib h]
  exact mathlib_global_finite_prime_evaluator_sum_on_index_set_eq_prime_power_filter h

theorem source_restricted_finite_prime_evaluator_sum_on_index_set_eq_prime_power_filter
    {W : WeilFormSymbols} {f g : TestFunction} {lambda : ℝ}
    (h : SourceRestrictedFinitePrimeArithmeticData W f g lambda) :
    SourceRestrictedFinitePrimeEvaluatorSumOnIndexSet W f g lambda h =
      ∑ n ∈ (W.restrictedPrimeIndexSet lambda).filter IsPrimePow,
        if hn : n ∈ W.restrictedPrimeIndexSet lambda then
          MathlibFinitePrimeEvaluatorAtom W f g n (h.atIndex n hn)
        else
          0 := by
  rw [source_restricted_finite_prime_evaluator_sum_on_index_set_eq_mathlib h]
  exact mathlib_restricted_finite_prime_evaluator_sum_on_index_set_eq_prime_power_filter h

theorem source_global_finite_prime_evaluator_sum_on_index_set_of_global
    {W : WeilFormSymbols} {f g : TestFunction}
    (h : SourceFinitePrimeArithmeticNormalization W f g) :
    SourceGlobalFinitePrimeEvaluatorSumOnIndexSet W f g
        (SourceFinitePrimeArithmeticDataOnIndexSet.ofGlobalNormalization h) =
      SourceGlobalFinitePrimeEvaluatorSum W f g h :=
  source_finite_prime_evaluator_sum_on_index_set_of_global h

theorem source_restricted_finite_prime_evaluator_sum_on_index_set_of_global
    {W : WeilFormSymbols} {f g : TestFunction} {lambda : ℝ}
    (h : SourceFinitePrimeArithmeticNormalization W f g) :
    SourceRestrictedFinitePrimeEvaluatorSumOnIndexSet W f g lambda
        (SourceFinitePrimeArithmeticDataOnIndexSet.ofGlobalNormalization h) =
      SourceRestrictedFinitePrimeEvaluatorSum W f g lambda h :=
  source_finite_prime_evaluator_sum_on_index_set_of_global h

structure MathlibGlobalFinitePrimeSumFormulaData
    (W : WeilFormSymbols) (f g : TestFunction)
    (h : SourceGlobalFinitePrimeArithmeticData W f g) where
  finitePrimeTermSumReadOff :
    (∑ n ∈ W.globalPrimeIndexSet,
      W.finitePrimeTerm n (W.convolutionStar f g)) =
      MathlibGlobalFinitePrimeEvaluatorSumOnIndexSet W f g h
  vonMangoldtPairingSumReadOff :
    (∑ n ∈ W.globalPrimeIndexSet,
      W.vonMangoldtWeight n * W.primePowerPairing n f g) =
      MathlibGlobalFinitePrimeEvaluatorSumOnIndexSet W f g h

structure MathlibRestrictedFinitePrimeSumFormulaData
    (W : WeilFormSymbols) (f g : TestFunction) (lambda : ℝ)
    (h : SourceRestrictedFinitePrimeArithmeticData W f g lambda) where
  finitePrimeTermSumReadOff :
    (∑ n ∈ W.restrictedPrimeIndexSet lambda,
      W.finitePrimeTerm n (W.convolutionStar f g)) =
      MathlibRestrictedFinitePrimeEvaluatorSumOnIndexSet W f g lambda h
  vonMangoldtPairingSumReadOff :
    (∑ n ∈ W.restrictedPrimeIndexSet lambda,
      W.vonMangoldtWeight n * W.primePowerPairing n f g) =
      MathlibRestrictedFinitePrimeEvaluatorSumOnIndexSet W f g lambda h

theorem source_weight_read_off
    {W : WeilFormSymbols} {f g : TestFunction} {n : ℕ}
    (h : SourceFinitePrimeArithmeticData W f g n) :
    W.vonMangoldtWeight n = ArithmeticFunction.vonMangoldt n :=
  h.weightReadOff

theorem source_prime_power_index_of_arithmetic_data
    {W : WeilFormSymbols} {f g : TestFunction} {n : ℕ}
    (h : SourceFinitePrimeArithmeticData W f g n) :
    IsPrimePow n :=
  h.sourcePrimePowerIndex

theorem source_prime_power_index_one_lt_of_arithmetic_data
    {W : WeilFormSymbols} {f g : TestFunction} {n : ℕ}
    (h : SourceFinitePrimeArithmeticData W f g n) :
    1 < n :=
  IsPrimePow.one_lt
    (source_prime_power_index_of_arithmetic_data h)

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

theorem source_atom_visible_in_source_test
    {W : WeilFormSymbols} {f g : TestFunction} {n : ℕ}
    (h : SourceFinitePrimeArithmeticData W f g n) :
    h.sourceTest.sourceAtomVisible n :=
  (PrimePowerTest.route_visibility_iff_source_visibility h.sourceTest n).1
    h.sourceAtomVisible

theorem source_atom_visible_in_pairing_source_test
    {W : WeilFormSymbols} {f g : TestFunction} {n : ℕ}
    (h : SourceFinitePrimeArithmeticData W f g n) :
    h.sourcePairing.model.sourceEvaluation.sourceTest.sourceAtomVisible n := by
  rw [h.pairingSourceTestReadOff]
  exact source_atom_visible_in_source_test h

theorem source_pairing_evaluation_uses_normalization_source_test
    {W : WeilFormSymbols} {f g : TestFunction}
    {h : SourceFinitePrimeArithmeticNormalization W f g}
    {sourceTest : PrimePowerTest.SourceTestEvaluationInterface W f g}
    (huses : UsesSourceTest h sourceTest) (n : ℕ) :
    (h.atIndex n).sourcePairing.model.sourceEvaluation.sourceTest =
      sourceTest := by
  rw [source_pairing_evaluation_source_test_read_off (h.atIndex n),
    huses n]

theorem source_atom_visible_uses_normalization_source_test
    {W : WeilFormSymbols} {f g : TestFunction}
    {h : SourceFinitePrimeArithmeticNormalization W f g}
    {sourceTest : PrimePowerTest.SourceTestEvaluationInterface W f g}
    (huses : UsesSourceTest h sourceTest) (n : ℕ) :
    sourceTest.sourceAtomVisible n := by
  have hvisible := source_atom_visible_in_source_test (h.atIndex n)
  simpa [huses n] using hvisible

theorem source_pairing_formula
    {W : WeilFormSymbols} {f g : TestFunction} {n : ℕ}
    (h : SourceFinitePrimeArithmeticData W f g n) :
    W.primePowerPairing n f g =
      (1 / Real.sqrt (n : ℝ)) *
        (h.sourcePairing.model.sourceForwardEvaluation +
          h.sourcePairing.model.sourceInverseEvaluation) :=
  PrimePowerPairing.source_prime_power_pairing_formula h.sourcePairing

theorem source_pairing_formula_inv_sqrt
    {W : WeilFormSymbols} {f g : TestFunction} {n : ℕ}
    (h : SourceFinitePrimeArithmeticData W f g n) :
    W.primePowerPairing n f g =
      (1 / Real.sqrt (n : ℝ)) *
        (h.sourcePairing.model.sourceForwardEvaluation +
          h.sourcePairing.model.sourceInverseEvaluation) :=
  PrimePowerPairing.source_prime_power_pairing_formula_real_sqrt
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
      ArithmeticFunction.vonMangoldt n * h.sourcePrimePowerPairing :=
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
  exact source_pairing_formula_source_evaluations h

theorem source_finite_prime_term_formula_source_evaluations
    {W : WeilFormSymbols} {f g : TestFunction} {n : ℕ}
    (h : SourceFinitePrimeArithmeticData W f g n) :
    W.finitePrimeTerm n (W.convolutionStar f g) =
      ArithmeticFunction.vonMangoldt n *
        ((1 / Real.sqrt (n : ℝ)) *
          (h.sourcePairing.model.sourceEvaluation.forwardValue +
            h.sourcePairing.model.sourceEvaluation.inverseValue)) := by
  rw [h.termReadOff]
  congr 1
  rw [← h.pairingReadOff]
  exact source_pairing_formula_source_evaluations h

theorem source_finite_prime_term_formula_mathlib_source_evaluator
    {W : WeilFormSymbols} {f g : TestFunction} {n : ℕ}
    (h : SourceFinitePrimeArithmeticData W f g n) :
    W.finitePrimeTerm n (W.convolutionStar f g) =
      MathlibFinitePrimeEvaluatorAtom W f g n h := by
  rw [source_finite_prime_term_formula_source_evaluator h,
    source_finite_prime_evaluator_atom_eq_mathlib h]

theorem source_finite_prime_term_formula_mathlib_source_evaluations
    {W : WeilFormSymbols} {f g : TestFunction} {n : ℕ}
    (h : SourceFinitePrimeArithmeticData W f g n) :
    W.finitePrimeTerm n (W.convolutionStar f g) =
      ArithmeticFunction.vonMangoldt n *
        ((1 / Real.sqrt (n : ℝ)) *
          (h.sourcePairing.model.sourceEvaluation.forwardValue +
            h.sourcePairing.model.sourceEvaluation.inverseValue)) := by
  exact source_finite_prime_term_formula_source_evaluations h

theorem source_finite_prime_term_formula_mathlib_pairing
    {W : WeilFormSymbols} {f g : TestFunction} {n : ℕ}
    (h : SourceFinitePrimeArithmeticData W f g n) :
    W.finitePrimeTerm n (W.convolutionStar f g) =
      ArithmeticFunction.vonMangoldt n * W.primePowerPairing n f g := by
  rw [h.termReadOff, h.pairingReadOff]

theorem source_von_mangoldt_pairing_product_formula_source_evaluator
    {W : WeilFormSymbols} {f g : TestFunction} {n : ℕ}
    (h : SourceFinitePrimeArithmeticData W f g n) :
    W.vonMangoldtWeight n * W.primePowerPairing n f g =
      SourceFinitePrimeEvaluatorAtom W f g n h := by
  dsimp [SourceFinitePrimeEvaluatorAtom]
  rw [h.weightReadOff]
  congr 1
  exact source_pairing_formula_source_evaluations h

theorem source_von_mangoldt_pairing_product_formula_source_evaluations
    {W : WeilFormSymbols} {f g : TestFunction} {n : ℕ}
    (h : SourceFinitePrimeArithmeticData W f g n) :
    W.vonMangoldtWeight n * W.primePowerPairing n f g =
      ArithmeticFunction.vonMangoldt n *
        ((1 / Real.sqrt (n : ℝ)) *
          (h.sourcePairing.model.sourceEvaluation.forwardValue +
            h.sourcePairing.model.sourceEvaluation.inverseValue)) := by
  rw [h.weightReadOff]
  congr 1
  exact source_pairing_formula_source_evaluations h

theorem source_finite_prime_local_formula_data
    {W : WeilFormSymbols} {f g : TestFunction} {n : ℕ}
    (h : SourceFinitePrimeArithmeticData W f g n) :
    SourceFinitePrimeLocalFormulaData W f g n h where
  weightReadOff := h.weightReadOff
  pairingFormulaSourceEvaluator := source_pairing_formula_source_evaluator h
  termFormulaSourceEvaluator :=
    source_finite_prime_term_formula_source_evaluator h

theorem source_on_index_set_weight_read_off
    {W : WeilFormSymbols} {f g : TestFunction} {indexSet : Finset ℕ}
    (h : SourceFinitePrimeArithmeticDataOnIndexSet W f g indexSet)
    {n : ℕ} (hn : n ∈ indexSet) :
    W.vonMangoldtWeight n = ArithmeticFunction.vonMangoldt n :=
  source_weight_read_off (h.atIndex n hn)

theorem source_on_index_set_prime_power_index
    {W : WeilFormSymbols} {f g : TestFunction} {indexSet : Finset ℕ}
    (h : SourceFinitePrimeArithmeticDataOnIndexSet W f g indexSet)
    {n : ℕ} (hn : n ∈ indexSet) :
    IsPrimePow n :=
  source_prime_power_index_of_arithmetic_data (h.atIndex n hn)

theorem source_on_index_set_one_lt
    {W : WeilFormSymbols} {f g : TestFunction} {indexSet : Finset ℕ}
    (h : SourceFinitePrimeArithmeticDataOnIndexSet W f g indexSet)
    {n : ℕ} (hn : n ∈ indexSet) :
    1 < n :=
  source_prime_power_index_one_lt_of_arithmetic_data (h.atIndex n hn)

theorem source_on_index_set_atom_visible_in_source_test
    {W : WeilFormSymbols} {f g : TestFunction} {indexSet : Finset ℕ}
    (h : SourceFinitePrimeArithmeticDataOnIndexSet W f g indexSet)
    {n : ℕ} (hn : n ∈ indexSet) :
    (h.atIndex n hn).sourceTest.sourceAtomVisible n :=
  source_atom_visible_in_source_test (h.atIndex n hn)

theorem source_on_index_set_pairing_formula_source_evaluator
    {W : WeilFormSymbols} {f g : TestFunction} {indexSet : Finset ℕ}
    (h : SourceFinitePrimeArithmeticDataOnIndexSet W f g indexSet)
    {n : ℕ} (hn : n ∈ indexSet) :
    W.primePowerPairing n f g =
      (1 / Real.sqrt (n : ℝ)) *
        ((h.atIndex n hn).sourcePairing.model.sourceEvaluation.sourceEvaluator.valueAt
            (W.convolutionStar f g) (n : ℝ) +
          (h.atIndex n hn).sourcePairing.model.sourceEvaluation.sourceEvaluator.valueAt
            (W.convolutionStar f g) ((n : ℝ)⁻¹)) :=
  source_pairing_formula_source_evaluator (h.atIndex n hn)

theorem source_on_index_set_pairing_formula_source_evaluations
    {W : WeilFormSymbols} {f g : TestFunction} {indexSet : Finset ℕ}
    (h : SourceFinitePrimeArithmeticDataOnIndexSet W f g indexSet)
    {n : ℕ} (hn : n ∈ indexSet) :
    W.primePowerPairing n f g =
      (1 / Real.sqrt (n : ℝ)) *
        ((h.atIndex n hn).sourcePairing.model.sourceEvaluation.forwardValue +
          (h.atIndex n hn).sourcePairing.model.sourceEvaluation.inverseValue) :=
  source_pairing_formula_source_evaluations (h.atIndex n hn)

theorem source_on_index_set_finite_prime_term_formula_source_evaluator
    {W : WeilFormSymbols} {f g : TestFunction} {indexSet : Finset ℕ}
    (h : SourceFinitePrimeArithmeticDataOnIndexSet W f g indexSet)
    {n : ℕ} (hn : n ∈ indexSet) :
    W.finitePrimeTerm n (W.convolutionStar f g) =
      SourceFinitePrimeEvaluatorAtom W f g n (h.atIndex n hn) :=
  source_finite_prime_term_formula_source_evaluator (h.atIndex n hn)

theorem source_on_index_set_finite_prime_term_formula_source_evaluations
    {W : WeilFormSymbols} {f g : TestFunction} {indexSet : Finset ℕ}
    (h : SourceFinitePrimeArithmeticDataOnIndexSet W f g indexSet)
    {n : ℕ} (hn : n ∈ indexSet) :
    W.finitePrimeTerm n (W.convolutionStar f g) =
      ArithmeticFunction.vonMangoldt n *
        ((1 / Real.sqrt (n : ℝ)) *
          ((h.atIndex n hn).sourcePairing.model.sourceEvaluation.forwardValue +
            (h.atIndex n hn).sourcePairing.model.sourceEvaluation.inverseValue)) :=
  source_finite_prime_term_formula_source_evaluations (h.atIndex n hn)

theorem source_on_index_set_finite_prime_term_formula_mathlib_source_evaluations
    {W : WeilFormSymbols} {f g : TestFunction} {indexSet : Finset ℕ}
    (h : SourceFinitePrimeArithmeticDataOnIndexSet W f g indexSet)
    {n : ℕ} (hn : n ∈ indexSet) :
    W.finitePrimeTerm n (W.convolutionStar f g) =
      ArithmeticFunction.vonMangoldt n *
        ((1 / Real.sqrt (n : ℝ)) *
          ((h.atIndex n hn).sourcePairing.model.sourceEvaluation.forwardValue +
            (h.atIndex n hn).sourcePairing.model.sourceEvaluation.inverseValue)) :=
  source_finite_prime_term_formula_mathlib_source_evaluations (h.atIndex n hn)

theorem source_on_index_set_finite_prime_term_formula_mathlib_pairing
    {W : WeilFormSymbols} {f g : TestFunction} {indexSet : Finset ℕ}
    (h : SourceFinitePrimeArithmeticDataOnIndexSet W f g indexSet)
    {n : ℕ} (hn : n ∈ indexSet) :
    W.finitePrimeTerm n (W.convolutionStar f g) =
      ArithmeticFunction.vonMangoldt n * W.primePowerPairing n f g :=
  source_finite_prime_term_formula_mathlib_pairing (h.atIndex n hn)

theorem source_on_index_set_von_mangoldt_pairing_product_formula_source_evaluator
    {W : WeilFormSymbols} {f g : TestFunction} {indexSet : Finset ℕ}
    (h : SourceFinitePrimeArithmeticDataOnIndexSet W f g indexSet)
    {n : ℕ} (hn : n ∈ indexSet) :
    W.vonMangoldtWeight n * W.primePowerPairing n f g =
      SourceFinitePrimeEvaluatorAtom W f g n (h.atIndex n hn) :=
  source_von_mangoldt_pairing_product_formula_source_evaluator
    (h.atIndex n hn)

theorem source_on_index_set_von_mangoldt_pairing_product_formula_source_evaluations
    {W : WeilFormSymbols} {f g : TestFunction} {indexSet : Finset ℕ}
    (h : SourceFinitePrimeArithmeticDataOnIndexSet W f g indexSet)
    {n : ℕ} (hn : n ∈ indexSet) :
    W.vonMangoldtWeight n * W.primePowerPairing n f g =
      ArithmeticFunction.vonMangoldt n *
        ((1 / Real.sqrt (n : ℝ)) *
          ((h.atIndex n hn).sourcePairing.model.sourceEvaluation.forwardValue +
            (h.atIndex n hn).sourcePairing.model.sourceEvaluation.inverseValue)) :=
  source_von_mangoldt_pairing_product_formula_source_evaluations (h.atIndex n hn)

theorem source_on_index_set_local_formula_data
    {W : WeilFormSymbols} {f g : TestFunction} {indexSet : Finset ℕ}
    (h : SourceFinitePrimeArithmeticDataOnIndexSet W f g indexSet)
    {n : ℕ} (hn : n ∈ indexSet) :
    SourceFinitePrimeLocalFormulaData W f g n (h.atIndex n hn) :=
  source_finite_prime_local_formula_data (h.atIndex n hn)

theorem source_local_formula_weight_read_off
    {W : WeilFormSymbols} {f g : TestFunction} {n : ℕ}
    {h : SourceFinitePrimeArithmeticData W f g n}
    (formula : SourceFinitePrimeLocalFormulaData W f g n h) :
    W.vonMangoldtWeight n = ArithmeticFunction.vonMangoldt n :=
  formula.weightReadOff

theorem source_local_formula_pairing_formula_source_evaluator
    {W : WeilFormSymbols} {f g : TestFunction} {n : ℕ}
    {h : SourceFinitePrimeArithmeticData W f g n}
    (formula : SourceFinitePrimeLocalFormulaData W f g n h) :
    W.primePowerPairing n f g =
      (1 / Real.sqrt (n : ℝ)) *
        (h.sourcePairing.model.sourceEvaluation.sourceEvaluator.valueAt
            (W.convolutionStar f g) (n : ℝ) +
          h.sourcePairing.model.sourceEvaluation.sourceEvaluator.valueAt
            (W.convolutionStar f g) ((n : ℝ)⁻¹)) :=
  formula.pairingFormulaSourceEvaluator

theorem source_local_formula_pairing_formula_source_evaluations
    {W : WeilFormSymbols} {f g : TestFunction} {n : ℕ}
    {h : SourceFinitePrimeArithmeticData W f g n}
    (_formula : SourceFinitePrimeLocalFormulaData W f g n h) :
    W.primePowerPairing n f g =
      (1 / Real.sqrt (n : ℝ)) *
        (h.sourcePairing.model.sourceEvaluation.forwardValue +
          h.sourcePairing.model.sourceEvaluation.inverseValue) :=
  source_pairing_formula_source_evaluations h

theorem source_local_formula_term_formula_source_evaluator
    {W : WeilFormSymbols} {f g : TestFunction} {n : ℕ}
    {h : SourceFinitePrimeArithmeticData W f g n}
    (formula : SourceFinitePrimeLocalFormulaData W f g n h) :
    W.finitePrimeTerm n (W.convolutionStar f g) =
      SourceFinitePrimeEvaluatorAtom W f g n h :=
  formula.termFormulaSourceEvaluator

theorem source_local_formula_term_formula_source_evaluations
    {W : WeilFormSymbols} {f g : TestFunction} {n : ℕ}
    {h : SourceFinitePrimeArithmeticData W f g n}
    (_formula : SourceFinitePrimeLocalFormulaData W f g n h) :
    W.finitePrimeTerm n (W.convolutionStar f g) =
      SourceFinitePrimeEvaluatorAtom W f g n h :=
  source_finite_prime_term_formula_source_evaluator h

theorem source_local_formula_von_mangoldt_pairing_source_evaluations
    {W : WeilFormSymbols} {f g : TestFunction} {n : ℕ}
    {h : SourceFinitePrimeArithmeticData W f g n}
    (_formula : SourceFinitePrimeLocalFormulaData W f g n h) :
    W.vonMangoldtWeight n * W.primePowerPairing n f g =
      SourceFinitePrimeEvaluatorAtom W f g n h :=
  source_von_mangoldt_pairing_product_formula_source_evaluator h

theorem source_finite_prime_term_sum_formula_source_evaluations
    {W : WeilFormSymbols} {f g : TestFunction} {indexSet : Finset ℕ}
    (h : SourceFinitePrimeArithmeticNormalization W f g) :
    (∑ n ∈ indexSet, W.finitePrimeTerm n (W.convolutionStar f g)) =
      SourceFinitePrimeEvaluatorSum W f g indexSet h := by
  dsimp [SourceFinitePrimeEvaluatorSum]
  refine Finset.sum_congr rfl ?_
  intro n _hn
  exact source_finite_prime_term_formula_source_evaluator (h.atIndex n)

theorem source_von_mangoldt_pairing_sum_formula_source_evaluations
    {W : WeilFormSymbols} {f g : TestFunction} {indexSet : Finset ℕ}
    (h : SourceFinitePrimeArithmeticNormalization W f g) :
    (∑ n ∈ indexSet, W.vonMangoldtWeight n * W.primePowerPairing n f g) =
      SourceFinitePrimeEvaluatorSum W f g indexSet h := by
  dsimp [SourceFinitePrimeEvaluatorSum]
  refine Finset.sum_congr rfl ?_
  intro n _hn
  exact source_von_mangoldt_pairing_product_formula_source_evaluator
    (h.atIndex n)

theorem source_finite_prime_term_sum_on_index_set_formula_source_evaluations
    {W : WeilFormSymbols} {f g : TestFunction} {indexSet : Finset ℕ}
    (h : SourceFinitePrimeArithmeticDataOnIndexSet W f g indexSet) :
    (∑ n ∈ indexSet, W.finitePrimeTerm n (W.convolutionStar f g)) =
      SourceFinitePrimeEvaluatorSumOnIndexSet W f g indexSet h := by
  dsimp [SourceFinitePrimeEvaluatorSumOnIndexSet]
  refine Finset.sum_congr rfl ?_
  intro n hn
  simp [hn, source_finite_prime_term_formula_source_evaluator
    (h.atIndex n hn)]

theorem source_von_mangoldt_pairing_sum_on_index_set_formula_source_evaluations
    {W : WeilFormSymbols} {f g : TestFunction} {indexSet : Finset ℕ}
    (h : SourceFinitePrimeArithmeticDataOnIndexSet W f g indexSet) :
    (∑ n ∈ indexSet, W.vonMangoldtWeight n * W.primePowerPairing n f g) =
      SourceFinitePrimeEvaluatorSumOnIndexSet W f g indexSet h := by
  dsimp [SourceFinitePrimeEvaluatorSumOnIndexSet]
  refine Finset.sum_congr rfl ?_
  intro n hn
  simp [hn, source_von_mangoldt_pairing_product_formula_source_evaluator
    (h.atIndex n hn)]

theorem source_global_finite_prime_term_sum_formula_source_evaluations
    {W : WeilFormSymbols} {f g : TestFunction}
    (h : SourceFinitePrimeArithmeticNormalization W f g) :
    (∑ n ∈ W.globalPrimeIndexSet,
      W.finitePrimeTerm n (W.convolutionStar f g)) =
      SourceGlobalFinitePrimeEvaluatorSum W f g h :=
  source_finite_prime_term_sum_formula_source_evaluations h

theorem source_global_von_mangoldt_pairing_sum_formula_source_evaluations
    {W : WeilFormSymbols} {f g : TestFunction}
    (h : SourceFinitePrimeArithmeticNormalization W f g) :
    (∑ n ∈ W.globalPrimeIndexSet,
      W.vonMangoldtWeight n * W.primePowerPairing n f g) =
      SourceGlobalFinitePrimeEvaluatorSum W f g h :=
  source_von_mangoldt_pairing_sum_formula_source_evaluations h

theorem source_restricted_finite_prime_term_sum_formula_source_evaluations
    {W : WeilFormSymbols} {f g : TestFunction} {lambda : ℝ}
    (h : SourceFinitePrimeArithmeticNormalization W f g) :
    (∑ n ∈ W.restrictedPrimeIndexSet lambda,
      W.finitePrimeTerm n (W.convolutionStar f g)) =
      SourceRestrictedFinitePrimeEvaluatorSum W f g lambda h :=
  source_finite_prime_term_sum_formula_source_evaluations h

theorem source_restricted_von_mangoldt_pairing_sum_formula_source_evaluations
    {W : WeilFormSymbols} {f g : TestFunction} {lambda : ℝ}
    (h : SourceFinitePrimeArithmeticNormalization W f g) :
    (∑ n ∈ W.restrictedPrimeIndexSet lambda,
      W.vonMangoldtWeight n * W.primePowerPairing n f g) =
      SourceRestrictedFinitePrimeEvaluatorSum W f g lambda h :=
  source_von_mangoldt_pairing_sum_formula_source_evaluations h

end PrimePowerArithmetic
end CCM25Concrete
end Source
end ConnesWeilRH
