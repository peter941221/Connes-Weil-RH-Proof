/-
Copyright (c) 2026 ConnesWeilRH contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ConnesWeilRH contributors
-/

import ConnesWeilRH.Source.CC20YoshidaMellin
import Mathlib.LinearAlgebra.Vandermonde

/-!
# Conditional Yoshida detector construction

This module contains the concrete read-off from half-density Mellin moments to
the positivity field required by `YoshidaDetector`.  It does not assume detector
existence and it does not close the remaining finite Mellin interpolation
problem.
-/

namespace ConnesWeilRH
namespace Source
namespace CC20YoshidaInterpolationNode

open AnalyticCore
open MeasureTheory
open Filter
open scoped Topology

theorem normalizedCC20ConcreteEvaluationData_mellinAt_double_convolutionSquare
    (g : normalizedCC20ConcreteTestAlgebra.Test) (s : ℂ) :
    normalizedCC20ConcreteEvaluationData.mellinAt
        (normalizedCC20ConcreteTestAlgebra.convolutionSquare
          (normalizedCC20ConcreteTestAlgebra.convolutionSquare g)) s =
      (4 : ℂ) * normalizedCC20ConcreteEvaluationData.mellinAt g s := by
  rw [normalizedCC20ConcreteEvaluationData_mellinAt_eq_mellin,
    normalizedCC20ConcreteEvaluationData_mellinAt_eq_mellin]
  have hfun :
      (fun x : ℝ =>
          normalizedCC20ConcreteTestAlgebra.legacy.encode
            (normalizedCC20ConcreteTestAlgebra.convolutionSquare
              (normalizedCC20ConcreteTestAlgebra.convolutionSquare g)) x) =
        fun x : ℝ =>
          (4 : ℂ) • normalizedCC20ConcreteTestAlgebra.legacy.encode g x := by
    funext x
    simp [AnalyticCore.SourceConcreteBaseLayer.concreteLegacyTestEquiv,
      AnalyticCore.SourceConcreteBaseLayer.concreteTestAlgebra, smul_eq_mul]
    ring_nf
  rw [hfun]
  simpa [smul_eq_mul, mul_comm] using
    (mellin_const_smul
      (fun x : ℝ => normalizedCC20ConcreteTestAlgebra.legacy.encode g x)
      s (4 : ℂ))

theorem normalizedCC20Yoshida_weilLocalSum_positive_of_half_mellin_values
    {g : normalizedCC20ConcreteTestAlgebra.Test}
    (hplus :
      normalizedCC20TestSpace.mellinAt g (Complex.I / 2) = (-1 : ℂ))
    (hminus :
      normalizedCC20TestSpace.mellinAt g (-Complex.I / 2) = (-1 : ℂ)) :
    0 <
      normalizedCC20TestSpace.weilLocalSum
        (normalizedCC20TestSpace.starConvolution g) := by
  rw [normalizedCC20TestSpace_weilLocalSum_eq,
    normalizedCC20TestSpace_starConvolution_eq,
    normalizedCC20ConcreteEvaluationData.polePairing_eq_mellin_convolutionSquare_half_sum]
  have hplus' :
      normalizedCC20ConcreteEvaluationData.mellinAt
          (normalizedCC20ConcreteTestAlgebra.convolutionSquare
            (normalizedCC20ConcreteTestAlgebra.convolutionSquare g))
          (Complex.I / 2) =
        (-4 : ℂ) := by
    rw [normalizedCC20ConcreteEvaluationData_mellinAt_double_convolutionSquare]
    rw [normalizedCC20TestSpace_mellinAt_eq] at hplus
    rw [hplus]
    norm_num
  have hminus' :
      normalizedCC20ConcreteEvaluationData.mellinAt
          (normalizedCC20ConcreteTestAlgebra.convolutionSquare
            (normalizedCC20ConcreteTestAlgebra.convolutionSquare g))
          (-Complex.I / 2) =
        (-4 : ℂ) := by
    rw [normalizedCC20ConcreteEvaluationData_mellinAt_double_convolutionSquare]
    rw [normalizedCC20TestSpace_mellinAt_eq] at hminus
    rw [hminus]
    norm_num
  rw [hplus', hminus']
  norm_num

structure ConcreteYoshidaMomentData
    (rho : ℂ)
    (g : normalizedCC20ConcreteTestAlgebra.Test) : Prop where
  compactSupportSmooth :
    normalizedCC20TestSpace.compactSupportSmooth g
  vanishesOnF :
    CC20VanishesOn normalizedCC20TestSpace cc20TripleFiniteVanishingSet g
  detectsRho :
    normalizedCC20TestSpace.mellinAt g rho ≠ 0
  mellinAt_posHalf :
    normalizedCC20TestSpace.mellinAt g (Complex.I / 2) = (-1 : ℂ)
  mellinAt_negHalf :
    normalizedCC20TestSpace.mellinAt g (-Complex.I / 2) = (-1 : ℂ)

theorem concreteYoshidaMomentData_vanishesOn_cc20Triple
    {rho : ℂ} {g : normalizedCC20ConcreteTestAlgebra.Test}
    (h : ConcreteYoshidaMomentData rho g) :
    CC20VanishesOn normalizedCC20TestSpace cc20TripleFiniteVanishingSet g :=
  h.vanishesOnF

theorem concreteYoshidaMomentData_detects_rho
    {rho : ℂ} {g : normalizedCC20ConcreteTestAlgebra.Test}
    (h : ConcreteYoshidaMomentData rho g) :
    normalizedCC20TestSpace.mellinAt g rho ≠ 0 :=
  h.detectsRho

inductive CC20YoshidaExpandedMomentNode where
  | zero
  | half
  | one
  | targetRho
  | posHalfDensity
  | negHalfDensity
  deriving DecidableEq, Fintype

namespace CC20YoshidaExpandedMomentNode

noncomputable def nodeValue (rho : ℂ) :
    CC20YoshidaExpandedMomentNode → ℂ
  | zero => criticalVanishingPointValue CriticalVanishingPoint.zero
  | half => criticalVanishingPointValue CriticalVanishingPoint.half
  | one => criticalVanishingPointValue CriticalVanishingPoint.one
  | targetRho => rho
  | posHalfDensity => Complex.I / 2
  | negHalfDensity => -Complex.I / 2

def targetValue : CC20YoshidaExpandedMomentNode → ℂ
  | zero => 0
  | half => 0
  | one => 0
  | targetRho => -1
  | posHalfDensity => -1
  | negHalfDensity => -1

noncomputable def expandedNodeValueFinset (rho : ℂ) : Finset ℂ :=
  Finset.univ.image (nodeValue rho)

abbrev NodeValueImage (rho : ℂ) : Type :=
  {z : ℂ // z ∈ expandedNodeValueFinset rho}

noncomputable def targetValueOnNodeValue (_rho z : ℂ) : ℂ :=
  if z = criticalVanishingPointValue CriticalVanishingPoint.zero then 0
  else if z = criticalVanishingPointValue CriticalVanishingPoint.half then 0
  else if z = criticalVanishingPointValue CriticalVanishingPoint.one then 0
  else -1

theorem targetValue_eq_of_nodeValue_eq
    {rho : ℂ}
    (hrho : RHDefinitionBridge.standard.sourceNontrivialZero rho)
    (hoff : rho.re ≠ 1 / 2)
    {a b : CC20YoshidaExpandedMomentNode}
    (h : nodeValue rho a = nodeValue rho b) :
    targetValue a = targetValue b := by
  cases a <;> cases b <;>
    simp [nodeValue, targetValue, criticalVanishingPointValue] at h ⊢
  all_goals
    first
    | rfl
    | exfalso
      first
      | exact (standard_source_nontrivial_zero_ne_cc20_zero hrho)
          (by simpa [criticalVanishingPointValue] using h)
      | exact (standard_source_nontrivial_zero_ne_cc20_zero hrho)
          (by simpa [criticalVanishingPointValue] using h.symm)
      | exact (standard_source_nontrivial_zero_ne_cc20_half_of_off_line hoff)
          (by simpa [criticalVanishingPointValue] using h)
      | exact (standard_source_nontrivial_zero_ne_cc20_half_of_off_line hoff)
          (by simpa [criticalVanishingPointValue] using h.symm)
      | exact (standard_source_nontrivial_zero_ne_cc20_one hrho)
          (by simpa [criticalVanishingPointValue] using h)
      | exact (standard_source_nontrivial_zero_ne_cc20_one hrho)
          (by simpa [criticalVanishingPointValue] using h.symm)
      | have hre := congrArg Complex.re h
        norm_num [Complex.I_re] at hre

theorem targetValueOnNodeValue_eq_targetValue
    {rho : ℂ}
    (hrho : RHDefinitionBridge.standard.sourceNontrivialZero rho)
    (hoff : rho.re ≠ 1 / 2)
    (i : CC20YoshidaExpandedMomentNode) :
    targetValueOnNodeValue rho (nodeValue rho i) =
      targetValue i := by
  cases i
  · simp [targetValueOnNodeValue, nodeValue, targetValue,
      criticalVanishingPointValue]
  · simp [targetValueOnNodeValue, nodeValue, targetValue,
      criticalVanishingPointValue]
  · simp [targetValueOnNodeValue, nodeValue, targetValue,
      criticalVanishingPointValue]
  · have hzero : rho ≠ 0 := by
      simpa [criticalVanishingPointValue] using
        standard_source_nontrivial_zero_ne_cc20_zero hrho
    have hhalf : rho ≠ 1 / 2 := by
      simpa [criticalVanishingPointValue] using
        standard_source_nontrivial_zero_ne_cc20_half_of_off_line hoff
    have hone : rho ≠ 1 := by
      simpa [criticalVanishingPointValue] using
        standard_source_nontrivial_zero_ne_cc20_one hrho
    simp [targetValueOnNodeValue, nodeValue, targetValue,
      criticalVanishingPointValue, hzero, hone]
    simpa using hhalf
  · have hhalf : Complex.I / 2 ≠ (1 / 2 : ℂ) := by
      intro h
      have hre := congrArg Complex.re h
      norm_num [Complex.I_re] at hre
    have hone : Complex.I / 2 ≠ (1 : ℂ) := by
      intro h
      have hre := congrArg Complex.re h
      norm_num [Complex.I_re] at hre
    simp [targetValueOnNodeValue, nodeValue, targetValue,
      criticalVanishingPointValue, hone]
    simpa using hhalf
  · have hhalf : -Complex.I / 2 ≠ (1 / 2 : ℂ) := by
      intro h
      have hre := congrArg Complex.re h
      norm_num [Complex.I_re] at hre
    have hone : -Complex.I / 2 ≠ (1 : ℂ) := by
      intro h
      have hre := congrArg Complex.re h
      norm_num [Complex.I_re] at hre
    simp [targetValueOnNodeValue, nodeValue, targetValue,
      criticalVanishingPointValue, hone]
    simpa using hhalf

def ConcreteExpandedMellinRealizes
    (rho : ℂ) (g : normalizedCC20ConcreteTestAlgebra.Test) : Prop :=
  ∀ n : CC20YoshidaExpandedMomentNode,
    normalizedCC20TestSpace.mellinAt g (nodeValue rho n) = targetValue n

structure PositiveIntervalCompactTest where
  test : normalizedCC20ConcreteTestAlgebra.Test
  lower : ℝ
  upper : ℝ
  lower_pos : 0 < lower
  compactSupportSmooth :
    normalizedCC20TestSpace.compactSupportSmooth test
  support_subset :
    Function.support
      (fun x : ℝ =>
        normalizedCC20ConcreteTestAlgebra.legacy.encode test x) ⊆
      Set.Icc lower upper

def PositiveIntervalCompactTest.IsSupportedIn
    (p : PositiveIntervalCompactTest) (a b : ℝ) : Prop :=
  Function.support
      (fun x : ℝ =>
        normalizedCC20ConcreteTestAlgebra.legacy.encode p.test x) ⊆
    Set.Ioo a b

/-- A positive-interval test carrying evidence that its actual function stays
inside one fixed route window. -/
abbrev WindowedPositiveIntervalCompactTest (a b : ℝ) :=
  {p : PositiveIntervalCompactTest // p.IsSupportedIn a b}

noncomputable def expandedMellinVector
    (rho : ℂ) (p : PositiveIntervalCompactTest) :
    CC20YoshidaExpandedMomentNode → ℂ :=
  fun i => normalizedCC20TestSpace.mellinAt p.test (nodeValue rho i)

noncomputable def imageMellinVector
    (rho : ℂ) (p : PositiveIntervalCompactTest) :
    NodeValueImage rho → ℂ :=
  fun z => normalizedCC20TestSpace.mellinAt p.test z.1

noncomputable def windowedImageMellinVector
    (rho : ℂ) (a b : ℝ)
    (p : WindowedPositiveIntervalCompactTest a b) :
    NodeValueImage rho → ℂ :=
  imageMellinVector rho p.1

noncomputable def positiveIntervalCompactTestCombination
    (c : PositiveIntervalCompactTest →₀ ℂ) :
    normalizedCC20ConcreteTestAlgebra.Test :=
  normalizedCC20ConcreteTestAlgebra.legacy.decode
    (c.sum fun p a =>
      a • normalizedCC20ConcreteTestAlgebra.legacy.encode p.test)

noncomputable def windowedPositiveIntervalCompactTestCombination
    {a b : ℝ} (c : WindowedPositiveIntervalCompactTest a b →₀ ℂ) :
    normalizedCC20ConcreteTestAlgebra.Test :=
  positiveIntervalCompactTestCombination (c.mapDomain Subtype.val)

theorem positiveIntervalCompactTestCombination_compactSupportSmooth
    (c : PositiveIntervalCompactTest →₀ ℂ) :
    normalizedCC20TestSpace.compactSupportSmooth
      (positiveIntervalCompactTestCombination c) := by
  rw [normalizedCC20TestSpace_compactSupportSmooth_eq]
  unfold positiveIntervalCompactTestCombination
  simp only [AnalyticCore.LegacyTestEquiv.encode_decode_apply]
  rw [Finsupp.sum]
  let summand : PositiveIntervalCompactTest → ℝ → ℂ :=
    fun p x =>
      (c p • normalizedCC20ConcreteTestAlgebra.legacy.encode p.test) x
  have hcompact :
      HasCompactSupport (∑ p ∈ c.support, summand p) := by
    exact
      (HasCompactSupport.finset_sum
        (s := c.support)
        (f := summand)
        (fun p _hp => by
          have hp := p.compactSupportSmooth
          rw [normalizedCC20TestSpace_compactSupportSmooth_eq] at hp
          simpa [summand, SchwartzMap.smul_apply] using
            (HasCompactSupport.smul_left
              (f := fun _x : ℝ => c p)
              (f' := fun x : ℝ =>
                normalizedCC20ConcreteTestAlgebra.legacy.encode p.test x)
              hp)))
  have hfun :
      (fun x : ℝ =>
          (∑ p ∈ c.support,
            c p • normalizedCC20ConcreteTestAlgebra.legacy.encode p.test) x) =
        (∑ p ∈ c.support, summand p) := by
    funext x
    simp [summand, Finset.sum_apply, SchwartzMap.smul_apply]
  rw [hfun]
  exact hcompact

theorem windowedPositiveIntervalCompactTestCombination_compactSupportSmooth
    {a b : ℝ} (c : WindowedPositiveIntervalCompactTest a b →₀ ℂ) :
    normalizedCC20TestSpace.compactSupportSmooth
      (windowedPositiveIntervalCompactTestCombination c) := by
  exact
    positiveIntervalCompactTestCombination_compactSupportSmooth
      (c.mapDomain Subtype.val)

theorem windowedPositiveIntervalCompactTestCombination_support_subset
    {a b : ℝ} (c : WindowedPositiveIntervalCompactTest a b →₀ ℂ) :
    Function.support
        (fun x : ℝ =>
          normalizedCC20ConcreteTestAlgebra.legacy.encode
            (windowedPositiveIntervalCompactTestCombination c) x) ⊆
      Set.Ioo a b := by
  classical
  intro x hx
  rw [Function.mem_support] at hx
  by_contra hxwindow
  apply hx
  unfold windowedPositiveIntervalCompactTestCombination
  unfold positiveIntervalCompactTestCombination
  simp only [AnalyticCore.LegacyTestEquiv.encode_decode_apply]
  rw [Finsupp.sum_mapDomain_index_inj Subtype.val_injective]
  rw [Finsupp.sum]
  simp only [SchwartzMap.sum_apply]
  apply Finset.sum_eq_zero
  intro p hp
  have hpnot :
      x ∉ Function.support
        (fun y : ℝ =>
          normalizedCC20ConcreteTestAlgebra.legacy.encode p.1.test y) := by
    intro hpsupport
    exact hxwindow (p.2 hpsupport)
  have hpzero :
      normalizedCC20ConcreteTestAlgebra.legacy.encode p.1.test x = 0 :=
    not_not.mp hpnot
  simp [SchwartzMap.smul_apply, hpzero]

theorem positiveIntervalCompactTestCombination_support_subset
    (c : PositiveIntervalCompactTest →₀ ℂ) :
    ∃ lower upper : ℝ,
      0 < lower ∧
      Function.support
        (fun x : ℝ =>
          normalizedCC20ConcreteTestAlgebra.legacy.encode
            (positiveIntervalCompactTestCombination c) x) ⊆
        Set.Icc lower upper := by
  classical
  by_cases hne : c.support.Nonempty
  · let lower : ℝ := c.support.inf' hne fun p => p.lower
    let upper : ℝ := c.support.sup' hne fun p => p.upper
    refine ⟨lower, upper, ?_, ?_⟩
    · dsimp [lower]
      exact (Finset.lt_inf'_iff hne).mpr fun p _hp => p.lower_pos
    · intro x hx
      rw [Function.mem_support] at hx
      rw [Set.mem_Icc]
      by_contra hnot
      have hxzero :
          normalizedCC20ConcreteTestAlgebra.legacy.encode
            (positiveIntervalCompactTestCombination c) x = 0 := by
        unfold positiveIntervalCompactTestCombination
        simp only [AnalyticCore.LegacyTestEquiv.encode_decode_apply]
        rw [Finsupp.sum]
        calc
          (∑ p ∈ c.support,
              c p •
                normalizedCC20ConcreteTestAlgebra.legacy.encode p.test) x =
              ∑ p ∈ c.support,
                (c p •
                  normalizedCC20ConcreteTestAlgebra.legacy.encode p.test) x := by
            simp
          _ = 0 := by
            refine Finset.sum_eq_zero ?_
            intro p hp
            have hnotlocal : x ∉ Set.Icc p.lower p.upper := by
              rw [Set.mem_Icc]
              intro hxlocal
              apply hnot
              constructor
              · have hlower_le_p : lower ≤ p.lower := by
                  dsimp [lower]
                  exact Finset.inf'_le (fun q => q.lower) hp
                exact hlower_le_p.trans hxlocal.1
              · have hp_le_upper : p.upper ≤ upper := by
                  dsimp [upper]
                  exact Finset.le_sup' (fun q => q.upper) hp
                exact hxlocal.2.trans hp_le_upper
            have hptest_zero :
                normalizedCC20ConcreteTestAlgebra.legacy.encode p.test x = 0 := by
              by_contra hne_test
              have hxsupp :
                  x ∈ Function.support
                    (fun x : ℝ =>
                      normalizedCC20ConcreteTestAlgebra.legacy.encode
                        p.test x) := by
                rw [Function.mem_support]
                exact hne_test
              exact hnotlocal (p.support_subset hxsupp)
            simp [SchwartzMap.smul_apply, hptest_zero]
      exact hx hxzero
  · have h_empty : c.support = ∅ :=
      Finset.not_nonempty_iff_eq_empty.mp hne
    refine ⟨1, 1, by norm_num, ?_⟩
    intro x hx
    rw [Function.mem_support] at hx
    have hxzero :
        normalizedCC20ConcreteTestAlgebra.legacy.encode
          (positiveIntervalCompactTestCombination c) x = 0 := by
      unfold positiveIntervalCompactTestCombination
      simp [Finsupp.sum, h_empty]
    exact False.elim (hx hxzero)

theorem expandedMellinVector_positiveIntervalCompactTestCombination
    (rho : ℂ)
    (c : PositiveIntervalCompactTest →₀ ℂ)
    (i : CC20YoshidaExpandedMomentNode) :
    normalizedCC20TestSpace.mellinAt
        (positiveIntervalCompactTestCombination c)
        (nodeValue rho i) =
      c.sum fun p a => a * expandedMellinVector rho p i := by
  have hmellin :
      mellin
          (fun x : ℝ =>
            normalizedCC20ConcreteTestAlgebra.legacy.encode
              (positiveIntervalCompactTestCombination c) x)
          (nodeValue rho i) =
        c.sum fun p a =>
          a *
            mellin
              (fun x : ℝ =>
                normalizedCC20ConcreteTestAlgebra.legacy.encode p.test x)
              (nodeValue rho i) := by
    unfold positiveIntervalCompactTestCombination
    rw [mellin]
    calc
      (∫ t : ℝ in Set.Ioi 0,
          (t : ℂ) ^ (nodeValue rho i - 1) •
            normalizedCC20ConcreteTestAlgebra.legacy.encode
              (normalizedCC20ConcreteTestAlgebra.legacy.decode
                (c.sum fun p a =>
                  a •
                    normalizedCC20ConcreteTestAlgebra.legacy.encode
                      p.test)) t) =
          ∫ t : ℝ in Set.Ioi 0,
            c.support.sum fun p : PositiveIntervalCompactTest =>
              (t : ℂ) ^ (nodeValue rho i - 1) •
                ((c p •
                  normalizedCC20ConcreteTestAlgebra.legacy.encode
                    p.test) t) := by
            refine setIntegral_congr_fun measurableSet_Ioi ?_
            intro t _ht
            simp [Finsupp.sum, SchwartzMap.sum_apply, Finset.mul_sum]
      _ =
          c.support.sum fun p : PositiveIntervalCompactTest =>
            ∫ t : ℝ in Set.Ioi 0,
              (t : ℂ) ^ (nodeValue rho i - 1) •
                ((c p •
                  normalizedCC20ConcreteTestAlgebra.legacy.encode
                    p.test) t) := by
            rw [integral_finsetSum]
            intro p _hp
            exact
              (testFunction_mellinConvergent_of_support_subset_Icc
                (normalizedCC20ConcreteTestAlgebra.legacy.encode p.test)
                (nodeValue rho i) p.lower_pos p.support_subset).const_smul
                (c p)
      _ =
          c.sum fun p a =>
            a *
              mellin
                (fun x : ℝ =>
                  normalizedCC20ConcreteTestAlgebra.legacy.encode
                    p.test x)
                (nodeValue rho i) := by
            rw [Finsupp.sum]
            refine Finset.sum_congr rfl ?_
            intro p _hp
            simpa [mellin, SchwartzMap.smul_apply, smul_eq_mul] using
              (mellin_const_smul
                (fun x : ℝ =>
                  normalizedCC20ConcreteTestAlgebra.legacy.encode p.test x)
                (nodeValue rho i)
                (c p))
  rw [normalizedCC20TestSpace_mellinAt_eq,
    normalizedCC20ConcreteEvaluationData_mellinAt_eq_mellin, hmellin]
  refine Finsupp.sum_congr ?_
  intro p a
  rw [expandedMellinVector, normalizedCC20TestSpace_mellinAt_eq,
    normalizedCC20ConcreteEvaluationData_mellinAt_eq_mellin]

theorem imageMellinVector_positiveIntervalCompactTestCombination
    (rho : ℂ)
    (c : PositiveIntervalCompactTest →₀ ℂ)
    (z : NodeValueImage rho) :
    normalizedCC20TestSpace.mellinAt
        (positiveIntervalCompactTestCombination c) z.1 =
      c.sum fun p a => a * imageMellinVector rho p z := by
  have hmellin :
      mellin
          (fun x : ℝ =>
            normalizedCC20ConcreteTestAlgebra.legacy.encode
              (positiveIntervalCompactTestCombination c) x)
          z.1 =
        c.sum fun p a =>
          a *
            mellin
              (fun x : ℝ =>
                normalizedCC20ConcreteTestAlgebra.legacy.encode p.test x)
              z.1 := by
    unfold positiveIntervalCompactTestCombination
    rw [mellin]
    calc
      (∫ t : ℝ in Set.Ioi 0,
          (t : ℂ) ^ (z.1 - 1) •
            normalizedCC20ConcreteTestAlgebra.legacy.encode
              (normalizedCC20ConcreteTestAlgebra.legacy.decode
                (c.sum fun p a =>
                  a •
                    normalizedCC20ConcreteTestAlgebra.legacy.encode
                      p.test)) t) =
          ∫ t : ℝ in Set.Ioi 0,
            c.support.sum fun p : PositiveIntervalCompactTest =>
              (t : ℂ) ^ (z.1 - 1) •
                ((c p •
                  normalizedCC20ConcreteTestAlgebra.legacy.encode
                    p.test) t) := by
            refine setIntegral_congr_fun measurableSet_Ioi ?_
            intro t _ht
            simp [Finsupp.sum, SchwartzMap.sum_apply, Finset.mul_sum]
      _ =
          c.support.sum fun p : PositiveIntervalCompactTest =>
            ∫ t : ℝ in Set.Ioi 0,
              (t : ℂ) ^ (z.1 - 1) •
                ((c p •
                  normalizedCC20ConcreteTestAlgebra.legacy.encode
                    p.test) t) := by
            rw [integral_finsetSum]
            intro p _hp
            exact
              (testFunction_mellinConvergent_of_support_subset_Icc
                (normalizedCC20ConcreteTestAlgebra.legacy.encode p.test)
                z.1 p.lower_pos p.support_subset).const_smul
                (c p)
      _ =
          c.sum fun p a =>
            a *
              mellin
                (fun x : ℝ =>
                  normalizedCC20ConcreteTestAlgebra.legacy.encode
                    p.test x)
                z.1 := by
            rw [Finsupp.sum]
            refine Finset.sum_congr rfl ?_
            intro p _hp
            simpa [mellin, SchwartzMap.smul_apply, smul_eq_mul] using
              (mellin_const_smul
                (fun x : ℝ =>
                  normalizedCC20ConcreteTestAlgebra.legacy.encode p.test x)
                z.1
                (c p))
  rw [normalizedCC20TestSpace_mellinAt_eq,
    normalizedCC20ConcreteEvaluationData_mellinAt_eq_mellin, hmellin]
  refine Finsupp.sum_congr ?_
  intro p a
  rw [imageMellinVector, normalizedCC20TestSpace_mellinAt_eq,
    normalizedCC20ConcreteEvaluationData_mellinAt_eq_mellin]

theorem windowedImageMellinVector_combination
    (rho : ℂ) {a b : ℝ}
    (c : WindowedPositiveIntervalCompactTest a b →₀ ℂ)
    (z : NodeValueImage rho) :
    normalizedCC20TestSpace.mellinAt
        (windowedPositiveIntervalCompactTestCombination c) z.1 =
      c.sum fun p coefficient =>
        coefficient * windowedImageMellinVector rho a b p z := by
  rw [windowedPositiveIntervalCompactTestCombination,
    imageMellinVector_positiveIntervalCompactTestCombination]
  simpa [windowedImageMellinVector] using
    (Finsupp.sum_mapDomain_index_inj
      (s := c)
      (h := fun p coefficient =>
        coefficient * imageMellinVector rho p z)
      Subtype.val_injective)

noncomputable def weightedMellinKernel
    (rho : ℂ) (coeff : NodeValueImage rho → ℂ) (t : ℝ) : ℂ :=
  ∑ z : NodeValueImage rho, coeff z * (t : ℂ) ^ (z.1 - 1)

noncomputable def expMomentSum
    {rho : ℂ} (coeff : NodeValueImage rho → ℂ) (n : ℕ) (u : ℝ) : ℂ :=
  ∑ z : NodeValueImage rho,
    coeff z * (z.1 - 1) ^ n * Complex.exp ((z.1 - 1) * (u : ℂ))

theorem weightedMellinKernel_exp_eq_expMomentSum_zero
    (rho : ℂ) (coeff : NodeValueImage rho → ℂ) (u : ℝ) :
    weightedMellinKernel rho coeff (Real.exp u) =
      expMomentSum coeff 0 u := by
  unfold weightedMellinKernel expMomentSum
  refine Finset.sum_congr rfl ?_
  intro z _
  rw [pow_zero, mul_one]
  congr 1
  rw [Complex.cpow_def_of_ne_zero]
  · rw [Complex.ofReal_exp, Complex.log_exp]
    · ring_nf
    · simpa using Real.pi_pos
    · simpa using Real.pi_nonneg
  · exact Complex.ofReal_ne_zero.mpr (Real.exp_ne_zero u)

theorem hasDerivAt_expMomentSum
    {rho : ℂ} (coeff : NodeValueImage rho → ℂ) (n : ℕ) (u : ℝ) :
    HasDerivAt (fun x : ℝ => expMomentSum coeff n x)
      (expMomentSum coeff (n + 1) u) u := by
  classical
  unfold expMomentSum
  refine HasDerivAt.fun_sum
    (u := (Finset.univ : Finset (NodeValueImage rho))) ?_
  intro z _hz
  let a : ℂ := z.1 - 1
  have hlin : HasDerivAt (fun x : ℝ => a * (x : ℂ)) a u := by
    simpa using ((hasDerivAt_id (u : ℂ)).const_mul a).comp_ofReal
  have hexp : HasDerivAt (fun x : ℝ => Complex.exp (a * (x : ℂ)))
      (a * Complex.exp (a * (u : ℂ))) u := by
    simpa [mul_comm, mul_left_comm, mul_assoc] using hlin.cexp
  have hterm := hexp.const_mul (coeff z * a ^ n)
  simpa [a, pow_succ, mul_comm, mul_left_comm, mul_assoc] using hterm

theorem expMomentSum_eq_zero_of_weightedMellinKernel_exp_eq_zero
    {rho : ℂ} (coeff : NodeValueImage rho → ℂ)
    (hzero : ∀ u : ℝ, weightedMellinKernel rho coeff (Real.exp u) = 0) :
    ∀ n : ℕ, ∀ u : ℝ, expMomentSum coeff n u = 0 := by
  intro n
  induction n with
  | zero =>
      intro u
      rw [← weightedMellinKernel_exp_eq_expMomentSum_zero rho coeff u]
      exact hzero u
  | succ n ih =>
      intro u
      have hderiv := hasDerivAt_expMomentSum coeff n u
      have hconst :
          HasDerivAt (fun x : ℝ => expMomentSum coeff n x) 0 u := by
        convert (hasDerivAt_const (x := u) (c := (0 : ℂ))) using 1
        ext x
        exact ih x
      exact hderiv.unique hconst

/-- Vanishing on one open log-window is enough to kill every exponential
moment on that window.  The derivative recurrence avoids appealing to a
separate analytic-continuation interface. -/
theorem expMomentSum_eq_zero_of_weightedMellinKernel_exp_eq_zero_on_Ioo
    {rho : ℂ} (coeff : NodeValueImage rho → ℂ) {a b : ℝ}
    (hzero : ∀ u ∈ Set.Ioo a b,
      weightedMellinKernel rho coeff (Real.exp u) = 0) :
    ∀ n : ℕ, ∀ u ∈ Set.Ioo a b, expMomentSum coeff n u = 0 := by
  intro n
  induction n with
  | zero =>
      intro u hu
      rw [← weightedMellinKernel_exp_eq_expMomentSum_zero rho coeff u]
      exact hzero u hu
  | succ n ih =>
      intro u hu
      have hderiv := hasDerivAt_expMomentSum coeff n u
      have hconst :
          HasDerivAt (fun x : ℝ => expMomentSum coeff n x) 0 u := by
        apply (hasDerivAt_const (x := u) (c := (0 : ℂ))).congr_of_eventuallyEq
        filter_upwards [Ioo_mem_nhds hu.1 hu.2] with x hx
        exact ih x hx
      exact hderiv.unique hconst

theorem expMomentSum_zero_at_zero_eq_power_sum
    {rho : ℂ} (coeff : NodeValueImage rho → ℂ) (n : ℕ) :
    expMomentSum coeff n 0 =
      ∑ z : NodeValueImage rho, coeff z * (z.1 - 1) ^ n := by
  unfold expMomentSum
  refine Finset.sum_congr rfl ?_
  intro z _
  simp [mul_comm, mul_left_comm]

theorem continuousAt_weightedMellinKernel_of_pos
    (rho : ℂ) (coeff : NodeValueImage rho → ℂ) {t : ℝ}
    (ht : 0 < t) :
    ContinuousAt (fun x : ℝ => weightedMellinKernel rho coeff x) t := by
  classical
  unfold weightedMellinKernel
  refine tendsto_finsetSum (Finset.univ : Finset (NodeValueImage rho)) ?_
  intro z _hz
  exact continuousAt_const.mul
    (Complex.continuousAt_ofReal_cpow_const t (z.1 - 1) (Or.inr ht.ne'))

theorem continuousAt_weightedMellinKernel_phase_re_of_pos
    (rho : ℂ) (coeff : NodeValueImage rho → ℂ) (phase : ℂ) {t : ℝ}
    (ht : 0 < t) :
    ContinuousAt
      (fun x : ℝ => (phase * weightedMellinKernel rho coeff x).re) t := by
  exact
    Complex.continuous_re.continuousAt.comp
      (continuousAt_const.mul
        (continuousAt_weightedMellinKernel_of_pos rho coeff ht))

theorem exists_positive_interval_compact_test_real_bump
    {a b t : ℝ} (hat : a < t) (htb : t < b) (ha : 0 < a) :
    ∃ p : PositiveIntervalCompactTest,
      Function.support
        (fun x : ℝ =>
          normalizedCC20ConcreteTestAlgebra.legacy.encode p.test x) ⊆
        Set.Ioo a b ∧
      (∀ x : ℝ,
        0 ≤
          (normalizedCC20ConcreteTestAlgebra.legacy.encode p.test x).re) ∧
      (∀ x : ℝ,
        (normalizedCC20ConcreteTestAlgebra.legacy.encode p.test x).im = 0) ∧
      normalizedCC20ConcreteTestAlgebra.legacy.encode p.test t = 1 := by
  obtain ⟨u, htsupp, hcompact, hsmooth, hrange, hut⟩ :=
    exists_contDiff_tsupport_subset (s := Set.Ioo a b) (x := t) (n := ⊤)
      (Ioo_mem_nhds hat htb)
  let v : ℝ → ℂ := Complex.ofRealCLM ∘ u
  have hvcompact : HasCompactSupport v := hcompact.comp_left (by simp)
  let hvsmooth := Complex.ofRealCLM.contDiff.comp hsmooth
  let g : TestFunction := hvcompact.toSchwartzMap hvsmooth
  let test : normalizedCC20ConcreteTestAlgebra.Test :=
    normalizedCC20ConcreteTestAlgebra.legacy.decode g
  have hsupport :
      Function.support
        (fun x : ℝ =>
          normalizedCC20ConcreteTestAlgebra.legacy.encode test x) ⊆
        Set.Icc a b := by
    intro y hy
    have hyts : y ∈ tsupport v := by
      apply subset_tsupport
      simpa [test, g, v] using hy
    have hytsu : y ∈ tsupport u := tsupport_comp_subset (by simp) u hyts
    have hyIoo : y ∈ Set.Ioo a b := htsupp hytsu
    exact ⟨le_of_lt hyIoo.1, le_of_lt hyIoo.2⟩
  have hsupportIoo :
      Function.support
        (fun x : ℝ =>
          normalizedCC20ConcreteTestAlgebra.legacy.encode test x) ⊆
        Set.Ioo a b := by
    intro y hy
    have hyts : y ∈ tsupport v := by
      apply subset_tsupport
      simpa [test, g, v] using hy
    have hytsu : y ∈ tsupport u := tsupport_comp_subset (by simp) u hyts
    exact htsupp hytsu
  have hcompactSmooth :
      normalizedCC20TestSpace.compactSupportSmooth test := by
    rw [normalizedCC20TestSpace_compactSupportSmooth_eq]
    simpa [test, g, v] using hvcompact
  refine
    ⟨
      { test := test
        lower := a
        upper := b
        lower_pos := ha
        compactSupportSmooth := hcompactSmooth
        support_subset := hsupport },
      hsupportIoo, ?_, ?_, ?_⟩
  · intro x
    have hxrange : u x ∈ Set.Icc (0 : ℝ) 1 := hrange ⟨x, rfl⟩
    simpa [test, g, v] using hxrange.1
  · intro x
    simp [test, g, v]
  · simp [test, g, v, hut]

theorem weightedMellinKernel_phase_re_pos_at_point
    (rho : ℂ) (coeff : NodeValueImage rho → ℂ) {t : ℝ}
    (hne : weightedMellinKernel rho coeff t ≠ 0) :
    0 <
      ((star (weightedMellinKernel rho coeff t)) *
        weightedMellinKernel rho coeff t).re := by
  have hnorm :
      0 < Complex.normSq (weightedMellinKernel rho coeff t) := by
    exact Complex.normSq_pos.mpr hne
  have hnormRe :
      0 < ((Complex.normSq (weightedMellinKernel rho coeff t) : ℂ).re) := by
    simpa using hnorm
  rw [Complex.normSq_eq_conj_mul_self] at hnormRe
  simpa using hnormRe

theorem weightedMellinKernel_phase_re_positive_interval
    (rho : ℂ) (coeff : NodeValueImage rho → ℂ) {t : ℝ}
    (ht : 0 < t) (hne : weightedMellinKernel rho coeff t ≠ 0) :
    ∃ a b : ℝ,
      0 < a ∧ a < t ∧ t < b ∧
      ∀ x ∈ Set.Ioo a b,
        0 <
          ((star (weightedMellinKernel rho coeff t)) *
            weightedMellinKernel rho coeff x).re := by
  let phase : ℂ := star (weightedMellinKernel rho coeff t)
  have hpos :
      0 <
        (phase * weightedMellinKernel rho coeff t).re := by
    simpa [phase] using
      weightedMellinKernel_phase_re_pos_at_point rho coeff hne
  have hcont :
      ContinuousAt
        (fun x : ℝ => (phase * weightedMellinKernel rho coeff x).re) t :=
    continuousAt_weightedMellinKernel_phase_re_of_pos rho coeff phase ht
  have hevent :
      ∀ᶠ x in 𝓝 t,
        0 < (phase * weightedMellinKernel rho coeff x).re := by
    exact hcont.eventually (isOpen_Ioi.mem_nhds hpos)
  rcases Filter.Eventually.exists_Ioo_subset hevent with
    ⟨a, b, htIoo, hIoo⟩
  refine
    ⟨max a (t / 2), b, lt_max_of_lt_right (half_pos ht),
      max_lt htIoo.1 (half_lt_self ht), htIoo.2, ?_⟩
  intro x hx
  have hxIoo : x ∈ Set.Ioo a b :=
    ⟨lt_of_le_of_lt (le_max_left a (t / 2)) hx.1, hx.2⟩
  simpa [phase] using hIoo hxIoo

theorem integrableOn_weightedMellinKernel_mul_test
    (rho : ℂ) (coeff : NodeValueImage rho → ℂ)
    (p : PositiveIntervalCompactTest) :
    IntegrableOn
      (fun x : ℝ =>
        weightedMellinKernel rho coeff x *
          normalizedCC20ConcreteTestAlgebra.legacy.encode p.test x)
      (Set.Ioi 0) := by
  let f : TestFunction := normalizedCC20ConcreteTestAlgebra.legacy.encode p.test
  have hsum :
      IntegrableOn
        (fun x : ℝ =>
          ∑ z : NodeValueImage rho,
            (x : ℂ) ^ (z.1 - 1) • ((coeff z • f) x))
        (Set.Ioi 0) := by
    apply integrable_finsetSum
    intro z _hz
    have hzconv : MellinConvergent (fun x : ℝ => f x) z.1 :=
      testFunction_mellinConvergent_of_support_subset_Icc
        f z.1 p.lower_pos p.support_subset
    exact hzconv.const_smul (coeff z)
  refine (integrableOn_congr_fun ?_ measurableSet_Ioi).mpr hsum
  intro x _hx
  change
    weightedMellinKernel rho coeff x *
        normalizedCC20ConcreteTestAlgebra.legacy.encode p.test x =
      ∑ z : NodeValueImage rho,
        (x : ℂ) ^ (z.1 - 1) • ((coeff z • f) x)
  rw [weightedMellinKernel, Finset.sum_mul]
  refine Finset.sum_congr rfl ?_
  intro z _hz
  simp [f, SchwartzMap.smul_apply, smul_eq_mul]
  ring

theorem weightedMellinKernel_phase_integral_re_eq
    (rho : ℂ) (coeff : NodeValueImage rho → ℂ)
    (p : PositiveIntervalCompactTest) (phase : ℂ) :
    (phase *
        (∫ x : ℝ in Set.Ioi 0,
          weightedMellinKernel rho coeff x *
            normalizedCC20ConcreteTestAlgebra.legacy.encode p.test x)).re =
      ∫ x : ℝ in Set.Ioi 0,
        (phase *
          (weightedMellinKernel rho coeff x *
            normalizedCC20ConcreteTestAlgebra.legacy.encode p.test x)).re := by
  let h : ℝ → ℂ :=
    fun x =>
      weightedMellinKernel rho coeff x *
        normalizedCC20ConcreteTestAlgebra.legacy.encode p.test x
  have hh : IntegrableOn h (Set.Ioi 0) :=
    integrableOn_weightedMellinKernel_mul_test rho coeff p
  have hphase :
      Integrable (fun x => phase * h x) (volume.restrict (Set.Ioi 0)) :=
    hh.integrable.const_mul phase
  change
    (phase * (∫ x : ℝ in Set.Ioi 0, h x)).re =
      ∫ x : ℝ in Set.Ioi 0, (phase * h x).re
  rw [← integral_const_mul]
  exact (Complex.reCLM.integral_comp_comm hphase).symm

def WeightedMellinKernelPositivePointSeparation (rho : ℂ) : Prop :=
  ∀ coeff : NodeValueImage rho → ℂ,
    coeff ≠ 0 →
      ∃ t : ℝ, 0 < t ∧ weightedMellinKernel rho coeff t ≠ 0

/-- Point separation inside one predetermined interval of the log
coordinate. -/
def WeightedMellinKernelLogWindowPointSeparation
    (rho : ℂ) (a b : ℝ) : Prop :=
  ∀ coeff : NodeValueImage rho → ℂ,
    coeff ≠ 0 →
      ∃ u ∈ Set.Ioo a b,
        weightedMellinKernel rho coeff (Real.exp u) ≠ 0

/-- Point separation inside one predetermined positive interval. -/
def WeightedMellinKernelWindowPointSeparation
    (rho : ℂ) (a b : ℝ) : Prop :=
  ∀ coeff : NodeValueImage rho → ℂ,
    coeff ≠ 0 →
      ∃ t ∈ Set.Ioo a b, weightedMellinKernel rho coeff t ≠ 0

def WeightedMellinKernelPositiveLineIndependence (rho : ℂ) : Prop :=
  ∀ coeff : NodeValueImage rho → ℂ,
    (∀ t : ℝ, 0 < t → weightedMellinKernel rho coeff t = 0) →
      coeff = 0

def WeightedMellinKernelLogLineIndependence (rho : ℂ) : Prop :=
  ∀ coeff : NodeValueImage rho → ℂ,
    (∀ u : ℝ, weightedMellinKernel rho coeff (Real.exp u) = 0) →
      coeff = 0

/-- Independence restricted to a predetermined open interval in the log
coordinate. -/
def WeightedMellinKernelLogWindowIndependence
    (rho : ℂ) (a b : ℝ) : Prop :=
  ∀ coeff : NodeValueImage rho → ℂ,
    (∀ u ∈ Set.Ioo a b,
      weightedMellinKernel rho coeff (Real.exp u) = 0) →
      coeff = 0

theorem weighted_mellin_kernel_log_line_independence
    {rho : ℂ} :
    WeightedMellinKernelLogLineIndependence rho := by
  intro coeff hzero
  classical
  let α := NodeValueImage rho
  let e : Fin (Fintype.card α) ≃ α := (Fintype.equivFin α).symm
  have hmom : ∀ n : ℕ,
      (∑ z : α, coeff z * (z.1 - 1) ^ n) = 0 := by
    intro n
    have h :=
      expMomentSum_eq_zero_of_weightedMellinKernel_exp_eq_zero
        coeff hzero n 0
    rwa [expMomentSum_zero_at_zero_eq_power_sum] at h
  have hinj :
      Function.Injective
        (fun i : Fin (Fintype.card α) => (e i).1 - 1) := by
    intro i j hij
    apply e.injective
    apply Subtype.ext
    have h := congrArg (fun w : ℂ => w + 1) hij
    simpa [sub_eq_add_neg, add_assoc] using h
  let v : Fin (Fintype.card α) → ℂ := fun i => coeff (e i)
  have hvzero : v = 0 := by
    apply Matrix.eq_zero_of_forall_pow_sum_mul_pow_eq_zero
      (f := fun i : Fin (Fintype.card α) => (e i).1 - 1)
      (v := v) hinj
    intro n
    have hn := hmom (n : ℕ)
    change
      (∑ j : Fin (Fintype.card α),
        v j * ((e j).1 - 1) ^ (n : ℕ)) = 0
    rw [show
      (∑ j : Fin (Fintype.card α),
        v j * ((e j).1 - 1) ^ (n : ℕ)) =
          ∑ z : α, coeff z * (z.1 - 1) ^ (n : ℕ) by
        dsimp [v]
        exact Equiv.sum_comp e
          (fun z : α => coeff z * (z.1 - 1) ^ (n : ℕ))]
    exact hn
  funext z
  obtain ⟨i, rfl⟩ := e.surjective z
  exact congrFun hvzero i

/-- A log-window containing zero already separates the finite Mellin node
family.  All power moments are read off at zero and the existing Vandermonde
argument then recovers every coefficient. -/
theorem weighted_mellin_kernel_log_window_independence
    {rho : ℂ} {a b : ℝ} (ha : a < 0) (hb : 0 < b) :
    WeightedMellinKernelLogWindowIndependence rho a b := by
  intro coeff hzero
  classical
  let α := NodeValueImage rho
  let e : Fin (Fintype.card α) ≃ α := (Fintype.equivFin α).symm
  have hmom : ∀ n : ℕ,
      (∑ z : α, coeff z * (z.1 - 1) ^ n) = 0 := by
    intro n
    have h :=
      expMomentSum_eq_zero_of_weightedMellinKernel_exp_eq_zero_on_Ioo
        coeff hzero n 0 ⟨ha, hb⟩
    rwa [expMomentSum_zero_at_zero_eq_power_sum] at h
  have hinj :
      Function.Injective
        (fun i : Fin (Fintype.card α) => (e i).1 - 1) := by
    intro i j hij
    apply e.injective
    apply Subtype.ext
    have h := congrArg (fun w : ℂ => w + 1) hij
    simpa [sub_eq_add_neg, add_assoc] using h
  let v : Fin (Fintype.card α) → ℂ := fun i => coeff (e i)
  have hvzero : v = 0 := by
    apply Matrix.eq_zero_of_forall_pow_sum_mul_pow_eq_zero
      (f := fun i : Fin (Fintype.card α) => (e i).1 - 1)
      (v := v) hinj
    intro n
    have hn := hmom (n : ℕ)
    change
      (∑ j : Fin (Fintype.card α),
        v j * ((e j).1 - 1) ^ (n : ℕ)) = 0
    rw [show
      (∑ j : Fin (Fintype.card α),
        v j * ((e j).1 - 1) ^ (n : ℕ)) =
          ∑ z : α, coeff z * (z.1 - 1) ^ (n : ℕ) by
        dsimp [v]
        exact Equiv.sum_comp e
          (fun z : α => coeff z * (z.1 - 1) ^ (n : ℕ))]
    exact hn
  funext z
  obtain ⟨i, rfl⟩ := e.surjective z
  exact congrFun hvzero i

def WeightedMellinKernelBumpSeparation (rho : ℂ) : Prop :=
  ∀ (coeff : NodeValueImage rho → ℂ) (t : ℝ),
    0 < t →
      weightedMellinKernel rho coeff t ≠ 0 →
        ∃ p : PositiveIntervalCompactTest,
          (∫ x : ℝ in Set.Ioi 0,
            weightedMellinKernel rho coeff x *
              normalizedCC20ConcreteTestAlgebra.legacy.encode p.test x) ≠ 0

def WeightedMellinKernelStrictPhaseBumpDetection (rho : ℂ) : Prop :=
  ∀ (coeff : NodeValueImage rho → ℂ) (t : ℝ),
    0 < t →
      weightedMellinKernel rho coeff t ≠ 0 →
        ∃ (p : PositiveIntervalCompactTest) (phase : ℂ),
          0 <
            (phase *
              (∫ x : ℝ in Set.Ioi 0,
                weightedMellinKernel rho coeff x *
                  normalizedCC20ConcreteTestAlgebra.legacy.encode
                    p.test x)).re

/-- Strict bump detection while keeping the bump inside one predetermined
positive interval. -/
def WeightedMellinKernelWindowStrictPhaseBumpDetection
    (rho : ℂ) (a b : ℝ) : Prop :=
  ∀ (coeff : NodeValueImage rho → ℂ) (t : ℝ),
    t ∈ Set.Ioo a b →
      weightedMellinKernel rho coeff t ≠ 0 →
        ∃ (p : PositiveIntervalCompactTest) (phase : ℂ),
          Function.support
              (fun x : ℝ =>
                normalizedCC20ConcreteTestAlgebra.legacy.encode p.test x) ⊆
            Set.Ioo a b ∧
          0 <
            (phase *
              (∫ x : ℝ in Set.Ioi 0,
                weightedMellinKernel rho coeff x *
                  normalizedCC20ConcreteTestAlgebra.legacy.encode
                    p.test x)).re

theorem weightedMellinKernel_positive_line_independence_of_log_line_independence
    {rho : ℂ}
    (hlog : WeightedMellinKernelLogLineIndependence rho) :
    WeightedMellinKernelPositiveLineIndependence rho := by
  intro coeff hzero
  exact hlog coeff fun u => hzero (Real.exp u) (Real.exp_pos u)

theorem weightedMellinKernel_positive_point_separation_of_positive_line_independence
    {rho : ℂ}
    (hind : WeightedMellinKernelPositiveLineIndependence rho) :
    WeightedMellinKernelPositivePointSeparation rho := by
  intro coeff hcoeff
  by_contra hnone
  apply hcoeff
  apply hind
  intro t ht
  by_contra hne
  exact hnone ⟨t, ht, hne⟩

theorem weightedMellinKernel_positive_point_separation_of_log_line_independence
    {rho : ℂ}
    (hlog : WeightedMellinKernelLogLineIndependence rho) :
    WeightedMellinKernelPositivePointSeparation rho :=
  weightedMellinKernel_positive_point_separation_of_positive_line_independence
    (weightedMellinKernel_positive_line_independence_of_log_line_independence
      hlog)

theorem weightedMellinKernel_log_window_point_separation_of_independence
    {rho : ℂ} {a b : ℝ}
    (hind : WeightedMellinKernelLogWindowIndependence rho a b) :
    WeightedMellinKernelLogWindowPointSeparation rho a b := by
  intro coeff hcoeff
  by_contra hnone
  apply hcoeff
  apply hind
  intro u hu
  by_contra hne
  exact hnone ⟨u, hu, hne⟩

/-- Every positive window containing `1` separates the finite Mellin node
family. -/
theorem weightedMellinKernel_window_point_separation
    {rho : ℂ} {a b : ℝ}
    (ha : 0 < a) (ha_one : a < 1) (hone_b : 1 < b) :
    WeightedMellinKernelWindowPointSeparation rho a b := by
  have hlog_a : Real.log a < 0 := by
    rw [Real.log_lt_iff_lt_exp ha, Real.exp_zero]
    exact ha_one
  have hlog_b : 0 < Real.log b := Real.log_pos hone_b
  have hsep :
      WeightedMellinKernelLogWindowPointSeparation
        rho (Real.log a) (Real.log b) :=
    weightedMellinKernel_log_window_point_separation_of_independence
      (weighted_mellin_kernel_log_window_independence hlog_a hlog_b)
  intro coeff hcoeff
  rcases hsep coeff hcoeff with ⟨u, hu, hne⟩
  refine ⟨Real.exp u, ?_, hne⟩
  constructor
  · exact (Real.log_lt_iff_lt_exp ha).mp hu.1
  · exact (Real.lt_log_iff_exp_lt (lt_trans zero_lt_one hone_b)).mp hu.2

theorem weightedMellinKernel_bump_separation_of_strict_phase_detection
    {rho : ℂ}
    (hphase : WeightedMellinKernelStrictPhaseBumpDetection rho) :
    WeightedMellinKernelBumpSeparation rho := by
  intro coeff t ht hne
  rcases hphase coeff t ht hne with ⟨p, phase, hpos⟩
  refine ⟨p, ?_⟩
  intro hintegral
  rw [hintegral] at hpos
  simp at hpos

theorem weightedMellinKernel_strict_phase_bump_detection_of_interval
    {rho : ℂ} (coeff : NodeValueImage rho → ℂ) {a b t : ℝ}
    (ha : 0 < a) (hat : a < t) (htb : t < b)
    (hne : weightedMellinKernel rho coeff t ≠ 0)
    (hphase_pos :
      ∀ x ∈ Set.Ioo a b,
        0 <
          ((star (weightedMellinKernel rho coeff t)) *
            weightedMellinKernel rho coeff x).re) :
    ∃ (p : PositiveIntervalCompactTest) (phase : ℂ),
      Function.support
          (fun x : ℝ =>
            normalizedCC20ConcreteTestAlgebra.legacy.encode p.test x) ⊆
        Set.Ioo a b ∧
      0 <
        (phase *
          (∫ x : ℝ in Set.Ioi 0,
            weightedMellinKernel rho coeff x *
              normalizedCC20ConcreteTestAlgebra.legacy.encode p.test x)).re := by
  have ht : 0 < t := ha.trans hat
  rcases exists_positive_interval_compact_test_real_bump hat htb ha with
    ⟨p, hsuppIoo, hnonneg, him, htone⟩
  let phase : ℂ := star (weightedMellinKernel rho coeff t)
  let realIntegrand : ℝ → ℝ :=
    fun x =>
      (phase *
        (weightedMellinKernel rho coeff x *
          normalizedCC20ConcreteTestAlgebra.legacy.encode p.test x)).re
  refine ⟨p, phase, hsuppIoo, ?_⟩
  rw [weightedMellinKernel_phase_integral_re_eq]
  have hnonneg_ae :
      0 ≤ᵐ[volume.restrict (Set.Ioi 0)] realIntegrand := by
    refine Eventually.of_forall ?_
    intro x
    by_cases hxmem : x ∈ Function.support
        (fun y : ℝ =>
          normalizedCC20ConcreteTestAlgebra.legacy.encode p.test y)
    · have hxIoo : x ∈ Set.Ioo a b := hsuppIoo hxmem
      have hxpos :
          0 < (phase * weightedMellinKernel rho coeff x).re := by
        simpa [phase] using hphase_pos x hxIoo
      have hbump_re := hnonneg x
      have hbump_im := him x
      have hmul :
          realIntegrand x =
            (phase * weightedMellinKernel rho coeff x).re *
              (normalizedCC20ConcreteTestAlgebra.legacy.encode
                p.test x).re := by
        dsimp [realIntegrand]
        rw [← mul_assoc]
        rw [Complex.mul_re]
        simp [hbump_im]
      rw [hmul]
      exact mul_nonneg hxpos.le hbump_re
    · have hbump_zero :
          normalizedCC20ConcreteTestAlgebra.legacy.encode p.test x = 0 := by
        exact not_not.mp hxmem
      simp [realIntegrand, hbump_zero]
  have hint : Integrable realIntegrand (volume.restrict (Set.Ioi 0)) := by
    have hcomplex :
        Integrable
          (fun x : ℝ =>
            phase *
              (weightedMellinKernel rho coeff x *
                normalizedCC20ConcreteTestAlgebra.legacy.encode p.test x))
          (volume.restrict (Set.Ioi 0)) :=
      (integrableOn_weightedMellinKernel_mul_test rho coeff p).integrable.const_mul
        phase
    exact hcomplex.re
  have hreal_at : 0 < realIntegrand t := by
    dsimp [realIntegrand]
    rw [htone]
    simpa [phase, mul_assoc] using
      weightedMellinKernel_phase_re_pos_at_point rho coeff hne
  have hcont : ContinuousAt realIntegrand t := by
    have hK :
        ContinuousAt (fun x : ℝ => weightedMellinKernel rho coeff x) t :=
      continuousAt_weightedMellinKernel_of_pos rho coeff ht
    have hphaseK :
        ContinuousAt
          (fun x : ℝ => phase * weightedMellinKernel rho coeff x) t :=
      continuousAt_const.mul hK
    have hbump :
        ContinuousAt
          (fun x : ℝ =>
            normalizedCC20ConcreteTestAlgebra.legacy.encode p.test x) t :=
      (SchwartzMap.continuous
        (normalizedCC20ConcreteTestAlgebra.legacy.encode p.test)).continuousAt
    have hcomplex :
        ContinuousAt
          (fun x : ℝ =>
            (phase * weightedMellinKernel rho coeff x) *
              normalizedCC20ConcreteTestAlgebra.legacy.encode p.test x) t :=
      hphaseK.mul hbump
    simpa [realIntegrand, mul_assoc] using
      Complex.continuous_re.continuousAt.comp hcomplex
  have hsupport_pos :
      0 < (volume.restrict (Set.Ioi 0)) (Function.support realIntegrand) := by
    have hevent : ∀ᶠ x in 𝓝 t, 0 < realIntegrand x :=
      hcont.eventually (isOpen_Ioi.mem_nhds hreal_at)
    rcases Filter.Eventually.exists_Ioo_subset hevent with
      ⟨l, u, htIoo, hIoo⟩
    let low : ℝ := max l (t / 2)
    have hlow_pos : 0 < low := lt_max_of_lt_right (half_pos ht)
    have hlow_lt_t : low < t := max_lt htIoo.1 (half_lt_self ht)
    have hlow_lt_u : low < u := lt_trans hlow_lt_t htIoo.2
    have hsubset : Set.Ioo low u ⊆ Function.support realIntegrand := by
      intro x hx
      rw [Function.mem_support]
      exact
        ne_of_gt
          (hIoo
            ⟨lt_of_le_of_lt (le_max_left l (t / 2)) hx.1, hx.2⟩)
    have hinterval_pos :
        0 < (volume.restrict (Set.Ioi 0)) (Set.Ioo low u) := by
      rw [Measure.restrict_apply measurableSet_Ioo]
      have hinter : Set.Ioo low u ∩ Set.Ioi 0 = Set.Ioo low u := by
        ext x
        constructor
        · intro hx
          exact hx.1
        · intro hx
          exact ⟨hx, lt_trans hlow_pos hx.1⟩
      rw [hinter, Real.volume_Ioo]
      exact ENNReal.ofReal_pos.mpr (sub_pos.mpr hlow_lt_u)
    exact measure_pos_of_superset hsubset hinterval_pos.ne'
  have hpos : 0 < ∫ x : ℝ in Set.Ioi 0, realIntegrand x :=
    (integral_pos_iff_support_of_nonneg_ae hnonneg_ae hint).2 hsupport_pos
  simpa [realIntegrand] using hpos

theorem weightedMellinKernel_strict_phase_bump_detection
    {rho : ℂ} :
    WeightedMellinKernelStrictPhaseBumpDetection rho := by
  intro coeff t ht hne
  rcases weightedMellinKernel_phase_re_positive_interval rho coeff ht hne with
    ⟨a, b, ha, hat, htb, hphase_pos⟩
  rcases weightedMellinKernel_strict_phase_bump_detection_of_interval
      coeff ha hat htb hne hphase_pos with
    ⟨p, phase, _hsupp, hpos⟩
  exact ⟨p, phase, hpos⟩

/-- The local phase-positive interval can be intersected with any fixed
positive window containing the detected point, so the resulting bump never
leaves that window. -/
theorem weightedMellinKernel_window_strict_phase_bump_detection
    {rho : ℂ} {a b : ℝ} (ha : 0 < a) :
    WeightedMellinKernelWindowStrictPhaseBumpDetection rho a b := by
  intro coeff t ht hne
  have htpos : 0 < t := ha.trans ht.1
  rcases weightedMellinKernel_phase_re_positive_interval
      rho coeff htpos hne with
    ⟨localA, localB, hlocalA_pos, hlocalA_t, ht_localB, hphase_pos⟩
  let clippedA : ℝ := max localA a
  let clippedB : ℝ := min localB b
  have hclippedA_pos : 0 < clippedA := by
    exact lt_max_of_lt_right ha
  have hclippedA_t : clippedA < t := by
    exact max_lt hlocalA_t ht.1
  have ht_clippedB : t < clippedB := by
    exact lt_min ht_localB ht.2
  have hphase_clipped :
      ∀ x ∈ Set.Ioo clippedA clippedB,
        0 <
          ((star (weightedMellinKernel rho coeff t)) *
            weightedMellinKernel rho coeff x).re := by
    intro x hx
    apply hphase_pos x
    exact
      ⟨lt_of_le_of_lt (le_max_left localA a) hx.1,
        lt_of_lt_of_le hx.2 (min_le_left localB b)⟩
  rcases weightedMellinKernel_strict_phase_bump_detection_of_interval
      coeff hclippedA_pos hclippedA_t ht_clippedB hne hphase_clipped with
    ⟨p, phase, hsupp, hpos⟩
  refine ⟨p, phase, ?_, hpos⟩
  intro x hx
  have hxclipped := hsupp hx
  exact
    ⟨lt_of_le_of_lt (le_max_right localA a) hxclipped.1,
      lt_of_lt_of_le hxclipped.2 (min_le_right localB b)⟩

theorem image_weighted_mellin_sum_eq_kernel_integral
    (rho : ℂ)
    (p : PositiveIntervalCompactTest)
    (coeff : NodeValueImage rho → ℂ) :
    (∑ z : NodeValueImage rho,
      imageMellinVector rho p z * coeff z) =
      ∫ x : ℝ in Set.Ioi 0,
        weightedMellinKernel rho coeff x *
          normalizedCC20ConcreteTestAlgebra.legacy.encode p.test x := by
  let f : TestFunction := normalizedCC20ConcreteTestAlgebra.legacy.encode p.test
  have hsum :
      (∑ z : NodeValueImage rho,
        imageMellinVector rho p z * coeff z) =
        ∑ z : NodeValueImage rho,
          ∫ x : ℝ in Set.Ioi 0,
            (x : ℂ) ^ (z.1 - 1) • ((coeff z • f) x) := by
    refine Finset.sum_congr rfl ?_
    intro z _hz
    rw [imageMellinVector, normalizedCC20TestSpace_mellinAt_eq,
      normalizedCC20ConcreteEvaluationData_mellinAt_eq_mellin]
    simpa [f, mellin, SchwartzMap.smul_apply, smul_eq_mul, mul_comm,
      mul_left_comm, mul_assoc] using
      (mellin_const_smul
        (fun x : ℝ => normalizedCC20ConcreteTestAlgebra.legacy.encode p.test x)
        z.1 (coeff z)).symm
  rw [hsum]
  calc
    (∑ z : NodeValueImage rho,
        ∫ x : ℝ in Set.Ioi 0,
          (x : ℂ) ^ (z.1 - 1) • ((coeff z • f) x)) =
        ∫ x : ℝ in Set.Ioi 0,
          ∑ z : NodeValueImage rho,
            (x : ℂ) ^ (z.1 - 1) • ((coeff z • f) x) := by
          rw [integral_finsetSum]
          intro z _hz
          exact
            (testFunction_mellinConvergent_of_support_subset_Icc
              f z.1 p.lower_pos p.support_subset).const_smul
              (coeff z)
    _ =
        ∫ x : ℝ in Set.Ioi 0,
          weightedMellinKernel rho coeff x *
            normalizedCC20ConcreteTestAlgebra.legacy.encode p.test x := by
          refine setIntegral_congr_fun measurableSet_Ioi ?_
          intro x _hx
          change
            (∑ z : NodeValueImage rho,
              (x : ℂ) ^ (z.1 - 1) • ((coeff z • f) x)) =
            (∑ z : NodeValueImage rho, coeff z * (x : ℂ) ^ (z.1 - 1)) *
              normalizedCC20ConcreteTestAlgebra.legacy.encode p.test x
          rw [Finset.sum_mul]
          refine Finset.sum_congr rfl ?_
          intro z _hz
          simp [f, SchwartzMap.smul_apply, smul_eq_mul]
          ring

theorem image_weighted_mellin_detection_of_kernel_integral_detection
    {rho : ℂ}
    (hdetect :
      ∀ coeff : NodeValueImage rho → ℂ,
        coeff ≠ 0 →
          ∃ p : PositiveIntervalCompactTest,
            (∫ x : ℝ in Set.Ioi 0,
              weightedMellinKernel rho coeff x *
                normalizedCC20ConcreteTestAlgebra.legacy.encode p.test x) ≠
              0) :
    ∀ coeff : NodeValueImage rho → ℂ,
      coeff ≠ 0 →
        ∃ p : PositiveIntervalCompactTest,
          (∑ z : NodeValueImage rho,
            imageMellinVector rho p z * coeff z) ≠ 0 := by
  intro coeff hcoeff
  rcases hdetect coeff hcoeff with ⟨p, hp⟩
  refine ⟨p, ?_⟩
  rw [image_weighted_mellin_sum_eq_kernel_integral rho p coeff]
  exact hp

theorem image_weighted_mellin_detection_of_kernel_point_and_bump_separation
    {rho : ℂ}
    (hpoint : WeightedMellinKernelPositivePointSeparation rho)
    (hbump : WeightedMellinKernelBumpSeparation rho) :
    ∀ coeff : NodeValueImage rho → ℂ,
      coeff ≠ 0 →
        ∃ p : PositiveIntervalCompactTest,
          (∑ z : NodeValueImage rho,
            imageMellinVector rho p z * coeff z) ≠ 0 := by
  refine image_weighted_mellin_detection_of_kernel_integral_detection ?_
  intro coeff hcoeff
  rcases hpoint coeff hcoeff with ⟨t, htpos, htne⟩
  exact hbump coeff t htpos htne

theorem image_weighted_mellin_detection_on_window
    {rho : ℂ} {a b : ℝ}
    (hpoint : WeightedMellinKernelWindowPointSeparation rho a b)
    (hbump : WeightedMellinKernelWindowStrictPhaseBumpDetection rho a b) :
    ∀ coeff : NodeValueImage rho → ℂ,
      coeff ≠ 0 →
        ∃ p : PositiveIntervalCompactTest,
          p.IsSupportedIn a b ∧
          (∑ z : NodeValueImage rho,
            imageMellinVector rho p z * coeff z) ≠ 0 := by
  intro coeff hcoeff
  rcases hpoint coeff hcoeff with ⟨t, ht, htne⟩
  rcases hbump coeff t ht htne with ⟨p, phase, hsupp, hpos⟩
  have hintegral :
      (∫ x : ℝ in Set.Ioi 0,
        weightedMellinKernel rho coeff x *
          normalizedCC20ConcreteTestAlgebra.legacy.encode p.test x) ≠ 0 := by
    intro hzero
    rw [hzero] at hpos
    simp at hpos
  refine ⟨p, hsupp, ?_⟩
  rw [image_weighted_mellin_sum_eq_kernel_integral]
  exact hintegral

theorem expandedMellinVector_span_top_of_linear_dual_separation
    {rho : ℂ}
    (hsep :
      ∀ L : (CC20YoshidaExpandedMomentNode → ℂ) →ₗ[ℂ] ℂ,
        L ≠ 0 →
          ∃ p : PositiveIntervalCompactTest,
            L (expandedMellinVector rho p) ≠ 0) :
    Submodule.span ℂ (Set.range (expandedMellinVector rho)) = ⊤ := by
  classical
  by_contra htop
  let P : Submodule ℂ (CC20YoshidaExpandedMomentNode → ℂ) :=
    Submodule.span ℂ (Set.range (expandedMellinVector rho))
  have hproper : P < ⊤ := by
    exact (show P ≠ ⊤ from htop).lt_top
  rcases Submodule.exists_le_ker_of_lt_top P hproper with
    ⟨L, hL_ne, hP_le_ker⟩
  rcases hsep L hL_ne with ⟨p, hp⟩
  have hp_mem : expandedMellinVector rho p ∈ P :=
    Submodule.subset_span (Set.mem_range_self p)
  exact hp (hP_le_ker hp_mem)

theorem positive_interval_expanded_mellin_surjective_of_span_top
    {rho : ℂ}
    (hspan :
      Submodule.span ℂ (Set.range (expandedMellinVector rho)) = ⊤) :
    ∀ y : CC20YoshidaExpandedMomentNode → ℂ,
      ∃ g lower upper,
        0 < lower ∧
        normalizedCC20TestSpace.compactSupportSmooth g ∧
        Function.support
          (fun x : ℝ =>
            normalizedCC20ConcreteTestAlgebra.legacy.encode g x) ⊆
          Set.Icc lower upper ∧
        ∀ i : CC20YoshidaExpandedMomentNode,
          normalizedCC20TestSpace.mellinAt g (nodeValue rho i) = y i := by
  intro y
  have hy_mem :
      y ∈ Submodule.span ℂ (Set.range (expandedMellinVector rho)) := by
    rw [hspan]
    exact Submodule.mem_top
  rcases Finsupp.mem_span_range_iff_exists_finsupp.mp hy_mem with
    ⟨c, hc⟩
  let g : normalizedCC20ConcreteTestAlgebra.Test :=
    positiveIntervalCompactTestCombination c
  rcases positiveIntervalCompactTestCombination_support_subset c with
    ⟨lower, upper, hlower, hsupp⟩
  refine ⟨g, lower, upper, hlower, ?_, hsupp, ?_⟩
  · exact positiveIntervalCompactTestCombination_compactSupportSmooth c
  · intro i
    rw [expandedMellinVector_positiveIntervalCompactTestCombination rho c i]
    have hpoint := congr_fun hc i
    simpa [Finsupp.sum, Pi.smul_apply, smul_eq_mul] using hpoint

theorem positive_interval_expanded_mellin_surjective_of_linear_dual_separation
    {rho : ℂ}
    (hsep :
      ∀ L : (CC20YoshidaExpandedMomentNode → ℂ) →ₗ[ℂ] ℂ,
        L ≠ 0 →
          ∃ p : PositiveIntervalCompactTest,
            L (expandedMellinVector rho p) ≠ 0) :
    ∀ y : CC20YoshidaExpandedMomentNode → ℂ,
      ∃ g lower upper,
        0 < lower ∧
        normalizedCC20TestSpace.compactSupportSmooth g ∧
        Function.support
          (fun x : ℝ =>
            normalizedCC20ConcreteTestAlgebra.legacy.encode g x) ⊆
          Set.Icc lower upper ∧
        ∀ i : CC20YoshidaExpandedMomentNode,
          normalizedCC20TestSpace.mellinAt g (nodeValue rho i) = y i := by
  exact
    positive_interval_expanded_mellin_surjective_of_span_top
      (expandedMellinVector_span_top_of_linear_dual_separation hsep)

theorem imageMellinVector_span_top_of_linear_dual_separation
    {rho : ℂ}
    (hsep :
      ∀ L : (NodeValueImage rho → ℂ) →ₗ[ℂ] ℂ,
        L ≠ 0 →
          ∃ p : PositiveIntervalCompactTest,
            L (imageMellinVector rho p) ≠ 0) :
    Submodule.span ℂ (Set.range (imageMellinVector rho)) = ⊤ := by
  classical
  by_contra htop
  let P : Submodule ℂ (NodeValueImage rho → ℂ) :=
    Submodule.span ℂ (Set.range (imageMellinVector rho))
  have hproper : P < ⊤ := by
    exact (show P ≠ ⊤ from htop).lt_top
  rcases Submodule.exists_le_ker_of_lt_top P hproper with
    ⟨L, hL_ne, hP_le_ker⟩
  rcases hsep L hL_ne with ⟨p, hp⟩
  have hp_mem : imageMellinVector rho p ∈ P :=
    Submodule.subset_span (Set.mem_range_self p)
  exact hp (hP_le_ker hp_mem)

theorem positive_interval_node_value_image_mellin_surjective_of_span_top
    {rho : ℂ}
    (hspan :
      Submodule.span ℂ (Set.range (imageMellinVector rho)) = ⊤) :
    ∀ y : NodeValueImage rho → ℂ,
      ∃ g lower upper,
        0 < lower ∧
        normalizedCC20TestSpace.compactSupportSmooth g ∧
        Function.support
          (fun x : ℝ =>
            normalizedCC20ConcreteTestAlgebra.legacy.encode g x) ⊆
          Set.Icc lower upper ∧
        ∀ z : NodeValueImage rho,
          normalizedCC20TestSpace.mellinAt g z.1 = y z := by
  intro y
  have hy_mem :
      y ∈ Submodule.span ℂ (Set.range (imageMellinVector rho)) := by
    rw [hspan]
    exact Submodule.mem_top
  rcases Finsupp.mem_span_range_iff_exists_finsupp.mp hy_mem with
    ⟨c, hc⟩
  let g : normalizedCC20ConcreteTestAlgebra.Test :=
    positiveIntervalCompactTestCombination c
  rcases positiveIntervalCompactTestCombination_support_subset c with
    ⟨lower, upper, hlower, hsupp⟩
  refine ⟨g, lower, upper, hlower, ?_, hsupp, ?_⟩
  · exact positiveIntervalCompactTestCombination_compactSupportSmooth c
  · intro z
    rw [imageMellinVector_positiveIntervalCompactTestCombination rho c z]
    have hpoint := congr_fun hc z
    simpa [Finsupp.sum, Pi.smul_apply, smul_eq_mul] using hpoint

theorem positive_interval_node_value_image_mellin_surjective_of_linear_dual_separation
    {rho : ℂ}
    (hsep :
      ∀ L : (NodeValueImage rho → ℂ) →ₗ[ℂ] ℂ,
        L ≠ 0 →
          ∃ p : PositiveIntervalCompactTest,
            L (imageMellinVector rho p) ≠ 0) :
    ∀ y : NodeValueImage rho → ℂ,
      ∃ g lower upper,
        0 < lower ∧
        normalizedCC20TestSpace.compactSupportSmooth g ∧
        Function.support
          (fun x : ℝ =>
            normalizedCC20ConcreteTestAlgebra.legacy.encode g x) ⊆
          Set.Icc lower upper ∧
        ∀ z : NodeValueImage rho,
          normalizedCC20TestSpace.mellinAt g z.1 = y z := by
  exact
    positive_interval_node_value_image_mellin_surjective_of_span_top
      (imageMellinVector_span_top_of_linear_dual_separation hsep)

theorem concreteExpandedMellinRealizes_of_node_value_image_mellin_surjective
    {rho : ℂ}
    (hrho : RHDefinitionBridge.standard.sourceNontrivialZero rho)
    (hoff : rho.re ≠ 1 / 2)
    (hsurj :
      ∀ y : {z : ℂ // z ∈ expandedNodeValueFinset rho} → ℂ,
        ∃ g lower upper,
          0 < lower ∧
          normalizedCC20TestSpace.compactSupportSmooth g ∧
          Function.support
            (fun x : ℝ =>
              normalizedCC20ConcreteTestAlgebra.legacy.encode g x) ⊆
            Set.Icc lower upper ∧
          ∀ z : {z : ℂ // z ∈ expandedNodeValueFinset rho},
            normalizedCC20TestSpace.mellinAt g z.1 = y z) :
    ∃ g lower upper,
      0 < lower ∧
      normalizedCC20TestSpace.compactSupportSmooth g ∧
      Function.support
        (fun x : ℝ =>
          normalizedCC20ConcreteTestAlgebra.legacy.encode g x) ⊆
        Set.Icc lower upper ∧
      ConcreteExpandedMellinRealizes rho g := by
  rcases hsurj (fun z => targetValueOnNodeValue rho z.1) with
    ⟨g, lower, upper, hlower, hcompact, hsupp, hvalue⟩
  refine ⟨g, lower, upper, hlower, hcompact, hsupp, ?_⟩
  intro i
  have hvalue_i :
      normalizedCC20TestSpace.mellinAt g (nodeValue rho i) =
        targetValueOnNodeValue rho (nodeValue rho i) := by
    simpa using
      hvalue ⟨nodeValue rho i, by simp [expandedNodeValueFinset]⟩
  rw [hvalue_i]
  exact targetValueOnNodeValue_eq_targetValue hrho hoff i

noncomputable def linearFunctionalCoordinates
    (L : (CC20YoshidaExpandedMomentNode → ℂ) →ₗ[ℂ] ℂ) :
    CC20YoshidaExpandedMomentNode → ℂ :=
  fun i => L ((Pi.basisFun ℂ CC20YoshidaExpandedMomentNode) i)

theorem linearFunctional_apply_eq_sum_coordinates
    (L : (CC20YoshidaExpandedMomentNode → ℂ) →ₗ[ℂ] ℂ)
    (v : CC20YoshidaExpandedMomentNode → ℂ) :
    L v =
      ∑ i : CC20YoshidaExpandedMomentNode,
        v i * linearFunctionalCoordinates L i := by
  let b := Pi.basisFun ℂ CC20YoshidaExpandedMomentNode
  calc
    L v =
        L (∑ i : CC20YoshidaExpandedMomentNode, (b.repr v) i • b i) := by
          rw [b.sum_repr v]
    _ =
        ∑ i : CC20YoshidaExpandedMomentNode,
          v i * linearFunctionalCoordinates L i := by
          rw [map_sum]
          refine Finset.sum_congr rfl ?_
          intro i _hi
          rw [map_smul]
          change
            ((Pi.basisFun ℂ CC20YoshidaExpandedMomentNode).repr v i) *
                L ((Pi.basisFun ℂ CC20YoshidaExpandedMomentNode) i) =
              v i * linearFunctionalCoordinates L i
          rw [Pi.basisFun_repr]
          rfl

theorem linearFunctionalCoordinates_ne_zero
    {L : (CC20YoshidaExpandedMomentNode → ℂ) →ₗ[ℂ] ℂ}
    (hL : L ≠ 0) :
    linearFunctionalCoordinates L ≠ 0 := by
  intro hcoords
  apply hL
  apply LinearMap.ext
  intro v
  rw [linearFunctional_apply_eq_sum_coordinates]
  simp [hcoords]

theorem linear_dual_separation_of_weighted_expanded_mellin_detection
    {rho : ℂ}
    (hdetect :
      ∀ coeff : CC20YoshidaExpandedMomentNode → ℂ,
        coeff ≠ 0 →
          ∃ p : PositiveIntervalCompactTest,
            (∑ i : CC20YoshidaExpandedMomentNode,
              expandedMellinVector rho p i * coeff i) ≠ 0) :
    ∀ L : (CC20YoshidaExpandedMomentNode → ℂ) →ₗ[ℂ] ℂ,
      L ≠ 0 →
        ∃ p : PositiveIntervalCompactTest,
          L (expandedMellinVector rho p) ≠ 0 := by
  intro L hL
  rcases hdetect (linearFunctionalCoordinates L)
      (linearFunctionalCoordinates_ne_zero hL) with
    ⟨p, hp⟩
  refine ⟨p, ?_⟩
  rw [linearFunctional_apply_eq_sum_coordinates]
  exact hp

noncomputable def imageLinearFunctionalCoordinates
    {rho : ℂ}
    (L : (NodeValueImage rho → ℂ) →ₗ[ℂ] ℂ) :
    NodeValueImage rho → ℂ := by
  classical
  exact fun z => L ((Pi.basisFun ℂ (NodeValueImage rho)) z)

theorem imageLinearFunctional_apply_eq_sum_coordinates
    {rho : ℂ}
    (L : (NodeValueImage rho → ℂ) →ₗ[ℂ] ℂ)
    (v : NodeValueImage rho → ℂ) :
    L v =
      ∑ z : NodeValueImage rho,
        v z * imageLinearFunctionalCoordinates L z := by
  classical
  let b := Pi.basisFun ℂ (NodeValueImage rho)
  calc
    L v =
        L (∑ z : NodeValueImage rho, (b.repr v) z • b z) := by
          rw [b.sum_repr v]
    _ =
        ∑ z : NodeValueImage rho,
          v z * imageLinearFunctionalCoordinates L z := by
          rw [map_sum]
          refine Finset.sum_congr rfl ?_
          intro z _hz
          rw [map_smul]
          change
            ((Pi.basisFun ℂ (NodeValueImage rho)).repr v z) *
                L ((Pi.basisFun ℂ (NodeValueImage rho)) z) =
              v z * imageLinearFunctionalCoordinates L z
          rw [Pi.basisFun_repr]
          rfl

theorem imageLinearFunctionalCoordinates_ne_zero
    {rho : ℂ}
    {L : (NodeValueImage rho → ℂ) →ₗ[ℂ] ℂ}
    (hL : L ≠ 0) :
    imageLinearFunctionalCoordinates L ≠ 0 := by
  intro hcoords
  apply hL
  apply LinearMap.ext
  intro v
  rw [imageLinearFunctional_apply_eq_sum_coordinates]
  simp [hcoords]

theorem image_linear_dual_separation_of_weighted_mellin_detection
    {rho : ℂ}
    (hdetect :
      ∀ coeff : NodeValueImage rho → ℂ,
        coeff ≠ 0 →
          ∃ p : PositiveIntervalCompactTest,
            (∑ z : NodeValueImage rho,
              imageMellinVector rho p z * coeff z) ≠ 0) :
    ∀ L : (NodeValueImage rho → ℂ) →ₗ[ℂ] ℂ,
      L ≠ 0 →
        ∃ p : PositiveIntervalCompactTest,
          L (imageMellinVector rho p) ≠ 0 := by
  intro L hL
  rcases hdetect (imageLinearFunctionalCoordinates L)
      (imageLinearFunctionalCoordinates_ne_zero hL) with
    ⟨p, hp⟩
  refine ⟨p, ?_⟩
  rw [imageLinearFunctional_apply_eq_sum_coordinates]
  exact hp

theorem positive_interval_node_value_image_mellin_surjective_of_weighted_detection
    {rho : ℂ}
    (hdetect :
      ∀ coeff : NodeValueImage rho → ℂ,
        coeff ≠ 0 →
          ∃ p : PositiveIntervalCompactTest,
            (∑ z : NodeValueImage rho,
              imageMellinVector rho p z * coeff z) ≠ 0) :
    ∀ y : NodeValueImage rho → ℂ,
      ∃ g lower upper,
        0 < lower ∧
        normalizedCC20TestSpace.compactSupportSmooth g ∧
        Function.support
          (fun x : ℝ =>
            normalizedCC20ConcreteTestAlgebra.legacy.encode g x) ⊆
          Set.Icc lower upper ∧
        ∀ z : NodeValueImage rho,
          normalizedCC20TestSpace.mellinAt g z.1 = y z := by
  exact
    positive_interval_node_value_image_mellin_surjective_of_linear_dual_separation
      (image_linear_dual_separation_of_weighted_mellin_detection hdetect)

theorem windowed_image_linear_dual_separation_of_weighted_mellin_detection
    {rho : ℂ} {a b : ℝ}
    (hdetect :
      ∀ coeff : NodeValueImage rho → ℂ,
        coeff ≠ 0 →
          ∃ p : PositiveIntervalCompactTest,
            p.IsSupportedIn a b ∧
            (∑ z : NodeValueImage rho,
              imageMellinVector rho p z * coeff z) ≠ 0) :
    ∀ L : (NodeValueImage rho → ℂ) →ₗ[ℂ] ℂ,
      L ≠ 0 →
        ∃ p : WindowedPositiveIntervalCompactTest a b,
          L (windowedImageMellinVector rho a b p) ≠ 0 := by
  intro L hL
  rcases hdetect (imageLinearFunctionalCoordinates L)
      (imageLinearFunctionalCoordinates_ne_zero hL) with
    ⟨p, hsupp, hp⟩
  let windowed : WindowedPositiveIntervalCompactTest a b := ⟨p, hsupp⟩
  refine ⟨windowed, ?_⟩
  change L (imageMellinVector rho p) ≠ 0
  rw [imageLinearFunctional_apply_eq_sum_coordinates]
  exact hp

theorem windowedImageMellinVector_span_top_of_linear_dual_separation
    {rho : ℂ} {a b : ℝ}
    (hsep :
      ∀ L : (NodeValueImage rho → ℂ) →ₗ[ℂ] ℂ,
        L ≠ 0 →
          ∃ p : WindowedPositiveIntervalCompactTest a b,
            L (windowedImageMellinVector rho a b p) ≠ 0) :
    Submodule.span ℂ
        (Set.range (windowedImageMellinVector rho a b)) = ⊤ := by
  classical
  by_contra htop
  let P : Submodule ℂ (NodeValueImage rho → ℂ) :=
    Submodule.span ℂ (Set.range (windowedImageMellinVector rho a b))
  have hproper : P < ⊤ := by
    exact (show P ≠ ⊤ from htop).lt_top
  rcases Submodule.exists_le_ker_of_lt_top P hproper with
    ⟨L, hL_ne, hP_le_ker⟩
  rcases hsep L hL_ne with ⟨p, hp⟩
  have hp_mem : windowedImageMellinVector rho a b p ∈ P :=
    Submodule.subset_span (Set.mem_range_self p)
  exact hp (hP_le_ker hp_mem)

theorem windowed_node_value_image_mellin_surjective_of_span_top
    {rho : ℂ} {a b : ℝ}
    (hspan :
      Submodule.span ℂ
          (Set.range (windowedImageMellinVector rho a b)) = ⊤) :
    ∀ y : NodeValueImage rho → ℂ,
      ∃ g,
        normalizedCC20TestSpace.compactSupportSmooth g ∧
        Function.support
            (fun x : ℝ =>
              normalizedCC20ConcreteTestAlgebra.legacy.encode g x) ⊆
          Set.Ioo a b ∧
        ∀ z : NodeValueImage rho,
          normalizedCC20TestSpace.mellinAt g z.1 = y z := by
  intro y
  have hy_mem :
      y ∈ Submodule.span ℂ
        (Set.range (windowedImageMellinVector rho a b)) := by
    rw [hspan]
    exact Submodule.mem_top
  rcases Finsupp.mem_span_range_iff_exists_finsupp.mp hy_mem with
    ⟨c, hc⟩
  let g : normalizedCC20ConcreteTestAlgebra.Test :=
    windowedPositiveIntervalCompactTestCombination c
  refine ⟨g, ?_, ?_, ?_⟩
  · exact windowedPositiveIntervalCompactTestCombination_compactSupportSmooth c
  · exact windowedPositiveIntervalCompactTestCombination_support_subset c
  · intro z
    rw [windowedImageMellinVector_combination]
    have hpoint := congr_fun hc z
    simpa [Finsupp.sum, Pi.smul_apply, smul_eq_mul] using hpoint

/-- Full finite Mellin interpolation inside any predetermined positive window
containing `1`. -/
theorem fixed_window_node_value_image_mellin_surjective
    {rho : ℂ} {a b : ℝ}
    (ha : 0 < a) (ha_one : a < 1) (hone_b : 1 < b) :
    ∀ y : NodeValueImage rho → ℂ,
      ∃ g,
        normalizedCC20TestSpace.compactSupportSmooth g ∧
        Function.support
            (fun x : ℝ =>
              normalizedCC20ConcreteTestAlgebra.legacy.encode g x) ⊆
          Set.Ioo a b ∧
        ∀ z : NodeValueImage rho,
          normalizedCC20TestSpace.mellinAt g z.1 = y z := by
  have hdetect :=
    image_weighted_mellin_detection_on_window
      (weightedMellinKernel_window_point_separation
        (rho := rho) ha ha_one hone_b)
      (weightedMellinKernel_window_strict_phase_bump_detection
        (rho := rho) ha)
  exact
    windowed_node_value_image_mellin_surjective_of_span_top
      (windowedImageMellinVector_span_top_of_linear_dual_separation
        (windowed_image_linear_dual_separation_of_weighted_mellin_detection
          hdetect))

noncomputable def expandedFiniteLinearCombination
    (coeff : CC20YoshidaExpandedMomentNode → ℂ)
    (basisTest :
      CC20YoshidaExpandedMomentNode →
        normalizedCC20ConcreteTestAlgebra.Test) :
    normalizedCC20ConcreteTestAlgebra.Test :=
  normalizedCC20ConcreteTestAlgebra.legacy.decode
    (∑ j,
      coeff j • normalizedCC20ConcreteTestAlgebra.legacy.encode (basisTest j))

theorem expandedFiniteLinearCombination_compactSupportSmooth
    (coeff : CC20YoshidaExpandedMomentNode → ℂ)
    (basisTest :
      CC20YoshidaExpandedMomentNode →
        normalizedCC20ConcreteTestAlgebra.Test)
    (hcompact : ∀ j,
      normalizedCC20TestSpace.compactSupportSmooth (basisTest j)) :
    normalizedCC20TestSpace.compactSupportSmooth
      (expandedFiniteLinearCombination coeff basisTest) := by
  rw [normalizedCC20TestSpace_compactSupportSmooth_eq]
  unfold expandedFiniteLinearCombination
  simp only [AnalyticCore.LegacyTestEquiv.encode_decode_apply]
  exact
    (HasCompactSupport.finset_sum
      (s := (Finset.univ : Finset CC20YoshidaExpandedMomentNode))
      (f := fun j : CC20YoshidaExpandedMomentNode =>
        fun x : ℝ =>
          (coeff j •
            normalizedCC20ConcreteTestAlgebra.legacy.encode
              (basisTest j)) x)
      (fun j _hj => by
        have hj := hcompact j
        rw [normalizedCC20TestSpace_compactSupportSmooth_eq] at hj
        simpa [SchwartzMap.smul_apply] using
          (HasCompactSupport.smul_left
            (f := fun _x : ℝ => coeff j)
            (f' := fun x : ℝ =>
              normalizedCC20ConcreteTestAlgebra.legacy.encode
                (basisTest j) x)
            hj)))

theorem expandedMellinAt_finiteLinearCombination
    (rho : ℂ)
    (coeff : CC20YoshidaExpandedMomentNode → ℂ)
    (basisTest :
      CC20YoshidaExpandedMomentNode →
        normalizedCC20ConcreteTestAlgebra.Test)
    (i : CC20YoshidaExpandedMomentNode)
    (hconv : ∀ j,
      MellinConvergent
        (fun x : ℝ =>
          normalizedCC20ConcreteTestAlgebra.legacy.encode
            (basisTest j) x)
        (nodeValue rho i)) :
    normalizedCC20TestSpace.mellinAt
        (expandedFiniteLinearCombination coeff basisTest)
        (nodeValue rho i) =
      Matrix.mulVec
        (Matrix.of fun i j =>
          normalizedCC20TestSpace.mellinAt (basisTest j) (nodeValue rho i))
        coeff i := by
  have hmellin :
      mellin
          (fun x : ℝ =>
            normalizedCC20ConcreteTestAlgebra.legacy.encode
              (expandedFiniteLinearCombination coeff basisTest) x)
          (nodeValue rho i) =
        ∑ j : CC20YoshidaExpandedMomentNode,
          coeff j *
            mellin
              (fun x : ℝ =>
                normalizedCC20ConcreteTestAlgebra.legacy.encode
                  (basisTest j) x)
              (nodeValue rho i) := by
    unfold expandedFiniteLinearCombination
    rw [mellin]
    calc
      (∫ t : ℝ in Set.Ioi 0,
          (t : ℂ) ^ (nodeValue rho i - 1) •
            normalizedCC20ConcreteTestAlgebra.legacy.encode
              (normalizedCC20ConcreteTestAlgebra.legacy.decode
                (∑ j : CC20YoshidaExpandedMomentNode,
                  coeff j •
                    normalizedCC20ConcreteTestAlgebra.legacy.encode
                      (basisTest j))) t) =
          ∫ t : ℝ in Set.Ioi 0,
            ∑ j : CC20YoshidaExpandedMomentNode,
              (t : ℂ) ^ (nodeValue rho i - 1) •
                ((coeff j •
                  normalizedCC20ConcreteTestAlgebra.legacy.encode
                    (basisTest j)) t) := by
            refine setIntegral_congr_fun measurableSet_Ioi ?_
            intro t _ht
            simp [SchwartzMap.sum_apply, Finset.mul_sum]
      _ =
          ∑ j : CC20YoshidaExpandedMomentNode,
            ∫ t : ℝ in Set.Ioi 0,
              (t : ℂ) ^ (nodeValue rho i - 1) •
                ((coeff j •
                  normalizedCC20ConcreteTestAlgebra.legacy.encode
                    (basisTest j)) t) := by
            rw [integral_finsetSum]
            intro j _hj
            exact hconv j |>.const_smul (coeff j)
      _ =
          ∑ j : CC20YoshidaExpandedMomentNode,
            coeff j *
              mellin
                (fun x : ℝ =>
                  normalizedCC20ConcreteTestAlgebra.legacy.encode
                    (basisTest j) x)
                (nodeValue rho i) := by
            refine Finset.sum_congr rfl ?_
            intro j _hj
            simpa [mellin, SchwartzMap.smul_apply, smul_eq_mul] using
              (mellin_const_smul
                (fun x : ℝ =>
                  normalizedCC20ConcreteTestAlgebra.legacy.encode
                    (basisTest j) x)
                (nodeValue rho i)
                (coeff j))
  rw [normalizedCC20TestSpace_mellinAt_eq,
    normalizedCC20ConcreteEvaluationData_mellinAt_eq_mellin, hmellin]
  rw [Matrix.mulVec, dotProduct]
  refine Finset.sum_congr rfl ?_
  intro j _hj
  rw [Matrix.of_apply, normalizedCC20TestSpace_mellinAt_eq,
    normalizedCC20ConcreteEvaluationData_mellinAt_eq_mellin]
  ring

theorem concreteExpandedMellinRealizes_of_basis_matrix_det_ne_zero
    {rho : ℂ}
    (basisTest :
      CC20YoshidaExpandedMomentNode →
        normalizedCC20ConcreteTestAlgebra.Test)
    (hcompact : ∀ j,
      normalizedCC20TestSpace.compactSupportSmooth (basisTest j))
    (hconv : ∀ i j,
      MellinConvergent
        (fun x : ℝ =>
          normalizedCC20ConcreteTestAlgebra.legacy.encode
            (basisTest j) x)
        (nodeValue rho i))
    (hdet :
      (Matrix.of fun i j =>
        normalizedCC20TestSpace.mellinAt
          (basisTest j) (nodeValue rho i)).det ≠ 0) :
    ∃ g : normalizedCC20ConcreteTestAlgebra.Test,
      normalizedCC20TestSpace.compactSupportSmooth g ∧
      ConcreteExpandedMellinRealizes rho g := by
  let M : Matrix
      CC20YoshidaExpandedMomentNode
      CC20YoshidaExpandedMomentNode ℂ :=
    Matrix.of fun i j =>
      normalizedCC20TestSpace.mellinAt (basisTest j) (nodeValue rho i)
  let coeff : CC20YoshidaExpandedMomentNode → ℂ :=
    Matrix.mulVec M⁻¹ targetValue
  refine ⟨expandedFiniteLinearCombination coeff basisTest, ?_, ?_⟩
  · exact expandedFiniteLinearCombination_compactSupportSmooth
      coeff basisTest hcompact
  · intro i
    have hunit : IsUnit M.det := by
      exact isUnit_iff_ne_zero.mpr (by simpa [M] using hdet)
    rw [expandedMellinAt_finiteLinearCombination
      rho coeff basisTest i (hconv i)]
    change Matrix.mulVec M (Matrix.mulVec M⁻¹ targetValue) i =
      targetValue i
    rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv M hunit,
      Matrix.one_mulVec]

theorem concreteExpandedMellinRealizes_of_positive_interval_supported_basis
    {rho : ℂ}
    (basisTest :
      CC20YoshidaExpandedMomentNode →
        normalizedCC20ConcreteTestAlgebra.Test)
    (lower upper : CC20YoshidaExpandedMomentNode → ℝ)
    (hcompact : ∀ j,
      normalizedCC20TestSpace.compactSupportSmooth (basisTest j))
    (hlower : ∀ j, 0 < lower j)
    (hsupp : ∀ j,
      Function.support
        (fun x : ℝ =>
          normalizedCC20ConcreteTestAlgebra.legacy.encode
            (basisTest j) x) ⊆ Set.Icc (lower j) (upper j))
    (hdet :
      (Matrix.of fun i j =>
        normalizedCC20TestSpace.mellinAt
          (basisTest j) (nodeValue rho i)).det ≠ 0) :
    ∃ g : normalizedCC20ConcreteTestAlgebra.Test,
      normalizedCC20TestSpace.compactSupportSmooth g ∧
      ConcreteExpandedMellinRealizes rho g := by
  exact concreteExpandedMellinRealizes_of_basis_matrix_det_ne_zero
    basisTest hcompact
    (fun i j =>
      testFunction_mellinConvergent_of_support_subset_Icc
        (normalizedCC20ConcreteTestAlgebra.legacy.encode (basisTest j))
        (nodeValue rho i) (hlower j) (hsupp j))
    hdet

theorem concreteExpandedMellinRealizes_vanishesOn_cc20Triple
    {rho : ℂ} {g : normalizedCC20ConcreteTestAlgebra.Test}
    (h : ConcreteExpandedMellinRealizes rho g) :
    CC20VanishesOn normalizedCC20TestSpace cc20TripleFiniteVanishingSet g := by
  intro p _hp
  cases p with
  | zero =>
      simpa [ConcreteExpandedMellinRealizes, nodeValue, targetValue] using
        h zero
  | half =>
      simpa [ConcreteExpandedMellinRealizes, nodeValue, targetValue] using
        h half
  | one =>
      simpa [ConcreteExpandedMellinRealizes, nodeValue, targetValue] using
        h one

theorem concreteExpandedMellinRealizes_detects_rho
    {rho : ℂ} {g : normalizedCC20ConcreteTestAlgebra.Test}
    (h : ConcreteExpandedMellinRealizes rho g) :
    normalizedCC20TestSpace.mellinAt g rho ≠ 0 := by
  rw [show normalizedCC20TestSpace.mellinAt g rho = (-1 : ℂ) by
    simpa [ConcreteExpandedMellinRealizes, nodeValue, targetValue] using
      h targetRho]
  norm_num [targetValue]

theorem concreteExpandedMellinRealizes_posHalf
    {rho : ℂ} {g : normalizedCC20ConcreteTestAlgebra.Test}
    (h : ConcreteExpandedMellinRealizes rho g) :
    normalizedCC20TestSpace.mellinAt g (Complex.I / 2) = (-1 : ℂ) := by
  simpa [ConcreteExpandedMellinRealizes, nodeValue, targetValue] using
    h posHalfDensity

theorem concreteExpandedMellinRealizes_negHalf
    {rho : ℂ} {g : normalizedCC20ConcreteTestAlgebra.Test}
    (h : ConcreteExpandedMellinRealizes rho g) :
    normalizedCC20TestSpace.mellinAt g (-Complex.I / 2) = (-1 : ℂ) := by
  simpa [ConcreteExpandedMellinRealizes, nodeValue, targetValue] using
    h negHalfDensity

end CC20YoshidaExpandedMomentNode

open CC20YoshidaExpandedMomentNode

theorem concreteYoshidaMomentData_of_expanded_mellin_realizes
    {rho : ℂ} {g : normalizedCC20ConcreteTestAlgebra.Test}
    (hcompact : normalizedCC20TestSpace.compactSupportSmooth g)
    (hrealizes :
      CC20YoshidaExpandedMomentNode.ConcreteExpandedMellinRealizes rho g) :
    ConcreteYoshidaMomentData rho g where
  compactSupportSmooth := hcompact
  vanishesOnF :=
    CC20YoshidaExpandedMomentNode.concreteExpandedMellinRealizes_vanishesOn_cc20Triple
      hrealizes
  detectsRho :=
    CC20YoshidaExpandedMomentNode.concreteExpandedMellinRealizes_detects_rho
      hrealizes
  mellinAt_posHalf :=
    CC20YoshidaExpandedMomentNode.concreteExpandedMellinRealizes_posHalf
      hrealizes
  mellinAt_negHalf :=
    CC20YoshidaExpandedMomentNode.concreteExpandedMellinRealizes_negHalf
      hrealizes

theorem exists_concreteYoshidaMomentData_of_positive_interval_supported_basis
    {rho : ℂ}
    (basisTest :
      CC20YoshidaExpandedMomentNode →
        normalizedCC20ConcreteTestAlgebra.Test)
    (lower upper : CC20YoshidaExpandedMomentNode → ℝ)
    (hcompact : ∀ j,
      normalizedCC20TestSpace.compactSupportSmooth (basisTest j))
    (hlower : ∀ j, 0 < lower j)
    (hsupp : ∀ j,
      Function.support
        (fun x : ℝ =>
          normalizedCC20ConcreteTestAlgebra.legacy.encode
            (basisTest j) x) ⊆ Set.Icc (lower j) (upper j))
    (hdet :
      (Matrix.of fun i j =>
        normalizedCC20TestSpace.mellinAt
          (basisTest j)
          (CC20YoshidaExpandedMomentNode.nodeValue rho i)).det ≠ 0) :
    ∃ g : normalizedCC20ConcreteTestAlgebra.Test,
      ConcreteYoshidaMomentData rho g := by
  rcases
    concreteExpandedMellinRealizes_of_positive_interval_supported_basis
      basisTest lower upper hcompact hlower hsupp hdet with
    ⟨g, hgcompact, hrealizes⟩
  exact
    ⟨g, concreteYoshidaMomentData_of_expanded_mellin_realizes
      hgcompact hrealizes⟩

theorem exists_concreteYoshidaMomentData_of_positive_interval_expanded_mellin_surjective
    {rho : ℂ}
    (hsurj : ∀ y : CC20YoshidaExpandedMomentNode → ℂ,
      ∃ g lower upper,
        0 < lower ∧
        normalizedCC20TestSpace.compactSupportSmooth g ∧
        Function.support
          (fun x : ℝ =>
            normalizedCC20ConcreteTestAlgebra.legacy.encode g x) ⊆
          Set.Icc lower upper ∧
        (∀ i : CC20YoshidaExpandedMomentNode,
          normalizedCC20TestSpace.mellinAt g
            (CC20YoshidaExpandedMomentNode.nodeValue rho i) = y i)) :
    ∃ g : normalizedCC20ConcreteTestAlgebra.Test,
      ConcreteYoshidaMomentData rho g := by
  rcases hsurj CC20YoshidaExpandedMomentNode.targetValue with
    ⟨g, _lower, _upper, _hlower, hcompact, _hsupp, hvalue⟩
  refine ⟨g, concreteYoshidaMomentData_of_expanded_mellin_realizes hcompact ?_⟩
  intro i
  simpa [CC20YoshidaExpandedMomentNode.ConcreteExpandedMellinRealizes]
    using hvalue i

theorem exists_concreteYoshidaMomentData_of_node_value_image_mellin_surjective
    {rho : ℂ}
    (hrho : RHDefinitionBridge.standard.sourceNontrivialZero rho)
    (hoff : rho.re ≠ 1 / 2)
    (hsurj :
      ∀ y :
          {z : ℂ //
            z ∈ CC20YoshidaExpandedMomentNode.expandedNodeValueFinset rho} →
            ℂ,
        ∃ g lower upper,
          0 < lower ∧
          normalizedCC20TestSpace.compactSupportSmooth g ∧
          Function.support
            (fun x : ℝ =>
              normalizedCC20ConcreteTestAlgebra.legacy.encode g x) ⊆
            Set.Icc lower upper ∧
          ∀ z :
              {z : ℂ //
                z ∈ CC20YoshidaExpandedMomentNode.expandedNodeValueFinset rho},
            normalizedCC20TestSpace.mellinAt g z.1 = y z) :
    ∃ g : normalizedCC20ConcreteTestAlgebra.Test,
      ConcreteYoshidaMomentData rho g := by
  rcases
    concreteExpandedMellinRealizes_of_node_value_image_mellin_surjective
        hrho hoff hsurj with
    ⟨g, _lower, _upper, _hlower, hcompact, _hsupp, hrealizes⟩
  exact
    ⟨g, concreteYoshidaMomentData_of_expanded_mellin_realizes
      hcompact hrealizes⟩

theorem concreteYoshidaMomentData_weilLocalSum_positive
    {rho : ℂ} {g : normalizedCC20ConcreteTestAlgebra.Test}
    (h : ConcreteYoshidaMomentData rho g) :
    0 <
      normalizedCC20TestSpace.weilLocalSum
        (normalizedCC20TestSpace.starConvolution g) :=
  normalizedCC20Yoshida_weilLocalSum_positive_of_half_mellin_values
    h.mellinAt_posHalf h.mellinAt_negHalf

theorem concreteYoshidaMomentData_halfDensityPoleSum_negative
    {rho : ℂ} {g : normalizedCC20ConcreteTestAlgebra.Test}
    (h : ConcreteYoshidaMomentData rho g) :
    (normalizedCC20ConcreteEvaluationData.mellinAt
        (normalizedCC20ConcreteTestAlgebra.convolutionSquare
          (normalizedCC20ConcreteTestAlgebra.convolutionSquare g))
        (Complex.I / 2)).re +
      (normalizedCC20ConcreteEvaluationData.mellinAt
        (normalizedCC20ConcreteTestAlgebra.convolutionSquare
          (normalizedCC20ConcreteTestAlgebra.convolutionSquare g))
        (-Complex.I / 2)).re < 0 := by
  have hplus :
      normalizedCC20ConcreteEvaluationData.mellinAt
          (normalizedCC20ConcreteTestAlgebra.convolutionSquare
            (normalizedCC20ConcreteTestAlgebra.convolutionSquare g))
          (Complex.I / 2) =
        (-4 : ℂ) := by
    rw [normalizedCC20ConcreteEvaluationData_mellinAt_double_convolutionSquare]
    have hpos := h.mellinAt_posHalf
    rw [normalizedCC20TestSpace_mellinAt_eq] at hpos
    rw [hpos]
    norm_num
  have hminus :
      normalizedCC20ConcreteEvaluationData.mellinAt
          (normalizedCC20ConcreteTestAlgebra.convolutionSquare
            (normalizedCC20ConcreteTestAlgebra.convolutionSquare g))
          (-Complex.I / 2) =
        (-4 : ℂ) := by
    rw [normalizedCC20ConcreteEvaluationData_mellinAt_double_convolutionSquare]
    have hneg := h.mellinAt_negHalf
    rw [normalizedCC20TestSpace_mellinAt_eq] at hneg
    rw [hneg]
    norm_num
  rw [hplus, hminus]
  norm_num

theorem concreteYoshidaMomentData_not_halfDensityPoleSum_nonnegative
    {rho : ℂ} {g : normalizedCC20ConcreteTestAlgebra.Test}
    (h : ConcreteYoshidaMomentData rho g) :
    ¬ 0 ≤
      (normalizedCC20ConcreteEvaluationData.mellinAt
          (normalizedCC20ConcreteTestAlgebra.convolutionSquare
            (normalizedCC20ConcreteTestAlgebra.convolutionSquare g))
          (Complex.I / 2)).re +
        (normalizedCC20ConcreteEvaluationData.mellinAt
          (normalizedCC20ConcreteTestAlgebra.convolutionSquare
            (normalizedCC20ConcreteTestAlgebra.convolutionSquare g))
          (-Complex.I / 2)).re :=
  not_le_of_gt (concreteYoshidaMomentData_halfDensityPoleSum_negative h)

theorem normalizedCC20_halfDensityPoleSum_sign_contradicts_moment_data
    (hSign : NormalizedCC20FiniteVanishingToHalfDensityPoleSumNonnegative)
    {rho : ℂ} {g : normalizedCC20ConcreteTestAlgebra.Test}
    (h : ConcreteYoshidaMomentData rho g) :
    False := by
  have hnonneg :=
    hSign g
      (by
        simpa [normalizedCC20TestSpace_compactSupportSmooth_eq] using
          h.compactSupportSmooth)
      (by
        intro p hp
        simpa [normalizedCC20TestSpace_mellinAt_eq] using
          h.vanishesOnF p hp)
  exact concreteYoshidaMomentData_not_halfDensityPoleSum_nonnegative h hnonneg

theorem exists_normalizedCC20_halfDensityPoleSum_counterexample :
    ∃ g : normalizedCC20ConcreteTestAlgebra.Test,
      HasCompactSupport
        (fun x : ℝ =>
          normalizedCC20ConcreteTestAlgebra.legacy.encode g x) ∧
      (∀ p : CriticalVanishingPoint,
        p ∈ cc20TripleFiniteVanishingSet →
          normalizedCC20ConcreteEvaluationData.mellinAt
            g (criticalVanishingPointValue p) = 0) ∧
      ¬ 0 ≤
        (normalizedCC20ConcreteEvaluationData.mellinAt
            (normalizedCC20ConcreteTestAlgebra.convolutionSquare
              (normalizedCC20ConcreteTestAlgebra.convolutionSquare g))
            (Complex.I / 2)).re +
          (normalizedCC20ConcreteEvaluationData.mellinAt
            (normalizedCC20ConcreteTestAlgebra.convolutionSquare
              (normalizedCC20ConcreteTestAlgebra.convolutionSquare g))
            (-Complex.I / 2)).re := by
  let rho : ℂ := 2
  have hdetect :
      ∀ coeff : NodeValueImage rho → ℂ,
        coeff ≠ 0 →
          ∃ p : PositiveIntervalCompactTest,
            (∑ z : NodeValueImage rho,
              imageMellinVector rho p z * coeff z) ≠ 0 :=
    image_weighted_mellin_detection_of_kernel_point_and_bump_separation
      (weightedMellinKernel_positive_point_separation_of_log_line_independence
        weighted_mellin_kernel_log_line_independence)
      (weightedMellinKernel_bump_separation_of_strict_phase_detection
        weightedMellinKernel_strict_phase_bump_detection)
  rcases
      positive_interval_node_value_image_mellin_surjective_of_weighted_detection
        hdetect
        (fun z : NodeValueImage rho => targetValueOnNodeValue rho z.1) with
    ⟨g, _lower, _upper, _hlower, hcompact, _hsupp, hvalue⟩
  have hzero :
      normalizedCC20TestSpace.mellinAt g
        (criticalVanishingPointValue CriticalVanishingPoint.zero) = 0 := by
    have hz := hvalue
      ⟨CC20YoshidaExpandedMomentNode.nodeValue rho
          CC20YoshidaExpandedMomentNode.zero,
        by simp [expandedNodeValueFinset]⟩
    simpa [rho, CC20YoshidaExpandedMomentNode.nodeValue, targetValueOnNodeValue,
      criticalVanishingPointValue] using hz
  have hhalf :
      normalizedCC20TestSpace.mellinAt g
        (criticalVanishingPointValue CriticalVanishingPoint.half) = 0 := by
    have hz := hvalue
      ⟨CC20YoshidaExpandedMomentNode.nodeValue rho
          CC20YoshidaExpandedMomentNode.half,
        by simp [expandedNodeValueFinset]⟩
    simpa [rho, CC20YoshidaExpandedMomentNode.nodeValue, targetValueOnNodeValue,
      criticalVanishingPointValue] using hz
  have hone :
      normalizedCC20TestSpace.mellinAt g
        (criticalVanishingPointValue CriticalVanishingPoint.one) = 0 := by
    have hz := hvalue
      ⟨CC20YoshidaExpandedMomentNode.nodeValue rho
          CC20YoshidaExpandedMomentNode.one,
        by simp [expandedNodeValueFinset]⟩
    simpa [rho, CC20YoshidaExpandedMomentNode.nodeValue, targetValueOnNodeValue,
      criticalVanishingPointValue] using hz
  have hdetectRho : normalizedCC20TestSpace.mellinAt g rho ≠ 0 := by
    have htwo := hvalue
      ⟨CC20YoshidaExpandedMomentNode.nodeValue rho
          CC20YoshidaExpandedMomentNode.targetRho,
        by simp [expandedNodeValueFinset]⟩
    have htwo_ne_zero : rho ≠ 0 := by
      dsimp [rho]
      norm_num
    have htwo_ne_half : rho ≠ (2 : ℂ)⁻¹ := by
      dsimp [rho]
      norm_num
    have htwo_ne_one : rho ≠ (1 : ℂ) := by
      dsimp [rho]
      norm_num
    have htwo_eq :
        normalizedCC20TestSpace.mellinAt g rho = (-1 : ℂ) := by
      simpa [rho, CC20YoshidaExpandedMomentNode.nodeValue,
        targetValueOnNodeValue, criticalVanishingPointValue, htwo_ne_zero,
        htwo_ne_half, htwo_ne_one] using htwo
    rw [htwo_eq]
    norm_num
  have hposHalf :
      normalizedCC20TestSpace.mellinAt g (Complex.I / 2) = (-1 : ℂ) := by
    have hz := hvalue
      ⟨CC20YoshidaExpandedMomentNode.nodeValue rho
          CC20YoshidaExpandedMomentNode.posHalfDensity,
        by simp [expandedNodeValueFinset]⟩
    have hI_ne_zero : Complex.I / 2 ≠ (0 : ℂ) := by
      intro h
      have him := congrArg Complex.im h
      norm_num [Complex.I_im] at him
    have hI_ne_half : Complex.I / 2 ≠ (2 : ℂ)⁻¹ := by
      intro h
      have hre := congrArg Complex.re h
      norm_num [Complex.I_re] at hre
    have hI_ne_one : Complex.I / 2 ≠ (1 : ℂ) := by
      intro h
      have hre := congrArg Complex.re h
      norm_num [Complex.I_re] at hre
    simpa [rho, CC20YoshidaExpandedMomentNode.nodeValue,
      targetValueOnNodeValue, criticalVanishingPointValue, hI_ne_zero,
      hI_ne_half, hI_ne_one] using hz
  have hnegHalf :
      normalizedCC20TestSpace.mellinAt g (-Complex.I / 2) = (-1 : ℂ) := by
    have hz := hvalue
      ⟨CC20YoshidaExpandedMomentNode.nodeValue rho
          CC20YoshidaExpandedMomentNode.negHalfDensity,
        by simp [expandedNodeValueFinset]⟩
    have hI_ne_zero : -Complex.I / 2 ≠ (0 : ℂ) := by
      intro h
      have him := congrArg Complex.im h
      norm_num [Complex.I_im] at him
    have hI_ne_half : -Complex.I / 2 ≠ (2 : ℂ)⁻¹ := by
      intro h
      have hre := congrArg Complex.re h
      norm_num [Complex.I_re] at hre
    have hI_ne_one : -Complex.I / 2 ≠ (1 : ℂ) := by
      intro h
      have hre := congrArg Complex.re h
      norm_num [Complex.I_re] at hre
    simpa [rho, CC20YoshidaExpandedMomentNode.nodeValue,
      targetValueOnNodeValue, criticalVanishingPointValue, hI_ne_zero,
      hI_ne_half, hI_ne_one] using hz
  let hmoment : ConcreteYoshidaMomentData rho g :=
    { compactSupportSmooth := hcompact
      vanishesOnF := by
        intro p _hp
        cases p
        · exact hzero
        · exact hhalf
        · exact hone
      detectsRho := hdetectRho
      mellinAt_posHalf := hposHalf
      mellinAt_negHalf := hnegHalf }
  refine ⟨g, ?_, ?_, ?_⟩
  · simpa [normalizedCC20TestSpace_compactSupportSmooth_eq] using hcompact
  · intro p hp
    have hv := hmoment.vanishesOnF p hp
    simpa [normalizedCC20TestSpace_mellinAt_eq] using hv
  · exact concreteYoshidaMomentData_not_halfDensityPoleSum_nonnegative hmoment

theorem not_normalizedCC20FiniteVanishingToHalfDensityPoleSumNonnegative :
    ¬ NormalizedCC20FiniteVanishingToHalfDensityPoleSumNonnegative := by
  intro hSign
  rcases exists_normalizedCC20_halfDensityPoleSum_counterexample with
    ⟨g, hcompact, hvanish, hnegative⟩
  exact hnegative (hSign g hcompact hvanish)

theorem not_normalizedCC20FiniteVanishingToPolePairingSign :
    ¬ NormalizedCC20FiniteVanishingToPolePairingSign := by
  intro hSign
  exact not_normalizedCC20FiniteVanishingToHalfDensityPoleSumNonnegative
    (by
      intro g hcompact hvanish
      simpa
        [normalizedCC20ConcreteEvaluationData.polePairing_eq_mellin_convolutionSquare_half_sum]
        using hSign g hcompact hvanish)

theorem normalizedCC20_finiteVanishingToPolePairingSign_of_weil_criterion
    (hcriterion :
      CC20FiniteVanishingWeilCriterion
        normalizedCC20TestSpace cc20TripleFiniteVanishingSet) :
    NormalizedCC20FiniteVanishingToPolePairingSign := by
  intro g hcompact hvanish
  have hnonpos :
      CC20WeilNonpositive normalizedCC20TestSpace g :=
    hcriterion g
      (by
        simpa [normalizedCC20TestSpace_compactSupportSmooth_eq] using
          hcompact)
      (by
        intro p hp
        simpa [normalizedCC20TestSpace_mellinAt_eq] using
          hvanish p hp)
  unfold CC20WeilNonpositive at hnonpos
  rw [normalizedCC20TestSpace_weilLocalSum_eq,
    normalizedCC20TestSpace_starConvolution_eq] at hnonpos
  exact neg_nonpos.mp hnonpos

theorem not_normalizedCC20FiniteVanishingWeilCriterion :
    ¬ CC20FiniteVanishingWeilCriterion
      normalizedCC20TestSpace cc20TripleFiniteVanishingSet := by
  intro hcriterion
  exact not_normalizedCC20FiniteVanishingToPolePairingSign
    (normalizedCC20_finiteVanishingToPolePairingSign_of_weil_criterion
      hcriterion)

theorem normalizedCC20YoshidaDetectorExists_of_moment_data
    (hmoment :
      ∀ {rho : ℂ},
        RHDefinitionBridge.standard.sourceNontrivialZero rho →
          rho.re ≠ 1 / 2 →
            ∃ g : normalizedCC20ConcreteTestAlgebra.Test,
              ConcreteYoshidaMomentData rho g) :
    CC20YoshidaDetectorExists
      normalizedCC20TestSpace
      cc20TripleFiniteVanishingSet := by
  intro rho hrho hoff
  rcases hmoment hrho hoff with ⟨g, hg⟩
  exact
    Nonempty.intro
      { test := g
        compactSupportSmooth := hg.compactSupportSmooth
        vanishesOnF := concreteYoshidaMomentData_vanishesOn_cc20Triple hg
        detectsRho := concreteYoshidaMomentData_detects_rho hg
        weilSumPositiveIfOffLine := fun _hrho _hoff =>
          concreteYoshidaMomentData_weilLocalSum_positive hg }

theorem normalizedCC20YoshidaDetectorExists_of_positive_interval_supported_basis_provider
    (hbasis :
      ∀ {rho : ℂ},
        RHDefinitionBridge.standard.sourceNontrivialZero rho →
          rho.re ≠ 1 / 2 →
            ∃ (basisTest :
                CC20YoshidaExpandedMomentNode →
                  normalizedCC20ConcreteTestAlgebra.Test)
              (lower upper : CC20YoshidaExpandedMomentNode → ℝ),
              (∀ j : CC20YoshidaExpandedMomentNode, 0 < lower j) ∧
              (∀ j : CC20YoshidaExpandedMomentNode,
                normalizedCC20TestSpace.compactSupportSmooth (basisTest j)) ∧
              (∀ j : CC20YoshidaExpandedMomentNode,
                Function.support
                  (fun x : ℝ =>
                    normalizedCC20ConcreteTestAlgebra.legacy.encode
                      (basisTest j) x) ⊆ Set.Icc (lower j) (upper j)) ∧
              (Matrix.of fun i j =>
                normalizedCC20TestSpace.mellinAt
                  (basisTest j)
                  (CC20YoshidaExpandedMomentNode.nodeValue rho i)).det ≠ 0) :
    CC20YoshidaDetectorExists
      normalizedCC20TestSpace
      cc20TripleFiniteVanishingSet := by
  refine normalizedCC20YoshidaDetectorExists_of_moment_data ?_
  intro rho hrho hoff
  rcases hbasis hrho hoff with
    ⟨basisTest, lower, upper, hlower, hcompact, hsupp, hdet⟩
  exact exists_concreteYoshidaMomentData_of_positive_interval_supported_basis
    basisTest lower upper hcompact hlower hsupp hdet

theorem normalizedCC20YoshidaDetectorExists_of_positive_interval_expanded_mellin_surjective
    (hsurj :
      ∀ {rho : ℂ},
        RHDefinitionBridge.standard.sourceNontrivialZero rho →
          rho.re ≠ 1 / 2 →
            ∀ y : CC20YoshidaExpandedMomentNode → ℂ,
              ∃ g lower upper,
                0 < lower ∧
                normalizedCC20TestSpace.compactSupportSmooth g ∧
                Function.support
                  (fun x : ℝ =>
                    normalizedCC20ConcreteTestAlgebra.legacy.encode g x) ⊆
                  Set.Icc lower upper ∧
                (∀ i : CC20YoshidaExpandedMomentNode,
                  normalizedCC20TestSpace.mellinAt g
                    (CC20YoshidaExpandedMomentNode.nodeValue rho i) = y i)) :
    CC20YoshidaDetectorExists
      normalizedCC20TestSpace
      cc20TripleFiniteVanishingSet := by
  refine normalizedCC20YoshidaDetectorExists_of_moment_data ?_
  intro rho hrho hoff
  exact
    exists_concreteYoshidaMomentData_of_positive_interval_expanded_mellin_surjective
      (hsurj hrho hoff)

theorem normalizedCC20YoshidaDetectorExists_of_node_value_image_mellin_surjective
    (hsurj :
      ∀ {rho : ℂ},
        RHDefinitionBridge.standard.sourceNontrivialZero rho →
          rho.re ≠ 1 / 2 →
            ∀ y :
                {z : ℂ //
                  z ∈
                    CC20YoshidaExpandedMomentNode.expandedNodeValueFinset rho} →
                  ℂ,
              ∃ g lower upper,
                0 < lower ∧
                normalizedCC20TestSpace.compactSupportSmooth g ∧
                Function.support
                  (fun x : ℝ =>
                    normalizedCC20ConcreteTestAlgebra.legacy.encode g x) ⊆
                  Set.Icc lower upper ∧
                (∀ z :
                    {z : ℂ //
                      z ∈
                        CC20YoshidaExpandedMomentNode.expandedNodeValueFinset
                          rho},
                  normalizedCC20TestSpace.mellinAt g z.1 = y z)) :
    CC20YoshidaDetectorExists
      normalizedCC20TestSpace
      cc20TripleFiniteVanishingSet := by
  refine normalizedCC20YoshidaDetectorExists_of_moment_data ?_
  intro rho hrho hoff
  exact
    exists_concreteYoshidaMomentData_of_node_value_image_mellin_surjective
      hrho hoff (hsurj hrho hoff)

theorem normalizedCC20YoshidaDetectorExists_of_node_value_image_weighted_detection
    (hdetect :
      ∀ {rho : ℂ},
        RHDefinitionBridge.standard.sourceNontrivialZero rho →
          rho.re ≠ 1 / 2 →
            ∀ coeff :
                CC20YoshidaExpandedMomentNode.NodeValueImage rho → ℂ,
              coeff ≠ 0 →
                ∃ p :
                  CC20YoshidaExpandedMomentNode.PositiveIntervalCompactTest,
                  (∑ z :
                    CC20YoshidaExpandedMomentNode.NodeValueImage rho,
                    CC20YoshidaExpandedMomentNode.imageMellinVector rho p z *
                      coeff z) ≠ 0) :
    CC20YoshidaDetectorExists
      normalizedCC20TestSpace
      cc20TripleFiniteVanishingSet := by
  refine normalizedCC20YoshidaDetectorExists_of_node_value_image_mellin_surjective ?_
  intro rho hrho hoff
  exact
    positive_interval_node_value_image_mellin_surjective_of_weighted_detection
      (hdetect hrho hoff)

theorem normalizedCC20YoshidaDetectorExists_of_node_value_image_kernel_separation
    (hpoint :
      ∀ {rho : ℂ},
        RHDefinitionBridge.standard.sourceNontrivialZero rho →
          rho.re ≠ 1 / 2 →
            WeightedMellinKernelPositivePointSeparation rho)
    (hbump :
      ∀ {rho : ℂ},
        RHDefinitionBridge.standard.sourceNontrivialZero rho →
          rho.re ≠ 1 / 2 →
            WeightedMellinKernelBumpSeparation rho) :
    CC20YoshidaDetectorExists
      normalizedCC20TestSpace
      cc20TripleFiniteVanishingSet := by
  refine normalizedCC20YoshidaDetectorExists_of_node_value_image_weighted_detection ?_
  intro rho hrho hoff
  exact
    image_weighted_mellin_detection_of_kernel_point_and_bump_separation
      (hpoint hrho hoff) (hbump hrho hoff)

theorem normalizedCC20YoshidaDetectorExists_of_node_value_image_log_independence_and_bump
    (hind :
      ∀ {rho : ℂ},
        RHDefinitionBridge.standard.sourceNontrivialZero rho →
          rho.re ≠ 1 / 2 →
            WeightedMellinKernelLogLineIndependence rho)
    (hbump :
      ∀ {rho : ℂ},
        RHDefinitionBridge.standard.sourceNontrivialZero rho →
          rho.re ≠ 1 / 2 →
            WeightedMellinKernelBumpSeparation rho) :
    CC20YoshidaDetectorExists
      normalizedCC20TestSpace
      cc20TripleFiniteVanishingSet := by
  refine normalizedCC20YoshidaDetectorExists_of_node_value_image_kernel_separation ?_ hbump
  intro rho hrho hoff
  exact weightedMellinKernel_positive_point_separation_of_log_line_independence
    (hind hrho hoff)

theorem normalizedCC20YoshidaDetectorExists_of_node_value_image_log_independence_and_phase_bump
    (hind :
      ∀ {rho : ℂ},
        RHDefinitionBridge.standard.sourceNontrivialZero rho →
          rho.re ≠ 1 / 2 →
            WeightedMellinKernelLogLineIndependence rho)
    (hphase :
      ∀ {rho : ℂ},
        RHDefinitionBridge.standard.sourceNontrivialZero rho →
          rho.re ≠ 1 / 2 →
            WeightedMellinKernelStrictPhaseBumpDetection rho) :
    CC20YoshidaDetectorExists
      normalizedCC20TestSpace
      cc20TripleFiniteVanishingSet := by
  refine
    normalizedCC20YoshidaDetectorExists_of_node_value_image_log_independence_and_bump
      hind ?_
  intro rho hrho hoff
  exact weightedMellinKernel_bump_separation_of_strict_phase_detection
    (hphase hrho hoff)

theorem normalizedCC20YoshidaDetectorExists_of_node_value_image_log_independence
    (hind :
      ∀ {rho : ℂ},
        RHDefinitionBridge.standard.sourceNontrivialZero rho →
          rho.re ≠ 1 / 2 →
            CC20YoshidaExpandedMomentNode.WeightedMellinKernelLogLineIndependence
              rho) :
    CC20YoshidaDetectorExists
      normalizedCC20TestSpace
      cc20TripleFiniteVanishingSet := by
  refine
    normalizedCC20YoshidaDetectorExists_of_node_value_image_log_independence_and_phase_bump
      hind ?_
  intro _rho _hrho _hoff
  exact
    CC20YoshidaExpandedMomentNode.weightedMellinKernel_strict_phase_bump_detection

theorem normalizedCC20ConcreteYoshidaMomentDataExists :
    ∀ {rho : ℂ},
      RHDefinitionBridge.standard.sourceNontrivialZero rho →
        rho.re ≠ 1 / 2 →
          ∃ g : normalizedCC20ConcreteTestAlgebra.Test,
            ConcreteYoshidaMomentData rho g := by
  intro rho hrho hoff
  have hdetect :
      ∀ coeff : NodeValueImage rho → ℂ,
        coeff ≠ 0 →
          ∃ p : PositiveIntervalCompactTest,
            (∑ z : NodeValueImage rho,
              imageMellinVector rho p z * coeff z) ≠ 0 :=
    image_weighted_mellin_detection_of_kernel_point_and_bump_separation
      (weightedMellinKernel_positive_point_separation_of_log_line_independence
        weighted_mellin_kernel_log_line_independence)
      (weightedMellinKernel_bump_separation_of_strict_phase_detection
        weightedMellinKernel_strict_phase_bump_detection)
  exact
    exists_concreteYoshidaMomentData_of_node_value_image_mellin_surjective
      hrho hoff
      (positive_interval_node_value_image_mellin_surjective_of_weighted_detection
        hdetect)

theorem normalizedCC20YoshidaDetectorExists :
    CC20YoshidaDetectorExists
      normalizedCC20TestSpace
      cc20TripleFiniteVanishingSet := by
  exact
    normalizedCC20YoshidaDetectorExists_of_node_value_image_log_independence
      (fun {_rho} _hrho _hoff =>
        CC20YoshidaExpandedMomentNode.weighted_mellin_kernel_log_line_independence)

/-- The current additive `starConvolution` cannot be the source convolution:
finite-window Mellin interpolation supplies a test with Mellin value one,
while the concrete operation doubles that value instead of squaring it. -/
theorem not_normalizedCC20MellinConvolutionLaw :
    ¬ NormalizedCC20MellinConvolutionLaw := by
  intro hLaw
  unfold NormalizedCC20MellinConvolutionLaw at hLaw
  let rho : ℂ := 0
  let z : NodeValueImage rho :=
    ⟨CC20YoshidaExpandedMomentNode.nodeValue rho
        CC20YoshidaExpandedMomentNode.zero,
      by simp [expandedNodeValueFinset]⟩
  rcases fixed_window_node_value_image_mellin_surjective
      (rho := rho) (a := (3 : ℝ) / 4) (b := (5 : ℝ) / 4)
      (by norm_num) (by norm_num) (by norm_num)
      (fun _ => (1 : ℂ)) with
    ⟨g, _hcompact, _hsupport, hvalue⟩
  have hg :
      normalizedCC20ConcreteEvaluationData.mellinAt g z.1 = 1 := by
    simpa [normalizedCC20TestSpace_mellinAt_eq] using hvalue z
  have hdouble :
      normalizedCC20ConcreteEvaluationData.mellinAt
          (normalizedCC20ConcreteTestAlgebra.convolutionStar g g) z.1 = 2 := by
    rw [← normalizedCC20ConcreteTestAlgebra.convolutionSquare_eq,
      normalizedCC20ConcreteEvaluationData_mellinAt_convolutionSquare, hg]
    norm_num
  have hsquare :
      normalizedCC20ConcreteEvaluationData.mellinAt
          (normalizedCC20ConcreteTestAlgebra.convolutionStar g g) z.1 = 1 := by
    rw [hLaw g g z.1, hg]
    norm_num
  have htwo_eq_one : (2 : ℂ) = 1 := hdouble.symm.trans hsquare
  norm_num at htwo_eq_one

end CC20YoshidaInterpolationNode
end Source
end ConnesWeilRH
