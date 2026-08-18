/-
Copyright (c) 2026 ConnesWeilRH contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ConnesWeilRH.Dev.C1XiCenterTwoGammaComplexSplit

/-!
# C1XiCenterTwoGammaComplexSplitReduction - a conditional real-owner reduction

The finite Gamma_R prefix is additive over the real and imaginary components
of a complex test.  This file packages the resulting reduction to a
real-valued sign producer while keeping component prime-free support explicit.
The support premise is intentional: narrow support of the complex square does
not imply narrow support of both component squares.
-/

namespace ConnesWeilRH
namespace Source
namespace C1XiCenterTwoGammaComplexSplitReduction

open C1XiCenterTwoGammaConstrainedPrefix
open C1XiCenterTwoGammaComplexSplit
open C1LaneRD3Root
open CC20YoshidaConvolution
open CC20YoshidaConvolution.CompactLogTest
open CCM25Concrete.CompactLogConvolution

noncomputable section

/-- The test takes real values pointwise. -/
def realValuedTest (g : CompactLogTest) : Prop :=
  ∀ x : Real, (g.test x).im = 0

@[simp] theorem realPartTest_realValued (g : CompactLogTest) :
    realValuedTest (realPartTest g) := by
  intro x
  simp

@[simp] theorem imagPartTest_realValued (g : CompactLogTest) :
    realValuedTest (imagPartTest g) := by
  intro x
  simp

theorem realPartTest_support_subset
    (g : CompactLogTest) {s : Set Real}
    (hsupport : Function.support g.test ⊆ s) :
    Function.support (realPartTest g).test ⊆ s := by
  intro x hx
  apply hsupport
  intro hzero
  apply hx
  simp [hzero]

theorem imagPartTest_support_subset
    (g : CompactLogTest) {s : Set Real}
    (hsupport : Function.support g.test ⊆ s) :
    Function.support (imagPartTest g).test ⊆ s := by
  intro x hx
  apply hsupport
  intro hzero
  apply hx
  simp [hzero]

/-- Both component squares are prime-free.  This is a separate premise rather
than a consequence of prime-free support for the original complex square. -/
def componentPrimeFreeSquare (g : CompactLogTest) : Prop :=
  laneRPrimeFreeSquare (realPartTest g) ∧
    laneRPrimeFreeSquare (imagPartTest g)

theorem primeFreeSquare_of_support_Icc
    (g : CompactLogTest) {w : Real}
    (hsupport : Function.support g.test ⊆ Set.Icc (-w) w)
    (hw : w < (3 / 10 : Real)) :
    laneRPrimeFreeSquare g := by
  unfold laneRPrimeFreeSquare
  have hnarrow : Function.support g.test ⊆
      Set.Ioo (-(3 / 5 : Real) / 2) ((3 / 5 : Real) / 2) := by
    intro x hx
    rcases hsupport hx with ⟨hlower, hupper⟩
    constructor <;> nlinarith
  have hsquare := convolutionSquare_support_subset_symmetric
    g (a := (3 / 5 : Real)) hnarrow
  have hlog : (3 / 5 : Real) < Real.log 2 := by
    nlinarith [Real.log_two_gt_d9]
  intro x hx
  rcases hsquare hx with ⟨hlower, hupper⟩
  constructor <;> linarith

theorem componentPrimeFreeSquare_of_support_Icc
    (g : CompactLogTest) {w : Real}
    (hsupport : Function.support g.test ⊆ Set.Icc (-w) w)
    (hw : w < (3 / 10 : Real)) :
    componentPrimeFreeSquare g := by
  constructor
  · apply primeFreeSquare_of_support_Icc (realPartTest g) (w := w)
    · exact realPartTest_support_subset g hsupport
    · exact hw
  · apply primeFreeSquare_of_support_Icc (imagPartTest g) (w := w)
    · exact imagPartTest_support_subset g hsupport
    · exact hw

theorem componentPrimeFreeSquare_tripleVanishingRoot_of_Icc
    (h : CompactLogTest) {w : Real}
    (hsupport : Function.support h.test ⊆ Set.Icc (-w) w)
    (hw : w < (3 / 10 : Real)) :
    componentPrimeFreeSquare (tripleVanishingRoot h) := by
  apply componentPrimeFreeSquare_of_support_Icc
    (tripleVanishingRoot h) (w := w)
  · exact tripleVanishingRoot_support_subset_Icc h hsupport
  · exact hw

/-- The finite-prefix sign producer restricted to real-valued tests. -/
def realValuedLaneRPrefixSignTarget : Prop :=
  ∀ g : CompactLogTest,
    realValuedTest g →
      laneRConstrainedPrimeFree g →
        laneRFinitePrefixQuadraticValue g ≤ 0

/-- A real-valued sign producer yields the complex prefix sign whenever both
component squares retain the prime-free support needed by the producer. -/
theorem laneRFinitePrefixQuadraticValue_nonpos_of_realValued_target
    (hreal : realValuedLaneRPrefixSignTarget)
    {g : CompactLogTest}
    (hvanishes : laneRTripleVanishing g)
    (hcomponents : componentPrimeFreeSquare g) :
    laneRFinitePrefixQuadraticValue g ≤ 0 := by
  have hrealVanishing := realPartTest_satisfies_laneRTripleVanishing hvanishes
  have himagVanishing := imagPartTest_satisfies_laneRTripleVanishing hvanishes
  have hrealBound := hreal (realPartTest g) (realPartTest_realValued g)
    ⟨hrealVanishing, hcomponents.1⟩
  have himagBound := hreal (imagPartTest g) (imagPartTest_realValued g)
    ⟨himagVanishing, hcomponents.2⟩
  rw [laneRFinitePrefixQuadraticValue_split g]
  linarith

theorem laneRFinitePrefixQuadraticValue_nonpos_tripleVanishingRoot_of_realValued_target
    (hreal : realValuedLaneRPrefixSignTarget)
    (h : CompactLogTest) {w : Real}
    (hsupport : Function.support h.test ⊆ Set.Icc (-w) w)
    (hw : w < (3 / 10 : Real)) :
    laneRFinitePrefixQuadraticValue (tripleVanishingRoot h) ≤ 0 := by
  apply laneRFinitePrefixQuadraticValue_nonpos_of_realValued_target hreal
  · exact tripleVanishingRoot_satisfies_laneRTripleVanishing h
  · exact componentPrimeFreeSquare_tripleVanishingRoot_of_Icc h hsupport hw

end
end C1XiCenterTwoGammaComplexSplitReduction
end Source
end ConnesWeilRH
