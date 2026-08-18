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

/-- Both component squares are prime-free.  This is a separate premise rather
than a consequence of prime-free support for the original complex square. -/
def componentPrimeFreeSquare (g : CompactLogTest) : Prop :=
  laneRPrimeFreeSquare (realPartTest g) ∧
    laneRPrimeFreeSquare (imagPartTest g)

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

end
end C1XiCenterTwoGammaComplexSplitReduction
end Source
end ConnesWeilRH
