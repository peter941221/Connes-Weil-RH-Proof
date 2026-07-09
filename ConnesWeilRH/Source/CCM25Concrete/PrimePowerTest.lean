/-
Copyright (c) 2026 ConnesWeilRH contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ConnesWeilRH contributors
-/

import ConnesWeilRH.Basic

/-!
# CCM25 common source test and finite-prime visibility

This module packages the common source test object used by the CCM25
finite-prime layer.  The route-level `TestFunction` is now Mathlib's Schwartz
space on `ℝ` with complex values; this file prevents later finite-prime
visibility and prime-power evaluation data from silently using different
convolution-square objects.
-/

namespace ConnesWeilRH
namespace Source
namespace CCM25Concrete
namespace PrimePowerTest

structure SourceTestEvaluationInterface
    (W : WeilFormSymbols) (f g : TestFunction) where
  sourceLeftTest : TestFunction := f
  sourceRightTest : TestFunction := g
  sourceConvolutionSquare : TestFunction := W.convolutionStar f g
  leftTestReadOff : sourceLeftTest = f
  rightTestReadOff : sourceRightTest = g
  convolutionSquareReadOff :
    sourceConvolutionSquare = W.convolutionStar f g

theorem source_left_test_read_off
    {W : WeilFormSymbols} {f g : TestFunction}
    (h : SourceTestEvaluationInterface W f g) :
    h.sourceLeftTest = f :=
  h.leftTestReadOff

theorem source_right_test_read_off
    {W : WeilFormSymbols} {f g : TestFunction}
    (h : SourceTestEvaluationInterface W f g) :
    h.sourceRightTest = g :=
  h.rightTestReadOff

theorem source_convolution_square_read_off
    {W : WeilFormSymbols} {f g : TestFunction}
    (h : SourceTestEvaluationInterface W f g) :
    h.sourceConvolutionSquare = W.convolutionStar f g :=
  h.convolutionSquareReadOff

def SourceTestEvaluationInterface.sourceAtomVisible
    {W : WeilFormSymbols} {f g : TestFunction}
    (h : SourceTestEvaluationInterface W f g) (n : ℕ) : Prop :=
  W.finitePrimeAtomVisible n h.sourceConvolutionSquare

theorem source_atom_visible_read_off
    {W : WeilFormSymbols} {f g : TestFunction}
    (h : SourceTestEvaluationInterface W f g) (n : ℕ) :
    h.sourceAtomVisible n =
      W.finitePrimeAtomVisible n h.sourceConvolutionSquare :=
  rfl

theorem route_visibility_iff_source_visibility
    {W : WeilFormSymbols} {f g : TestFunction}
    (h : SourceTestEvaluationInterface W f g) (n : ℕ) :
    W.finitePrimeAtomVisible n (W.convolutionStar f g) ↔
      h.sourceAtomVisible n := by
  rw [← h.convolutionSquareReadOff]
  rfl

end PrimePowerTest
end CCM25Concrete
end Source
end ConnesWeilRH
