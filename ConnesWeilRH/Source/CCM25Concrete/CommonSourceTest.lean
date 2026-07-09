/-
Copyright (c) 2026 ConnesWeilRH contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ConnesWeilRH contributors
-/

import ConnesWeilRH.Source.CCM25Concrete.PrimePowerTest

/-!
# CCM25 concrete common source test

Goal 0A fixes the common CCM25 source test and its convolution square by
definition.  The first read-off theorem below unfolds that definition; it does
not project a square read-off field from an arbitrary source-test interface.
-/

namespace ConnesWeilRH
namespace Source
namespace CCM25Concrete
namespace CommonSourceTest

/-- The concrete common square `F_g = g * g` used by the CCM25 source layer. -/
def concreteSourceConvolutionSquare
    (W : WeilFormSymbols) (g : TestFunction) : TestFunction :=
  W.convolutionStar g g

/--
Goal 0A read-off for the concrete common square.

This theorem is definitional: the proof is `rfl`, so it does not consume
`PrimePowerTest.SourceTestEvaluationInterface.convolutionSquareReadOff`.
-/
theorem concrete_source_convolution_square_read_off
    (W : WeilFormSymbols) (g : TestFunction) :
    concreteSourceConvolutionSquare W g = W.convolutionStar g g :=
  rfl

/--
Goal 0B source visibility predicate attached to the concrete common square.

This is not an independent visibility relation.  It is the CCM25 route
visibility predicate evaluated at the concrete square from Goal 0A.
-/
def sourceAtomVisibleOfConcreteTest
    (W : WeilFormSymbols) (g : TestFunction) (n : ℕ) : Prop :=
  W.finitePrimeAtomVisible n (concreteSourceConvolutionSquare W g)

theorem route_visibility_iff_concrete_source_visibility
    (W : WeilFormSymbols) (g : TestFunction) (n : ℕ) :
    W.finitePrimeAtomVisible n (W.convolutionStar g g) ↔
      sourceAtomVisibleOfConcreteTest W g n := by
  rfl

theorem concrete_source_visibility_read_off
    (W : WeilFormSymbols) (g : TestFunction) (n : ℕ) :
    sourceAtomVisibleOfConcreteTest W g n =
      W.finitePrimeAtomVisible n (concreteSourceConvolutionSquare W g) :=
  rfl

/-- Concrete common source-test data for the fixed pair `(g,g)`. -/
structure ConcreteCommonSourceTest (W : WeilFormSymbols) where
  sourceTest : TestFunction

namespace ConcreteCommonSourceTest

/-- The concrete source square attached to a common source test. -/
def sourceConvolutionSquare
    {W : WeilFormSymbols} (h : ConcreteCommonSourceTest W) : TestFunction :=
  concreteSourceConvolutionSquare W h.sourceTest

theorem source_convolution_square_read_off
    {W : WeilFormSymbols} (h : ConcreteCommonSourceTest W) :
    h.sourceConvolutionSquare = W.convolutionStar h.sourceTest h.sourceTest :=
  rfl

/-- Source atom visibility attached to the concrete common square. -/
def sourceAtomVisible
    {W : WeilFormSymbols} (h : ConcreteCommonSourceTest W) (n : ℕ) : Prop :=
  sourceAtomVisibleOfConcreteTest W h.sourceTest n

theorem route_visibility_iff_source_visibility
    {W : WeilFormSymbols} (h : ConcreteCommonSourceTest W) (n : ℕ) :
    W.finitePrimeAtomVisible n
        (W.convolutionStar h.sourceTest h.sourceTest) ↔
      h.sourceAtomVisible n := by
  exact route_visibility_iff_concrete_source_visibility W h.sourceTest n

theorem source_atom_visible_read_off
    {W : WeilFormSymbols} (h : ConcreteCommonSourceTest W) (n : ℕ) :
    h.sourceAtomVisible n =
      sourceAtomVisibleOfConcreteTest W h.sourceTest n :=
  rfl

/--
The concrete common source test as the existing finite-prime evaluator
interface.

The square and visibility fields are filled from the concrete definitions in
this module.  Downstream Goal 2B code should consume this constructor instead
of accepting an unrelated source-test interface.
-/
def toSourceTestEvaluationInterface
    {W : WeilFormSymbols} (h : ConcreteCommonSourceTest W) :
    PrimePowerTest.SourceTestEvaluationInterface W h.sourceTest h.sourceTest where
  sourceLeftTest := h.sourceTest
  sourceRightTest := h.sourceTest
  sourceConvolutionSquare := h.sourceConvolutionSquare
  leftTestReadOff := rfl
  rightTestReadOff := rfl
  convolutionSquareReadOff := h.source_convolution_square_read_off

theorem evaluator_square_eq_concrete_square
    {W : WeilFormSymbols} (h : ConcreteCommonSourceTest W) :
    (h.toSourceTestEvaluationInterface).sourceConvolutionSquare =
      h.sourceConvolutionSquare :=
  rfl

end ConcreteCommonSourceTest

/-- Constructor for the concrete common source test at a named test `g`. -/
def concreteCommonSourceTest
    (W : WeilFormSymbols) (g : TestFunction) : ConcreteCommonSourceTest W where
  sourceTest := g

theorem concrete_common_source_test_source_read_off
    (W : WeilFormSymbols) (g : TestFunction) :
    (concreteCommonSourceTest W g).sourceTest = g :=
  rfl

/-- The concrete source-test evaluator for the fixed pair `(g,g)`. -/
def concreteSourceTestEvaluationInterface
    (W : WeilFormSymbols) (g : TestFunction) :
    PrimePowerTest.SourceTestEvaluationInterface W g g :=
  (concreteCommonSourceTest W g).toSourceTestEvaluationInterface

theorem concrete_source_test_evaluator_square_read_off
    (W : WeilFormSymbols) (g : TestFunction) :
    (concreteSourceTestEvaluationInterface W g).sourceConvolutionSquare =
      concreteSourceConvolutionSquare W g :=
  rfl

theorem concrete_route_visibility_iff_source_visibility
    (W : WeilFormSymbols) (g : TestFunction) (n : ℕ) :
    W.finitePrimeAtomVisible n (W.convolutionStar g g) ↔
      (concreteSourceTestEvaluationInterface W g).sourceAtomVisible n := by
  exact PrimePowerTest.route_visibility_iff_source_visibility
    (concreteSourceTestEvaluationInterface W g) n

theorem concrete_evaluator_visibility_uses_concrete_predicate
    (W : WeilFormSymbols) (g : TestFunction) (n : ℕ) :
    (concreteSourceTestEvaluationInterface W g).sourceAtomVisible n =
      sourceAtomVisibleOfConcreteTest W g n :=
  rfl

end CommonSourceTest
end CCM25Concrete
end Source
end ConnesWeilRH
