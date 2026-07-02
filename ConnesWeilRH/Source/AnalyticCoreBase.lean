/-
Copyright (c) 2026 ConnesWeilRH contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ConnesWeilRH contributors
-/

import ConnesWeilRH.Basic
import ConnesWeilRH.Source.CC20Concrete.TraceScale
import Mathlib.NumberTheory.ArithmeticFunction.VonMangoldt

/-!
# Shared source analytic base

This module contains the common source-facing carriers used by the CCM24,
CCM25, and CC20 source-model discharges.  Heavier theorem rows and peeling
records live in downstream modules so the support-window interface can be
refined without forcing every source object into one file.
-/

namespace ConnesWeilRH
namespace Source
namespace AnalyticCore

open scoped ArithmeticFunction

/-- Bridge between the new source test object and the legacy `TestFunction`. -/
structure LegacyTestEquiv (Test : Type) where
  encode : Test → TestFunction
  decode : TestFunction → Test
  encode_decode : ∀ F : TestFunction, encode (decode F) = F
  decode_encode : ∀ f : Test, decode (encode f) = f

namespace LegacyTestEquiv

@[simp]
theorem encode_decode_apply {Test : Type} (e : LegacyTestEquiv Test)
    (F : TestFunction) :
    e.encode (e.decode F) = F :=
  e.encode_decode F

@[simp]
theorem decode_encode_apply {Test : Type} (e : LegacyTestEquiv Test)
    (f : Test) :
    e.decode (e.encode f) = f :=
  e.decode_encode f

end LegacyTestEquiv

/--
The shared source test algebra.

`convolutionStar` is the CCM25 half-density square product.  The same object is
also the test whose support is controlled by CCM24 and whose trace amplitude is
read by CC20.
-/
structure SourceTestAlgebra where
  Test : Type
  legacy : LegacyTestEquiv Test
  convolutionStar : Test → Test → Test
  involution : Test → Test
  convolutionSquare : Test → Test := fun g => convolutionStar g g
  convolutionSquare_eq : ∀ g : Test, convolutionSquare g = convolutionStar g g

namespace SourceTestAlgebra

def legacyConvolutionStar (A : SourceTestAlgebra) :
    TestFunction → TestFunction → TestFunction :=
  fun f g => A.legacy.encode
    (A.convolutionStar (A.legacy.decode f) (A.legacy.decode g))

theorem legacy_convolution_star_square
    (A : SourceTestAlgebra) (g : A.Test) :
    A.legacyConvolutionStar (A.legacy.encode g) (A.legacy.encode g) =
      A.legacy.encode (A.convolutionSquare g) := by
  simp [legacyConvolutionStar, A.convolutionSquare_eq g]

end SourceTestAlgebra

/-- Source evaluation and Mellin/pole evaluations for the shared test object. -/
structure SourceEvaluationData (A : SourceTestAlgebra) where
  valueAt : A.Test → ℝ → ℝ
  mellinAt : A.Test → ℂ → ℂ
  poleFunctional : A.Test → ℝ
  polePairing : A.Test → ℝ
  poleFunctional_eq_mellin :
    ∀ F : A.Test,
      poleFunctional F =
        (mellinAt F (Complex.I / 2)).re +
          (mellinAt F (-Complex.I / 2)).re
  polePairing_eq_functional_square :
    ∀ g : A.Test,
      polePairing g = poleFunctional (A.convolutionSquare g)

/-- CCM24-facing support/window data for the shared source tests. -/
structure SourceSupportWindowData (A : SourceTestAlgebra) where
  PlaceSet : Type
  Window : Type
  sourcePlaceSet : PlaceSet
  sourceSupportWindow : Window
  sourceTest : A.Test
  canonicalHilbertModel : PlaceSet → Prop
  scalingActionImplemented : PlaceSet → Prop
  fourierGradingCompatible : PlaceSet → Prop
  supportInWindow : A.Test → Window → Prop
  fourierSupportInWindow : A.Test → Window → Prop
  supportTransported : A.Test → Window → Prop
  convolutionSupportTransported : A.Test → Window → Prop
  windowContainedInLambda : Window → ℝ → Prop
  lambdaCompatible : Window → ℝ → Prop
  boundedComparisonMap : PlaceSet → Prop
  boundedComparisonInverse : PlaceSet → Prop

end AnalyticCore
end Source
end ConnesWeilRH
