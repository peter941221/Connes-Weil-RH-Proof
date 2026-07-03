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

/-- Point/window incidence coordinate for the CCM24 source-window carrier. -/
structure SourceWindowMembershipCoordinate (SupportPoint Window : Type) where
  pointCoordinate : SupportPoint → Window → ℝ
  lowerEndpoint : Window → ℝ
  upperEndpoint : Window → ℝ

namespace SourceWindowMembershipCoordinate

/-- The lower closed-window incidence relation behind the base carrier. -/
def pointInClosedWindow
    {SupportPoint Window : Type}
    (C : SourceWindowMembershipCoordinate SupportPoint Window)
    (x : SupportPoint) (I : Window) : Prop :=
  C.lowerEndpoint I ≤ C.pointCoordinate x I ∧
    C.pointCoordinate x I ≤ C.upperEndpoint I

def pointInBaseWindow
    {SupportPoint Window : Type}
    (C : SourceWindowMembershipCoordinate SupportPoint Window)
    (x : SupportPoint) (I : Window) : Prop :=
  C.pointInClosedWindow x I

theorem pointInBaseWindow_iff
    {SupportPoint Window : Type}
    (C : SourceWindowMembershipCoordinate SupportPoint Window)
    (x : SupportPoint) (I : Window) :
    C.pointInBaseWindow x I ↔
      C.lowerEndpoint I ≤ C.pointCoordinate x I ∧
        C.pointCoordinate x I ≤ C.upperEndpoint I :=
  Iff.rfl

def baseCarrier
    {SupportPoint Window : Type}
    (C : SourceWindowMembershipCoordinate SupportPoint Window)
    (I : Window) : Set SupportPoint :=
  {x | C.pointInBaseWindow x I}

theorem mem_baseCarrier_iff
    {SupportPoint Window : Type}
    (C : SourceWindowMembershipCoordinate SupportPoint Window)
    (x : SupportPoint) (I : Window) :
    x ∈ C.baseCarrier I ↔ C.pointInBaseWindow x I :=
  Iff.rfl

end SourceWindowMembershipCoordinate

/-- Logarithmic scale coordinate for CCM24 source support points. -/
structure SourceSupportLogScaleCoordinate (SupportPoint : Type) where
  logScale : SupportPoint → ℝ

namespace SourceSupportLogScaleCoordinate

noncomputable def scale
    {SupportPoint : Type}
    (C : SourceSupportLogScaleCoordinate SupportPoint)
    (x : SupportPoint) : ℝ :=
  Real.exp (C.logScale x)

end SourceSupportLogScaleCoordinate

/-- CCM24 source-window coordinate object for support points. -/
structure SourceWindowCoordinate (SupportPoint Window : Type) where
  windowMembershipCoordinate :
    SourceWindowMembershipCoordinate SupportPoint Window
  supportLogScaleCoordinate :
    SourceSupportLogScaleCoordinate SupportPoint

namespace SourceWindowCoordinate

def baseCarrier
    {SupportPoint Window : Type}
    (C : SourceWindowCoordinate SupportPoint Window)
    (I : Window) : Set SupportPoint :=
  C.windowMembershipCoordinate.baseCarrier I

noncomputable def scale
    {SupportPoint Window : Type}
    (C : SourceWindowCoordinate SupportPoint Window)
    (x : SupportPoint) : ℝ :=
  C.supportLogScaleCoordinate.scale x

end SourceWindowCoordinate

/-- CCM24-facing support/window data for the shared source tests. -/
structure SourceSupportWindowData (A : SourceTestAlgebra) where
  PlaceSet : Type
  Window : Type
  sourcePlaceSet : PlaceSet
  sourceSupportWindow : Window
  sourceTest : A.Test
  SupportPoint : Type
  supportCarrier : A.Test → Set SupportPoint
  fourierSupportCarrier : A.Test → Set SupportPoint
  sourceWindowCoordinate : SourceWindowCoordinate SupportPoint Window
  canonicalHilbertModel : PlaceSet → Prop
  scalingActionImplemented : PlaceSet → Prop
  fourierGradingCompatible : PlaceSet → Prop
  boundedComparisonMap : PlaceSet → Prop
  boundedComparisonInverse : PlaceSet → Prop

namespace SourceSupportWindowData

def windowBaseCarrier
    {A : SourceTestAlgebra} (S : SourceSupportWindowData A)
    (I : S.Window) : Set S.SupportPoint :=
  S.sourceWindowCoordinate.baseCarrier I

noncomputable def supportScale
    {A : SourceTestAlgebra} (S : SourceSupportWindowData A)
    (x : S.SupportPoint) : ℝ :=
  S.sourceWindowCoordinate.scale x

def windowCarrier
    {A : SourceTestAlgebra} (S : SourceSupportWindowData A)
    (I : S.Window) : Set S.SupportPoint :=
  {x | x ∈ S.windowBaseCarrier I ∧ S.supportScale x = 1}

def supportInWindow
    {A : SourceTestAlgebra} (S : SourceSupportWindowData A)
    (f : A.Test) (I : S.Window) : Prop :=
  S.supportCarrier f ⊆ S.windowCarrier I

def fourierSupportInWindow
    {A : SourceTestAlgebra} (S : SourceSupportWindowData A)
    (f : A.Test) (I : S.Window) : Prop :=
  S.fourierSupportCarrier f ⊆ S.windowCarrier I

def supportTransported
    {A : SourceTestAlgebra} (S : SourceSupportWindowData A)
    (f : A.Test) (I : S.Window) : Prop :=
  S.supportInWindow f I

def convolutionSupportTransported
    {A : SourceTestAlgebra} (S : SourceSupportWindowData A)
    (f : A.Test) (I : S.Window) : Prop :=
  S.fourierSupportInWindow f I

def pointInLambdaCutoff
    {A : SourceTestAlgebra} (S : SourceSupportWindowData A)
    (x : S.SupportPoint) (lambda : ℝ) : Prop :=
  lambda⁻¹ ≤ S.supportScale x ∧ S.supportScale x ≤ lambda

def lambdaCarrier
    {A : SourceTestAlgebra} (S : SourceSupportWindowData A)
    (lambda : ℝ) : Set S.SupportPoint :=
  {x | S.pointInLambdaCutoff x lambda}

def windowContainedInLambda
    {A : SourceTestAlgebra} (S : SourceSupportWindowData A)
    (I : S.Window) (lambda : ℝ) : Prop :=
  S.windowCarrier I ⊆ S.lambdaCarrier lambda

def lambdaCompatible
    {A : SourceTestAlgebra} (S : SourceSupportWindowData A)
    (I : S.Window) (lambda : ℝ) : Prop :=
  S.windowContainedInLambda I lambda

theorem supportTransported_of_supportInWindow
    {A : SourceTestAlgebra} {S : SourceSupportWindowData A}
    {f : A.Test} {I : S.Window} :
    S.supportInWindow f I → S.supportTransported f I := by
  intro hSupport
  exact hSupport

theorem convolutionSupportTransported_of_fourierSupportInWindow
    {A : SourceTestAlgebra} {S : SourceSupportWindowData A}
    {f : A.Test} {I : S.Window} :
    S.fourierSupportInWindow f I →
      S.convolutionSupportTransported f I := by
  intro hFourier
  exact hFourier

theorem lambdaCompatible_of_windowContainedInLambda
    {A : SourceTestAlgebra} {S : SourceSupportWindowData A}
    {I : S.Window} {lambda : ℝ} :
    S.windowContainedInLambda I lambda → S.lambdaCompatible I lambda := by
  intro hWindow
  exact hWindow

theorem windowPoint_supportScale_eq_one
    {A : SourceTestAlgebra} {S : SourceSupportWindowData A}
    {I : S.Window}
    {x : S.SupportPoint}
    (hx : x ∈ S.windowCarrier I) :
    S.supportScale x = 1 := by
  exact hx.2

theorem windowPoint_supportScale_lowerBound
    {A : SourceTestAlgebra} {S : SourceSupportWindowData A}
    {I : S.Window} {lambda : ℝ}
    (hlambda : 1 < lambda) {x : S.SupportPoint}
    (hx : x ∈ S.windowCarrier I) :
    lambda⁻¹ ≤ S.supportScale x := by
  rw [windowPoint_supportScale_eq_one hx]
  exact inv_le_one_of_one_le₀ hlambda.le

theorem windowPoint_supportScale_upperBound
    {A : SourceTestAlgebra} {S : SourceSupportWindowData A}
    {I : S.Window} {lambda : ℝ}
    (hlambda : 1 < lambda) {x : S.SupportPoint}
    (hx : x ∈ S.windowCarrier I) :
    S.supportScale x ≤ lambda := by
  rw [windowPoint_supportScale_eq_one hx]
  exact hlambda.le

theorem windowPoint_mem_lambdaCutoff
    {A : SourceTestAlgebra} {S : SourceSupportWindowData A}
    {I : S.Window} {lambda : ℝ}
    (hlambda : 1 < lambda) {x : S.SupportPoint}
    (hx : x ∈ S.windowCarrier I) :
    S.pointInLambdaCutoff x lambda := by
  exact
    ⟨windowPoint_supportScale_lowerBound hlambda hx,
      windowPoint_supportScale_upperBound hlambda hx⟩

theorem windowCarrier_subset_lambdaCarrier
    {A : SourceTestAlgebra} {S : SourceSupportWindowData A}
    {I : S.Window} {lambda : ℝ}
    (hlambda : 1 < lambda) :
    S.windowCarrier I ⊆ S.lambdaCarrier lambda := by
  intro x hx
  exact windowPoint_mem_lambdaCutoff hlambda hx

theorem windowContainedInLambda_of_one_lt
    {A : SourceTestAlgebra} {S : SourceSupportWindowData A}
    {I : S.Window} {lambda : ℝ}
    (hlambda : 1 < lambda) :
    S.windowContainedInLambda I lambda :=
  windowCarrier_subset_lambdaCarrier hlambda

end SourceSupportWindowData

end AnalyticCore
end Source
end ConnesWeilRH
