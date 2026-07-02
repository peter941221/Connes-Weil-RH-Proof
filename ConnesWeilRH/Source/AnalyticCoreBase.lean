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
  SupportPoint : Type
  supportCarrier : A.Test → Set SupportPoint
  fourierSupportCarrier : A.Test → Set SupportPoint
  windowCarrier : Window → Set SupportPoint
  supportScale : SupportPoint → ℝ
  canonicalHilbertModel : PlaceSet → Prop
  scalingActionImplemented : PlaceSet → Prop
  fourierGradingCompatible : PlaceSet → Prop
  boundedComparisonMap : PlaceSet → Prop
  boundedComparisonInverse : PlaceSet → Prop

namespace SourceSupportWindowData

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

structure SourceSupportWindowContainmentData
    {A : SourceTestAlgebra} (S : SourceSupportWindowData A)
    (f : A.Test) (I : S.Window)
    (supportSet : Type) (supportMembership : supportSet → Prop) where
  supportWindowSet : Type
  supportWindowMembership : supportWindowSet → Prop
  supportToWindow : supportSet → supportWindowSet
  supportImage_mem_window :
    ∀ point : supportSet,
      supportMembership point →
        supportWindowMembership (supportToWindow point)
  carrierToSupport :
    ∀ x : S.SupportPoint,
      x ∈ S.supportCarrier f → supportSet
  carrierToSupport_mem :
    ∀ x : S.SupportPoint,
      ∀ hx : x ∈ S.supportCarrier f,
        supportMembership (carrierToSupport x hx)
  windowPoint : supportWindowSet → S.SupportPoint
  windowPoint_mem_window :
    ∀ point : supportWindowSet,
      supportWindowMembership point →
        windowPoint point ∈ S.windowCarrier I
  supportToWindow_realizes_carrier :
    ∀ x : S.SupportPoint,
      ∀ hx : x ∈ S.supportCarrier f,
        windowPoint
          (supportToWindow (carrierToSupport x hx)) = x

namespace SourceSupportWindowContainmentData

theorem supportCarrier_subset_windowCarrier
    {A : SourceTestAlgebra} {S : SourceSupportWindowData A}
    {f : A.Test} {I : S.Window}
    {supportSet : Type} {supportMembership : supportSet → Prop}
    (D :
      SourceSupportWindowContainmentData
        S f I supportSet supportMembership) :
    S.supportCarrier f ⊆ S.windowCarrier I := by
  intro x hx
  rw [← D.supportToWindow_realizes_carrier x hx]
  exact
    D.windowPoint_mem_window
      (D.supportToWindow (D.carrierToSupport x hx))
      (D.supportImage_mem_window
        (D.carrierToSupport x hx)
        (D.carrierToSupport_mem x hx))

theorem supportWindowMembershipRealizesSupportInWindow
    {A : SourceTestAlgebra} {S : SourceSupportWindowData A}
    {f : A.Test} {I : S.Window}
    {supportSet : Type} {supportMembership : supportSet → Prop}
    (D :
      SourceSupportWindowContainmentData
        S f I supportSet supportMembership) :
    ∀ point : supportSet,
      supportMembership point →
        D.supportWindowMembership (D.supportToWindow point) →
          S.supportInWindow f I := by
  intro _point _hSupport _hWindow
  exact D.supportCarrier_subset_windowCarrier

theorem supportSetContainedInWindow
    {A : SourceTestAlgebra} {S : SourceSupportWindowData A}
    {f : A.Test} {I : S.Window}
    {supportSet : Type} {supportMembership : supportSet → Prop}
    (D :
      SourceSupportWindowContainmentData
        S f I supportSet supportMembership) :
    ∀ point : supportSet,
      supportMembership point → S.supportInWindow f I := by
  intro point hpoint
  exact
    D.supportWindowMembershipRealizesSupportInWindow
      point hpoint (D.supportImage_mem_window point hpoint)

end SourceSupportWindowContainmentData

structure SourceLambdaWindowContainmentData
    {A : SourceTestAlgebra} (S : SourceSupportWindowData A)
    (I : S.Window) where
  windowPoint_mem_lambdaCutoff :
    ∀ lambda : ℝ,
      1 < lambda →
        ∀ x : S.SupportPoint,
          x ∈ S.windowCarrier I → S.pointInLambdaCutoff x lambda

namespace SourceLambdaWindowContainmentData

theorem windowCarrier_subset_lambdaCarrier
    {A : SourceTestAlgebra} {S : SourceSupportWindowData A}
    {I : S.Window}
    (D : SourceLambdaWindowContainmentData S I) :
    ∀ lambda : ℝ,
      1 < lambda → S.windowCarrier I ⊆ S.lambdaCarrier lambda := by
  intro lambda hlambda x hx
  exact D.windowPoint_mem_lambdaCutoff lambda hlambda x hx

theorem windowContainedInLambda
    {A : SourceTestAlgebra} {S : SourceSupportWindowData A}
    {I : S.Window}
    (D : SourceLambdaWindowContainmentData S I) :
    ∀ lambda : ℝ,
      1 < lambda → S.windowContainedInLambda I lambda := by
  intro lambda hlambda
  exact D.windowCarrier_subset_lambdaCarrier lambda hlambda

end SourceLambdaWindowContainmentData

end SourceSupportWindowData

end AnalyticCore
end Source
end ConnesWeilRH
