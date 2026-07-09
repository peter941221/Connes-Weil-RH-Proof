/-
Copyright (c) 2026 ConnesWeilRH contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ConnesWeilRH contributors
-/

import Mathlib.NumberTheory.LSeries.RiemannZeta
import Mathlib.NumberTheory.ArithmeticFunction.VonMangoldt
import Mathlib.Data.Real.Basic
import Mathlib.Analysis.Distribution.SchwartzSpace.Fourier

/-!
# Connes-Weil RH basic boundary

This module fixes the final target for the Connes-Weil route. The final theorem
must conclude Mathlib's canonical `RiemannHypothesis`, not a project-local
replacement.
-/

namespace ConnesWeilRH

abbrev RH : Prop := _root_.RiemannHypothesis

theorem rh_iff_mathlib : RH ↔ _root_.RiemannHypothesis :=
  Iff.rfl

structure SourceObligation where
  sourceKey : String
  sourceFile : String
  lineRange : String
  manuscriptRole : String
  statement : Prop

namespace SourceObligation

def Holds (o : SourceObligation) : Prop :=
  o.statement

end SourceObligation

abbrev TestFunction := SchwartzMap ℝ ℂ

structure WeilFormSymbols where
  qw : TestFunction → TestFunction → ℝ
  qwLambda : ℝ → TestFunction → TestFunction → ℝ
  psi : TestFunction → ℝ
  convolutionStar : TestFunction → TestFunction → TestFunction
  globalPrimeIndexSet : Finset ℕ
  restrictedPrimeIndexSet : ℝ → Finset ℕ
  finitePrimeTerm : ℕ → TestFunction → ℝ
  archimedeanTerm : TestFunction → ℝ
  poleFunctional : TestFunction → ℝ
  polePairing : TestFunction → ℝ
  primePowerPairing : ℕ → TestFunction → TestFunction → ℝ

namespace WeilFormSymbols

def finitePrimeAtomVisible
    (W : WeilFormSymbols) (n : ℕ) (F : TestFunction) : Prop :=
  W.finitePrimeTerm n F ≠ 0

noncomputable def vonMangoldtWeight
    (_W : WeilFormSymbols) (n : ℕ) : ℝ :=
  ArithmeticFunction.vonMangoldt n

def QWDefinitionStatement (W : WeilFormSymbols) : Prop :=
  ∀ f g : TestFunction,
    W.qw f g = W.psi (W.convolutionStar f g)

def PsiSignStatement (W : WeilFormSymbols) : Prop :=
  ∀ F : TestFunction,
    W.psi F =
      W.poleFunctional F - W.archimedeanTerm F -
        ∑ n ∈ W.globalPrimeIndexSet, W.finitePrimeTerm n F

def QWLambdaFormulaStatement (W : WeilFormSymbols) : Prop :=
  ∀ lambda : ℝ, 1 < lambda →
    ∀ f : TestFunction,
      W.qwLambda lambda f f =
        W.archimedeanTerm (W.convolutionStar f f) +
          W.polePairing f -
            ∑ n ∈ W.restrictedPrimeIndexSet lambda,
              W.vonMangoldtWeight n * W.primePowerPairing n f f

def GlobalPrimeIndexCoverageStatement
    (W : WeilFormSymbols) (F : TestFunction) : Prop :=
  ∀ n : ℕ, W.finitePrimeAtomVisible n F → n ∈ W.globalPrimeIndexSet

def RestrictedPrimeIndexCoverageStatement
    (W : WeilFormSymbols) (lambda : ℝ) (F : TestFunction) : Prop :=
  ∀ n : ℕ,
    W.finitePrimeAtomVisible n F → 1 < n → (n : ℝ) ≤ lambda ^ 2 →
      n ∈ W.restrictedPrimeIndexSet lambda

def FinitePrimeTermNormalizationStatement
    (W : WeilFormSymbols) (f g : TestFunction) : Prop :=
  ∀ n : ℕ,
    W.finitePrimeTerm n (W.convolutionStar f g) =
      W.vonMangoldtWeight n * W.primePowerPairing n f g

structure FinitePrimeVisibilityStatement
    (W : WeilFormSymbols) (f g : TestFunction) where
  globalPrimeIndexCoverage :
    GlobalPrimeIndexCoverageStatement W (W.convolutionStar f g)
  restrictedPrimeIndexCoverage :
    ∀ lambda : ℝ,
      1 < lambda →
        RestrictedPrimeIndexCoverageStatement W lambda
          (W.convolutionStar f g)
  finitePrimeTermNormalization :
    FinitePrimeTermNormalizationStatement W f g

def FinitePrimeNormalizationStatement (W : WeilFormSymbols) : Prop :=
  ∀ f g : TestFunction, FinitePrimeVisibilityStatement W f g

def PoleNormalizationStatement (W : WeilFormSymbols) : Prop :=
  ∀ f : TestFunction,
    W.polePairing f = W.poleFunctional (W.convolutionStar f f)

end WeilFormSymbols

structure ArchimedeanTraceSymbols where
  Test : Type
  supportSquareTrace : Test → ℝ
  sourceNoDefectTrace : Test → ℝ
  positiveTrace : Test → ℝ
  traceClass : Test → Prop
  cyclicLegal : Test → Prop
  hilbertSchmidtGate : Test → Prop
  mellinHalfDensityMatched : Prop
  uInfinityNormalized : Prop
  qduNormalized : Prop
  archimedeanSignNormalized : Prop

namespace ArchimedeanTraceSymbols

def TraceSquareStatement (A : ArchimedeanTraceSymbols) : Prop :=
  ∀ g : A.Test,
    A.traceClass g →
      A.cyclicLegal g →
        A.supportSquareTrace g = A.sourceNoDefectTrace g ∧
          0 ≤ A.positiveTrace g

def OrdinaryTraceSupportSquareStatement (A : ArchimedeanTraceSymbols) : Prop :=
  ∀ g : A.Test,
    A.traceClass g →
      A.cyclicLegal g →
        A.positiveTrace g = A.supportSquareTrace g

def TraceClassTemplateStatement (A : ArchimedeanTraceSymbols) : Prop :=
  ∀ g : A.Test,
    A.hilbertSchmidtGate g → A.traceClass g ∧ A.cyclicLegal g

def MellinHalfDensityConventionStatement (A : ArchimedeanTraceSymbols) :
    Prop :=
  A.mellinHalfDensityMatched

def SignsAndNormalizationsStatement (A : ArchimedeanTraceSymbols) : Prop :=
  A.uInfinityNormalized ∧ A.qduNormalized ∧ A.archimedeanSignNormalized

end ArchimedeanTraceSymbols

structure SemilocalModelSymbols where
  PlaceSet : Type
  sourcePlaceSet : PlaceSet
  Window : Type
  Test : Type
  sourceTest : Test
  sourceInvolution : Test → Test
  SupportPoint : Type
  supportCarrier : Test → Set SupportPoint
  fourierSupportCarrier : Test → Set SupportPoint
  fourierSupportCarrier_eq_supportCarrier_involution :
    ∀ f : Test, fourierSupportCarrier f = supportCarrier (sourceInvolution f)
  windowCarrier : Window → Set SupportPoint
  lambdaCarrier : ℝ → Set SupportPoint
  canonicalHilbertModel : PlaceSet → Prop
  scalingActionImplemented : PlaceSet → Prop
  fourierGradingCompatible : PlaceSet → Prop
  boundedComparisonMap : PlaceSet → Prop
  boundedComparisonInverse : PlaceSet → Prop

namespace SemilocalModelSymbols

def supportInWindow (M : SemilocalModelSymbols) (f : M.Test)
    (I : M.Window) : Prop :=
  M.supportCarrier f ⊆ M.windowCarrier I

@[simp] theorem supportInWindow_iff
    {M : SemilocalModelSymbols} {f : M.Test} {I : M.Window} :
    M.supportInWindow f I ↔ M.supportCarrier f ⊆ M.windowCarrier I :=
  Iff.rfl

theorem supportInWindow_of_subset
    {M : SemilocalModelSymbols} {f : M.Test} {I : M.Window}
    (h : M.supportCarrier f ⊆ M.windowCarrier I) :
    M.supportInWindow f I :=
  h

theorem supportCarrier_subset_windowCarrier_of_supportInWindow
    {M : SemilocalModelSymbols} {f : M.Test} {I : M.Window}
    (h : M.supportInWindow f I) :
    M.supportCarrier f ⊆ M.windowCarrier I :=
  h

def fourierSupportInWindow (M : SemilocalModelSymbols) (f : M.Test)
    (I : M.Window) : Prop :=
  M.fourierSupportCarrier f ⊆ M.windowCarrier I

@[simp] theorem fourierSupportInWindow_iff
    {M : SemilocalModelSymbols} {f : M.Test} {I : M.Window} :
    M.fourierSupportInWindow f I ↔
      M.fourierSupportCarrier f ⊆ M.windowCarrier I :=
  Iff.rfl

theorem fourierSupportInWindow_of_subset
    {M : SemilocalModelSymbols} {f : M.Test} {I : M.Window}
    (h : M.fourierSupportCarrier f ⊆ M.windowCarrier I) :
    M.fourierSupportInWindow f I :=
  h

theorem fourierSupportCarrier_subset_windowCarrier_of_fourierSupportInWindow
    {M : SemilocalModelSymbols} {f : M.Test} {I : M.Window}
    (h : M.fourierSupportInWindow f I) :
    M.fourierSupportCarrier f ⊆ M.windowCarrier I :=
  h

def windowContainedInLambda (M : SemilocalModelSymbols) (I : M.Window)
    (lambda : ℝ) : Prop :=
  M.windowCarrier I ⊆ M.lambdaCarrier lambda

@[simp] theorem windowContainedInLambda_iff
    {M : SemilocalModelSymbols} {I : M.Window} {lambda : ℝ} :
    M.windowContainedInLambda I lambda ↔
      M.windowCarrier I ⊆ M.lambdaCarrier lambda :=
  Iff.rfl

theorem windowContainedInLambda_of_subset
    {M : SemilocalModelSymbols} {I : M.Window} {lambda : ℝ}
    (h : M.windowCarrier I ⊆ M.lambdaCarrier lambda) :
    M.windowContainedInLambda I lambda :=
  h

theorem windowCarrier_subset_lambdaCarrier_of_windowContainedInLambda
    {M : SemilocalModelSymbols} {I : M.Window} {lambda : ℝ}
    (h : M.windowContainedInLambda I lambda) :
    M.windowCarrier I ⊆ M.lambdaCarrier lambda :=
  h

def soninSpaceComparison (M : SemilocalModelSymbols) (I : M.Window) :
    Prop :=
  M.supportInWindow M.sourceTest I ∧
    M.fourierSupportInWindow M.sourceTest I

def fixedWindowExhaustionCompatible
    (M : SemilocalModelSymbols) (I : M.Window) : Prop :=
  M.soninSpaceComparison I ∧
    M.canonicalHilbertModel M.sourcePlaceSet ∧
      (∀ V : M.PlaceSet,
        M.canonicalHilbertModel V → M.scalingActionImplemented V) ∧
        (∀ V : M.PlaceSet,
          M.canonicalHilbertModel V → M.fourierGradingCompatible V) ∧
          (∀ V : M.PlaceSet,
            M.canonicalHilbertModel V → M.boundedComparisonMap V) ∧
            (∀ V : M.PlaceSet,
              M.canonicalHilbertModel V → M.boundedComparisonInverse V)

@[simp] theorem fixedWindowExhaustionCompatible_iff
    {M : SemilocalModelSymbols} {I : M.Window} :
    M.fixedWindowExhaustionCompatible I ↔
      M.soninSpaceComparison I ∧
        M.canonicalHilbertModel M.sourcePlaceSet ∧
          (∀ V : M.PlaceSet,
            M.canonicalHilbertModel V → M.scalingActionImplemented V) ∧
            (∀ V : M.PlaceSet,
              M.canonicalHilbertModel V → M.fourierGradingCompatible V) ∧
              (∀ V : M.PlaceSet,
                M.canonicalHilbertModel V → M.boundedComparisonMap V) ∧
                (∀ V : M.PlaceSet,
                  M.canonicalHilbertModel V →
                    M.boundedComparisonInverse V) :=
  Iff.rfl

def supportTransported (M : SemilocalModelSymbols) (f : M.Test)
    (I : M.Window) : Prop :=
  M.supportInWindow f I

@[simp] theorem supportTransported_iff
    {M : SemilocalModelSymbols} {f : M.Test} {I : M.Window} :
    M.supportTransported f I ↔ M.supportInWindow f I :=
  Iff.rfl

theorem supportTransported_of_supportInWindow
    {M : SemilocalModelSymbols} {f : M.Test} {I : M.Window}
    (h : M.supportInWindow f I) :
    M.supportTransported f I :=
  h

theorem supportInWindow_of_supportTransported
    {M : SemilocalModelSymbols} {f : M.Test} {I : M.Window}
    (h : M.supportTransported f I) :
    M.supportInWindow f I :=
  h

def convolutionSupportTransported (M : SemilocalModelSymbols) (f : M.Test)
    (I : M.Window) : Prop :=
  M.fourierSupportInWindow f I

@[simp] theorem convolutionSupportTransported_iff
    {M : SemilocalModelSymbols} {f : M.Test} {I : M.Window} :
    M.convolutionSupportTransported f I ↔
      M.fourierSupportInWindow f I :=
  Iff.rfl

theorem convolutionSupportTransported_of_fourierSupportInWindow
    {M : SemilocalModelSymbols} {f : M.Test} {I : M.Window}
    (h : M.fourierSupportInWindow f I) :
    M.convolutionSupportTransported f I :=
  h

theorem fourierSupportInWindow_of_convolutionSupportTransported
    {M : SemilocalModelSymbols} {f : M.Test} {I : M.Window}
    (h : M.convolutionSupportTransported f I) :
    M.fourierSupportInWindow f I :=
  h

structure FourierSupportInvolutionGeometryData
    (M : SemilocalModelSymbols) (I : M.Window) where
  carrier_eq_involutionSupport :
    M.fourierSupportCarrier M.sourceTest =
      M.supportCarrier (M.sourceInvolution M.sourceTest)
  fourierSupportInWindow :
    M.fourierSupportInWindow M.sourceTest I
  convolutionSupportTransported :
    M.convolutionSupportTransported M.sourceTest I
  soninSpaceComparison :
    M.soninSpaceComparison I

namespace FourierSupportInvolutionGeometryData

theorem fourierSupportCarrier_subset_windowCarrier
    {M : SemilocalModelSymbols} {I : M.Window}
    (D : FourierSupportInvolutionGeometryData M I) :
    M.fourierSupportCarrier M.sourceTest ⊆ M.windowCarrier I :=
  D.fourierSupportInWindow

theorem convolutionSupportTransported_of_data
    {M : SemilocalModelSymbols} {I : M.Window}
    (D : FourierSupportInvolutionGeometryData M I) :
    M.convolutionSupportTransported M.sourceTest I :=
  D.convolutionSupportTransported

theorem soninSpaceComparison_of_data
    {M : SemilocalModelSymbols} {I : M.Window}
    (D : FourierSupportInvolutionGeometryData M I) :
    M.soninSpaceComparison I :=
  D.soninSpaceComparison

end FourierSupportInvolutionGeometryData

def lambdaCompatible (M : SemilocalModelSymbols) (I : M.Window)
    (lambda : ℝ) : Prop :=
  M.windowContainedInLambda I lambda

@[simp] theorem lambdaCompatible_iff
    {M : SemilocalModelSymbols} {I : M.Window} {lambda : ℝ} :
    M.lambdaCompatible I lambda ↔ M.windowContainedInLambda I lambda :=
  Iff.rfl

theorem lambdaCompatible_of_windowContainedInLambda
    {M : SemilocalModelSymbols} {I : M.Window} {lambda : ℝ}
    (h : M.windowContainedInLambda I lambda) :
    M.lambdaCompatible I lambda :=
  h

theorem windowContainedInLambda_of_lambdaCompatible
    {M : SemilocalModelSymbols} {I : M.Window} {lambda : ℝ}
    (h : M.lambdaCompatible I lambda) :
    M.windowContainedInLambda I lambda :=
  h

def CanonicalSemilocalModelStatement (M : SemilocalModelSymbols) : Prop :=
  ∀ S : M.PlaceSet,
    M.canonicalHilbertModel S →
      M.scalingActionImplemented S ∧ M.fourierGradingCompatible S

def SupportTransportStatement (M : SemilocalModelSymbols) : Prop :=
  ∀ f : M.Test,
    ∀ I : M.Window,
      M.supportInWindow f I →
        M.fourierSupportInWindow f I →
          M.supportTransported f I ∧ M.convolutionSupportTransported f I

def BoundedComparisonStatement (M : SemilocalModelSymbols) : Prop :=
  ∀ S : M.PlaceSet,
    M.canonicalHilbertModel S →
      M.boundedComparisonMap S ∧ M.boundedComparisonInverse S

def SoninComparisonStatement (M : SemilocalModelSymbols) : Prop :=
  ∀ I : M.Window,
    M.soninSpaceComparison I → M.fixedWindowExhaustionCompatible I

end SemilocalModelSymbols

inductive CriticalVanishingPoint where
  | zero
  | half
  | one
  deriving DecidableEq

structure TripleVanishingSymbols where
  vanishesAt : CriticalVanishingPoint → Prop

namespace TripleVanishingSymbols

def TripleVanishingStatement (T : TripleVanishingSymbols) : Prop :=
  ∀ p : CriticalVanishingPoint, T.vanishesAt p

end TripleVanishingSymbols

structure WeilPositivityInput where
  tripleVanishing : Prop
  fullWeilPositivity : Sort 1

structure FiniteVanishingCriterionPackage where
  finiteSetAdmissible : Prop
  criterion :
    ∀ input : WeilPositivityInput,
      input.tripleVanishing → input.fullWeilPositivity → RH

end ConnesWeilRH
