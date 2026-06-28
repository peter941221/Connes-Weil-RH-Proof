/-
Copyright (c) 2026 ConnesWeilRH contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ConnesWeilRH contributors
-/

import Mathlib.NumberTheory.LSeries.RiemannZeta
import Mathlib.Data.Real.Basic

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

abbrev TestFunction := Type

structure WeilFormSymbols where
  qw : TestFunction → TestFunction → ℝ
  qwLambda : ℝ → TestFunction → TestFunction → ℝ
  psi : TestFunction → ℝ
  convolutionStar : TestFunction → TestFunction → TestFunction
  globalPrimeIndexSet : Finset ℕ
  restrictedPrimeIndexSet : ℝ → Finset ℕ
  finitePrimeAtomVisible : ℕ → TestFunction → Prop
  finitePrimeTerm : ℕ → TestFunction → ℝ
  archimedeanTerm : TestFunction → ℝ
  poleFunctional : TestFunction → ℝ
  polePairing : TestFunction → ℝ
  primePowerPairing : ℕ → TestFunction → TestFunction → ℝ
  vonMangoldtWeight : ℕ → ℝ

namespace WeilFormSymbols

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
    W.finitePrimeAtomVisible n F → n ∈ W.restrictedPrimeIndexSet lambda

def FinitePrimeTermNormalizationStatement
    (W : WeilFormSymbols) (f g : TestFunction) : Prop :=
  ∀ n : ℕ,
    W.finitePrimeTerm n (W.convolutionStar f g) =
      W.vonMangoldtWeight n * W.primePowerPairing n f g

def FinitePrimeVisibilityStatement
    (W : WeilFormSymbols) (f g : TestFunction) : Prop :=
  let F := W.convolutionStar f g
  GlobalPrimeIndexCoverageStatement W F ∧
    (∀ lambda : ℝ,
      1 < lambda → RestrictedPrimeIndexCoverageStatement W lambda F) ∧
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
  Window : Type
  Test : Type
  canonicalHilbertModel : PlaceSet → Prop
  scalingActionImplemented : PlaceSet → Prop
  fourierGradingCompatible : PlaceSet → Prop
  supportInWindow : Test → Window → Prop
  fourierSupportInWindow : Test → Window → Prop
  supportTransported : Test → Window → Prop
  convolutionSupportTransported : Test → Window → Prop
  windowContainedInLambda : Window → ℝ → Prop
  lambdaCompatible : Window → ℝ → Prop
  boundedComparisonMap : PlaceSet → Prop
  boundedComparisonInverse : PlaceSet → Prop
  soninSpaceComparison : Window → Prop
  fixedWindowExhaustionCompatible : Window → Prop

namespace SemilocalModelSymbols

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
  fullWeilPositivity : Prop

structure FiniteVanishingCriterionPackage where
  finiteSetAdmissible : Prop
  criterion :
    ∀ input : WeilPositivityInput,
      input.tripleVanishing → input.fullWeilPositivity → RH

end ConnesWeilRH
