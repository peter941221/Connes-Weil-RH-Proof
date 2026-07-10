/-
Copyright (c) 2026 ConnesWeilRH contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ConnesWeilRH contributors
-/

import ConnesWeilRH.Source.AnalyticCoreBase
import ConnesWeilRH.Source.CC20TestSpace

/-!
# Concrete CC20 test-space owner

This module assembles the concrete `CC20TestSpace` used by the Yoshida and
Proposition C.1 route.  It does not prove detector existence and it does not
store Proposition C.1; those remain downstream theorems.
-/

namespace ConnesWeilRH
namespace Source

open AnalyticCore

/-- Carrier and route projection for the concrete CC20 test space. -/
structure CC20ConcreteCarrierData where
  Test : Type
  toRouteTest : Test → TestFunction

/-- Mellin evaluation and compact-smooth predicate for a concrete carrier. -/
structure CC20MellinCompactData (Carrier : Type) where
  mellinAt : Carrier → ℂ → ℂ
  compactSupportSmooth : Carrier → Prop

/-- Star-convolution and local Weil-sum operations for a concrete carrier. -/
structure CC20WeilOperationData (Carrier : Type) where
  starConvolution : Carrier → Carrier
  weilLocalSum : Carrier → ℝ

noncomputable abbrev normalizedCC20ConcreteTestAlgebra :
    SourceTestAlgebra :=
  SourceConcreteBaseLayer.concreteTestAlgebra

noncomputable def normalizedCC20ConcreteEvaluationData :
    SourceEvaluationData normalizedCC20ConcreteTestAlgebra :=
  {}

noncomputable def normalizedCC20ConcreteCarrierData :
    CC20ConcreteCarrierData where
  Test := normalizedCC20ConcreteTestAlgebra.Test
  toRouteTest := normalizedCC20ConcreteTestAlgebra.legacy.encode

noncomputable def normalizedCC20MellinCompactData :
    CC20MellinCompactData normalizedCC20ConcreteTestAlgebra.Test where
  mellinAt := fun g s =>
    normalizedCC20ConcreteEvaluationData.mellinAt g s
  compactSupportSmooth := fun g =>
    HasCompactSupport
      (fun x : ℝ => normalizedCC20ConcreteTestAlgebra.legacy.encode g x)

noncomputable def normalizedCC20WeilOperationData :
    CC20WeilOperationData normalizedCC20ConcreteTestAlgebra.Test where
  starConvolution := normalizedCC20ConcreteTestAlgebra.convolutionSquare
  weilLocalSum := fun g =>
    -normalizedCC20ConcreteEvaluationData.polePairing g

/--
The concrete CC20 test-space owner.  The fields are projections from the
carrier, Mellin/compact, and Weil-operation data above.
-/
noncomputable def normalizedCC20TestSpace : CC20TestSpace where
  Test := normalizedCC20ConcreteCarrierData.Test
  toRouteTest := normalizedCC20ConcreteCarrierData.toRouteTest
  mellinAt := normalizedCC20MellinCompactData.mellinAt
  starConvolution := normalizedCC20WeilOperationData.starConvolution
  weilLocalSum := normalizedCC20WeilOperationData.weilLocalSum
  compactSupportSmooth := normalizedCC20MellinCompactData.compactSupportSmooth

@[simp] theorem normalizedCC20TestSpace_toRouteTest_eq
    (g : normalizedCC20ConcreteTestAlgebra.Test) :
    normalizedCC20TestSpace.toRouteTest g =
      normalizedCC20ConcreteTestAlgebra.legacy.encode g :=
  rfl

@[simp] theorem normalizedCC20TestSpace_mellinAt_eq
    (g : normalizedCC20ConcreteTestAlgebra.Test) (s : ℂ) :
    normalizedCC20TestSpace.mellinAt g s =
      normalizedCC20ConcreteEvaluationData.mellinAt g s :=
  rfl

@[simp] theorem normalizedCC20ConcreteEvaluationData_mellinAt_eq_mellin
    (g : normalizedCC20ConcreteTestAlgebra.Test) (s : ℂ) :
    normalizedCC20ConcreteEvaluationData.mellinAt g s =
      mellin (fun x : ℝ => normalizedCC20ConcreteTestAlgebra.legacy.encode g x) s :=
  rfl

@[simp] theorem normalizedCC20TestSpace_starConvolution_eq
    (g : normalizedCC20ConcreteTestAlgebra.Test) :
    normalizedCC20TestSpace.starConvolution g =
      normalizedCC20ConcreteTestAlgebra.convolutionSquare g :=
  rfl

@[simp] theorem normalizedCC20TestSpace_weilLocalSum_eq
    (g : normalizedCC20ConcreteTestAlgebra.Test) :
    normalizedCC20TestSpace.weilLocalSum g =
      -normalizedCC20ConcreteEvaluationData.polePairing g :=
  rfl

@[simp] theorem normalizedCC20TestSpace_compactSupportSmooth_eq
    (g : normalizedCC20ConcreteTestAlgebra.Test) :
    normalizedCC20TestSpace.compactSupportSmooth g =
      HasCompactSupport
        (fun x : ℝ => normalizedCC20ConcreteTestAlgebra.legacy.encode g x) :=
  rfl

theorem normalizedCC20ConcreteEvaluationData_mellinAt_convolutionSquare
    (g : normalizedCC20ConcreteTestAlgebra.Test) (s : ℂ) :
    normalizedCC20ConcreteEvaluationData.mellinAt
        (normalizedCC20ConcreteTestAlgebra.convolutionSquare g) s =
      (2 : ℂ) * normalizedCC20ConcreteEvaluationData.mellinAt g s := by
  rw [normalizedCC20ConcreteEvaluationData_mellinAt_eq_mellin,
    normalizedCC20ConcreteEvaluationData_mellinAt_eq_mellin]
  have hfun :
      (fun x : ℝ =>
          normalizedCC20ConcreteTestAlgebra.legacy.encode
            (normalizedCC20ConcreteTestAlgebra.convolutionSquare g) x) =
        fun x : ℝ =>
          (2 : ℂ) • normalizedCC20ConcreteTestAlgebra.legacy.encode g x := by
    funext x
    simp [AnalyticCore.SourceConcreteBaseLayer.concreteLegacyTestEquiv,
      AnalyticCore.SourceConcreteBaseLayer.concreteTestAlgebra, smul_eq_mul]
    ring_nf
  rw [hfun]
  simpa [smul_eq_mul, mul_comm] using
    (mellin_const_smul
      (fun x : ℝ => normalizedCC20ConcreteTestAlgebra.legacy.encode g x)
      s (2 : ℂ))

theorem normalizedCC20TestSpace_starConvolution_compactSupportSmooth
    {g : normalizedCC20TestSpace.Test}
    (hcompact : normalizedCC20TestSpace.compactSupportSmooth g) :
    normalizedCC20TestSpace.compactSupportSmooth
      (normalizedCC20TestSpace.starConvolution g) := by
  rw [normalizedCC20TestSpace_compactSupportSmooth_eq] at hcompact ⊢
  simpa [normalizedCC20TestSpace_starConvolution_eq,
    AnalyticCore.SourceConcreteBaseLayer.concreteTestAlgebra] using
    hcompact.add hcompact

theorem normalizedCC20TestSpace_starConvolution_vanishesOn
    {g : normalizedCC20TestSpace.Test}
    (hvanish :
      CC20VanishesOn normalizedCC20TestSpace cc20TripleFiniteVanishingSet
        g) :
    CC20VanishesOn normalizedCC20TestSpace cc20TripleFiniteVanishingSet
      (normalizedCC20TestSpace.starConvolution g) := by
  intro p hp
  have hg := hvanish p hp
  rw [normalizedCC20TestSpace_starConvolution_eq,
    normalizedCC20TestSpace_mellinAt_eq,
    normalizedCC20ConcreteEvaluationData_mellinAt_convolutionSquare]
  rw [normalizedCC20TestSpace_mellinAt_eq] at hg
  rw [hg]
  norm_num

/-- The multiplicativity law that a genuine convolution model must satisfy
under Mellin evaluation.  This contract is intentionally stated separately
from the current concrete operations so that toy carrier implementations can
be rejected before they reach the RH criterion. -/
def NormalizedCC20MellinConvolutionLaw : Prop :=
  ∀ f g : normalizedCC20ConcreteTestAlgebra.Test, ∀ s : ℂ,
    normalizedCC20ConcreteEvaluationData.mellinAt
        (normalizedCC20ConcreteTestAlgebra.convolutionStar f g) s =
      normalizedCC20ConcreteEvaluationData.mellinAt f s *
        normalizedCC20ConcreteEvaluationData.mellinAt g s

/-- Exact semantic exposure of the current weak CC20 model. -/
theorem normalizedCC20TestSpace_is_additive_pole_model :
    (∀ g : normalizedCC20ConcreteTestAlgebra.Test,
      normalizedCC20ConcreteTestAlgebra.legacy.encode
          (normalizedCC20TestSpace.starConvolution g) =
        normalizedCC20ConcreteTestAlgebra.legacy.encode g +
          normalizedCC20ConcreteTestAlgebra.legacy.encode g) ∧
    (∀ g : normalizedCC20ConcreteTestAlgebra.Test,
      normalizedCC20TestSpace.weilLocalSum g =
        -normalizedCC20ConcreteEvaluationData.polePairing g) := by
  constructor
  · intro g
    rfl
  · intro g
    rfl

def NormalizedCC20PolePairingNonnegativeOnFiniteVanishing : Prop :=
  ∀ g : normalizedCC20TestSpace.Test,
    normalizedCC20TestSpace.compactSupportSmooth g →
      CC20VanishesOn normalizedCC20TestSpace cc20TripleFiniteVanishingSet g →
        0 ≤
          normalizedCC20ConcreteEvaluationData.polePairing
            (normalizedCC20ConcreteTestAlgebra.convolutionSquare g)

def NormalizedCC20FiniteVanishingToPolePairingSign : Prop :=
  ∀ g : normalizedCC20ConcreteTestAlgebra.Test,
    HasCompactSupport
      (fun x : ℝ => normalizedCC20ConcreteTestAlgebra.legacy.encode g x) →
      (∀ p : CriticalVanishingPoint,
        p ∈ cc20TripleFiniteVanishingSet →
          normalizedCC20ConcreteEvaluationData.mellinAt
            g (criticalVanishingPointValue p) = 0) →
        0 ≤
          normalizedCC20ConcreteEvaluationData.polePairing
            (normalizedCC20ConcreteTestAlgebra.convolutionSquare g)

def NormalizedCC20FiniteVanishingToHalfDensityPoleSumNonnegative : Prop :=
  ∀ g : normalizedCC20ConcreteTestAlgebra.Test,
    HasCompactSupport
      (fun x : ℝ => normalizedCC20ConcreteTestAlgebra.legacy.encode g x) →
      (∀ p : CriticalVanishingPoint,
        p ∈ cc20TripleFiniteVanishingSet →
          normalizedCC20ConcreteEvaluationData.mellinAt
            g (criticalVanishingPointValue p) = 0) →
        0 ≤
          (normalizedCC20ConcreteEvaluationData.mellinAt
            (normalizedCC20ConcreteTestAlgebra.convolutionSquare
              (normalizedCC20ConcreteTestAlgebra.convolutionSquare g))
            (Complex.I / 2)).re +
          (normalizedCC20ConcreteEvaluationData.mellinAt
            (normalizedCC20ConcreteTestAlgebra.convolutionSquare
              (normalizedCC20ConcreteTestAlgebra.convolutionSquare g))
            (-Complex.I / 2)).re

theorem normalizedCC20_finiteVanishingToPolePairingSign_of_halfDensityPoleSum
    (hSign : NormalizedCC20FiniteVanishingToHalfDensityPoleSumNonnegative) :
    NormalizedCC20FiniteVanishingToPolePairingSign := by
  intro g hcompact hvanish
  simpa [normalizedCC20ConcreteEvaluationData.polePairing_eq_mellin_convolutionSquare_half_sum]
    using hSign g hcompact hvanish

theorem normalizedCC20_polePairing_nonnegative_of_finiteVanishingToPolePairingSign
    (hSign : NormalizedCC20FiniteVanishingToPolePairingSign) :
    NormalizedCC20PolePairingNonnegativeOnFiniteVanishing := by
  intro g hcompact hvanish
  exact hSign g (by simpa [normalizedCC20TestSpace_compactSupportSmooth_eq] using hcompact)
    (by
      intro p hp
      simpa [normalizedCC20TestSpace_mellinAt_eq] using hvanish p hp)

theorem normalizedCC20_finite_vanishing_weil_criterion_of_polePairing_nonnegative
    (hSign : NormalizedCC20PolePairingNonnegativeOnFiniteVanishing) :
    CC20FiniteVanishingWeilCriterion
      normalizedCC20TestSpace cc20TripleFiniteVanishingSet := by
  intro g hcompact hvanish
  unfold CC20WeilNonpositive
  rw [normalizedCC20TestSpace_weilLocalSum_eq,
    normalizedCC20TestSpace_starConvolution_eq]
  exact neg_nonpos.mpr (hSign g hcompact hvanish)

end Source
end ConnesWeilRH
