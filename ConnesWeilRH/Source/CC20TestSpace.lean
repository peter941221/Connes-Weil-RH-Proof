/-
Copyright (c) 2026 ConnesWeilRH contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ConnesWeilRH contributors
-/

import ConnesWeilRH.Source.CC20RHExit

/-!
# CC20 test-space interface

This module exposes the route-facing predicates needed by a CC20 Proposition
C.1 proof.  It does not assert that an arbitrary test space has Yoshida
detectors; that existence theorem belongs to a concrete CC20 test-space owner.
-/

namespace ConnesWeilRH
namespace Source

structure CC20TestSpace where
  Test : Type
  toRouteTest : Test → TestFunction
  mellinAt : Test → ℂ → ℂ
  starConvolution : Test → Test
  weilLocalSum : Test → ℝ
  compactSupportSmooth : Test → Prop

def CC20VanishesOn
    (C : CC20TestSpace)
    (F : Finset CriticalVanishingPoint)
    (g : C.Test) : Prop :=
  ∀ p : CriticalVanishingPoint,
    p ∈ F → C.mellinAt g (criticalVanishingPointValue p) = 0

def CC20WeilNonpositive
    (C : CC20TestSpace)
    (g : C.Test) : Prop :=
  C.weilLocalSum (C.starConvolution g) ≤ 0

def CC20FiniteVanishingWeilCriterion
    (C : CC20TestSpace)
    (F : Finset CriticalVanishingPoint) : Prop :=
  ∀ g : C.Test,
    C.compactSupportSmooth g →
      CC20VanishesOn C F g →
        CC20WeilNonpositive C g

structure CC20RouteInputRealizesFiniteVanishingCriterion
    (C : CC20TestSpace)
    (F : Finset CriticalVanishingPoint)
    (input : WeilPositivityInput) where
  routeInputIsCC20Criterion :
    input.fullWeilPositivity →
      CC20FiniteVanishingWeilCriterion C F
  routeTripleVanishingIsMellinVanishing :
    input.tripleVanishing →
      ∀ g : C.Test,
        C.compactSupportSmooth g →
          CC20VanishesOn C F g

end Source
end ConnesWeilRH
