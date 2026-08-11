import ConnesWeilRH.Dev.WellFormHealthyRepoint
import ConnesWeilRH.Dev.CompactArchTotal
import ConnesWeilRH.Source.CC20TestSpace
import ConnesWeilRH.Source.CC20YoshidaCriterion

/-! # C1HealthyTestSpace — the honest healthy-carrier `CC20TestSpace` instance

`docs/proofs/960` records that `CC20FiniteVanishingWeilCriterion` has NO
healthy-carrier `CC20TestSpace` instance: the healthy machine is an L2 Hilbert
operator, not a `TestFunction` + `weilLocal` test space.  This module supplies
the missing object layer.

It builds `healthyCC20TestSpace : CC20TestSpace` on the healthy compact-log
carrier `CompactLogTest` using the genuine definitions:

  * `toRouteTest`          = `CompactLogTest.test`  (real Schwartz `TestFunction`)
  * `mellinAt`             = `healthyEval.mellinAt g.test s` (healthy Mellin algebra)
  * `starConvolution`      = `CompactLogTest.convolutionSquare`
  * `weilLocalSum`         = the archimedean Eq.3.7 term `totalArchimedean` read at
                             the convolution square, negated (the archimedean slot).
  * `compactSupportSmooth` = `HasCompactSupport ⇑g.test`, realized by `g.compactSupport`.

It also proves honest structural plumbing: star-convolution preserves
compact-support-smooth and the archimedean read-out factors through the healthy
explicit total term.

HONEST SCOPE:  `weilLocalSum` here is the **archimedean component only**; the full
explicit-Weil balance (pole / prime / restricted sums) and the sign proof
`weilLocalSum (star g) <= 0` are the open RH-equivalent math.  That criterion is made
*stateable* here but NOT asserted.  RH NOT claimed.
-/
namespace ConnesWeilRH
namespace Source
namespace C1

open AnalyticCore
open CCM25Concrete.CompactLogConvolution
open CCM25Concrete.CompactArchTotal
open Dev.WellFormHealthyRepoint

/-- The healthy `CC20TestSpace` on the compact-log carrier.  The `weilLocalSum`
   slot reads the real archimedean Eq.3.7 term at the convolution square. -/
noncomputable def healthyCC20TestSpace : ConnesWeilRH.Source.CC20TestSpace where
  Test := CompactLogTest
  toRouteTest := fun g => g.test
  mellinAt := fun g s => Dev.WellFormHealthyRepoint.healthyEval.mellinAt g.test s
  starConvolution := fun g => CompactLogTest.convolutionSquare g
  weilLocalSum := fun g => - (totalArchimedean (CompactLogTest.convolutionSquare g).test)
  compactSupportSmooth := fun g => HasCompactSupport (⇑g.test)

/-- Realization of compact-smooth by the built-in support data. -/
theorem healthyCC20CompactSupportSmooth (g : CompactLogTest) :
    healthyCC20TestSpace.compactSupportSmooth g :=
  g.compactSupport

/-- The healthy star-convolution is compact-smooth when the input is. -/
theorem healthyStarCompact (g : CompactLogTest) :
    healthyCC20TestSpace.compactSupportSmooth
      (healthyCC20TestSpace.starConvolution g) :=
  (CompactLogTest.convolutionSquare g).compactSupport

/-- The archimedean read-out factors through the healthy explicit total term. -/
theorem healthyWeilReadoff (g : CompactLogTest) :
    healthyCC20TestSpace.weilLocalSum g =
      - (totalArchimedean (CompactLogTest.convolutionSquare g).test) := by
  rfl

/-- The C1 finite-vanishing criterion is now stateable as a Prop on the healthy
   carrier.  Proving it is the open RH-equivalent step; it is not asserted. -/
def healthyCriterionState (F : Finset CriticalVanishingPoint) : Prop :=
  ConnesWeilRH.Source.CC20FiniteVanishingWeilCriterion healthyCC20TestSpace F

end C1
end Source
end ConnesWeilRH
