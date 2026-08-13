import ConnesWeilRH.Dev.C1LogPositiveBridge
import ConnesWeilRH.Source.CC20TestSpace
import ConnesWeilRH.Source.CC20YoshidaCriterion

/-! # C1HealthyTestSpace - the compact-log `CC20TestSpace` instance

`docs/proofs/960` records that `CC20FiniteVanishingWeilCriterion` has NO
healthy-carrier `CC20TestSpace` instance: the healthy machine is an L2 Hilbert
operator, not a `TestFunction` + `weilLocal` test space.  This module supplies
the missing object layer.

It builds `healthyCC20TestSpace : CC20TestSpace` on the healthy compact-log
carrier `CompactLogTest` using the genuine definitions:

  * `toRouteTest`          = the zero-extended positive-variable test
                             `x ↦ F(log x)` for `x > 0`
  * `mellinAt`             = bilateral Laplace evaluation in the log coordinate
  * `starConvolution`      = `CompactLogTest.convolutionSquare`
  * `weilLocalSum`         = the negative of the complete same-owner `Psi`
  * `compactSupportSmooth` = compact support of the positive-variable route test.

It also proves the structural plumbing: star-convolution preserves
compact-support-smooth, and applying `weilLocalSum` to `starConvolution g`
reads the negative source Weil value of exactly one convolution square. This
sign matches the route contract that source `QW >= 0` supplies CC20 local-sum
nonpositivity.

SCOPE: this closes the local object, coordinate, and sign-convention layer.
It does not transport the normalized route's Yoshida detector machinery to
this owner, and it does not prove the finite-vanishing sign. RH NOT claimed.
-/
namespace ConnesWeilRH
namespace Source
namespace C1

open AnalyticCore
open CCM25Concrete.CompactLogConvolution
open CC20YoshidaConvolution
open C1SameOwnerWeil
open C1LogPositiveBridge

/-- The coordinate-consistent `CC20TestSpace` on the compact-log carrier. The
generic criterion supplies the half-density square exactly once. -/
noncomputable def healthyCC20TestSpace : ConnesWeilRH.Source.CC20TestSpace where
  Test := CompactLogTest
  toRouteTest := C1LogPositiveBridge.toPositiveRouteTest
  mellinAt := CompactLogTest.laplaceAt
  starConvolution := fun g => CompactLogTest.convolutionSquare g
  weilLocalSum := fun F => -C1SameOwnerWeil.psi F
  compactSupportSmooth := fun g =>
    HasCompactSupport (C1LogPositiveBridge.toPositiveRouteTest g)

/-- Realization of compact-smooth by the built-in support data. -/
theorem healthyCC20CompactSupportSmooth (g : CompactLogTest) :
    healthyCC20TestSpace.compactSupportSmooth g :=
  C1LogPositiveBridge.toPositiveRouteTest_compactSupport g

/-- The healthy star-convolution is compact-smooth when the input is. -/
theorem healthyStarCompact (g : CompactLogTest) :
    healthyCC20TestSpace.compactSupportSmooth
      (healthyCC20TestSpace.starConvolution g) :=
  C1LogPositiveBridge.toPositiveRouteTest_compactSupport g.convolutionSquare

/-- Mellin evaluation is the bilateral Laplace transform of the same log test. -/
theorem healthyMellinReadoff (g : CompactLogTest) (s : Complex) :
    healthyCC20TestSpace.mellinAt g s = CompactLogTest.laplaceAt g s := by
  rfl

/-- The route-facing positive-variable Mellin transform reads the same value as
the log-coordinate `mellinAt` slot. -/
theorem healthyRouteMellinReadoff (g : CompactLogTest) (s : Complex) :
    mellin (fun x : Real => healthyCC20TestSpace.toRouteTest g x) s =
      healthyCC20TestSpace.mellinAt g s := by
  exact mellin_toPositiveRouteTest_eq_laplaceAt g s

/-- The CC20 local sum is the negative source Weil functional. -/
theorem healthyWeilReadoff (g : CompactLogTest) :
    healthyCC20TestSpace.weilLocalSum g =
      -C1SameOwnerWeil.psi g := by
  rfl

/-- `CC20WeilNonpositive` applies `weilLocalSum` to `starConvolution g`.
This readback guards against accidentally taking a second convolution square. -/
theorem healthyWeilSquareReadoff (g : CompactLogTest) :
    healthyCC20TestSpace.weilLocalSum
        (healthyCC20TestSpace.starConvolution g) =
      -C1SameOwnerWeil.qw g := by
  rfl

/-- The project criterion's nonpositive local sum is exactly source Weil
nonnegativity on the same owner. -/
theorem healthyCC20WeilNonpositive_iff_qw_nonnegative (g : CompactLogTest) :
    ConnesWeilRH.Source.CC20WeilNonpositive healthyCC20TestSpace g ↔
      0 <= C1SameOwnerWeil.qw g := by
  rw [ConnesWeilRH.Source.CC20WeilNonpositive, healthyWeilSquareReadoff]
  exact neg_nonpos

/-- The genuine finite-vanishing Weil criterion on the same compact-log owner.
Proving this proposition is an RH-level mathematical step; it is not asserted. -/
def healthyCriterionState (F : Finset CriticalVanishingPoint) : Prop :=
  ConnesWeilRH.Source.CC20FiniteVanishingWeilCriterion healthyCC20TestSpace F

/-- The complete healthy criterion has no hidden compact-support or sign
convention residue: its only content is nonnegativity of `qw` for every test
with the requested Mellin vanishings. -/
theorem healthyCriterionState_iff_all_vanishing_qw_nonnegative
    (F : Finset CriticalVanishingPoint) :
    healthyCriterionState F ↔
      ∀ g : CompactLogTest,
        ConnesWeilRH.Source.CC20VanishesOn healthyCC20TestSpace F g →
          0 ≤ C1SameOwnerWeil.qw g := by
  constructor
  · intro hcriterion g hvanishing
    exact (healthyCC20WeilNonpositive_iff_qw_nonnegative g).mp
      (hcriterion g (healthyCC20CompactSupportSmooth g) hvanishing)
  · intro hqw g _hcompact hvanishing
    exact (healthyCC20WeilNonpositive_iff_qw_nonnegative g).mpr
      (hqw g hvanishing)

end C1
end Source
end ConnesWeilRH
