/-
Copyright (c) 2026 ConnesWeilRH contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ConnesWeilRH.Dev.C1XiCenterTwoGammaSummedKernel
import ConnesWeilRH.Dev.C1LaneRD3Root

/-!
# C1XiCenterTwoGammaConstrainedPrefix - the N = 21 finite owner

This file names the finite Gamma_R prefix selected by the Lane R numerical
screen and keeps it attached to the exact shifted tail from
`C1XiCenterTwoGammaSummedKernel`.  It also exposes the real-valued quadratic
readback and the triple-Laplace-vanishing/prime-free predicates used by the
Lane R target.

The finite constrained-prefix sign is intentionally not asserted here.  The
definitions below make that missing producer an explicit proposition rather
than hiding it inside an adapter or a numerical declaration.
-/

namespace ConnesWeilRH
namespace Source
namespace C1XiCenterTwoGammaConstrainedPrefix

open Set
open Filter
open C1SameOwnerWeil
open C1XiCenterTwoGamma
open C1XiCenterTwoGammaSummedKernel
open CCM25Concrete.CompactLogConvolution
open C1LaneRD3Root
open scoped Topology

noncomputable section

/-- The finite prefix length selected by the Lane R budget screen. -/
def laneRPrefixLength : Nat := 21

theorem laneRPrefixLength_pos : 0 < laneRPrefixLength := by
  norm_num [laneRPrefixLength]

/-- The finite prefix of the same paired Gamma_R profile owner used by the
summed-kernel decomposition. -/
noncomputable def gammaRArchProfilePrefix
    (F : CompactLogTest) (N : Nat) : Complex :=
  ∑ n ∈ Finset.range N, gammaRArchProfileIntegral F n

/-- The real-valued version of one paired Gamma_R profile integral. -/
noncomputable def gammaRArchProfileRealIntegral
    (F : CompactLogTest) (n : Nat) : Real :=
  ∫ y : Real in Ioi (0 : Real),
    (gammaRArchProfileTerm F n y).re

/-- The real part of one complex profile integral is its real profile
integral.  This is the pointwise-to-real readback used by the quadratic form.
-/
theorem gammaRArchProfileIntegral_re_eq_realIntegral
    (F : CompactLogTest) (n : Nat) :
    (gammaRArchProfileIntegral F n).re =
      gammaRArchProfileRealIntegral F n := by
  unfold gammaRArchProfileIntegral gammaRArchProfileRealIntegral
  exact (integral_re (integrableOn_gammaRArchProfileTerm_public F n)).symm

/-- The real part commutes with the finite profile prefix. -/
theorem gammaRArchProfilePrefix_re_eq_sum_realIntegral
    (F : CompactLogTest) (N : Nat) :
    (gammaRArchProfilePrefix F N).re =
      ∑ n ∈ Finset.range N, gammaRArchProfileRealIntegral F n := by
  induction N with
  | zero =>
      simp [gammaRArchProfilePrefix]
  | succ N ih =>
      simp only [gammaRArchProfilePrefix, Finset.sum_range_succ,
        Complex.add_re]
      change (gammaRArchProfilePrefix F N).re +
          (gammaRArchProfileIntegral F N).re =
        (∑ n ∈ Finset.range N, gammaRArchProfileRealIntegral F n) +
          gammaRArchProfileRealIntegral F N
      rw [ih, gammaRArchProfileIntegral_re_eq_realIntegral]

/-- The constant plus finite-prefix part of the archimedean term. -/
noncomputable def gammaRArchFinitePrefixValue
    (F : CompactLogTest) (N : Nat) : Real :=
  ((((Real.log (4 * Real.pi) + Real.eulerMascheroniConstant : Real) : Complex) *
      F.test 0).re) +
    (gammaRArchProfilePrefix F N).re

/-- Exact same-owner decomposition into finite prefix and shifted tail. -/
theorem archimedeanTerm_eq_gammaRArchFinitePrefixValue_add_tail_re
    (F : CompactLogTest) (N : Nat) :
    C1SameOwnerWeil.archimedeanTerm F =
      gammaRArchFinitePrefixValue F N +
        (gammaRArchProfileTail F N).re := by
  simpa [gammaRArchFinitePrefixValue, gammaRArchProfilePrefix] using
    (archimedeanTerm_eq_constant_add_profilePrefix_add_tail_re F N)

/-- The fixed finite quadratic value used by the Lane R prefix target. -/
noncomputable def laneRFinitePrefixQuadraticValue
    (g : CompactLogTest) : Real :=
  gammaRArchFinitePrefixValue g.convolutionSquare laneRPrefixLength

/-- The exact N = 21 prefix/tail readback for a convolution square. -/
theorem archimedeanTerm_eq_laneRFinitePrefix_add_tail_re
    (g : CompactLogTest) :
    C1SameOwnerWeil.archimedeanTerm g.convolutionSquare =
      laneRFinitePrefixQuadraticValue g +
        (gammaRArchProfileTail g.convolutionSquare laneRPrefixLength).re := by
  exact archimedeanTerm_eq_gammaRArchFinitePrefixValue_add_tail_re
    g.convolutionSquare laneRPrefixLength

/-- A strictly negative complete archimedean value has a strictly negative
finite prefix for some length.  The length is test-dependent; this theorem
does not promote the numerical choice `21` to a uniform bound. -/
theorem exists_gammaRArchFinitePrefixValue_lt_zero_of_archimedeanTerm_neg
    (F : CompactLogTest)
    (hF : C1SameOwnerWeil.archimedeanTerm F < 0) :
    ∃ N : Nat, gammaRArchFinitePrefixValue F N < 0 := by
  have hpositive : 0 < -C1SameOwnerWeil.archimedeanTerm F := by
    linarith
  have htailNorm :
      Tendsto (fun N : Nat => ‖gammaRArchProfileTail F N‖)
        atTop (𝓝 (0 : Real)) := by
    simpa using (tendsto_gammaRArchProfileTail_zero F).norm
  have heventually : ∀ᶠ N : Nat in atTop,
      ‖gammaRArchProfileTail F N‖ < -C1SameOwnerWeil.archimedeanTerm F :=
    (tendsto_order.mp htailNorm).2 _ hpositive
  rcases heventually.exists with ⟨N, hN⟩
  refine ⟨N, ?_⟩
  have hlower :
      -‖gammaRArchProfileTail F N‖ ≤
        (gammaRArchProfileTail F N).re := by
    have hneg := Complex.re_le_norm (-gammaRArchProfileTail F N)
    have hneg' :
        -(gammaRArchProfileTail F N).re ≤
          ‖gammaRArchProfileTail F N‖ := by
      simpa [norm_neg] using hneg
    linarith
  have htailLower :
      C1SameOwnerWeil.archimedeanTerm F <
        (gammaRArchProfileTail F N).re := by
    linarith
  have hdecomp :=
    archimedeanTerm_eq_gammaRArchFinitePrefixValue_add_tail_re F N
  linarith

/-! ### The constrained Lane R owner -/

/-- Triple vanishing at the healthy nodes `0`, `1/2`, and `1`. -/
def laneRTripleVanishing (g : CompactLogTest) : Prop :=
  CC20VanishesOn C1.healthyCC20TestSpace
    cc20TripleFiniteVanishingSet g

/-- Prime-freeness of the Hermitian square in the log coordinate. -/
def laneRPrimeFreeSquare (g : CompactLogTest) : Prop :=
  Function.support g.convolutionSquare.test ⊆
    Ioo (-Real.log 2) (Real.log 2)

/-- The concrete prime-free constrained subfamily targeted by the first
finite-prefix screen. -/
def laneRConstrainedPrimeFree (g : CompactLogTest) : Prop :=
  laneRTripleVanishing g ∧ laneRPrimeFreeSquare g

/-- The D3 construction supplies the triple-vanishing constraint exactly. -/
theorem tripleVanishingRoot_satisfies_laneRTripleVanishing
    (h : CompactLogTest) :
    laneRTripleVanishing (tripleVanishingRoot h) := by
  exact tripleVanishingRoot_vanishesOn_cc20Triple h

/-- The D3 support transport supplies the prime-free constraint whenever the
base owner stays inside the stated interval. -/
theorem tripleVanishingRoot_satisfies_laneRPrimeFreeSquare_of_Icc
    (h : CompactLogTest) {w : Real}
    (hsupport : Function.support h.test ⊆ Icc (-w) w)
    (hw : w < (3 / 10 : Real)) :
    laneRPrimeFreeSquare (tripleVanishingRoot h) := by
  exact tripleVanishingRoot_square_support_subset_open_log_two_of_Icc
    h hsupport hw

/-- On the constrained prime-free owner, the Weil value reads back to the
negative archimedean term with no finite-prime remainder. -/
theorem qw_eq_neg_archimedeanTerm_of_laneRConstrainedPrimeFree
    {g : CompactLogTest}
    (hconstraint : laneRConstrainedPrimeFree g) :
    C1SameOwnerWeil.qw g =
      -C1SameOwnerWeil.archimedeanTerm g.convolutionSquare := by
  exact C1HealthyYoshidaDetector.qw_eq_neg_archimedeanTerm_of_vanishesOn_cc20Triple_of_primeFreeSquare
    g hconstraint.1 hconstraint.2

/-- The still-open finite-prefix sign proposition selected by the numerical
screen.  This is a target declaration, not an axiom or a proved theorem. -/
def laneRConstrainedPrefixSignTarget : Prop :=
  ∀ g : CompactLogTest,
    laneRConstrainedPrimeFree g →
      laneRFinitePrefixQuadraticValue g ≤ 0

end
end C1XiCenterTwoGammaConstrainedPrefix
end Source
end ConnesWeilRH
