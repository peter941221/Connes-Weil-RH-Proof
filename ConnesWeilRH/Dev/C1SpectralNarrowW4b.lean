import ConnesWeilRH.Dev.C1SpectralQwAssembly
import ConnesWeilRH.Dev.C1HealthyYoshidaDetector
import ConnesWeilRH.Dev.C1LaneRNarrowArch

/-!
# C1SpectralNarrowW4b - the W4b inequality on the narrow-support class

This leaf assembles the first *forall-class* instance of the W4b-bound: on
triple-vanishing tests whose Hermitian square is supported inside the narrow
archimedean budget window, the complete W4b target inequality

```text
Re (rightHalfSpectralSum g) >= -(1/2) * onLineSpectralMass g
```

holds unconditionally, and therefore `0 <= C1SameOwnerWeil.qw g` holds there
as well.

The assembly consumes only landed, axiom-clean pieces:

```text
qw g = - archimedeanTerm (g□)                       (triple vanishing kills the
                                                      pole; prime-free square
                                                      kills the prime sum)
archimedeanTerm (g□) <= 0                            (narrow budget window,
                                                      uniform in g)
onLineSpectralMass + 2 * Re (rightHalfSpectralSum)
  = qw g                                            (W5-lite ledger)
```

The class is nonempty (it contains `narrowArchRoot` and every
`C1LaneRD3Root.tripleVanishingRoot` of an `Icc (−narrowArchBaseWidth)
narrowArchBaseWidth`-supported base) and is closed under linear combinations
in the root-support form, because both vanishing and the support window are
preserved.

Boundary: this is a proper subclass of the vanishing test space.  The
universal W4b obligation (all vanishing tests) remains open, and RH remains
unclaimed.
-/

namespace ConnesWeilRH
namespace Source
namespace C1SpectralNarrowW4b

open CC20YoshidaNearZeros
open CCM25Concrete.CompactLogConvolution
open C1SameOwnerWeil
open C1SpectralWeil
open C1SpectralOnlineSplit
open C1SpectralOfflinePairing
open C1SpectralSummability
open C1CenterTwoCriterionBridge
open C1SpectralVanishingTransfer
open C1SpectralQwAssembly
open C1LaneRNarrowArch

noncomputable section

/-! ### The budget radius is prime-free -/

/-- `e^{-4} ≤ 1/5` by the elementary exponential lower bound. -/
theorem exp_neg_four_le_one_fifth : Real.exp (-4 : ℝ) ≤ 1 / 5 := by
  have h4 : (5 : ℝ) ≤ Real.exp 4 := by
    have h := Real.add_one_le_exp 4
    linarith
  have hprod : Real.exp (-4 : ℝ) * Real.exp 4 = 1 := by
    rw [← Real.exp_add]
    simp
  have hpos4 : (0 : ℝ) < Real.exp 4 := Real.exp_pos 4
  have hposm : (0 : ℝ) < Real.exp (-4) := Real.exp_pos _
  nlinarith [hprod, hpos4, hposm]

/-- The budget radius is at most `e^{-4}`. -/
theorem narrowArchRadius_le_one_fifth : narrowArchRadius ≤ 1 / 5 := by
  have hle : narrowArchRadius ≤ Real.exp (-4 : ℝ) := by
    unfold narrowArchRadius
    apply Real.exp_le_exp.2
    nlinarith [narrowArchCoefficient_pos]
  exact hle.trans exp_neg_four_le_one_fifth

/-- The narrow budget radius sits strictly inside the prime-free window
`(-log 2, log 2)`. -/
theorem narrowArchRadius_lt_log_two : narrowArchRadius < Real.log 2 := by
  have h1 : (3 / 5 : ℝ) < Real.log 2 := by
    have h := Real.log_two_gt_d9
    linarith
  have h2 : narrowArchRadius ≤ 1 / 5 := narrowArchRadius_le_one_fifth
  linarith

/-! ### The narrow-class positivity -/

/-- **Narrow-class Weil positivity.**  For every triple-vanishing test whose
Hermitian square is supported in the narrow budget window, the same-owner Weil
value is nonnegative.  This is an unconditional forall-class statement: no
realness, no nondegeneracy, and no per-test sign hypothesis is consumed. -/
theorem qw_nonneg_of_vanishesOn_cc20Triple_of_narrow_square_support
    (g : CompactLogTest)
    (hvanishes : CC20VanishesOn C1.healthyCC20TestSpace
        cc20TripleFiniteVanishingSet g)
    (hsupport : Function.support g.convolutionSquare.test ⊆
      Set.Ioo (-narrowArchRadius) narrowArchRadius) :
    0 ≤ C1SameOwnerWeil.qw g := by
  have hlog : Function.support g.convolutionSquare.test ⊆
      Set.Ioo (-Real.log 2) (Real.log 2) := by
    intro x hx
    rcases hsupport hx with ⟨hlo, hhi⟩
    constructor
    · nlinarith [narrowArchRadius_lt_log_two]
    · linarith [narrowArchRadius_lt_log_two]
  rw [C1HealthyYoshidaDetector.qw_eq_neg_archimedeanTerm_of_vanishesOn_cc20Triple_of_primeFreeSquare
    g hvanishes hlog]
  exact neg_nonneg.mpr
    (archimedeanTerm_nonpos_of_narrow_budget g narrowArchRadius
      narrowArchRadius_pos narrowArchRadius_lt_one hsupport narrowArchRadius_budget)

/-- **The W4b target inequality on the narrow class.**  The named right-half
phase inequality of the W4b-bound, the single sufficient condition of the
W5-lite ledger, holds for every triple-vanishing test with square support in
the narrow budget window.  This is the first unconditional forall-class
instance of the W4b inequality. -/
theorem rightHalfSpectralSum_re_ge_neg_half_of_narrow_square_support
    (g : CompactLogTest)
    (hvanishes : CC20VanishesOn C1.healthyCC20TestSpace
        cc20TripleFiniteVanishingSet g)
    (hsupport : Function.support g.convolutionSquare.test ⊆
      Set.Ioo (-narrowArchRadius) narrowArchRadius) :
    (rightHalfSpectralSum g).re ≥ -(1 / 2 : ℝ) * onLineSpectralMass g := by
  have hq := qw_nonneg_of_vanishesOn_cc20Triple_of_narrow_square_support
    g hvanishes hsupport
  rw [qw_eq_onLine_add_two_mul_re_rightHalfSpectralSum] at hq
  linarith

/-- Root-support entrance to the narrow class: a triple-vanishing test whose
own support fits in the base-width window has its Hermitian square inside the
budget window, hence nonnegative Weil value.  The root-support form makes the
linear-combination closure of the class immediate. -/
theorem qw_nonneg_of_vanishesOn_cc20Triple_of_narrow_root_support
    (g : CompactLogTest)
    (hvanishes : CC20VanishesOn C1.healthyCC20TestSpace
        cc20TripleFiniteVanishingSet g)
    (hsupport : Function.support (g.test : ℝ → ℂ) ⊆
      Set.Icc (-narrowArchBaseWidth) narrowArchBaseWidth) :
    0 ≤ C1SameOwnerWeil.qw g := by
  have hioo : Function.support (g.test : ℝ → ℂ) ⊆
      Set.Ioo (-narrowArchRadius / 2) (narrowArchRadius / 2) := by
    intro x hx
    rcases hsupport hx with ⟨hlo, hhi⟩
    dsimp [narrowArchBaseWidth] at hlo hhi
    constructor <;> nlinarith [narrowArchRadius_pos]
  exact qw_nonneg_of_vanishesOn_cc20Triple_of_narrow_square_support g hvanishes
    (CC20YoshidaConvolution.CompactLogTest.convolutionSquare_support_subset_symmetric
      g (a := narrowArchRadius) hioo)

/-! ### Axiom-cleanliness audit — every result above is a theorem; each
depends only on `[propext, Classical.choice, Quot.sound]`; no self-root, no
`sorryAx`, no new project axiom. -/
#print axioms exp_neg_four_le_one_fifth
#print axioms narrowArchRadius_le_one_fifth
#print axioms narrowArchRadius_lt_log_two
#print axioms qw_nonneg_of_vanishesOn_cc20Triple_of_narrow_square_support
#print axioms rightHalfSpectralSum_re_ge_neg_half_of_narrow_square_support
#print axioms qw_nonneg_of_vanishesOn_cc20Triple_of_narrow_root_support

end
end C1SpectralNarrowW4b
end Source
end ConnesWeilRH
