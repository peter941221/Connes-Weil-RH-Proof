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

The leaf also records the radius-parameterized principle behind the class and
its first widening rung: `widerArchRadius = exp (-2 * (c + 1))`, where the
budget expression collapses to `R - 1 < 0` by the same algebra that certifies
the original radius.  The factor `4` in `narrowArchRadius` was a proof
artifact, not the mathematical boundary of this family; every test admitted at
the narrow rung is therefore also admitted at the widened one (about twelve
times wider).

Boundary: this is still a proper subclass of the vanishing test space.  The
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

/-! ### The budget-window statement, parameterized in the radius -/

/-- **Budget-window Weil positivity (radius-parameterized).**  The narrow-class
statement above is an instance of a monotone principle: for ANY radius `R` that
satisfies (i) the archimedean narrow-budget inequality and (ii) sits inside the
prime-free window `(−log 2, log 2)`, every triple-vanishing test whose Hermitian
square is supported in `Ioo (−R) R` has nonnegative Weil value.  Widening the
class therefore reduces to proving more radii admissible. -/
theorem qw_nonneg_of_vanishesOn_cc20Triple_of_budget_window
    {R : ℝ} (hRpos : 0 < R) (hRlt : R < 1) (hprime : R ≤ Real.log 2)
    (hbudget : Real.log (4 * Real.pi) + Real.eulerMascheroniConstant + R -
        (1 / 2 : ℝ) * Real.log (1 / R) ≤ 0)
    (g : CompactLogTest)
    (hvanishes : CC20VanishesOn C1.healthyCC20TestSpace
        cc20TripleFiniteVanishingSet g)
    (hsupport : Function.support g.convolutionSquare.test ⊆ Set.Ioo (-R) R) :
    0 ≤ C1SameOwnerWeil.qw g := by
  have hlog : Function.support g.convolutionSquare.test ⊆
      Set.Ioo (-Real.log 2) (Real.log 2) := by
    intro x hx
    rcases hsupport hx with ⟨hlo, hhi⟩
    constructor
    · nlinarith [show -R ≥ -Real.log 2 from by linarith]
    · linarith [hprime]
  rw [C1HealthyYoshidaDetector.qw_eq_neg_archimedeanTerm_of_vanishesOn_cc20Triple_of_primeFreeSquare
    g hvanishes hlog]
  exact neg_nonneg.mpr
    (archimedeanTerm_nonpos_of_narrow_budget g R hRpos hRlt hsupport hbudget)

/-- **The W4b target inequality on any admissible budget window.**  The same
radius-parameterized principle for the named right-half phase inequality of the
W5-lite ledger. -/
theorem rightHalfSpectralSum_re_ge_neg_half_of_budget_window
    {R : ℝ} (hRpos : 0 < R) (hRlt : R < 1) (hprime : R ≤ Real.log 2)
    (hbudget : Real.log (4 * Real.pi) + Real.eulerMascheroniConstant + R -
        (1 / 2 : ℝ) * Real.log (1 / R) ≤ 0)
    (g : CompactLogTest)
    (hvanishes : CC20VanishesOn C1.healthyCC20TestSpace
        cc20TripleFiniteVanishingSet g)
    (hsupport : Function.support g.convolutionSquare.test ⊆ Set.Ioo (-R) R) :
    (rightHalfSpectralSum g).re ≥ -(1 / 2 : ℝ) * onLineSpectralMass g := by
  have hq := qw_nonneg_of_vanishesOn_cc20Triple_of_budget_window
    hRpos hRlt hprime hbudget g hvanishes hsupport
  rw [qw_eq_onLine_add_two_mul_re_rightHalfSpectralSum] at hq
  linarith

/-! ### The widened algebraic radius — first rung of the widening ladder -/

/-- `e^{-2} ≤ 1/3` by the elementary exponential lower bound. -/
theorem exp_neg_two_le_one_third : Real.exp (-2 : ℝ) ≤ 1 / 3 := by
  have h2 : (3 : ℝ) ≤ Real.exp 2 := by
    have h := Real.add_one_le_exp 2
    linarith
  have hprod : Real.exp (-2 : ℝ) * Real.exp 2 = 1 := by
    rw [← Real.exp_add]
    simp
  have hpos2 : (0 : ℝ) < Real.exp 2 := Real.exp_pos 2
  have hposm : (0 : ℝ) < Real.exp (-2) := Real.exp_pos _
  nlinarith [hprod, hpos2, hposm]

/-- The next rung of the widening ladder.  Choosing `log (1 / R) = 2 * (c + 1)`
collapses the narrow-budget expression to `R - 1`, which is negative by `R < 1`
alone — so the budget closes with exactly the same algebra that certifies
`narrowArchRadius`.  The factor `4` in `narrowArchRadius` was a proof artifact,
not the mathematical boundary of this family. -/
noncomputable def widerArchRadius : ℝ :=
  Real.exp (-2 * (narrowArchCoefficient + 1))

theorem widerArchRadius_pos : 0 < widerArchRadius := by
  exact Real.exp_pos _

theorem widerArchRadius_lt_one : widerArchRadius < 1 := by
  rw [widerArchRadius, Real.exp_lt_one_iff]
  nlinarith [narrowArchCoefficient_pos]

/-- The widened radius strictly contains the original one: the ladder rung is a
genuine widening of the class. -/
theorem widerArchRadius_gt_narrowArchRadius : narrowArchRadius < widerArchRadius := by
  unfold narrowArchRadius widerArchRadius
  apply Real.exp_lt_exp.2
  nlinarith [show (0 : ℝ) < narrowArchCoefficient + 1 from
    by linarith [narrowArchCoefficient_pos]]

theorem widerArchRadius_log_inv :
    Real.log (1 / widerArchRadius) = 2 * (narrowArchCoefficient + 1) := by
  rw [widerArchRadius, one_div, Real.log_inv, Real.log_exp]
  ring

/-- The budget inequality closes at the widened radius: the expression is
`widerArchRadius - 1 < 0`. -/
theorem widerArchRadius_budget :
    narrowArchCoefficient + widerArchRadius -
        (1 / 2 : ℝ) * Real.log (1 / widerArchRadius) ≤ 0 := by
  rw [widerArchRadius_log_inv]
  nlinarith [widerArchRadius_lt_one]

/-- The widened radius sits strictly inside the prime-free window. -/
theorem widerArchRadius_lt_log_two : widerArchRadius < Real.log 2 := by
  have hle : widerArchRadius ≤ Real.exp (-2 : ℝ) := by
    unfold widerArchRadius
    apply Real.exp_le_exp.2
    nlinarith [narrowArchCoefficient_pos]
  have hlog : (1 / 3 : ℝ) < Real.log 2 := by
    have h := Real.log_two_gt_d9
    linarith
  exact lt_of_le_of_lt (hle.trans exp_neg_two_le_one_third) hlog

/-! ### The widened instances -/

/-- **Widened-class Weil positivity.**  The W4b narrow-class instance at the
first rung of the widening ladder: square support inside
`Ioo (-widerArchRadius) widerArchRadius`, about twelve times wider than the
original budget window, still unconditional. -/
theorem qw_nonneg_of_vanishesOn_cc20Triple_of_wider_square_support
    (g : CompactLogTest)
    (hvanishes : CC20VanishesOn C1.healthyCC20TestSpace
        cc20TripleFiniteVanishingSet g)
    (hsupport : Function.support g.convolutionSquare.test ⊆
      Set.Ioo (-widerArchRadius) widerArchRadius) :
    0 ≤ C1SameOwnerWeil.qw g := by
  exact qw_nonneg_of_vanishesOn_cc20Triple_of_budget_window
    widerArchRadius_pos widerArchRadius_lt_one widerArchRadius_lt_log_two.le
    widerArchRadius_budget g hvanishes hsupport

/-- **The W4b target inequality on the widened class.** -/
theorem rightHalfSpectralSum_re_ge_neg_half_of_wider_square_support
    (g : CompactLogTest)
    (hvanishes : CC20VanishesOn C1.healthyCC20TestSpace
        cc20TripleFiniteVanishingSet g)
    (hsupport : Function.support g.convolutionSquare.test ⊆
      Set.Ioo (-widerArchRadius) widerArchRadius) :
    (rightHalfSpectralSum g).re ≥ -(1 / 2 : ℝ) * onLineSpectralMass g := by
  exact rightHalfSpectralSum_re_ge_neg_half_of_budget_window
    widerArchRadius_pos widerArchRadius_lt_one widerArchRadius_lt_log_two.le
    widerArchRadius_budget g hvanishes hsupport

/-! ### Axiom-cleanliness audit — every result above is a theorem; each
depends only on `[propext, Classical.choice, Quot.sound]`; no self-root, no
`sorryAx`, no new project axiom. -/
#print axioms exp_neg_four_le_one_fifth
#print axioms narrowArchRadius_le_one_fifth
#print axioms narrowArchRadius_lt_log_two
#print axioms qw_nonneg_of_vanishesOn_cc20Triple_of_narrow_square_support
#print axioms rightHalfSpectralSum_re_ge_neg_half_of_narrow_square_support
#print axioms qw_nonneg_of_vanishesOn_cc20Triple_of_narrow_root_support
#print axioms qw_nonneg_of_vanishesOn_cc20Triple_of_budget_window
#print axioms rightHalfSpectralSum_re_ge_neg_half_of_budget_window
#print axioms exp_neg_two_le_one_third
#print axioms widerArchRadius_pos
#print axioms widerArchRadius_lt_one
#print axioms widerArchRadius_gt_narrowArchRadius
#print axioms widerArchRadius_log_inv
#print axioms widerArchRadius_budget
#print axioms widerArchRadius_lt_log_two
#print axioms qw_nonneg_of_vanishesOn_cc20Triple_of_wider_square_support
#print axioms rightHalfSpectralSum_re_ge_neg_half_of_wider_square_support

end
end C1SpectralNarrowW4b
end Source
end ConnesWeilRH
