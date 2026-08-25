import ConnesWeilRH.Dev.C1SpectralQwAssembly
import ConnesWeilRH.Dev.C1HealthyYoshidaDetector
import ConnesWeilRH.Dev.C1LaneRNarrowArch
import ConnesWeilRH.Dev.C1SpectralNarrowW4b

/-!
# C1SpectralW4bBoundary - the budget family of the W4b class, and its first boundary-guided rung

The radius-parameterized principle landed in `C1SpectralNarrowW4b` says: every
radius `R` with `0 < R < 1`, `R ≤ log 2`, and budget expression

```text
B(R) = log (4π) + γ + R - (1/2) * log (1/R)   ≤  0
```

admits the full W4b target inequality on triple-vanishing tests whose Hermitian
square is supported in `Ioo (-R) R`.  This leaf analyzes that family of
admissible radii and lands its first boundary-guided rung.

## The shape of the admissible family

`B` is strictly increasing on `(0, ∞)` (the difference
`B(y) - B(x)` for `0 < x < y` is `(y - x) + (1/2) * log (y/x)`, a sum of two
positive terms).  The admissible radii are therefore an initial segment
`(0, R*]` of the positive line; `R*` is the unique zero of `B`.  The previous
rungs `narrowArchRadius = exp (-4(c+1))` and `widerArchRadius = exp (-2(c+1))`
were chosen so that the budget algebra collapses by cancellation — proof
artifacts, not the boundary.

## The first boundary-guided rung: `boundaryArchRadius = exp (-7)`

Instead of cancelling against `c`, this rung bounds `c = log (4π) + γ` from
above by a Lean-provable rational ceiling and closes the budget at
`R = exp (-7)` with norm_num arithmetic alone:

```text
c = 3 * log 2 + log (π/2) + γ                      (exact split, this leaf)
  < 3 * d9(log 2) + (d6(π)/2 - 1) + 2/3            (mathlib digit bounds)
  = 12438392659 / 3750000000                        (≈ 3.3169; true c ≈ 3.1084)

B(exp (-7)) = c + exp (-7) - 7/2
            < ceiling + 1/8 - 7/2                   (exp (-7) ≤ 1/8 via e^7 ≥ 8)
            = -(1742858728 / 30000000000)           < 0, margin ≈ 0.058
```

The ceiling uses only `Real.log_two_lt_d9`, `Real.pi_lt_d6` (through the crude
but elementary bound `log u ≤ u - 1` on `u = π/2 ∈ [1, 2]`), and
`Real.eulerMascheroniConstant_lt_two_thirds`.  Its ≈ 0.21 of headroom over the
true coefficient is exactly the fuel for the next rungs: sharpening any one of
the three ingredient bounds lowers the ceiling and pushes `R` toward `R*`
(numerically `R* ≈ 1.98e-3`, about twice `boundaryArchRadius`).

## Boundary

`Ioo (-boundaryArchRadius) boundaryArchRadius` is still a proper support class:
the universal W4b obligation over all vanishing tests (hence RH) remains open,
and the density/completeness question for the budget family — which needs a
topology on `CompactLogTest`, not yet chosen in this project — is recorded as
the next cut.

-/

namespace ConnesWeilRH
namespace Source
namespace C1SpectralW4bBoundary

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
open C1SpectralNarrowW4b

noncomputable section

/-! ### The exact split of the archimedean coefficient -/

/-- `log (4π) = 3 * log 2 + log (π/2)` because `4π = 8 · (π/2)`, so the
archimedean coefficient decomposes into three separately boundable pieces. -/
theorem narrowArchCoefficient_log_split :
    narrowArchCoefficient = 3 * Real.log 2 + Real.log (Real.pi / 2) +
        Real.eulerMascheroniConstant := by
  unfold narrowArchCoefficient
  have hpos : 0 < Real.pi / 2 := div_pos Real.pi_pos (by norm_num)
  have heq : (4 : ℝ) * Real.pi = (8 : ℝ) * (Real.pi / 2) := by
    field_simp
    ring
  calc
    Real.log (4 * Real.pi) + Real.eulerMascheroniConstant =
        Real.log ((8 : ℝ) * (Real.pi / 2)) + Real.eulerMascheroniConstant := by
      rw [heq]
    _ = Real.log 8 + Real.log (Real.pi / 2) + Real.eulerMascheroniConstant := by
      rw [Real.log_mul (by norm_num : (8 : ℝ) ≠ 0) (ne_of_gt hpos)]
    _ = 3 * Real.log 2 + Real.log (Real.pi / 2) + Real.eulerMascheroniConstant := by
      have h8cube : (8 : ℝ) = (2 : ℝ) ^ 3 := by norm_num
      rw [h8cube, Real.log_pow]
      ring

/-! ### Rational bounds on the coefficient -/

/-- A Lean-provable rational ceiling for `narrowArchCoefficient`.  It is the
sum of the three ingredient ceilings: `3 * d9(log 2)`, `d6(π)/2 - 1` (the
elementary bound `log u ≤ u - 1` applied to `u = π/2 < d6(π)/2 ∈ [1, 2]`), and
`2/3` for γ.  Its value ≈ 3.3169 leaves ≈ 0.21 of headroom over the true
coefficient ≈ 3.1084; each future rung spends part of that headroom to push the
admissible radius toward the family boundary `R*`. -/
def archCoefficientRationalCeiling : ℚ := 12438392659 / 3750000000

/-- The coefficient sits strictly below its rational ceiling: the only inputs
are mathlib digit bounds, no new analysis. -/
theorem narrowArchCoefficient_lt_ceiling :
    narrowArchCoefficient < (archCoefficientRationalCeiling : ℝ) := by
  rw [narrowArchCoefficient_log_split]
  have hlog2 : 3 * Real.log 2 < 3 * ((6931471808 : ℝ) / 10 ^ 10) := by
    nlinarith [Real.log_two_lt_d9]
  have hpihalf : Real.pi / 2 < (3141593 : ℝ) / (2 * 10 ^ 6) := by
    nlinarith [Real.pi_lt_d6]
  -- The elementary bound `log u <= u - 1` on `u = pi/2 in [1, 2]`.
  have hlogsub : Real.log (Real.pi / 2) ≤ Real.pi / 2 - 1 :=
    Real.log_le_sub_one_of_pos (div_pos Real.pi_pos (by norm_num))
  have hlogu : Real.log (Real.pi / 2) < (3141593 : ℝ) / (2 * 10 ^ 6) - 1 := by
    nlinarith [hlogsub, hpihalf]
  have hgamma : Real.eulerMascheroniConstant < (2 : ℝ) / 3 :=
    Real.eulerMascheroniConstant_lt_two_thirds
  -- The three ingredient ceilings sum to the recorded ceiling exactly.
  have hsum : 3 * ((6931471808 : ℝ) / 10 ^ 10) +
      ((3141593 : ℝ) / (2 * 10 ^ 6) - 1) + (2 : ℝ) / 3 =
      (archCoefficientRationalCeiling : ℝ) := by
    norm_num [archCoefficientRationalCeiling]
  nlinarith [hlog2, hlogu, hgamma, hsum]

/-- Coefficient lower bound: `c > 5/2`, the fact needed to see that the new
radius is a genuine widening of the previous rung. -/
theorem narrowArchCoefficient_gt_five_halves : (5 / 2 : ℝ) < narrowArchCoefficient := by
  rw [narrowArchCoefficient_log_split]
  have hlog2 : 3 * ((6931471803 : ℝ) / 10 ^ 10) ≤ 3 * Real.log 2 := by
    nlinarith [Real.log_two_gt_d9]
  have hlogu : 0 ≤ Real.log (Real.pi / 2) :=
    Real.log_nonneg (by nlinarith [show (3 : ℝ) < Real.pi from Real.pi_gt_three])
  have hgamma : (1 / 2 : ℝ) < Real.eulerMascheroniConstant :=
    Real.one_half_lt_eulerMascheroniConstant
  nlinarith [hlog2, hlogu, hgamma]

/-! ### The budget expression is strictly increasing -/

/-- Rewriting the budget in its monotone form: for any `R`,
`- (1/2) * log (1/R) = (1/2) * log R`. -/
theorem budgetExpr_eq_linear_plus_half_log {R : ℝ} :
    narrowArchCoefficient + R - (1 / 2 : ℝ) * Real.log (1 / R) =
      narrowArchCoefficient + R + (1 / 2 : ℝ) * Real.log R := by
  -- In mathlib v4.30 `one_div` states `1 / a = a⁻¹` directly (no intermediate
  -- multiplication), so `log_inv` closes the goal immediately after it.
  have hlog : Real.log (1 / R) = -Real.log R := by
    rw [one_div, Real.log_inv]
  rw [hlog]
  ring

/-- The budget expression is strictly increasing on the positive line: for
`0 < x < y`, `B(y) - B(x) = (y - x) + (1/2) * log (y/x)` and both summands are
positive.  Consequently the admissible radii form an initial segment `(0, R*]`. -/
theorem budgetExpression_strictMonoOn_pos :
    StrictMonoOn (fun R => narrowArchCoefficient + R - (1 / 2 : ℝ) * Real.log (1 / R))
      (Set.Ioi (0 : ℝ)) := by
  intro x hx y hy hxy
  have hlin : narrowArchCoefficient + x < narrowArchCoefficient + y := by
    nlinarith [hxy]
  have hloglt : Real.log x < Real.log y := (Real.log_lt_log_iff hx hy).mpr hxy
  have hhalf : (1 / 2 : ℝ) * Real.log x < (1 / 2 : ℝ) * Real.log y := by
    nlinarith [hloglt]
  -- The goal is a lambda application; beta-reduce it so the rewrite pattern matches.
  change narrowArchCoefficient + x - (1 / 2 : ℝ) * Real.log (1 / x) <
      narrowArchCoefficient + y - (1 / 2 : ℝ) * Real.log (1 / y)
  rw [@budgetExpr_eq_linear_plus_half_log x, @budgetExpr_eq_linear_plus_half_log y]
  exact add_lt_add hlin hhalf

/-! ### The first boundary-guided rung -/

/-- `e^{-7} ≤ 1/8` from the elementary lower bound `e^7 ≥ 1 + 7 = 8`. -/
theorem exp_neg_seven_le_one_eighth : Real.exp (-7 : ℝ) ≤ 1 / 8 := by
  have h7 : (8 : ℝ) ≤ Real.exp 7 := by
    have h := Real.add_one_le_exp 7
    linarith
  have hprod : Real.exp (-7 : ℝ) * Real.exp 7 = 1 := by
    rw [← Real.exp_add]
    simp
  have hpos7 : (0 : ℝ) < Real.exp 7 := Real.exp_pos 7
  have hposm : (0 : ℝ) < Real.exp (-7) := Real.exp_pos _
  nlinarith [h7, hprod, hpos7, hposm]

/-- The first boundary-guided radius of the widening ladder.  Unlike the
previous rungs, it is not defined through `c`; its admissibility follows from a
rational ceiling on `c` plus norm_num arithmetic. -/
noncomputable def boundaryArchRadius : ℝ := Real.exp (-7)

theorem boundaryArchRadius_pos : 0 < boundaryArchRadius := by
  exact Real.exp_pos _

theorem boundaryArchRadius_lt_one : boundaryArchRadius < 1 := by
  rw [boundaryArchRadius, Real.exp_lt_one_iff]
  norm_num

theorem boundaryArchRadius_log_inv :
    Real.log (1 / boundaryArchRadius) = (7 : ℝ) := by
  rw [boundaryArchRadius, one_div, Real.log_inv, Real.log_exp]
  ring

/-- The budget closes strictly at the boundary-guided radius:
`B(exp (-7)) < ceiling + 1/8 - 7/2 < 0`, with the last comparison pure rational
arithmetic (margin ≈ 0.058). -/
theorem boundaryArchRadius_budget_lt :
    narrowArchCoefficient + boundaryArchRadius -
        (1 / 2 : ℝ) * Real.log (1 / boundaryArchRadius) < 0 := by
  rw [boundaryArchRadius_log_inv]
  -- Bind the ceiling to a numeral so the final comparison is pure rational arithmetic.
  have hceil : narrowArchCoefficient < (12438392659 : ℝ) / 3750000000 := by
    apply lt_of_lt_of_le narrowArchCoefficient_lt_ceiling
    norm_num [archCoefficientRationalCeiling]
  -- `nlinarith` treats the def as an atom; expose `Real.exp (-7)` first so the
  -- hypothesis `exp (-7) <= 1/8` connects to the goal.
  unfold boundaryArchRadius
  nlinarith [hceil, exp_neg_seven_le_one_eighth]

theorem boundaryArchRadius_budget :
    narrowArchCoefficient + boundaryArchRadius -
        (1 / 2 : ℝ) * Real.log (1 / boundaryArchRadius) ≤ 0 := by
  exact boundaryArchRadius_budget_lt.le

/-- The boundary-guided radius sits strictly inside the prime-free window. -/
theorem boundaryArchRadius_lt_log_two : boundaryArchRadius < Real.log 2 := by
  rw [boundaryArchRadius]
  have hlog : (1 / 8 : ℝ) < Real.log 2 := by
    nlinarith [Real.log_two_gt_d9]
  exact lt_of_le_of_lt exp_neg_seven_le_one_eighth hlog

/-- The rung is a genuine widening: `boundaryArchRadius > widerArchRadius`
because `c > 5/2`, so `-7 < -2(c+1)` and the exponential order flips. -/
theorem boundaryArchRadius_gt_widerArchRadius : widerArchRadius < boundaryArchRadius := by
  unfold widerArchRadius boundaryArchRadius
  apply Real.exp_lt_exp.2
  nlinarith [show (5 / 2 : ℝ) < narrowArchCoefficient from
    narrowArchCoefficient_gt_five_halves]

/-- Consequence of strict monotonicity: every radius in `(0, boundaryArchRadius]`
is budget-admissible at once — future rungs only need a smaller rational ceiling
on the coefficient. -/
theorem budget_nonpos_of_le_boundaryArchRadius {R : ℝ} (hRpos : 0 < R)
    (hRle : R ≤ boundaryArchRadius) :
    narrowArchCoefficient + R - (1 / 2 : ℝ) * Real.log (1 / R) ≤ 0 := by
  rcases eq_or_lt_of_le hRle with (hRe | hRlt)
  · subst hRe
    exact boundaryArchRadius_budget
  · have hstrict := budgetExpression_strictMonoOn_pos hRpos boundaryArchRadius_pos hRlt
    exact le_of_lt (lt_trans hstrict boundaryArchRadius_budget_lt)

/-! ### The W4b instances on the boundary-guided class -/

/-- **Boundary-guided Weil positivity.**  Every triple-vanishing test whose
Hermitian square is supported in `Ioo (-boundaryArchRadius) boundaryArchRadius`
has nonnegative same-owner Weil value — unconditional, about three and a half
times wider than the previous rung. -/
theorem qw_nonneg_of_vanishesOn_cc20Triple_of_boundary_square_support
    (g : CompactLogTest)
    (hvanishes : CC20VanishesOn C1.healthyCC20TestSpace
        cc20TripleFiniteVanishingSet g)
    (hsupport : Function.support g.convolutionSquare.test ⊆
      Set.Ioo (-boundaryArchRadius) boundaryArchRadius) :
    0 ≤ C1SameOwnerWeil.qw g := by
  exact qw_nonneg_of_vanishesOn_cc20Triple_of_budget_window
    boundaryArchRadius_pos boundaryArchRadius_lt_one boundaryArchRadius_lt_log_two.le
    boundaryArchRadius_budget g hvanishes hsupport

/-- **The W4b target inequality on the boundary-guided class.** -/
theorem rightHalfSpectralSum_re_ge_neg_half_of_boundary_square_support
    (g : CompactLogTest)
    (hvanishes : CC20VanishesOn C1.healthyCC20TestSpace
        cc20TripleFiniteVanishingSet g)
    (hsupport : Function.support g.convolutionSquare.test ⊆
      Set.Ioo (-boundaryArchRadius) boundaryArchRadius) :
    (rightHalfSpectralSum g).re ≥ -(1 / 2 : ℝ) * onLineSpectralMass g := by
  exact rightHalfSpectralSum_re_ge_neg_half_of_budget_window
    boundaryArchRadius_pos boundaryArchRadius_lt_one boundaryArchRadius_lt_log_two.le
    boundaryArchRadius_budget g hvanishes hsupport

/-! ### Axiom-cleanliness audit — every result above is a theorem; each depends
only on `[propext, Classical.choice, Quot.sound]`; no self-root, no `sorryAx`,
no new project axiom. -/
#print axioms narrowArchCoefficient_log_split
#print axioms archCoefficientRationalCeiling
#print axioms narrowArchCoefficient_lt_ceiling
#print axioms narrowArchCoefficient_gt_five_halves
#print axioms budgetExpr_eq_linear_plus_half_log
#print axioms budgetExpression_strictMonoOn_pos
#print axioms exp_neg_seven_le_one_eighth
#print axioms boundaryArchRadius_pos
#print axioms boundaryArchRadius_lt_one
#print axioms boundaryArchRadius_log_inv
#print axioms boundaryArchRadius_budget_lt
#print axioms boundaryArchRadius_budget
#print axioms boundaryArchRadius_lt_log_two
#print axioms boundaryArchRadius_gt_widerArchRadius
#print axioms budget_nonpos_of_le_boundaryArchRadius
#print axioms qw_nonneg_of_vanishesOn_cc20Triple_of_boundary_square_support
#print axioms rightHalfSpectralSum_re_ge_neg_half_of_boundary_square_support

end
end C1SpectralW4bBoundary
end Source
end ConnesWeilRH
