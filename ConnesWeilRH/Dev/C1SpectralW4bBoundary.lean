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

## The second boundary-guided rung: `refinedBoundaryArchRadius = exp (-13/2)`

The headroom of the first ceiling is spent on its crudest piece, the log bound.
Replacing `log u ≤ u - 1` with a third-order Taylor estimate whose remainder has
a fixed sign — for all `t ≥ 0`,

```text
log (1 + t) ≤ t - t^2/2 + t^3/3        (the gap's derivative is t^3/(1+t) ≥ 0)
```

— applied at `t = π/2 - 1` and slid to the rational endpoint `d6(π)/2 - 1` by a
purely algebraic increasing step, gives the refined ceiling

```text
c < 3 * d9(log 2) + P_3(d6(π)/2 − 1) + 2/3
  = 77183772755855054857 / 24000000000000000000          (≈ 3.2160; true c ≈ 3.1084)
```

a drop of ≈ 0.1 over the first ceiling.  The budget then closes at
`R = exp (-13/2)` with the elementary bound `exp (-13/2) ≤ 1/30` (the cube of
`e^x ≥ 1 + x` at `x = 13/6`, since `(19/6)^3 > 30`) and norm_num arithmetic:

```text
B(exp (-13/2)) < ceiling' + 1/30 − 13/4
               = -(16227244144945143 / 24000000000000000000)   < 0, margin ≈ 6.8e-4
```

The admissible class widens by the factor `exp (7 − 13/2) = exp (1/2)`
(≈ 1.65×).  The remaining headroom to the family boundary `R*` is now dominated
by the γ ceiling `2/3` (true γ ≈ 0.577) and the higher-order terms of the log
bound — the next cuts on the ladder.

## Boundary

`Ioo (-refinedBoundaryArchRadius) refinedBoundaryArchRadius` is still a proper
support class (and so is every smaller radius, by the monotonicity lemmas):
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

/-! ### The second sharpening: a third-order Taylor bound for `log (1 + t)` -/

/-- The cubic Taylor polynomial of `log (1 + t)` at `t = 0`. -/
noncomputable def cubicLogTower (t : ℝ) := t - t ^ 2 / 2 + t ^ 3 / 3

/-- The gap between the bound and `log (1 + t)` has derivative `x^3 / (1 + x)`,
which is nonnegative for `x > 0` — that remainder sign is what makes the bound
valid on all of `[0, ∞)`. -/
theorem cubicLogTower_gap_hasDerivAt {x : ℝ} (hx : 0 < x) :
    HasDerivAt (fun t => cubicLogTower t - Real.log (1 + t)) (x ^ 3 / (1 + x)) x := by
  -- Polynomial part: the derivative of `t - t^2/2 + t^3/3` is `1 - x + x^2`.
  have hId := hasDerivAt_id x
  have hSqDiv2 := HasDerivAt.div_const (hasDerivAt_pow 2 x) 2
  have hCubeDiv3 := HasDerivAt.div_const (hasDerivAt_pow 3 x) 3
  -- Log part via the chain rule at point `1 + x`; `comp_const_add` hands back exactly
  -- the clean lambda `fun t => Real.log (1 + t)` with derivative `(1 + x)⁻¹`.
  have hpos : 0 < 1 + x := by linarith
  have hlogpart := HasDerivAt.comp_const_add (1 : ℝ) x (Real.hasDerivAt_log (ne_of_gt hpos))
  -- The assembled derivative's surface form differs from the clean target only by
  -- normalization; `hval` bridges exactly that gap.
  have hval : x ^ 3 / (1 + x) =
      ((1 - ((2 : ℝ) * x ^ (2 - 1)) / 2) + (((3 : ℝ) * x ^ (3 - 1)) / 3)) - (1 + x)⁻¹ := by
    field_simp [hpos.ne']
    ring
  have hpoly := HasDerivAt.add (HasDerivAt.sub hId hSqDiv2) hCubeDiv3
  have hfinal := HasDerivAt.sub hpoly hlogpart
  simp only [cubicLogTower, hval]
  exact hfinal

/-- **Third-order Taylor bound:** for all `t ≥ 0`, `log (1 + t) ≤ P_3(t)` — the
gap is nondecreasing on `[0, ∞)` and vanishes at `t = 0`. -/
theorem log_one_plus_t_le_cubicLogTower {t : ℝ} (ht : 0 ≤ t) :
    Real.log (1 + t) ≤ cubicLogTower t := by
  -- The gap function is differentiable on all of `Ici 0`, boundary point included: the
  -- polynomial part is, and `log (1 + u)` is since `1 + u ≥ 1 > 0` there.
  have hdiffat0 : DifferentiableAt ℝ (fun u => cubicLogTower u - Real.log (1 + u)) (0 : ℝ) := by
    -- Same derivative assembly as the gap theorem at point 0; only differentiability is
    -- needed here, so no value normalization.
    have hId := hasDerivAt_id (0 : ℝ)
    have hSqDiv2 := HasDerivAt.div_const (hasDerivAt_pow 2 (0 : ℝ)) (2 : ℝ)
    have hCubeDiv3 := HasDerivAt.div_const (hasDerivAt_pow 3 (0 : ℝ)) (3 : ℝ)
    have hlogpart := HasDerivAt.comp_const_add (1 : ℝ) (0 : ℝ)
        (Real.hasDerivAt_log (show (1 + 0 : ℝ) ≠ 0 by norm_num))
    exact (HasDerivAt.sub
        (HasDerivAt.add (HasDerivAt.sub hId hSqDiv2) hCubeDiv3)
        hlogpart).differentiableAt
  have hdiffon : DifferentiableOn ℝ (fun u => cubicLogTower u - Real.log (1 + u))
      (Set.Ici (0 : ℝ)) := by
    intro x hx
    rcases eq_or_lt_of_le (Set.mem_Ici.mp hx) with (hx0 | hposx)
    · subst hx0
      exact hdiffat0.differentiableWithinAt
    · exact (cubicLogTower_gap_hasDerivAt hposx).differentiableAt.differentiableWithinAt
  have hgapmono : MonotoneOn (fun u => cubicLogTower u - Real.log (1 + u))
      (Set.Ici (0 : ℝ)) := by
    apply monotoneOn_of_deriv_nonneg (convex_Ici 0) (hdiffon.continuousOn)
        (hdiffon.mono interior_subset)
    · intro x hx
      rw [interior_Ici, Set.mem_Ioi] at hx
      have hgap := cubicLogTower_gap_hasDerivAt hx
      rw [hgap.deriv]
      positivity
  have hgap0 : cubicLogTower 0 - Real.log (1 + 0) = 0 := by
    norm_num [cubicLogTower, Real.log_one]
  have hgappos : 0 ≤ cubicLogTower t - Real.log (1 + t) := by
    rw [← hgap0]
    change (fun u => cubicLogTower u - Real.log (1 + u)) 0 ≤
        (fun u => cubicLogTower u - Real.log (1 + u)) t
    apply hgapmono
    · norm_num
    · exact ht
    · exact ht
  linarith [hgappos]

/-- The refined ceiling piece for `log (π/2)`: with `t' := π/2 - 1` and the
rational endpoint `q := d6(π)/2 − 1`, `log (π/2) = log(1 + t') ≤ P₃(t')` by the
Taylor bound, and `P₃` is increasing on `[0, q]` with `t' < q`, so a purely
algebraic slide gives `≤ P₃(q)`. -/
theorem log_pi_half_le_third_order_bound :
    Real.log (Real.pi / 2) ≤ cubicLogTower ((3141593 : ℝ) / (2 * 10 ^ 6) - 1) := by
  let te := Real.pi / 2 - 1
  let qe := (3141593 : ℝ) / (2 * 10 ^ 6) - 1
  -- Every arithmetic goal below is written in fully unfolded form: `nlinarith` does not
  -- expand local lets.
  have htpos : 0 ≤ te := by
    change 0 ≤ Real.pi / 2 - 1
    nlinarith [Real.pi_gt_three]
  have htaylor : Real.log (Real.pi / 2) ≤ cubicLogTower te := by
    rw [show Real.pi / 2 = 1 + (Real.pi / 2 - 1) from by ring]
    exact log_one_plus_t_le_cubicLogTower htpos
  have hsumlt : te + qe < 2 := by
    change (Real.pi / 2 - 1) + ((3141593 : ℝ) / (2 * 10 ^ 6) - 1) < 2
    nlinarith [Real.pi_lt_d6]
  have hQ : 0 ≤ te ^ 2 + te * qe + qe ^ 2 := by
    -- Sum of squares: x^2 + xy + y^2 = (x + y/2)^2 + (3/4)y^2.
    have hso : te ^ 2 + te * qe + qe ^ 2 = (te + qe / 2) ^ 2 + (3 : ℝ) / 4 * qe ^ 2 := by ring
    rw [hso]
    positivity
  -- The factor in `P_3(qe) - P_3(te)` is positive: the sum is < 2 and the quadratic ≥ 0.
  have hbracket : 0 < 1 - (te + qe) / 2 + (te ^ 2 + te * qe + qe ^ 2) / 3 := by
    nlinarith [hsumlt, hQ]
  have hdiffpos : 0 < qe - te := by
    change 0 < ((3141593 : ℝ) / (2 * 10 ^ 6) - 1) - (Real.pi / 2 - 1)
    nlinarith [Real.pi_lt_d6]
  -- `P_3` is a cubic: the difference factors as (qe - te) times that bracket.
  have hdiff : cubicLogTower qe - cubicLogTower te =
      (qe - te) * (1 - (te + qe) / 2 + (te ^ 2 + te * qe + qe ^ 2) / 3) := by
    simp only [cubicLogTower]
    ring
  have hpoly : 0 < (qe - te) * (1 - (te + qe) / 2 + (te ^ 2 + te * qe + qe ^ 2) / 3) :=
    mul_pos hdiffpos hbracket
  -- `nlinarith` cannot push the factorization through nonlinear atoms; go via the
  -- positive difference instead (linear in the two polynomial values).
  have hdiffltpos : 0 < cubicLogTower qe - cubicLogTower te := by
    rw [hdiff]
    exact hpoly
  have hslide : cubicLogTower te ≤ cubicLogTower qe := by
    linarith [hdiffltpos]
  exact le_trans htaylor hslide

/-! ### The refined ceiling and the second boundary-guided rung -/

/-- A refined rational ceiling for `narrowArchCoefficient`: sum of the three
ingredient ceilings — `3 * d9(log 2)`, the third-order Taylor bound at
`d6(π)/2 − 1`, and `2/3` for γ.  Value ≈ 3.2160 (true c ≈ 3.1084); a drop of
≈ 0.1 over the first ceiling, spent entirely on replacing `log u ≤ u - 1` with
`log (1+t) ≤ t − t²/2 + t³/3`. -/
def refinedArchCoefficientRationalCeiling : ℚ := 77183772755855054857 / 24000000000000000000

/-- The coefficient sits strictly below the refined ceiling: inputs are only
mathlib digit bounds plus this leaf's Taylor bound, no new analysis. -/
theorem narrowArchCoefficient_lt_refined_ceiling :
    narrowArchCoefficient < (refinedArchCoefficientRationalCeiling : ℝ) := by
  rw [narrowArchCoefficient_log_split]
  have hlog2 : 3 * Real.log 2 < 3 * ((6931471808 : ℝ) / 10 ^ 10) := by
    nlinarith [Real.log_two_lt_d9]
  have hpihalf : Real.log (Real.pi / 2) ≤ cubicLogTower ((3141593 : ℝ) / (2 * 10 ^ 6) - 1) :=
    log_pi_half_le_third_order_bound
  have hgamma : Real.eulerMascheroniConstant < (2 : ℝ) / 3 :=
    Real.eulerMascheroniConstant_lt_two_thirds
  -- The three pieces of the refined ceiling sum to exactly the recorded constant.
  have hsum : 3 * ((6931471808 : ℝ) / 10 ^ 10) +
      cubicLogTower ((3141593 : ℝ) / (2 * 10 ^ 6) - 1) + (2 : ℝ) / 3 =
      (refinedArchCoefficientRationalCeiling : ℝ) := by
    norm_num [cubicLogTower, refinedArchCoefficientRationalCeiling]
  nlinarith [hlog2, hpihalf, hgamma, hsum]

/-- `e^{-13/2} ≤ 1/30`: from the elementary bound `e^x ≥ 1 + x` at `x = 13/6`,
cubed: `e^{13/2} = (e^{13/6})^3 ≥ (19/6)^3 > 30`. -/
theorem exp_neg_thirteen_halves_le_one_thirtieth : Real.exp (-((13 : ℝ) / 2)) ≤ 1 / 30 := by
  have hbase : 1 + (13 : ℝ) / 6 ≤ Real.exp ((13 : ℝ) / 6) := by
    have h := Real.add_one_le_exp ((13 : ℝ) / 6)
    linarith
  -- `E^3 - A^3 = (E - A)(E^2 + EA + A^2)` with `A := 1 + 13/6`, `E := exp (13/6)`: the
  -- first factor is nonnegative by `hbase` and the second strictly positive, so
  -- `A^3 ≤ E^3` — no unbundled monoid typeclass anywhere in sight.
  have hcubed : (1 + (13 : ℝ) / 6) ^ 3 ≤ (Real.exp ((13 : ℝ) / 6)) ^ 3 := by
    have hepos : 0 < Real.exp ((13 : ℝ) / 6) := Real.exp_pos _
    have hdiff : (Real.exp ((13 : ℝ) / 6)) ^ 3 - (1 + (13 : ℝ) / 6) ^ 3 =
        (Real.exp ((13 : ℝ) / 6) - (1 + (13 : ℝ) / 6)) *
          ((Real.exp ((13 : ℝ) / 6)) ^ 2 + Real.exp ((13 : ℝ) / 6) * (1 + (13 : ℝ) / 6) +
            (1 + (13 : ℝ) / 6) ^ 2) := by ring
    have hP : 0 ≤ Real.exp ((13 : ℝ) / 6) - (1 + (13 : ℝ) / 6) := sub_nonneg.mpr hbase
    have hQ : 0 < (Real.exp ((13 : ℝ) / 6)) ^ 2 + Real.exp ((13 : ℝ) / 6) * (1 + (13 : ℝ) / 6) +
        (1 + (13 : ℝ) / 6) ^ 2 := by positivity [hepos]
    rw [← sub_nonneg, hdiff]
    exact mul_nonneg hP (le_of_lt hQ)
  -- `e^{13/2}` is the cube of `e^{13/6}`.
  have heq : Real.exp ((13 : ℝ) / 2) = (Real.exp ((13 : ℝ) / 6)) ^ 3 := by
    rw [show (13 : ℝ) / 2 = ((13 : ℝ) / 6 + (13 : ℝ) / 6) + (13 : ℝ) / 6 from by ring,
      Real.exp_add, Real.exp_add]
    ring
  have hthirty : (30 : ℝ) ≤ Real.exp ((13 : ℝ) / 2) := by
    rw [heq]
    have hpow : (30 : ℝ) ≤ (1 + (13 : ℝ) / 6) ^ 3 := by norm_num
    nlinarith [hcubed, hpow]
  have hprod : Real.exp (-((13 : ℝ) / 2)) * Real.exp ((13 : ℝ) / 2) = 1 := by
    rw [← Real.exp_add]
    simp
  have hposA : (0 : ℝ) < Real.exp ((13 : ℝ) / 2) := Real.exp_pos _
  have hposB : (0 : ℝ) < Real.exp (-((13 : ℝ) / 2)) := Real.exp_pos _
  nlinarith [hthirty, hprod, hposA, hposB]

/-- The second boundary-guided radius of the widening ladder: `exp (-13/2)` ≈
`1.50e-3`, about 1.65× wider than the first rung; admissibility from a refined
ceiling plus norm_num arithmetic. -/
noncomputable def refinedBoundaryArchRadius : ℝ := Real.exp (-((13 : ℝ) / 2))

theorem refinedBoundaryArchRadius_pos : 0 < refinedBoundaryArchRadius := by
  exact Real.exp_pos _

theorem refinedBoundaryArchRadius_lt_one : refinedBoundaryArchRadius < 1 := by
  rw [refinedBoundaryArchRadius, Real.exp_lt_one_iff]
  norm_num

theorem refinedBoundaryArchRadius_log_inv :
    Real.log (1 / refinedBoundaryArchRadius) = (13 : ℝ) / 2 := by
  rw [refinedBoundaryArchRadius, one_div, Real.log_inv, Real.log_exp]
  ring

/-- The budget closes strictly at the second boundary-guided radius:
`B(exp (-13/2)) < ceiling' + 1/30 − 13/4 = -(16227244144945143 / 24000000000000000000)
< 0` — pure rational arithmetic, margin ≈ 6.8e-4. -/
theorem refinedBoundaryArchRadius_budget_lt :
    narrowArchCoefficient + refinedBoundaryArchRadius -
        (1 / 2 : ℝ) * Real.log (1 / refinedBoundaryArchRadius) < 0 := by
  rw [refinedBoundaryArchRadius_log_inv]
  -- Bind the ceiling to a numeral so the final comparison is pure rational arithmetic.
  have hceil : narrowArchCoefficient < (77183772755855054857 : ℝ) / 24000000000000000000 := by
    apply lt_of_lt_of_le narrowArchCoefficient_lt_refined_ceiling
    norm_num [refinedArchCoefficientRationalCeiling]
  -- `nlinarith` treats the def as an atom; expose `Real.exp (-((13 : ℝ) / 2))` first so
  -- the hypothesis connects to the goal.
  unfold refinedBoundaryArchRadius
  nlinarith [hceil, exp_neg_thirteen_halves_le_one_thirtieth]

theorem refinedBoundaryArchRadius_budget :
    narrowArchCoefficient + refinedBoundaryArchRadius -
        (1 / 2 : ℝ) * Real.log (1 / refinedBoundaryArchRadius) ≤ 0 := by
  exact refinedBoundaryArchRadius_budget_lt.le

/-- The second boundary-guided radius sits strictly inside the prime-free window. -/
theorem refinedBoundaryArchRadius_lt_log_two : refinedBoundaryArchRadius < Real.log 2 := by
  rw [refinedBoundaryArchRadius]
  have hlog : (1 / 30 : ℝ) < Real.log 2 := by
    nlinarith [Real.log_two_gt_d9]
  exact lt_of_le_of_lt exp_neg_thirteen_halves_le_one_thirtieth hlog

/-- The rung is a genuine widening: `boundaryArchRadius < refinedBoundaryArchRadius`
because `-7 < -13/2`. -/
theorem boundaryArchRadius_lt_refinedBoundaryArchRadius :
    boundaryArchRadius < refinedBoundaryArchRadius := by
  unfold boundaryArchRadius refinedBoundaryArchRadius
  apply Real.exp_lt_exp.2
  norm_num

/-- Consequence of strict monotonicity: every radius in
`(0, refinedBoundaryArchRadius]` is budget-admissible at once. -/
theorem budget_nonpos_of_le_refinedBoundaryArchRadius {R : ℝ} (hRpos : 0 < R)
    (hRle : R ≤ refinedBoundaryArchRadius) :
    narrowArchCoefficient + R - (1 / 2 : ℝ) * Real.log (1 / R) ≤ 0 := by
  rcases eq_or_lt_of_le hRle with (hRe | hRlt)
  · subst hRe
    exact refinedBoundaryArchRadius_budget
  · have hstrict := budgetExpression_strictMonoOn_pos hRpos refinedBoundaryArchRadius_pos hRlt
    exact le_of_lt (lt_trans hstrict refinedBoundaryArchRadius_budget_lt)

/-! ### The W4b instances on the second boundary-guided class -/

/-- **Second-rung Weil positivity.**  Every triple-vanishing test whose Hermitian
square is supported in `Ioo (-refinedBoundaryArchRadius) refinedBoundaryArchRadius`
has nonnegative same-owner Weil value — unconditional, about 1.65× wider than the
first boundary-guided rung. -/
theorem qw_nonneg_of_vanishesOn_cc20Triple_of_refined_boundary_square_support
    (g : CompactLogTest)
    (hvanishes : CC20VanishesOn C1.healthyCC20TestSpace
        cc20TripleFiniteVanishingSet g)
    (hsupport : Function.support g.convolutionSquare.test ⊆
      Set.Ioo (-refinedBoundaryArchRadius) refinedBoundaryArchRadius) :
    0 ≤ C1SameOwnerWeil.qw g := by
  exact qw_nonneg_of_vanishesOn_cc20Triple_of_budget_window
    refinedBoundaryArchRadius_pos refinedBoundaryArchRadius_lt_one
    refinedBoundaryArchRadius_lt_log_two.le refinedBoundaryArchRadius_budget g hvanishes hsupport

/-- **The W4b target inequality on the second boundary-guided class.** -/
theorem rightHalfSpectralSum_re_ge_neg_half_of_refined_boundary_square_support
    (g : CompactLogTest)
    (hvanishes : CC20VanishesOn C1.healthyCC20TestSpace
        cc20TripleFiniteVanishingSet g)
    (hsupport : Function.support g.convolutionSquare.test ⊆
      Set.Ioo (-refinedBoundaryArchRadius) refinedBoundaryArchRadius) :
    (rightHalfSpectralSum g).re ≥ -(1 / 2 : ℝ) * onLineSpectralMass g := by
  exact rightHalfSpectralSum_re_ge_neg_half_of_budget_window
    refinedBoundaryArchRadius_pos refinedBoundaryArchRadius_lt_one
    refinedBoundaryArchRadius_lt_log_two.le refinedBoundaryArchRadius_budget g hvanishes hsupport

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
#print axioms cubicLogTower_gap_hasDerivAt
#print axioms log_one_plus_t_le_cubicLogTower
#print axioms log_pi_half_le_third_order_bound
#print axioms refinedArchCoefficientRationalCeiling
#print axioms narrowArchCoefficient_lt_refined_ceiling
#print axioms exp_neg_thirteen_halves_le_one_thirtieth
#print axioms refinedBoundaryArchRadius_pos
#print axioms refinedBoundaryArchRadius_lt_one
#print axioms refinedBoundaryArchRadius_log_inv
#print axioms refinedBoundaryArchRadius_budget_lt
#print axioms refinedBoundaryArchRadius_budget
#print axioms refinedBoundaryArchRadius_lt_log_two
#print axioms boundaryArchRadius_lt_refinedBoundaryArchRadius
#print axioms budget_nonpos_of_le_refinedBoundaryArchRadius
#print axioms qw_nonneg_of_vanishesOn_cc20Triple_of_refined_boundary_square_support
#print axioms rightHalfSpectralSum_re_ge_neg_half_of_refined_boundary_square_support

end
end C1SpectralW4bBoundary
end Source
end ConnesWeilRH
