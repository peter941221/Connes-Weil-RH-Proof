import ConnesWeilRH.Dev.C1RouteALocalBumpPolynomial2486

/-  2487: interval-facing bounds for the two non-polynomial bump factors.

These lemmas are deliberately symbolic.  They turn a bound on the normalized
coordinate into a bound on the inverse-deficit power, and a lower bound on its
absolute value into an exponential bound.  They do not import any numerical
cell endpoint or claim the 2478 table is analytic data.
-/

namespace ConnesWeilRH.Dev

set_option linter.style.longLine false

theorem bumpDeficit2350_ge_one_sub_sq_of_abs_le2487
    {u t : ℝ} (ht : 0 ≤ t) (habs : |u| ≤ t) :
    1 - t ^ 2 ≤ bumpDeficit2350 u := by
  have hsq : u ^ 2 ≤ t ^ 2 := by
    have h := (sq_le_sq₀ (abs_nonneg u) ht).2 habs
    simpa [sq_abs] using h
  dsimp [bumpDeficit2350]
  linarith

theorem bumpDeficit2350_inv_pow_le_of_abs_le2487
    (order : ℕ) {u t : ℝ} (ht : 0 ≤ t) (htone : t < 1)
    (habs : |u| ≤ t) :
    (bumpDeficit2350 u)⁻¹ ^ (2 * order) ≤
      (1 - t ^ 2)⁻¹ ^ (2 * order) := by
  have hbase : 0 < 1 - t ^ 2 := by
    nlinarith [sq_nonneg t]
  have hdeficit : 0 < bumpDeficit2350 u :=
    lt_of_lt_of_le hbase
      (bumpDeficit2350_ge_one_sub_sq_of_abs_le2487 (u := u) (t := t) ht habs)
  have hinv : (bumpDeficit2350 u)⁻¹ ≤ (1 - t ^ 2)⁻¹ :=
    (inv_le_inv₀ hdeficit hbase).2
      (bumpDeficit2350_ge_one_sub_sq_of_abs_le2487 (u := u) (t := t) ht habs)
  exact pow_le_pow_left₀ (by positivity) hinv (2 * order)

theorem bumpDeficit2350_exp_le_of_abs_lower2487
    {u a : ℝ} (ha : 0 ≤ a) (haone : a < 1) (habs : a ≤ |u|)
    (huone : |u| < 1) :
    Real.exp (-30 / bumpDeficit2350 u) ≤
      Real.exp (-30 / (1 - a ^ 2)) := by
  have hbase : 0 < 1 - a ^ 2 := by
    nlinarith [sq_nonneg a]
  have hdeficit : 0 < bumpDeficit2350 u := by
    dsimp [bumpDeficit2350]
    nlinarith [sq_abs u, abs_nonneg u]
  have hsq : a ^ 2 ≤ u ^ 2 := by
    have habs' : |a| ≤ |u| := by simpa [abs_of_nonneg ha] using habs
    have h := (sq_le_sq₀ (abs_nonneg a) (abs_nonneg u)).2 habs'
    simpa [sq_abs] using h
  have hdeficit_le : bumpDeficit2350 u ≤ 1 - a ^ 2 := by
    dsimp [bumpDeficit2350]
    linarith
  have hinv : (1 - a ^ 2)⁻¹ ≤ (bumpDeficit2350 u)⁻¹ :=
    (inv_le_inv₀ hbase hdeficit).2 hdeficit_le
  have harg : -30 / bumpDeficit2350 u ≤ -30 / (1 - a ^ 2) := by
    rw [div_eq_mul_inv, div_eq_mul_inv]
    nlinarith
  exact Real.exp_le_exp.mpr harg

theorem scaledBumpJet2350_abs_le_of_interval_factors2487
    (order : ℕ) (horder : order ≤ 2)
    {radius position t a : ℝ} (hradius : 0 < radius)
    (hinside : |position| < radius) (ht : 0 ≤ t) (htone : t < 1)
    (hcoord : |position / radius| ≤ t) (ha : 0 ≤ a) (haone : a < 1)
    (halower : a ≤ |position / radius|) :
    |scaledBumpJet2350 order radius position| ≤
      Real.exp (-30 / (1 - a ^ 2)) *
        (1 - t ^ 2)⁻¹ ^ (2 * order) *
        bumpNumeratorAbsUpper2486 order t / radius ^ order := by
  have hratio : |position / radius| < 1 := by
    rw [abs_div, abs_of_pos hradius, div_lt_one hradius]
    exact hinside
  have hnum : |bumpNumerator2350 order (position / radius)| ≤
      bumpNumeratorAbsUpper2486 order t :=
    bumpNumerator_abs_le_local2486 order horder ht hcoord
  have hinverse := bumpDeficit2350_inv_pow_le_of_abs_le2487 order ht htone hcoord
  have hexponential := bumpDeficit2350_exp_le_of_abs_lower2487
    ha haone halower hratio
  apply scaledBumpJet2350_abs_le_of_local_bounds2485 order hradius hinside
    _ _ _ hnum hinverse hexponential
  · have hbase : 0 ≤ 1 - t ^ 2 := by
      nlinarith [sq_nonneg t]
    exact pow_nonneg (inv_nonneg.mpr hbase) _
  · exact Real.exp_nonneg _

end ConnesWeilRH.Dev
