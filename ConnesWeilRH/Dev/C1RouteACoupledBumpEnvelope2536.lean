import ConnesWeilRH.Dev.C1RouteABumpDerivativeLadder

/-!
Local order-0..4 bump bounds used by the record-2535 whole-cell evaluator.
The inverse-deficit power and exponential stay coupled, so cells may reach
the flat support boundary. No numerical table or weighted-family bound is
assumed to be certified by this module.
-/

namespace ConnesWeilRH.Dev

open scoped BigOperators
open ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit

theorem powerExp_le_at_lower2536 {position lower decay : ℝ} {order : ℕ}
    (hlower : 0 < lower) (hposition : lower ≤ position)
    (horder : (order : ℝ) ≤ decay * lower) :
    position ^ order * Real.exp (-decay * position) ≤
      lower ^ order * Real.exp (-decay * lower) := by
  have hratio : 1 ≤ position / lower := (le_div_iff₀ hlower).2 (by simpa using hposition)
  have h := mul_le_mul_of_nonneg_left (powerExpUpper2349 hratio horder)
    (pow_nonneg hlower.le order)
  have harg : -(decay * lower) * (position / lower) = -decay * position := by
    field_simp [ne_of_gt hlower]
  rw [harg, div_pow] at h
  convert h using 1 <;> field_simp [ne_of_gt hlower]

theorem polynomialAbsUpperLocal2536 {Index : Type*} (terms : Finset Index)
    (coefficient : Index → ℝ) (power : Index → ℕ) {position t : ℝ}
    (hposition : |position| ≤ t) :
    |∑ index ∈ terms, coefficient index * position ^ power index| ≤
      ∑ index ∈ terms, |coefficient index| * t ^ power index := by
  calc
    _ ≤ ∑ index ∈ terms, |coefficient index * position ^ power index| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ _ := Finset.sum_le_sum fun index _ => by
      rw [abs_mul, abs_pow]
      exact mul_le_mul_of_nonneg_left
        (pow_le_pow_left₀ (abs_nonneg _) hposition _) (abs_nonneg _)

noncomputable def bumpNumeratorAbsUpper2536 : ℕ → ℝ → ℝ
  | 0, _ => 1
  | 1, t => 60 * t
  | 2, t => 60 + 3480 * t ^ 2 + 180 * t ^ 4
  | 3, t => 10080 * t + 193680 * t ^ 3 + 31680 * t ^ 5 + 720 * t ^ 7
  | 4, t => 10080 + 1085040 * t ^ 2 + 10189440 * t ^ 4 +
      3575520 * t ^ 6 + 266400 * t ^ 8 + 3600 * t ^ 10
  | _, _ => 0

theorem bumpNumeratorAbsUpper2536_nonneg (order : ℕ) {t : ℝ} (ht : 0 ≤ t) :
    0 ≤ bumpNumeratorAbsUpper2536 order t := by
  unfold bumpNumeratorAbsUpper2536
  split <;> positivity

theorem bumpNumerator_abs_le_local2536 (order : ℕ) (horder : order ≤ 4)
    {position t : ℝ} (hposition : |position| ≤ t) :
    |bumpNumerator2350 order position| ≤ bumpNumeratorAbsUpper2536 order t := by
  interval_cases order
  · simp [bumpNumerator2350, bumpNumeratorAbsUpper2536]
  · have h := polynomialAbsUpperLocal2536 (Finset.univ : Finset (Fin 1))
      ![(-60 : ℝ)] ![1] hposition
    convert h using 1 <;>
      norm_num [bumpNumerator2350, bumpNumeratorAbsUpper2536, Fin.sum_univ_succ]
  · have h := polynomialAbsUpperLocal2536 (Finset.univ : Finset (Fin 3))
      ![(-60 : ℝ), 3480, 180] ![0, 2, 4] hposition
    convert h using 1 <;>
      norm_num [bumpNumerator2350, bumpNumeratorAbsUpper2536, Fin.sum_univ_succ] <;>
      ring_nf
  · have h := polynomialAbsUpperLocal2536 (Finset.univ : Finset (Fin 4))
      ![(10080 : ℝ), -193680, -31680, -720] ![1, 3, 5, 7] hposition
    convert h using 1 <;>
      norm_num [bumpNumerator2350, bumpNumeratorAbsUpper2536, Fin.sum_univ_succ] <;>
      ring_nf
  · have h := polynomialAbsUpperLocal2536 (Finset.univ : Finset (Fin 6))
      ![(10080 : ℝ), -1085040, 10189440, 3575520, 266400, 3600]
      ![0, 2, 4, 6, 8, 10] hposition
    convert h using 1 <;>
      norm_num [bumpNumerator2350, bumpNumeratorAbsUpper2536, Fin.sum_univ_succ] <;>
      ring_nf

noncomputable def localCoupledBumpUpper2536 (order : ℕ) (radius near far : ℝ) : ℝ :=
  bumpNumeratorAbsUpper2536 order far *
    ((1 - near ^ 2)⁻¹ ^ (2 * order) * Real.exp (-30 * (1 - near ^ 2)⁻¹)) /
      radius ^ order

theorem widthBump_iteratedDeriv_abs_le_local2536
    (order : ℕ) (horder : order ≤ 4) {radius position near far : ℝ}
    (hradius : 0 < radius) (hnear : 0 ≤ near) (hnear_one : near < 1)
    (hlower : near ≤ |position / radius|) (hupper : |position / radius| ≤ far) :
    |iteratedDeriv order (widthBump radius) position| ≤
      localCoupledBumpUpper2536 order radius near far := by
  have hfar : 0 ≤ far := (abs_nonneg _).trans hupper
  have hpoly := bumpNumeratorAbsUpper2536_nonneg order hfar
  have hqnear : 0 < 1 - near ^ 2 := by nlinarith
  have htnear : 1 ≤ (1 - near ^ 2)⁻¹ := by
    rw [inv_eq_one_div, le_div_iff₀ hqnear]
    nlinarith [sq_nonneg near]
  rw [widthBump_iteratedDeriv_global2350 order horder hradius]
  split_ifs with hinside
  · have hq : 0 < bumpDeficit2350 (position / radius) :=
      familyDeficit2345_pos hradius hinside
    have hqle : bumpDeficit2350 (position / radius) ≤ 1 - near ^ 2 := by
      have hs := pow_le_pow_left₀ hnear hlower 2
      simpa [bumpDeficit2350, sq_abs] using sub_le_sub_left hs 1
    have ht : (1 - near ^ 2)⁻¹ ≤ (bumpDeficit2350 (position / radius))⁻¹ := by
      simpa only [one_div] using one_div_le_one_div_of_le hq hqle
    have hpower : ((2 * order : ℕ) : ℝ) ≤ 30 * (1 - near ^ 2)⁻¹ := by
      have hn : ((2 * order : ℕ) : ℝ) ≤ 8 := by exact_mod_cast (show 2 * order ≤ 8 by omega)
      linarith
    have hexp := powerExp_le_at_lower2536 (inv_pos.mpr hqnear) ht hpower
    have hnum := bumpNumerator_abs_le_local2536 order horder hupper
    rw [scaledBumpJet2350, abs_div, abs_of_pos (pow_pos hradius order)]
    apply div_le_div_of_nonneg_right _ (pow_nonneg hradius.le order)
    rw [bumpJet2350, abs_mul, abs_mul, abs_of_pos (Real.exp_pos _),
      abs_of_nonneg (pow_nonneg (inv_nonneg.mpr hq.le) _), div_eq_mul_inv]
    change Real.exp (-30 * (bumpDeficit2350 (position / radius))⁻¹) *
      (bumpDeficit2350 (position / radius))⁻¹ ^ (2 * order) *
      |bumpNumerator2350 order (position / radius)| ≤ _
    calc
      _ = |bumpNumerator2350 order (position / radius)| *
          ((bumpDeficit2350 (position / radius))⁻¹ ^ (2 * order) *
            Real.exp (-30 * (bumpDeficit2350 (position / radius))⁻¹)) := by ring
      _ ≤ _ := mul_le_mul hnum hexp
        (mul_nonneg (pow_nonneg (inv_nonneg.mpr hq.le) _) (Real.exp_nonneg _)) hpoly
  · rw [abs_zero]
    unfold localCoupledBumpUpper2536
    positivity

end ConnesWeilRH.Dev
