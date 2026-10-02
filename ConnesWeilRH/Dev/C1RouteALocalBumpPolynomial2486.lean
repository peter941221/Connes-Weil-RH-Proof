import ConnesWeilRH.Dev.C1RouteALocalBumpEnvelope2485

/-  2486: local absolute envelope for the order-0..2 bump numerators.

These are the exact polynomial factors used by the local MPFR evaluator.  The
lemma is parameterized by an interval bound `|position| ≤ t`; it is not a
numeric certificate for any particular cell. -/

namespace ConnesWeilRH.Dev

noncomputable def bumpNumeratorAbsUpper2486 : ℕ → ℝ → ℝ
  | 0, _ => 1
  | 1, t => 60 * t
  | 2, t => 60 + 3480 * t ^ 2 + 180 * t ^ 4
  | _, _ => 0

theorem bumpNumerator_abs_le_local2486
    (order : ℕ) (horder : order ≤ 2) {position t : ℝ}
    (ht : 0 ≤ t) (hposition : |position| ≤ t) :
    |bumpNumerator2350 order position| ≤ bumpNumeratorAbsUpper2486 order t := by
  interval_cases order
  · simp [bumpNumerator2350, bumpNumeratorAbsUpper2486]
  · simp only [bumpNumerator2350, bumpNumeratorAbsUpper2486]
    rw [abs_mul]
    have h60abs : |(-60 : ℝ)| = 60 := by norm_num
    rw [h60abs]
    exact mul_le_mul_of_nonneg_left hposition (by norm_num)
  · have hpos2 : position ^ 2 ≤ t ^ 2 := by
      have h := (sq_le_sq₀ (abs_nonneg position) ht).2 hposition
      simpa [sq_abs] using h
    have hpos4 : position ^ 4 ≤ t ^ 4 := by
      have h := pow_le_pow_left₀ (by positivity) hpos2 2
      convert h using 1 <;> ring
    have h3480 : 0 ≤ (3480 : ℝ) * position ^ 2 :=
      mul_nonneg (by norm_num) (sq_nonneg position)
    have h180 : 0 ≤ (180 : ℝ) * position ^ 4 :=
      mul_nonneg (by norm_num) (by positivity)
    calc
      |bumpNumerator2350 2 position| ≤
          |(-60 : ℝ)| + |3480 * position ^ 2| + |180 * position ^ 4| := by
            rw [bumpNumerator2350]
            calc
              |-60 + 3480 * position ^ 2 + 180 * position ^ 4| ≤
                  |-60 + 3480 * position ^ 2| + |180 * position ^ 4| :=
                by simpa only [Real.norm_eq_abs] using
                  (norm_add_le (-60 + 3480 * position ^ 2) (180 * position ^ 4))
              _ ≤ (|-60| + |3480 * position ^ 2|) + |180 * position ^ 4| := by
                gcongr
                simpa only [Real.norm_eq_abs] using
                  (norm_add_le (-60 : ℝ) (3480 * position ^ 2))
      _ = 60 + 3480 * position ^ 2 + 180 * position ^ 4 := by
            have h60abs : |(-60 : ℝ)| = 60 := by norm_num
            rw [h60abs, abs_of_nonneg h3480, abs_of_nonneg h180]
      _ ≤ 60 + 3480 * t ^ 2 + 180 * t ^ 4 := by
            gcongr

end ConnesWeilRH.Dev
