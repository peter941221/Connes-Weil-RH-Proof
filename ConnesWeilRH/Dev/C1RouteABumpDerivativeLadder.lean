import ConnesWeilRH.Dev.C1RouteABumpEnvelope
import ConnesWeilRH.Dev.C1RouteAExternalOwnerZeroExtension
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas

namespace ConnesWeilRH.Dev

open scoped Topology BigOperators ContDiff
open ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit

noncomputable def bumpDeficit2350 (position : ℝ) : ℝ := 1 - position ^ 2

noncomputable def bumpNumerator2350 : ℕ → ℝ → ℝ
  | 0, _ => 1
  | 1, position => -60 * position
  | 2, position => -60 + 3480 * position ^ 2 + 180 * position ^ 4
  | 3, position => 10080 * position - 193680 * position ^ 3 -
      31680 * position ^ 5 - 720 * position ^ 7
  | 4, position => 10080 - 1085040 * position ^ 2 + 10189440 * position ^ 4 +
      3575520 * position ^ 6 + 266400 * position ^ 8 + 3600 * position ^ 10
  | _, _ => 0

noncomputable def bumpNumeratorPrime2350 : ℕ → ℝ → ℝ
  | 0, _ => 0
  | 1, _ => -60
  | 2, position => 6960 * position + 720 * position ^ 3
  | 3, position => 10080 - 581040 * position ^ 2 -
      158400 * position ^ 4 - 5040 * position ^ 6
  | _, _ => 0

def bumpConstant2350 : ℕ → ℕ
  | 0 => 1
  | 1 => 60
  | 2 => 3720
  | 3 => 236160
  | 4 => 15130080
  | _ => 0

noncomputable def bumpJet2350 (order : ℕ) (polynomial : ℝ → ℝ) (position : ℝ) : ℝ :=
  Real.exp (-30 / bumpDeficit2350 position) *
    (bumpDeficit2350 position)⁻¹ ^ (2 * order) * polynomial position

noncomputable def scaledBumpJet2350 (order : ℕ) (radius position : ℝ) : ℝ :=
  bumpJet2350 order (bumpNumerator2350 order) (position / radius) / radius ^ order

theorem bumpDeficit2350_hasDerivAt (position : ℝ) :
    HasDerivAt bumpDeficit2350 (-2 * position) position := by
  convert (hasDerivAt_const position (1 : ℝ)).sub ((hasDerivAt_id position).pow 2) using 1
  dsimp [bumpDeficit2350]
  ring

theorem bumpNumerator2350_hasDerivAt (order : ℕ) (horder : order ≤ 3) (position : ℝ) :
    HasDerivAt (bumpNumerator2350 order) (bumpNumeratorPrime2350 order position) position := by
  interval_cases order
  · exact hasDerivAt_const position 1
  · convert (hasDerivAt_id position).const_mul (-60 : ℝ) using 1
    simp [bumpNumeratorPrime2350]
  · convert ((hasDerivAt_const position (-60 : ℝ)).add
      (((hasDerivAt_id position).pow 2).const_mul 3480)).add
      (((hasDerivAt_id position).pow 4).const_mul 180) using 1
    dsimp [bumpNumerator2350, bumpNumeratorPrime2350]
    ring
  · convert (((hasDerivAt_id position).const_mul (10080 : ℝ)).sub
      (((hasDerivAt_id position).pow 3).const_mul 193680)).sub
      (((hasDerivAt_id position).pow 5).const_mul 31680) |>.sub
      (((hasDerivAt_id position).pow 7).const_mul 720) using 1
    dsimp [bumpNumerator2350, bumpNumeratorPrime2350]
    ring

theorem bumpNumerator2350_recurrence (order : ℕ) (horder : order ≤ 3) (position : ℝ) :
    bumpNumerator2350 (order + 1) position =
      bumpDeficit2350 position ^ 2 * bumpNumeratorPrime2350 order position +
        (-60 * position + 4 * (order : ℝ) * position * bumpDeficit2350 position) *
          bumpNumerator2350 order position := by
  interval_cases order <;>
    norm_num [bumpNumerator2350, bumpNumeratorPrime2350, bumpDeficit2350] <;> ring

theorem bumpJet2350_hasDerivAt (order : ℕ) (horder : order ≤ 3)
    {polynomial : ℝ → ℝ} {polynomialPrime position : ℝ}
    (hpolynomial : HasDerivAt polynomial polynomialPrime position)
    (hdeficit : bumpDeficit2350 position ≠ 0) :
    HasDerivAt (bumpJet2350 order polynomial)
      (Real.exp (-30 / bumpDeficit2350 position) *
        (bumpDeficit2350 position)⁻¹ ^ (2 * (order + 1)) *
        (bumpDeficit2350 position ^ 2 * polynomialPrime +
          (-60 * position + 4 * (order : ℝ) * position * bumpDeficit2350 position) *
            polynomial position)) position := by
  have hdeficitDeriv := bumpDeficit2350_hasDerivAt position
  have hlog := (hasDerivAt_const position (-30 : ℝ)).div hdeficitDeriv hdeficit
  have hjet := ((hlog.exp).mul ((hdeficitDeriv.inv hdeficit).pow (2 * order))).mul hpolynomial
  convert hjet using 1
  dsimp [bumpJet2350]
  interval_cases order <;> norm_num <;> field_simp [hdeficit] <;> ring

theorem normalizedBumpJet2350_hasDerivAt (order : ℕ) (horder : order ≤ 3)
    {position : ℝ} (hdeficit : bumpDeficit2350 position ≠ 0) :
    HasDerivAt (bumpJet2350 order (bumpNumerator2350 order))
      (bumpJet2350 (order + 1) (bumpNumerator2350 (order + 1)) position) position := by
  have hjet := bumpJet2350_hasDerivAt order horder
    (bumpNumerator2350_hasDerivAt order horder position) hdeficit
  simpa only [bumpJet2350, ← bumpNumerator2350_recurrence order horder position] using hjet

theorem scaledBumpJet2350_hasDerivAt (order : ℕ) (horder : order ≤ 3)
    {radius position : ℝ} (hradius : 0 < radius) (hinside : |position| < radius) :
    HasDerivAt (scaledBumpJet2350 order radius)
      (scaledBumpJet2350 (order + 1) radius position) position := by
  have hdeficit : bumpDeficit2350 (position / radius) ≠ 0 :=
    ne_of_gt (familyDeficit2345_pos hradius hinside)
  have hjet := ((normalizedBumpJet2350_hasDerivAt order horder hdeficit).comp position
    ((hasDerivAt_id position).div_const radius)).div_const (radius ^ order)
  convert hjet using 1
  dsimp [scaledBumpJet2350]
  rw [pow_succ]
  field_simp

theorem widthBump_iteratedDeriv_inside2350 (order : ℕ) (horder : order ≤ 4)
    {radius position : ℝ} (hradius : 0 < radius) (hinside : |position| < radius) :
    iteratedDeriv order (widthBump radius) position = scaledBumpJet2350 order radius position := by
  induction order generalizing position with
  | zero =>
    simp [scaledBumpJet2350, bumpJet2350, bumpNumerator2350, bumpDeficit2350,
      widthBump, if_pos hinside]
  | succ order ih =>
    have hprevious : order ≤ 4 := by omega
    have hstep : order ≤ 3 := by omega
    have heq : iteratedDeriv order (widthBump radius) =ᶠ[𝓝 position]
        scaledBumpJet2350 order radius := by
      filter_upwards [IsOpen.mem_nhds (isOpen_lt continuous_abs continuous_const) hinside]
        with coordinate hcoordinate
      exact ih hprevious hcoordinate
    rw [iteratedDeriv_succ, heq.deriv_eq]
    exact (scaledBumpJet2350_hasDerivAt order hstep hradius hinside).deriv

theorem widthBump_iteratedDeriv_strictOutside2350 (order : ℕ) (radius position : ℝ)
    (houtside : radius < |position|) :
    iteratedDeriv order (widthBump radius) position = 0 := by
  have heq : widthBump radius =ᶠ[𝓝 position] (fun _ => (0 : ℝ)) := by
    filter_upwards [IsOpen.mem_nhds (isOpen_lt continuous_const continuous_abs) houtside]
      with coordinate hcoordinate
    simp [widthBump, not_lt.mpr hcoordinate.le]
  rw [heq.iteratedDeriv_eq order]
  simp

theorem widthBump_iteratedDeriv_outside2350 (order : ℕ) {radius position : ℝ}
    (hradius : 0 < radius) (houtside : radius ≤ |position|) :
    iteratedDeriv order (widthBump radius) position = 0 := by
  let derivative := iteratedDeriv order (widthBump radius)
  have hcontinuous : Continuous derivative :=
    (widthBump_contDiff radius hradius).continuous_iteratedDeriv order
      (by exact_mod_cast (le_top : (order : ℕ∞) ≤ ⊤))
  have hclosed : IsClosed {coordinate | derivative coordinate = 0} :=
    isClosed_eq hcontinuous continuous_const
  have hright : Set.Ici radius ⊆ {coordinate | derivative coordinate = 0} := by
    rw [← closure_Ioi]
    apply closure_minimal _ hclosed
    intro coordinate hcoordinate
    exact widthBump_iteratedDeriv_strictOutside2350 order radius coordinate
      (lt_of_lt_of_le hcoordinate (le_abs_self coordinate))
  have hleft : Set.Iic (-radius) ⊆ {coordinate | derivative coordinate = 0} := by
    rw [← closure_Iio]
    apply closure_minimal _ hclosed
    intro coordinate hcoordinate
    apply widthBump_iteratedDeriv_strictOutside2350 order radius coordinate
    change coordinate < -radius at hcoordinate
    have habs := neg_le_abs coordinate
    linarith
  rcases le_abs.mp houtside with hposition | hposition
  · exact hright hposition
  · apply hleft
    change position ≤ -radius
    linarith

theorem widthBump_iteratedDeriv_global2350 (order : ℕ) (horder : order ≤ 4)
    {radius position : ℝ} (hradius : 0 < radius) :
    iteratedDeriv order (widthBump radius) position =
      if |position| < radius then scaledBumpJet2350 order radius position else 0 := by
  split_ifs with hinside
  · exact widthBump_iteratedDeriv_inside2350 order horder hradius hinside
  · exact widthBump_iteratedDeriv_outside2350 order hradius (not_lt.mp hinside)


theorem bumpNumerator2350_abs_le (order : ℕ) (horder : order ≤ 4)
    {position : ℝ} (hposition : |position| ≤ 1) :
    |bumpNumerator2350 order position| ≤ (bumpConstant2350 order : ℝ) := by
  interval_cases order
  · norm_num [bumpNumerator2350, bumpConstant2350]
  · have hbound := polynomialAbsUpper2349 (Finset.univ : Finset (Fin 1))
      ![(-60 : ℝ)] ![1] hposition
    convert hbound using 1 <;>
      norm_num [bumpNumerator2350, bumpConstant2350, Fin.sum_univ_succ]
  · have hbound := polynomialAbsUpper2349 (Finset.univ : Finset (Fin 3))
      ![(-60 : ℝ), 3480, 180] ![0, 2, 4] hposition
    convert hbound using 1 <;>
      norm_num [bumpNumerator2350, bumpConstant2350, Fin.sum_univ_succ]
    congr 1
    ring
  · have hbound := polynomialAbsUpper2349 (Finset.univ : Finset (Fin 4))
      ![(10080 : ℝ), -193680, -31680, -720] ![1, 3, 5, 7] hposition
    convert hbound using 1 <;>
      norm_num [bumpNumerator2350, bumpConstant2350, Fin.sum_univ_succ]
    congr 1
    ring
  · have hbound := polynomialAbsUpper2349 (Finset.univ : Finset (Fin 6))
      ![(10080 : ℝ), -1085040, 10189440, 3575520, 266400, 3600]
      ![0, 2, 4, 6, 8, 10] hposition
    convert hbound using 1 <;>
      norm_num [bumpNumerator2350, bumpConstant2350, Fin.sum_univ_succ]
    congr 1
    ring

theorem bumpJet2350_abs_le (order : ℕ) (horder : order ≤ 4)
    {position : ℝ} (hposition : |position| < 1) :
    |bumpJet2350 order (bumpNumerator2350 order) position| ≤
      (bumpConstant2350 order : ℝ) * Real.exp (-30) := by
  have hdeficit : 0 < bumpDeficit2350 position := by
    dsimp [bumpDeficit2350]
    nlinarith [sq_abs position, abs_nonneg position]
  have hinverse : 1 ≤ (bumpDeficit2350 position)⁻¹ := by
    rw [inv_eq_one_div, le_div_iff₀ hdeficit]
    dsimp [bumpDeficit2350]
    nlinarith [sq_nonneg position]
  have hexp := powerExpUpper2349 hinverse
    (show ((2 * order : ℕ) : ℝ) ≤ 30 by exact_mod_cast (show 2 * order ≤ 30 by omega))
  have hconstant : (0 : ℝ) ≤ bumpConstant2350 order := Nat.cast_nonneg _
  rw [bumpJet2350, div_eq_mul_inv, abs_mul, abs_mul, abs_of_pos (Real.exp_pos _),
    abs_of_nonneg (pow_nonneg (inv_nonneg.mpr hdeficit.le) _)]
  calc
    _ ≤ Real.exp (-30 * (bumpDeficit2350 position)⁻¹) *
        (bumpDeficit2350 position)⁻¹ ^ (2 * order) * (bumpConstant2350 order : ℝ) :=
      mul_le_mul_of_nonneg_left (bumpNumerator2350_abs_le order horder hposition.le)
        (mul_nonneg (Real.exp_nonneg _) (pow_nonneg (inv_nonneg.mpr hdeficit.le) _))
    _ = (bumpConstant2350 order : ℝ) *
        ((bumpDeficit2350 position)⁻¹ ^ (2 * order) *
          Real.exp (-30 * (bumpDeficit2350 position)⁻¹)) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left hexp hconstant

theorem scaledBumpJet2350_abs_le (order : ℕ) (horder : order ≤ 4)
    {radius position : ℝ} (hradius : 0 < radius) (hinside : |position| < radius) :
    |scaledBumpJet2350 order radius position| ≤
      (bumpConstant2350 order : ℝ) * Real.exp (-30) / radius ^ order := by
  have hratio : |position / radius| < 1 := by
    rw [abs_div, abs_of_pos hradius, div_lt_one hradius]
    exact hinside
  rw [scaledBumpJet2350, abs_div, abs_of_pos (pow_pos hradius order)]
  exact div_le_div_of_nonneg_right (bumpJet2350_abs_le order horder hratio)
    (pow_nonneg hradius.le _)

theorem widthBump_iteratedDeriv_abs_le2350 (order : ℕ) (horder : order ≤ 4)
    {radius position : ℝ} (hradius : 0 < radius) :
    |iteratedDeriv order (widthBump radius) position| ≤
      (bumpConstant2350 order : ℝ) * Real.exp (-30) / radius ^ order := by
  rw [widthBump_iteratedDeriv_global2350 order horder hradius]
  split_ifs with hinside
  · exact scaledBumpJet2350_abs_le order horder hradius hinside
  · rw [abs_zero]
    positivity

end ConnesWeilRH.Dev
