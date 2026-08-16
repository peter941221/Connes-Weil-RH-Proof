import ConnesWeilRH.Dev.C1XiVerticalFunctional

/-!
# C1XiContourDecay - vertical decay for the common contour owner

The existing compact-support estimate is stated on one unit Mellin strip.
This module transports that estimate to three adjacent strips, covering the
centered interval needed by the xi functional equation, and then adds the
reflected weight by the triangle inequality.

No contour limit, residue calculation, explicit-formula equality, or RH claim
is introduced here.
-/

namespace ConnesWeilRH
namespace Source
namespace C1XiContourDecay

open MeasureTheory
open CC20YoshidaConvolution
open CC20YoshidaNearZeros
open CCM25Concrete.CompactLogConvolution
open C1SpectralWeil
open C1XiVerticalFunctional
open scoped Interval

/-- Translate the compact-support estimate from `[0, 1]` to an arbitrary unit
Mellin strip.  The exponential weight is only a change of owner coordinate;
`laplaceAt_exponentialWeight_eq` identifies it with the original transform. -/
theorem exists_uniform_laplaceAt_vertical_quadratic_decay_on_unit_strip
    (F : CompactLogTest) (a : Real) :
    ∃ C : Real, 0 ≤ C ∧
      ∀ sigma ∈ Set.Icc a (a + 1), ∀ t : Real,
        ‖t / (2 * Real.pi)‖ ^ 2 *
            ‖CompactLogTest.laplaceAt F
              ((sigma : Complex) + (t : Complex) * Complex.I)‖ ≤ C := by
  obtain ⟨C, hC, hdecay⟩ :=
    exists_uniform_compactLog_laplaceAt_vertical_quadratic_decay
      (CompactLogTest.exponentialWeight F a)
  refine ⟨C, hC, ?_⟩
  intro sigma hsigma t
  let u : Real := sigma - a
  have hu : u ∈ Set.Icc (0 : Real) 1 := by
    constructor <;> dsimp [u] <;> linarith [hsigma.1, hsigma.2]
  have hbound := hdecay u hu t
  rw [laplaceAt_exponentialWeight_eq] at hbound
  have harg :
      ((u : Complex) + (t : Complex) * Complex.I) + (a : Complex) =
        (sigma : Complex) + (t : Complex) * Complex.I := by
    dsimp [u]
    push_cast
    ring
  simpa only [harg] using hbound

/-- The three unit strips `[-3/2,-1/2]`, `[-1/2,1/2]`, and
`[1/2,3/2]` give one bound on the whole centered interval. -/
theorem exists_uniform_laplaceAt_vertical_quadratic_decay_on_centered_extended_strip
    (F : CompactLogTest) :
    ∃ C : Real, 0 ≤ C ∧
      ∀ sigma ∈ Set.Icc (-3 / 2 : Real) (3 / 2 : Real), ∀ t : Real,
        ‖t / (2 * Real.pi)‖ ^ 2 *
            ‖CompactLogTest.laplaceAt F
              ((sigma : Complex) + (t : Complex) * Complex.I)‖ ≤ C := by
  obtain ⟨Cneg, hCneg, hneg⟩ :=
    exists_uniform_laplaceAt_vertical_quadratic_decay_on_unit_strip F
      (-3 / 2 : Real)
  obtain ⟨Cmid, hCmid, hmid⟩ :=
    exists_uniform_laplaceAt_vertical_quadratic_decay_on_unit_strip F
      (-1 / 2 : Real)
  obtain ⟨Cpos, hCpos, hpos⟩ :=
    exists_uniform_laplaceAt_vertical_quadratic_decay_on_unit_strip F
      (1 / 2 : Real)
  refine ⟨max Cneg (max Cmid Cpos),
    le_trans hCneg (le_max_left _ _), ?_⟩
  intro sigma hsigma t
  by_cases hleft : sigma ≤ (-1 / 2 : Real)
  · have hstrip : sigma ∈ Set.Icc (-3 / 2 : Real) ((-3 / 2 : Real) + 1) := by
      constructor <;> linarith [hsigma.1, hleft]
    exact (hneg sigma hstrip t).trans (le_max_left _ _)
  · by_cases hmiddle : sigma ≤ (1 / 2 : Real)
    · have hstrip : sigma ∈ Set.Icc (-1 / 2 : Real) ((-1 / 2 : Real) + 1) := by
        constructor <;> linarith [hsigma.1, hleft, hmiddle]
      exact (hmid sigma hstrip t).trans
        (le_trans (le_max_left Cmid Cpos)
          (le_max_right Cneg (max Cmid Cpos)))
    · have hstrip : sigma ∈ Set.Icc (1 / 2 : Real) ((1 / 2 : Real) + 1) := by
        constructor <;> linarith [hsigma.2, hmiddle]
      exact (hpos sigma hstrip t).trans
        (le_trans (le_max_right _ _) (le_max_right _ _))

/-- The centered Laplace weight has a uniform quadratic bound when the real
part of its outer xi coordinate lies in `[-1,2]`. -/
theorem exists_uniform_centeredLaplaceWeight_vertical_quadratic_decay
    (F : CompactLogTest) :
    ∃ C : Real, 0 ≤ C ∧
      ∀ sigma ∈ Set.Icc (-1 : Real) 2, ∀ t : Real,
        ‖t / (2 * Real.pi)‖ ^ 2 *
            ‖centeredLaplaceWeight F (verticalPoint sigma t)‖ ≤ C := by
  obtain ⟨C, hC, hdecay⟩ :=
    exists_uniform_laplaceAt_vertical_quadratic_decay_on_centered_extended_strip F
  refine ⟨C, hC, ?_⟩
  intro sigma hsigma t
  have hcenter : sigma - (1 / 2 : Real) ∈
      Set.Icc (-3 / 2 : Real) (3 / 2 : Real) := by
    constructor <;> linarith [hsigma.1, hsigma.2]
  have hbound := hdecay (sigma - (1 / 2 : Real)) hcenter t
  have harg :
      centeredLaplaceWeight F (verticalPoint sigma t) =
        CompactLogTest.laplaceAt F
          (((sigma - (1 / 2 : Real) : Real) : Complex) +
            (t : Complex) * Complex.I) := by
    unfold centeredLaplaceWeight verticalPoint
    congr 1
    push_cast
    ring
  rw [harg]
  exact hbound

/-- Translate the fourth-order compact-support estimate from `[0, 1]` to an
arbitrary unit Mellin strip. -/
theorem exists_uniform_laplaceAt_vertical_quartic_decay_on_unit_strip
    (F : CompactLogTest) (a : Real) :
    ∃ C : Real, 0 ≤ C ∧
      ∀ sigma ∈ Set.Icc a (a + 1), ∀ t : Real,
        ‖t / (2 * Real.pi)‖ ^ 4 *
            ‖CompactLogTest.laplaceAt F
              ((sigma : Complex) + (t : Complex) * Complex.I)‖ ≤ C := by
  obtain ⟨C, hC, hdecay⟩ :=
    exists_uniform_compactLog_laplaceAt_vertical_quartic_decay
      (CompactLogTest.exponentialWeight F a)
  refine ⟨C, hC, ?_⟩
  intro sigma hsigma t
  let u : Real := sigma - a
  have hu : u ∈ Set.Icc (0 : Real) 1 := by
    constructor <;> dsimp [u] <;> linarith [hsigma.1, hsigma.2]
  have hbound := hdecay u hu t
  rw [laplaceAt_exponentialWeight_eq] at hbound
  have harg :
      ((u : Complex) + (t : Complex) * Complex.I) + (a : Complex) =
        (sigma : Complex) + (t : Complex) * Complex.I := by
    dsimp [u]
    push_cast
    ring
  simpa only [harg] using hbound

/-- Three translated unit strips give fourth-order decay on the full centered
interval needed by the wide `[-1,2]` xi rectangle. -/
theorem exists_uniform_laplaceAt_vertical_quartic_decay_on_centered_extended_strip
    (F : CompactLogTest) :
    ∃ C : Real, 0 ≤ C ∧
      ∀ sigma ∈ Set.Icc (-3 / 2 : Real) (3 / 2 : Real), ∀ t : Real,
        ‖t / (2 * Real.pi)‖ ^ 4 *
            ‖CompactLogTest.laplaceAt F
              ((sigma : Complex) + (t : Complex) * Complex.I)‖ ≤ C := by
  obtain ⟨Cneg, hCneg, hneg⟩ :=
    exists_uniform_laplaceAt_vertical_quartic_decay_on_unit_strip F
      (-3 / 2 : Real)
  obtain ⟨Cmid, hCmid, hmid⟩ :=
    exists_uniform_laplaceAt_vertical_quartic_decay_on_unit_strip F
      (-1 / 2 : Real)
  obtain ⟨Cpos, hCpos, hpos⟩ :=
    exists_uniform_laplaceAt_vertical_quartic_decay_on_unit_strip F
      (1 / 2 : Real)
  refine ⟨max Cneg (max Cmid Cpos),
    le_trans hCneg (le_max_left _ _), ?_⟩
  intro sigma hsigma t
  by_cases hleft : sigma ≤ (-1 / 2 : Real)
  · have hstrip : sigma ∈ Set.Icc (-3 / 2 : Real) ((-3 / 2 : Real) + 1) := by
      constructor <;> linarith [hsigma.1, hleft]
    exact (hneg sigma hstrip t).trans (le_max_left _ _)
  · by_cases hmiddle : sigma ≤ (1 / 2 : Real)
    · have hstrip : sigma ∈ Set.Icc (-1 / 2 : Real) ((-1 / 2 : Real) + 1) := by
        constructor <;> linarith [hsigma.1, hleft, hmiddle]
      exact (hmid sigma hstrip t).trans
        (le_trans (le_max_left Cmid Cpos)
          (le_max_right Cneg (max Cmid Cpos)))
    · have hstrip : sigma ∈ Set.Icc (1 / 2 : Real) ((1 / 2 : Real) + 1) := by
        constructor <;> linarith [hsigma.2, hmiddle]
      exact (hpos sigma hstrip t).trans
        (le_trans (le_max_right _ _) (le_max_right _ _))

/-- The centered contour weight has uniform fourth-order decay on the fixed
wide strip `[-1,2]`. -/
theorem exists_uniform_centeredLaplaceWeight_vertical_quartic_decay_on_wideStrip
    (F : CompactLogTest) :
    ∃ C : Real, 0 ≤ C ∧
      ∀ sigma ∈ Set.Icc (-1 : Real) 2, ∀ t : Real,
        ‖t / (2 * Real.pi)‖ ^ 4 *
            ‖centeredLaplaceWeight F (verticalPoint sigma t)‖ ≤ C := by
  obtain ⟨C, hC, hdecay⟩ :=
    exists_uniform_laplaceAt_vertical_quartic_decay_on_centered_extended_strip F
  refine ⟨C, hC, ?_⟩
  intro sigma hsigma t
  have hcenter : sigma - (1 / 2 : Real) ∈
      Set.Icc (-3 / 2 : Real) (3 / 2 : Real) := by
    constructor <;> linarith [hsigma.1, hsigma.2]
  have hbound := hdecay (sigma - (1 / 2 : Real)) hcenter t
  have harg :
      centeredLaplaceWeight F (verticalPoint sigma t) =
        CompactLogTest.laplaceAt F
          (((sigma - (1 / 2 : Real) : Real) : Complex) +
            (t : Complex) * Complex.I) := by
    unfold centeredLaplaceWeight verticalPoint
    congr 1
    push_cast
    ring
  rw [harg]
  exact hbound

/-- On the critical strip, the centered weight has fourth-order decay along
the horizontal contour sides. -/
theorem exists_uniform_centeredLaplaceWeight_vertical_quartic_decay_on_criticalStrip
    (F : CompactLogTest) :
    ∃ C : Real, 0 ≤ C ∧
      ∀ sigma ∈ Set.Icc (0 : Real) 1, ∀ t : Real,
        ‖t / (2 * Real.pi)‖ ^ 4 *
            ‖centeredLaplaceWeight F (verticalPoint sigma t)‖ ≤ C := by
  obtain ⟨C, hC, hdecay⟩ :=
    exists_uniform_centered_laplaceAt_vertical_quartic_decay F
  refine ⟨C, hC, ?_⟩
  intro sigma hsigma t
  have hbound := hdecay sigma hsigma t
  have harg :
      centeredLaplaceWeight F (verticalPoint sigma t) =
        CompactLogTest.laplaceAt F
          (((sigma - (1 / 2 : Real) : Real) : Complex) +
            (t : Complex) * Complex.I) := by
    unfold centeredLaplaceWeight verticalPoint
    congr 1
    push_cast
    ring
  rw [harg]
  exact hbound

/-- The symmetric right-line weight obeys the same type of bound, with the
factor `2` coming only from the triangle inequality for the two reflected
Laplace transforms. -/
theorem exists_uniform_symmetrizedLaplaceWeight_vertical_quadratic_decay
    (F : CompactLogTest) :
    ∃ C : Real, 0 ≤ C ∧
      ∀ sigma ∈ Set.Icc (-1 : Real) 2, ∀ t : Real,
        ‖t / (2 * Real.pi)‖ ^ 2 *
            ‖symmetrizedLaplaceWeight F (verticalPoint sigma t)‖ ≤ C := by
  obtain ⟨C, hC, hdecay⟩ :=
    exists_uniform_centeredLaplaceWeight_vertical_quadratic_decay F
  refine ⟨2 * C, by positivity, ?_⟩
  intro sigma hsigma t
  have hreflect : (1 - sigma : Real) ∈ Set.Icc (-1 : Real) 2 := by
    constructor <;> linarith [hsigma.1, hsigma.2]
  have hleft := hdecay sigma hsigma t
  have hright := hdecay (1 - sigma) hreflect (-t)
  have hpoint : verticalPoint (1 - sigma) (-t) =
      1 - verticalPoint sigma t :=
    verticalPoint_reflection sigma t
  rw [hpoint] at hright
  have hquot :
      ‖(-t) / (2 * Real.pi)‖ ^ 2 =
        ‖t / (2 * Real.pi)‖ ^ 2 := by
    rw [neg_div, norm_neg]
  rw [hquot] at hright
  calc
    ‖t / (2 * Real.pi)‖ ^ 2 *
          ‖symmetrizedLaplaceWeight F (verticalPoint sigma t)‖ ≤
        ‖t / (2 * Real.pi)‖ ^ 2 *
          (‖centeredLaplaceWeight F (verticalPoint sigma t)‖ +
            ‖centeredLaplaceWeight F (1 - verticalPoint sigma t)‖) := by
      apply mul_le_mul_of_nonneg_left _ (sq_nonneg _)
      exact norm_add_le _ _
    _ = (‖t / (2 * Real.pi)‖ ^ 2 *
          ‖centeredLaplaceWeight F (verticalPoint sigma t)‖) +
        (‖t / (2 * Real.pi)‖ ^ 2 *
          ‖centeredLaplaceWeight F (1 - verticalPoint sigma t)‖) := by
      rw [mul_add]
    _ ≤ C + C := add_le_add hleft hright
    _ = 2 * C := by ring

end C1XiContourDecay
end Source
end ConnesWeilRH
